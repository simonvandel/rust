use rustc_data_structures::fx::FxHashMap;
use rustc_middle::{
    mir::visit::MutVisitor,
    mir::visit::PlaceContext,
    mir::visit::Visitor,
    mir::Body,
    mir::Operand,
    mir::{BorrowKind, Local, Location, Place, PlaceRef, ProjectionElem, Rvalue, Statement},
    ty::TyCtxt,
};

use super::{MirPass, MirSource};

pub struct RemoveDeref;

impl<'tcx> MirPass<'tcx> for RemoveDeref {
    fn run_pass(&self, tcx: TyCtxt<'tcx>, _: MirSource<'tcx>, body: &mut Body<'tcx>) {
        // First, find optimization opportunities. This is done in a pre-pass to keep the MIR
        // read-only so that we can do global analyses on the MIR in the process (e.g.
        // `Place::ty()`).
        let optimizations = {
            let mut optimization_finder = OptimizationFinder::new(body);
            optimization_finder.visit_body(body);
            optimization_finder.optimizations
        };

        // Then carry out those optimizations.
        MutVisitor::visit_body(&mut RemoveDerefVisitor { optimizations, tcx }, body);
    }
}

pub struct RemoveDerefVisitor<'tcx> {
    optimizations: OptimizationList<'tcx>,
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> MutVisitor<'tcx> for RemoveDerefVisitor<'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn visit_rvalue(&mut self, rvalue: &mut Rvalue<'tcx>, location: Location) {
        if let Some(place) = self.optimizations.unneeded_deref.remove(&location) {
            debug!("unneeded_deref: replacing {:?} with {:?}", rvalue, place);
            *rvalue = Rvalue::Use(Operand::Copy(place));
        }

        self.super_rvalue(rvalue, location)
    }
}

/// Finds optimization opportunities on the MIR.
struct OptimizationFinder<'b, 'tcx> {
    body: &'b Body<'tcx>,
    optimizations: OptimizationList<'tcx>,
}

impl OptimizationFinder<'b, 'tcx> {
    fn new(body: &'b Body<'tcx>) -> OptimizationFinder<'b, 'tcx> {
        OptimizationFinder { body, optimizations: OptimizationList::default() }
    }

    fn find_deref_of_address(&mut self, rvalue: &Rvalue<'tcx>, location: Location) -> Option<()> {
        // Look for the sequence
        //
        // _2 = &_1;
        // ...
        // _5 = (*_2);
        //
        // which we can replace the last statement with `_5 = _1;` to avoid the load of `_2`.
        if let Rvalue::Use(op) = rvalue {
            let local_being_derefed = match op.place()?.as_ref() {
                PlaceRef { local, projection: [ProjectionElem::Deref] } => Some(local),
                _ => None,
            }?;

            let stmt_index = location.statement_index;
            // Look behind for statement that assigns the local from a address of operator.
            // 6 is chosen as a heuristic determined by seeing the number of times
            // the optimization kicked in compiling rust std.
            let lower_index = stmt_index.saturating_sub(6);
            let statements_to_look_in = self.body.basic_blocks()[location.block].statements
                [lower_index..stmt_index]
                .iter()
                .rev();
            for stmt in statements_to_look_in {
                match &stmt.kind {
                    // Exhaustive match on statements to detect conditions that warrant we bail out of the optimization.
                    rustc_middle::mir::StatementKind::Assign(box (l, r))
                        if l.local == local_being_derefed =>
                    {
                        match r {
                            // Looking for immutable reference e.g _local_being_deref = &_1;
                            Rvalue::Ref(
                                _,
                                // Only apply the optimization if it is an immutable borrow.
                                BorrowKind::Shared,
                                place_taken_address_of,
                            ) => {
                                self.optimizations
                                    .unneeded_deref
                                    .insert(location, *place_taken_address_of);
                                return Some(());
                            }

                            // We found an assignment of `local_being_deref` that is not an immutable ref, e.g the following sequence
                            // _2 = &_1;
                            // _3 = &5
                            // _2 = _3;  <-- this means it is no longer valid to replace the last statement with `_5 = _1;`
                            // _5 = (*_2);
                            _ => return None,
                        }
                    }

                    // Inline asm can do anything, so bail out of the optimization.
                    rustc_middle::mir::StatementKind::LlvmInlineAsm(_) => return None,

                    // Check that `local_being_deref` is not being used in a mutating way which can cause misoptimization.
                    rustc_middle::mir::StatementKind::Assign(box (_, _))
                    | rustc_middle::mir::StatementKind::Coverage(_)
                    | rustc_middle::mir::StatementKind::Nop
                    | rustc_middle::mir::StatementKind::FakeRead(_, _)
                    | rustc_middle::mir::StatementKind::StorageLive(_)
                    | rustc_middle::mir::StatementKind::StorageDead(_)
                    | rustc_middle::mir::StatementKind::Retag(_, _)
                    | rustc_middle::mir::StatementKind::AscribeUserType(_, _)
                    | rustc_middle::mir::StatementKind::SetDiscriminant { .. } => {
                        if MutatingUseVisitor::has_mutating_use_in_stmt(
                            local_being_derefed,
                            stmt,
                            location,
                        ) {
                            return None;
                        }
                    }
                }
            }
        }
        Some(())
    }
}

impl Visitor<'tcx> for OptimizationFinder<'b, 'tcx> {
    fn visit_rvalue(&mut self, rvalue: &Rvalue<'tcx>, location: Location) {
        let _ = self.find_deref_of_address(rvalue, location);

        self.super_rvalue(rvalue, location)
    }
}

#[derive(Default)]
struct OptimizationList<'tcx> {
    unneeded_deref: FxHashMap<Location, Place<'tcx>>,
}

struct MutatingUseVisitor {
    has_mutating_use: bool,
    local_to_look_for: Local,
}

impl MutatingUseVisitor {
    fn has_mutating_use_in_stmt(local: Local, stmt: &Statement<'tcx>, location: Location) -> bool {
        let mut _self = Self { has_mutating_use: false, local_to_look_for: local };
        _self.visit_statement(stmt, location);
        _self.has_mutating_use
    }
}

impl<'tcx> Visitor<'tcx> for MutatingUseVisitor {
    fn visit_local(&mut self, local: &Local, context: PlaceContext, _: Location) {
        if *local == self.local_to_look_for {
            self.has_mutating_use |= context.is_mutating_use();
        }
    }
}
