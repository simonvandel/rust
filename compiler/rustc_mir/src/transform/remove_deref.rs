//! A pass that removes derefs if uneeded.
//!
//! Consider the following sequence:
//!
//! _2 = &_1;
//! ...
//! _5 = (*_2);
//!
//! where we can replace the last statement with `_5 = _1;`
//! to avoid the load of `_2`.
//! This optimization will only be done if nothing between
//! the first and last statement can modify `_2`.
use rustc_data_structures::fx::FxHashMap;
use rustc_middle::{
    mir::visit::MutVisitor,
    mir::visit::PlaceContext,
    mir::visit::Visitor,
    mir::BasicBlock,
    mir::BasicBlockData,
    mir::Body,
    mir::Operand,
    mir::{BorrowKind, Local, Location, Place, PlaceRef, ProjectionElem, Rvalue, Statement},
    ty::TyCtxt,
};

use super::{MirPass, MirSource};

pub struct RemoveDeref;

impl<'tcx> MirPass<'tcx> for RemoveDeref {
    fn run_pass(&self, tcx: TyCtxt<'tcx>, _: MirSource<'tcx>, body: &mut Body<'tcx>) {
        let optimizations = {
            let mut optimization_finder = OptimizationFinder::new();
            optimization_finder.visit_body(body);
            optimization_finder.optimizations
        };

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
            debug!("replacing {:?} with {:?}", rvalue, place);
            *rvalue = Rvalue::Use(Operand::Copy(place));
        }

        self.super_rvalue(rvalue, location)
    }
}

/// Finds optimization opportunities on the MIR.
struct OptimizationFinder<'tcx> {
    optimizations: OptimizationList<'tcx>,
    // Locals within the currently analysed basic block where this optimization potentially applies.
    // This list is updated as statements are visited.
    // Option<Local> is used to make it easy to iterate a local mutably
    // and "remove" it as a potential by setting it to None.
    locals_with_potential: Vec<Option<(Local, Place<'tcx>)>>,
}

impl OptimizationFinder<'tcx> {
    fn new() -> OptimizationFinder<'tcx> {
        OptimizationFinder {
            optimizations: OptimizationList::default(),
            locals_with_potential: vec![],
        }
    }

    /// Removes locals from the list of potential if they are used in a way that would cause misoptimization
    fn ensure_potential_is_valid(&mut self, statement: &Statement<'tcx>, location: Location) {
        for local in self.locals_with_potential.iter_mut().filter(|x| x.is_some()) {
            if MutatingUseVisitor::has_mutating_use_in_stmt(local.unwrap().0, statement, location) {
                debug!(
                    "Potential local {:?} is in mutating use in statement {:?}, so disqualifying it",
                    local.unwrap(),
                    statement
                );
                *local = None;
            }
        }
    }
}

impl Visitor<'tcx> for OptimizationFinder<'tcx> {
    fn visit_basic_block_data(&mut self, block: BasicBlock, data: &BasicBlockData<'tcx>) {
        self.locals_with_potential.clear();
        self.super_basic_block_data(block, data);
    }

    fn visit_statement(&mut self, statement: &Statement<'tcx>, location: Location) {
        match &statement.kind {
            rustc_middle::mir::StatementKind::Assign(box (l, r)) => {
                match r {
                    // Looking for immutable reference e.g _local_being_deref = &_1;
                    Rvalue::Ref(
                        _,
                        // Only apply the optimization if it is an immutable borrow.
                        BorrowKind::Shared,
                        place_ref,
                    ) => {
                        self.locals_with_potential.push(Some((l.local, *place_ref)));
                        // we found a potential in this statement, so we are done in this statement
                        return;
                    }
                    Rvalue::Use(op) => {
                        // Looking for _5 = (*_2);
                        if let Some(place_being_derefed) = op.place() {
                            match place_being_derefed.as_ref() {
                                PlaceRef { projection: [ProjectionElem::Deref], .. } => {
                                    if let Some(to_optimize) = self
                                        .locals_with_potential
                                        .iter_mut()
                                        .filter_map(|x| *x)
                                        .find(|x| x.0 == place_being_derefed.local)
                                    {
                                        // We found a local that is optimizable!
                                        self.optimizations
                                            .unneeded_deref
                                            .insert(location, to_optimize.1);
                                    } else {
                                        self.ensure_potential_is_valid(statement, location)
                                    }
                                }
                                _ => self.ensure_potential_is_valid(statement, location),
                            }
                        }
                    }
                    // Check that each of the locals with potential are not being used
                    // in a mutating way which can cause misoptimization.
                    _ => {
                        self.ensure_potential_is_valid(statement, location);
                    }
                }
                // check that all other uses of Assign do not cause issues for the potentials
                self.ensure_potential_is_valid(statement, location);
            }

            // Inline asm can do anything, so clear all potential.
            rustc_middle::mir::StatementKind::LlvmInlineAsm(_) => {
                self.locals_with_potential.clear()
            }

            rustc_middle::mir::StatementKind::Coverage(_)
            | rustc_middle::mir::StatementKind::Nop
            | rustc_middle::mir::StatementKind::FakeRead(_, _)
            | rustc_middle::mir::StatementKind::StorageLive(_)
            | rustc_middle::mir::StatementKind::StorageDead(_)
            | rustc_middle::mir::StatementKind::Retag(_, _)
            | rustc_middle::mir::StatementKind::AscribeUserType(_, _)
            | rustc_middle::mir::StatementKind::SetDiscriminant { .. } => {
                self.ensure_potential_is_valid(statement, location)
            }
        }

        // We do not call super.visit_statement as we do not need to go deeper than Statement
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
