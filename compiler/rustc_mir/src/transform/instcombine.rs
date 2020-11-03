//! Performs various peephole optimizations.

use crate::dataflow::Analysis;
use crate::transform::MirPass;
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::Mutability;
use rustc_index::vec::Idx;
use rustc_middle::mir::{
    visit::{MutVisitor, Visitor},
    BasicBlock, BasicBlockData, BorrowKind, Statement, StatementKind,
};

use rustc_middle::mir::{
    BinOp, Body, Constant, Local, Location, Operand, Place, PlaceRef, ProjectionElem, Rvalue,
};
use rustc_middle::ty::{self, TyCtxt};
use std::{fmt::Debug, hash::Hash, mem};

//////////////////////////////////////

use rustc_middle::mir::{self};

use crate::dataflow::{AnalysisDomain, Forward};

type AvailableStore<'tcx> = FxHashMap<Local, (Rvalue<'tcx>, Location, bool)>;

pub struct AvailableLocals;

impl<'tcx> AvailableLocals {
    fn transfer_function(
        &self,
        available: &'a mut AvailableStore<'tcx>,
    ) -> TransferFunction<'a, 'tcx> {
        TransferFunction { available }
    }
}

#[derive(Hash, Clone, Copy, Eq, PartialEq, Debug)]
pub struct LocalLocationPair {
    local: Local,
    location: Location,
}

impl AnalysisDomain<'tcx> for AvailableLocals {
    type Domain = AvailableStore<'tcx>;
    type Direction = Forward;

    const NAME: &'static str = "available_locals";

    fn bottom_value(&self, body: &mir::Body<'tcx>) -> Self::Domain {
        // bottom = nothing available
        FxHashMap::with_capacity_and_hasher(body.local_decls.len(), Default::default())
    }

    fn initialize_start_block(&self, _: &mir::Body<'tcx>, _: &mut Self::Domain) {
        // No variables are available until we observe an assignment
    }
}

impl Analysis<'tcx> for AvailableLocals {
    fn apply_statement_effect(
        &self,
        state: &mut Self::Domain,
        statement: &Statement<'tcx>,
        location: Location,
    ) {
        self.transfer_function(state).visit_statement(statement, location);
    }

    fn apply_terminator_effect(
        &self,
        state: &mut Self::Domain,
        terminator: &mir::Terminator<'tcx>,
        location: Location,
    ) {
        self.transfer_function(state).visit_terminator(terminator, location);
    }

    fn apply_call_return_effect(
        &self,
        _state: &mut Self::Domain,
        _block: BasicBlock,
        _func: &Operand<'tcx>,
        _args: &[Operand<'tcx>],
        _return_place: Place<'tcx>,
    ) {
        // todo!()
    }
}

struct TransferFunction<'a, 'tcx> {
    /// Locals that are available, i.e. can be reused in a expression
    available: &'a mut FxHashMap<Local, (Rvalue<'tcx>, Location, bool)>,
}

impl<'a, 'tcx> TransferFunction<'a, 'tcx> {
    fn invalidate_local(&mut self, local_invalidated: Local) {
        // Since we are now invalidating the value of a local, we may have to invalidate any other currently available
        // local that uses the now-invalidated local.
        for (lhs, (stored_rvalue, location, invalidated)) in
            self.available.iter_mut().filter(|(_, (_, _, invalidated))| !invalidated)
        {
            if *lhs == local_invalidated {
                *invalidated = true;
                debug!("Invalidated {:?}", lhs);
                return;
            }

            let mut participating_locals = stored_rvalue.participating_locals(*location);
            *invalidated = participating_locals.any(|x| x == local_invalidated);
            debug!(
                "Invalidation result `{:?}` for `{:?}` when `{:?}` was invalidated",
                invalidated, lhs, local_invalidated
            );
        }
    }

    fn add_available(&mut self, local: Local, rvalue: Rvalue<'tcx>, location: Location) {
        if self.available.contains_key(&local) {
            // If occupied this was a reassignment. Invalidate the old uses
            self.invalidate_local(local);
        }

        self.available.insert(local, (rvalue, location, false));
    }
}

impl<'a, 'tcx> Visitor<'tcx> for TransferFunction<'a, 'tcx> {
    fn visit_assign(
        &mut self,
        assigned_place: &Place<'tcx>,
        rvalue: &Rvalue<'tcx>,
        location: Location,
    ) {
        if let Some(assigned_local) = assigned_place.as_local() {
            let mut_reference_opt = match rvalue {
                Rvalue::Ref(_, BorrowKind::Mut { .. } | BorrowKind::Shallow, ref_of) => {
                    Some(ref_of)
                }
                Rvalue::AddressOf(Mutability::Mut, ref_of) => Some(ref_of),
                _ => None,
            };

            if let Some(mut_reference) = mut_reference_opt {
                // It is difficult to reason about availability of mutable places, so throw out any
                // availability information about the local taken a mutable reference of.
                debug!(
                    "Found mutable reference of `{:?}`. Invalidating {:?} and {:?}",
                    mut_reference, mut_reference.local, assigned_local
                );
                self.invalidate_local(mut_reference.local);
                self.invalidate_local(assigned_local)
            } else {
                self.add_available(assigned_local, rvalue.clone(), location);
            }
        }

        self.super_assign(assigned_place, rvalue, location);
    }

    fn visit_statement(&mut self, statement: &Statement<'tcx>, location: Location) {
        match statement.kind {
            StatementKind::StorageDead(dead) => {
                self.invalidate_local(dead);
            }
            _ => self.super_statement(statement, location),
        }
    }
}

//////////////////////////////

pub struct InstCombine;

impl<'tcx> MirPass<'tcx> for InstCombine {
    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        // First, find optimization opportunities. This is done in a pre-pass to keep the MIR
        // read-only so that we can do global analyses on the MIR in the process (e.g.
        // `Place::ty()`).
        let mut optimizations = {
            let mut optimization_finder = OptimizationFinder::new(body, tcx);
            optimization_finder.visit_body(body);
            optimization_finder.optimizations
        };

        // TODO make results visitor
        let mut results =
            AvailableLocals.into_engine(tcx, body).iterate_to_fixpoint().into_results_cursor(body);

        // Inspect the fixpoint state immediately before each `Drop` terminator.
        for (bb, block) in body.basic_blocks().iter_enumerated() {
            for (stmt_idx, stmt) in block.statements.iter().enumerate() {
                let location = Location { block: bb, statement_index: stmt_idx };
                results.seek_before_primary_effect(location);
                let state = results.get();
                debug!("state: {:?} before statement {:?}", state, stmt);
                // try to apply optimization on deref
                let statement = stmt;
                match &statement.kind {
                    rustc_middle::mir::StatementKind::Assign(box (_, r)) => {
                        match r {
                            Rvalue::Use(op) => {
                                // Looking for _5 = (*_2);
                                if let Some(place_being_derefed) = op.place() {
                                    match place_being_derefed.as_ref() {
                                        PlaceRef {
                                            projection: [ProjectionElem::Deref], ..
                                        } => {
                                            if let Some((_, (available_rvalue, _, _))) =
                                                state.iter().find(|(x, (_, _, invalidated))| {
                                                    **x == place_being_derefed.local && !invalidated
                                                })
                                            {
                                                match available_rvalue {
                                                    Rvalue::Ref(_, _, available_place) => {
                                                        debug!(
                                                            "Found optimization: {:?}",
                                                            available_place
                                                        );
                                                        optimizations
                                                            .unneeded_deref
                                                            .insert(location, *available_place);
                                                    }
                                                    _ => {}
                                                }
                                            }
                                        }
                                        _ => {}
                                    }
                                }
                            }
                            _ => {}
                        }
                    }

                    _ => {}
                }
            }
        }

        // Then carry out those optimizations.
        MutVisitor::visit_body(&mut InstCombineVisitor { optimizations, tcx }, body);
    }
}

pub struct InstCombineVisitor<'tcx> {
    optimizations: OptimizationList<'tcx>,
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> MutVisitor<'tcx> for InstCombineVisitor<'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn visit_rvalue(&mut self, rvalue: &mut Rvalue<'tcx>, location: Location) {
        if self.optimizations.and_stars.remove(&location) {
            debug!("replacing `&*`: {:?}", rvalue);
            let new_place = match rvalue {
                Rvalue::Ref(_, _, place) => {
                    if let &[ref proj_l @ .., proj_r] = place.projection.as_ref() {
                        place.projection = self.tcx().intern_place_elems(&[proj_r]);

                        Place {
                            // Replace with dummy
                            local: mem::replace(&mut place.local, Local::new(0)),
                            projection: self.tcx().intern_place_elems(proj_l),
                        }
                    } else {
                        unreachable!();
                    }
                }
                _ => bug!("Detected `&*` but didn't find `&*`!"),
            };
            *rvalue = Rvalue::Use(Operand::Copy(new_place))
        }

        if let Some(constant) = self.optimizations.arrays_lengths.remove(&location) {
            debug!("replacing `Len([_; N])`: {:?}", rvalue);
            *rvalue = Rvalue::Use(Operand::Constant(box constant));
        }

        if let Some(operand) = self.optimizations.unneeded_equality_comparison.remove(&location) {
            debug!("replacing {:?} with {:?}", rvalue, operand);
            *rvalue = Rvalue::Use(operand);
        }

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
    tcx: TyCtxt<'tcx>,
    optimizations: OptimizationList<'tcx>,
    // Locals within the currently analysed basic block where this optimization potentially applies.
    // This list is updated as statements are visited.
    // Option<Local> is used to make it easy to iterate a local mutably
    // and "remove" it as a potential by setting it to None.
    locals_with_potential: Vec<Option<(Local, Place<'tcx>)>>,
}

impl OptimizationFinder<'b, 'tcx> {
    fn new(body: &'b Body<'tcx>, tcx: TyCtxt<'tcx>) -> OptimizationFinder<'b, 'tcx> {
        OptimizationFinder {
            body,
            tcx,
            optimizations: OptimizationList::default(),
            locals_with_potential: vec![],
        }
    }

    fn find_unneeded_equality_comparison(&mut self, rvalue: &Rvalue<'tcx>, location: Location) {
        // find Ne(_place, false) or Ne(false, _place)
        // or   Eq(_place, true) or Eq(true, _place)
        if let Rvalue::BinaryOp(op, l, r) = rvalue {
            let const_to_find = if *op == BinOp::Ne {
                false
            } else if *op == BinOp::Eq {
                true
            } else {
                return;
            };
            // (const, _place)
            if let Some(o) = self.find_operand_in_equality_comparison_pattern(l, r, const_to_find) {
                self.optimizations.unneeded_equality_comparison.insert(location, o.clone());
            }
            // (_place, const)
            else if let Some(o) =
                self.find_operand_in_equality_comparison_pattern(r, l, const_to_find)
            {
                self.optimizations.unneeded_equality_comparison.insert(location, o.clone());
            }
        }
    }

    fn find_operand_in_equality_comparison_pattern(
        &self,
        l: &Operand<'tcx>,
        r: &'a Operand<'tcx>,
        const_to_find: bool,
    ) -> Option<&'a Operand<'tcx>> {
        let const_ = l.constant()?;
        if const_.literal.ty == self.tcx.types.bool
            && const_.literal.val.try_to_bool() == Some(const_to_find)
        {
            if r.place().is_some() {
                return Some(r);
            }
        }

        None
    }
}

/// Returns whether this place derefences a type `&_`
fn place_derefs_non_mutable_ref<'tcx>(
    place: &Place<'tcx>,
    body: &Body<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> bool {
    if let PlaceRef { local, projection: &[ref proj_base @ .., ProjectionElem::Deref] } =
        place.as_ref()
    {
        let ty = Place::ty_from(local, proj_base, body, tcx).ty;
        // The dereferenced place must have type `&_`.
        if let ty::Ref(_, _, Mutability::Not) = ty.kind() {
            return true;
        }
    }
    return false;
}

impl Visitor<'tcx> for OptimizationFinder<'b, 'tcx> {
    fn visit_basic_block_data(&mut self, block: BasicBlock, data: &BasicBlockData<'tcx>) {
        self.locals_with_potential.clear();
        self.super_basic_block_data(block, data);
    }

    fn visit_rvalue(&mut self, rvalue: &Rvalue<'tcx>, location: Location) {
        if let Rvalue::Ref(_, _, place) = rvalue {
            if place_derefs_non_mutable_ref(place, self.body, self.tcx) {
                self.optimizations.and_stars.insert(location);
            }
        }

        if let Rvalue::Len(ref place) = *rvalue {
            let place_ty = place.ty(&self.body.local_decls, self.tcx).ty;
            if let ty::Array(_, len) = place_ty.kind() {
                let span = self.body.source_info(location).span;
                let constant = Constant { span, literal: len, user_ty: None };
                self.optimizations.arrays_lengths.insert(location, constant);
            }
        }

        self.find_unneeded_equality_comparison(rvalue, location);

        self.super_rvalue(rvalue, location)
    }
}

#[derive(Default)]
struct OptimizationList<'tcx> {
    and_stars: FxHashSet<Location>,
    arrays_lengths: FxHashMap<Location, Constant<'tcx>>,
    unneeded_equality_comparison: FxHashMap<Location, Operand<'tcx>>,
    unneeded_deref: FxHashMap<Location, Place<'tcx>>,
}
