//! Performs various peephole optimizations.

use crate::transform::MirPass;
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::Mutability;
use rustc_index::vec::Idx;
use rustc_middle::mir::{
    visit::PlaceContext,
    visit::{MutVisitor, Visitor},
    BasicBlock, BasicBlockData, Statement,
};
use rustc_middle::mir::{
    BinOp, Body, BorrowKind, Constant, Local, Location, Operand, Place, PlaceRef, ProjectionElem,
    Rvalue,
};
use rustc_middle::ty::{self, TyCtxt};
use std::mem;

pub struct InstCombine;

impl<'tcx> MirPass<'tcx> for InstCombine {
    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        // First, find optimization opportunities. This is done in a pre-pass to keep the MIR
        // read-only so that we can do global analyses on the MIR in the process (e.g.
        // `Place::ty()`).
        let optimizations = {
            let mut optimization_finder = OptimizationFinder::new(body, tcx);
            optimization_finder.visit_body(body);
            optimization_finder.optimizations
        };

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

struct MutatingUseVisitor {
    has_mutating_use: bool,
    local_to_look_for: Local,
}

impl<'tcx> MutatingUseVisitor {
    fn has_mutating_use_in_stmt(local: Local, stmt: &Statement<'tcx>, location: Location) -> bool {
        let mut _self = Self { has_mutating_use: false, local_to_look_for: local };
        _self.visit_statement(stmt, location);
        _self.has_mutating_use
    }
}

impl<'tcx> Visitor<'tcx> for MutatingUseVisitor {
    fn visit_local(&mut self, local: &Local, context: PlaceContext, _: Location) {
        // TODO reverse this so that the visitor takes in the potentials, and updates removes when it finds mutating
        if *local == self.local_to_look_for {
            let is_dead = matches!(
                context,
                PlaceContext::NonUse(rustc_middle::mir::visit::NonUseContext::StorageDead)
            );
            self.has_mutating_use |= context.is_mutating_use() || is_dead;
        }
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
    /// Removes locals from the list of potential if they are used in a way that would cause misoptimization
    fn ensure_potentials_are_valid(&mut self, statement: &Statement<'tcx>, location: Location) {
        for local in self.locals_with_potential.iter_mut().filter(|x| x.is_some()) {
            debug!(
                "Checking if local {:?} is in mutating use in statement {:?}",
                local.unwrap(),
                statement
            );
            if MutatingUseVisitor::has_mutating_use_in_stmt(local.unwrap().0, statement, location)
                || MutatingUseVisitor::has_mutating_use_in_stmt(
                    local.unwrap().1.local,
                    statement,
                    location,
                )
            {
                debug!(
                    "Potential local {:?} is in mutating use in statement {:?}, so disqualifying it",
                    local.unwrap(),
                    statement
                );
                *local = None;
            }
        }
    }

    fn find_deref_of_address(&mut self, statement: &Statement<'tcx>, location: Location) {
        // FIXME(#78192): This optimization can result in unsoundness.
        if !self.tcx.sess.opts.debugging_opts.unsound_mir_opts {
            return;
        }

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
                                        return;
                                    }
                                }
                                // We didn't find the local that is optimizable,
                                // so we need to ensure that all potentials are still valid
                                _ => self.ensure_potentials_are_valid(statement, location),
                            }
                        }
                    }
                    // check that all other uses of Assign do not cause issues for the potentials
                    _ => {
                        self.ensure_potentials_are_valid(statement, location);
                    }
                }
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
                self.ensure_potentials_are_valid(statement, location)
            }
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

    fn visit_statement(&mut self, statement: &Statement<'tcx>, location: Location) {
        self.find_deref_of_address(statement, location);
        self.super_statement(statement, location);
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
