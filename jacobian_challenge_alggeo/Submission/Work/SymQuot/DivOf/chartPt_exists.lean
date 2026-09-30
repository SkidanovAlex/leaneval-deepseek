/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# A point of `Symⁿ C` lies in a chart of the form `Spec Γ(Cⁿ, Vⁿ)^{S_n}` (area SY, `divOf`)

The structure `Work.SymQuot.DivOf.ChartPt` asks for a point `p : Spec F ⟶ Symⁿ C` together with
an *affine open* `V ⊆ C` whose chart (the chart of the `S_n`-invariant open `Vⁿ ⊆ Cⁿ`) contains
the image of `p`.  This file proves that such data always exists
(`Work.SymQuot.DivOf.chartPt_exists`).

The proof is topological.  Lift the point `p` to a point `y` of `Cⁿ` along the (surjective)
quotient map `Sym.quot`; choose an affine open `V ⊆ C` containing the finitely many coordinates
of `y` (this is CB7, the class `CurveAffineCover`).  Then `y ∈ Vⁿ`, so `p` lands in the image of
the chart inclusion `chartι` of the chart of `Vⁿ`; since `Spec F` is a single point, `p` factors
through that open immersion by `IsOpenImmersion.lift`.
-/
import Mathlib
import Submission.Work.SymQuot.DivOf.ChartPt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.SymQuot.DivOf

/-- **Every point of `Symⁿ C` lies in one of the charts `Spec Γ(Cⁿ, Vⁿ)^{S_n}`** for `V ⊆ C`
an affine open. -/
theorem chartPt_exists {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {n : ℕ} [NeZero n]
    [Work.SymQuot.CurveAffineCover C] {F : Type u} [Field F] [Algebra K F]
    (p : Work.SpecLin.FPt (Work.SymQuot.Sym C n) F) :
    Nonempty (Work.SymQuot.DivOf.ChartPt C n p) := by
  classical
  -- Lift the (closed) point of `p` to a point `y` of `Cⁿ` along the quotient map.
  obtain ⟨y, hy⟩ := Work.SymQuot.Sym.quot_surjective C n
    (p.left.base (IsLocalRing.closedPoint F))
  -- An affine open of `C` containing all coordinates of `y` (this is CB7).
  obtain ⟨V, hVaff, hVy⟩ := Work.SymQuot.CurveAffineCover.exists_isAffineOpen_superset
    (C := C) (Set.range fun m : Fin n => (Work.SymQuot.proj C.toOver n m).left y)
    (Set.finite_range _)
  have hymem : y ∈ Work.SymQuot.piOpen C.toOver V n := by
    rw [Work.SymQuot.mem_piOpen]
    exact fun m => hVy ⟨m, rfl⟩
  -- The chart of the product open `Vⁿ ⊆ Cⁿ`.
  let Uc : (Work.SymQuot.symData C n).Chart :=
    ⟨Work.SymQuot.piOpen C.toOver V n,
      Work.SymQuot.Prod.isAffineOpen_piOpen C.toOver n V hVaff,
      Work.SymQuot.DivOf.symPiOpen_invariant C n V⟩
  -- The chart of `Vⁿ` contains the image of `p`: `p` is `Sym.quot y`, and `Sym.quot` factors
  -- through the chart of `Vⁿ` because `y ∈ Vⁿ`.
  have hmem : (Work.SymQuot.symData C n).chartι Uc
        ((Work.SymQuot.symData C n).action.chartMap Uc.1 Uc.2.2 ⟨y, hymem⟩)
      = p.left.base (IsLocalRing.closedPoint F) := by
    have h := congrArg (fun (f : Uc.1.toScheme ⟶ (Work.SymQuot.symData C n).Quotient) =>
      f ⟨y, hymem⟩) ((Work.SymQuot.symData C n).quotientMap_chartι Uc)
    exact h.symm.trans hy
  -- `Spec F` is a single point, so the whole range of `p` is contained in the chart.
  haveI : Subsingleton ↥(Work.SpecLin.specOf (K := K) F).left :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of F)))
  have hrange : Set.range p.left ⊆ Set.range ((Work.SymQuot.symData C n).chartι Uc) := by
    rintro _ ⟨w, rfl⟩
    rw [show w = IsLocalRing.closedPoint F from Subsingleton.elim _ _]
    exact ⟨_, hmem⟩
  -- Factor `p` through the open immersion `chartι Uc`.
  let q : Spec (CommRingCat.of F) ⟶ (Work.SymQuot.symData C n).chart Uc :=
    @IsOpenImmersion.lift _ _ _ ((Work.SymQuot.symData C n).chartι Uc) p.left
      (by infer_instance) hrange
  have hfac : q ≫ ((Work.SymQuot.symData C n).chartι Uc) = p.left :=
    @IsOpenImmersion.lift_fac _ _ _ ((Work.SymQuot.symData C n).chartι Uc) p.left
      (by infer_instance) hrange
  exact ⟨Work.SymQuot.DivOf.ChartPt.mk V hVaff q hfac⟩

end Work.SymQuot.DivOf
