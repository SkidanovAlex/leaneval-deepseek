/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# A point of `Symⁿ C` lies in a chart of a *nonempty* affine open (area SY, `divOf`)

`Work.SymQuot.DivOf.chartPt_exists` produces a `ChartPt d` for every field point of `Symⁿ C`,
but its open `V ⊆ C` could a priori be empty.  The divisor construction
(`Work.SymQuot.DivOf.divOfChart`) needs `[Nonempty d.V]`, since it works with the affine ring
`Γ(C_F, bcOpens F V)` (an empty open has the zero ring as its section ring).

Here we redo the (topological) proof of `chartPt_exists` keeping track of the fact that the
affine open produced contains the finitely many coordinates of a lift `y ∈ Cⁿ` of `p`; as
`n ≥ 1` (`NeZero n`) those coordinates exist, so `V` is nonempty.

* `exists_chartPt_nonempty` — there is `d : ChartPt C n p` with `Nonempty d.V`.
-/
import Mathlib
import Submission.Work.SymQuot.DivOf.chartPt_exists
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

/-- **Every point of `Symⁿ C` lies in a chart of a nonempty affine open**: there is a `ChartPt`
for `p` whose open `V ⊆ C` is nonempty.

The proof is the proof of `chartPt_exists`: lift `p` to `y ∈ Cⁿ` along the surjective quotient
map, choose an affine open `V ⊆ C` containing the coordinates of `y` (CB7), and factor `p`
through the chart of `Vⁿ`.  The extra information is that `V ⊇ {proj m y}` for some `m : Fin n`,
which is nonempty because `n ≥ 1`. -/
theorem exists_chartPt_nonempty {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {n : ℕ}
    [NeZero n] [Work.SymQuot.CurveAffineCover C] {F : Type u} [Field F] [Algebra K F]
    (p : Work.SpecLin.FPt (Work.SymQuot.Sym C n) F) :
    ∃ d : Work.SymQuot.DivOf.ChartPt C n p, Nonempty d.V := by
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
  -- The chart of `Vⁿ` contains the image of `p`.
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
  refine ⟨Work.SymQuot.DivOf.ChartPt.mk V hVaff q hfac, ?_⟩
  -- `V` contains the coordinate `proj m y` for any `m : Fin n`, and `Fin n` is nonempty.
  obtain ⟨m⟩ : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero (NeZero.ne n))
  exact ⟨⟨(Work.SymQuot.proj C.toOver n m).left y, hVy ⟨m, rfl⟩⟩⟩

end Work.SymQuot.DivOf
