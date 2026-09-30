/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.Work.SpecLin.Points.Basic
import Submission.Work.Charts.section_eq_of_closedPoint_eq
import Submission.Work.Charts.sum_single_eq_iff_exists_perm

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false

universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

namespace Work.SymQuot.DivOf

/-- **`ptPlace` is injective on field points of a curve.**

An `F`-point `p : Spec F ⟶ C` of the curve gives the section `ptLeft p : Spec F ⟶ C_F` of
`C_F ⟶ Spec F` and the place `ptPlace p` (a closed point of `C_F`).  Two points with the same
place are equal: both `ptLeft p` and `ptLeft q` are sections of the separated morphism
`C_F ⟶ Spec F` through the same point, and for a section of `X ⟶ Spec F` the residue field map
`κ(x) → F` is forced (`Work.Charts.section_eq_of_closedPoint_eq`). -/
private theorem ptPlace_injective_aux {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {F : Type u} [Field F] [Algebra K F] :
    Function.Injective (Work.SpecLin.ptPlace (C := C) (F := F)) := by
  intro p q h
  have hx : Work.SpecLin.ptToPoint p = Work.SpecLin.ptToPoint q :=
    congrArg Work.CurveBasics.Curve.Place.point h
  have hleft : Work.SpecLin.ptLeft p = Work.SpecLin.ptLeft q :=
    Work.Charts.section_eq_of_closedPoint_eq ((C.baseChange F).hom) (Work.SpecLin.ptLeft p)
      (Work.SpecLin.ptLeft q) (Work.SpecLin.Points.ptLeft_comp_hom p)
      (Work.SpecLin.Points.ptLeft_comp_hom q) (by simpa [Work.SpecLin.ptToPoint] using hx)
  apply Over.OverMorphism.ext
  rw [← Work.SpecLin.ptLeft_fst p, ← Work.SpecLin.ptLeft_fst q, hleft]

/-- **Two `n`-tuples of `F`-points of a curve with the same sum of point divisors differ by a
permutation of the coordinates.**

`ptDiv p` is the divisor `[p]` associated with the place `ptPlace p` of `C_F`, so a sum
`∑ m, ptDiv (x m)` is the multiset of the places `ptPlace (x m)`; comparing coefficients (the
characterisation `Work.Charts.sum_single_eq_iff_exists_perm` of equality of such sums of
singletons) produces a permutation `σ` with `ptPlace (y m) = ptPlace (x (σ m))`, and
injectivity of `ptPlace` upgrades this to `y m = x (σ m)`.  The converse is invariance of the
sum under a permutation of the index set. -/
theorem ptDiv_sum_eq_iff {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {F : Type u} [Field F] [Algebra K F] {n : ℕ}
    (x y : Fin n → Work.SpecLin.CurveFPt C F) :
    (∑ m, Work.SpecLin.ptDiv (x m)) = (∑ m, Work.SpecLin.ptDiv (y m)) ↔
      ∃ σ : Equiv.Perm (Fin n), ∀ m, y m = x (σ m) := by
  constructor
  · intro h
    -- Both sums are sums of the singletons at the places `ptPlace (x m)`, `ptPlace (y m)`.
    have h' : (∑ m : Fin n, (Finsupp.single (Work.SpecLin.ptPlace (x m)) (1 : ℤ) :
          (C.baseChange F).Place →₀ ℤ)) =
        ∑ m : Fin n, (Finsupp.single (Work.SpecLin.ptPlace (y m)) (1 : ℤ) :
          (C.baseChange F).Place →₀ ℤ) := by
      simpa only [Work.SpecLin.ptDiv, Work.CurveBasics.Curve.Div.place] using h
    -- Comparing multiplicities of places gives a permutation of the places.
    obtain ⟨σ, hσ⟩ := (Work.Charts.sum_single_eq_iff_exists_perm
      (fun m => Work.SpecLin.ptPlace (x m))
      (fun m => Work.SpecLin.ptPlace (y m))).mp h'
    -- Which, the place being injective, is a permutation of the coordinates.
    exact ⟨σ, fun m => ptPlace_injective_aux (hσ m)⟩
  · rintro ⟨σ, hσ⟩
    have h2 : (∑ m, Work.SpecLin.ptDiv (y m)) = ∑ m, Work.SpecLin.ptDiv (x (σ m)) :=
      Finset.sum_congr rfl (fun m _ => by rw [hσ m])
    rw [h2]
    exact (Equiv.sum_comp σ (fun m => Work.SpecLin.ptDiv (x m))).symm

end Work.SymQuot.DivOf
