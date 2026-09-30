import Mathlib
import Submission.Work.SpecLin.Conventions
import Submission.Work.SpecLin.Points.Setup
import Submission.Work.SpecLin.Chart.isAffineOpen_regularOpensAux
import Submission.Work.SpecLin.Alt.exists_regular_transcendental

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.SpecLin.Alt

/-- **Every finite set of points of a curve lies in an affine open subset** (sorry-free route).

This is the statement of `Work.SpecLin.Alt.affineOpenContaining`, assembled from the branch of
the development that is free of `sorry`: the existence of a transcendental rational function
regular on a prescribed finite set (`Work.SpecLin.Alt.exists_regular_transcendental`) together
with the affineness of `regularOpens C x` (`Work.SpecLin.Chart.isAffineOpen_regularOpensAux`,
which rests on the valuative criterion
`Work.SpecLin.Chart.valuativeCriterion_regularOpensMap`). -/
theorem affineOpenContaining_sorryFree {K : Type u} [Field K] (C : Work.CurveBasics.Curve K)
    (S : Set C.left) (hS : S.Finite) :
    ∃ W : C.left.Opens, AlgebraicGeometry.IsAffineOpen W ∧ S ⊆ (W : Set C.left) := by
  obtain ⟨x, hx, hSx⟩ := Work.SpecLin.Alt.exists_regular_transcendental C S hS
  exact ⟨Work.SpecLin.Chart.regularOpens C x,
    Work.SpecLin.Chart.isAffineOpen_regularOpensAux C x hx, hSx⟩

/-- **A single `R`-point of a curve takes values among at most two points.**

Every point of `Spec R` specialises to the closed point of `Spec R` (`R` is a valuation ring,
so its primes form a chain), continuous maps preserve specialisation, and a point of a curve
which is not the generic point is closed (a curve is one-dimensional).  Hence the image of
`Spec R` under an `R`-point is contained in `{generic point, image of the closed point}`. -/
theorem range_base_subset_pair {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    (p : Work.SpecLin.CurvePt C R) :
    Set.range p.left.base ⊆
      ({genericPoint C.left, p.left.base (IsLocalRing.closedPoint R)} : Set C.left) := by
  rintro y ⟨x, rfl⟩
  have hsp : (p.left.base x) ⤳ (p.left.base (IsLocalRing.closedPoint R)) :=
    Specializes.map (IsLocalRing.specializes_closedPoint x) (Scheme.Hom.continuous p.left)
  rcases (Order.le_one_iff (α := ℕ∞)).mp
    (Work.CurveBasics.Curve.coheight_le_one C (p.left.base x)) with h0 | h1
  · exact Or.inl (Work.CurveBasics.Curve.eq_genericPoint_of_coheight_eq_zero C h0)
  · refine Or.inr ?_
    have hcl : IsClosed ({p.left.base x} : Set C.left) :=
      Work.CurveBasics.Point.isClosed_of_coheight_eq_one C h1
    have hmem : p.left.base (IsLocalRing.closedPoint R) ∈ ({p.left.base x} : Set C.left) := by
      rw [← hcl.closure_eq]
      exact specializes_iff_mem_closure.mp hsp
    rw [Set.mem_singleton_iff] at hmem
    exact hmem.symm

/-- The two-element subset of a curve attached to an `R`-point is finite. -/
private theorem finite_pair {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} (b : C.left) :
    ({genericPoint C.left, b} : Set C.left).Finite :=
  (Set.finite_singleton b).insert (genericPoint C.left)

/-- **An affine open of the curve containing the images of finitely many `R`-points.**

For a smooth proper geometrically irreducible curve `C` over a field `K`, a `K`-valuation ring
`R` and two `n`-tuples `s`, `t` of `R`-points of `C`, there is an affine open `W ⊆ C` containing
the image of every one of them.

Proof route (do not try to prove that `Spec R` has finitely many points — that is false for
unbounded-rank valuation rings): the primes of `R` form a chain (`ValuationRing.linearOrder`),
continuous maps preserve specialization, and a curve has no 3-element specialization chain
(`Curve.krcoheight`-lemmas: every point of `C` is either the generic point or closed).  Hence
`Set.range (s m).left.base ⊆ {genericPoint C.left, (s m).left.base (IsLocalRing.closedPoint R)}`,
a set of at most two points, so the union over `Fin n` is finite; then apply
`Work.SpecLin.Alt.affineOpenContaining` (`Submission/Work/SpecLin/Alt/affineOpenContaining.lean`),
which places any finite set of points of `C` in an affine open. -/
theorem exists_isAffineOpen_containing_pts {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {n : ℕ} (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    (s t : Fin n → Work.SpecLin.CurvePt C R) :
    ∃ W : C.left.Opens, AlgebraicGeometry.IsAffineOpen W ∧
      (∀ m : Fin n, Set.range (s m).left.base ⊆ (W : Set C.left)) ∧
      (∀ m : Fin n, Set.range (t m).left.base ⊆ (W : Set C.left)) := by
  have hfin : ((⋃ m : Fin n, Set.range (s m).left.base) ∪
      (⋃ m : Fin n, Set.range (t m).left.base) : Set C.left).Finite := by
    refine Set.Finite.union ?_ ?_
    · exact Set.Finite.subset
        (Set.finite_iUnion
          (fun m : Fin n => finite_pair ((s m).left.base (IsLocalRing.closedPoint R))))
        (Set.iUnion_mono (fun m => range_base_subset_pair R (s m)))
    · exact Set.Finite.subset
        (Set.finite_iUnion
          (fun m : Fin n => finite_pair ((t m).left.base (IsLocalRing.closedPoint R))))
        (Set.iUnion_mono (fun m => range_base_subset_pair R (t m)))
  obtain ⟨W, hW, hsub⟩ := affineOpenContaining_sorryFree C _ hfin
  exact ⟨W, hW,
    fun m y hy => hsub (Or.inl (Set.mem_iUnion.mpr ⟨m, hy⟩)),
    fun m y hy => hsub (Or.inr (Set.mem_iUnion.mpr ⟨m, hy⟩))⟩

end Work.SpecLin.Alt
