import Mathlib
import Submission.Work.SpecLin.Conventions
import Submission.Work.SpecLin.Points.Basic
import Submission.Work.CurveBasics.Place.Coheight
import Submission.Work.CurveBasics.Point.isClosed_of_coheight_eq_one

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.SpecLin.Core

universe u

open CategoryTheory Limits AlgebraicGeometry in
/-- **A chain of length two of specialisations in a curve is trivial in the middle.**

Let `a`, `b`, `c` be points of a curve `C` with `c ≤ b ≤ a` for the specialisation order on
the points of a scheme (`a ≤ b ↔ b ⤳ a`, see `AlgebraicGeometry.Scheme.le_iff_specializes`).
Then `b = a` or `b = c`: a curve is one-dimensional, so there is no strictly increasing chain
of three points.

Proof.  If `b ≠ a`, then `b < a`, and `Order.coheight_add_one_le` gives
`coheight a + 1 ≤ coheight b`.  Were `b` the generic point of `C`, this would read
`coheight a + 1 ≤ 0`, which is impossible; hence, by
`Work.CurveBasics.Curve.eq_genericPoint_or_isClosed`, the singleton `{b}` is closed.  But
`c ≤ b` means `c ∈ closure {b} = {b}`, so `c = b`. -/
theorem curve_pair_of_le {k : Type u} [Field k] (C : Work.CurveBasics.Curve k) {a b c : C.left}
    (hba : b ≤ a) (hcb : c ≤ b) : b = a ∨ b = c := by
  by_cases h : b = a
  · exact Or.inl h
  refine Or.inr ?_
  -- `b ≤ a` and `b ≠ a`: since schemes are `T0`, we get `b < a`.
  have hab : ¬ a ≤ b := fun hab' =>
    h (T0Space.t0 (inseparable_iff_specializes_and.mpr
      ⟨(Scheme.le_iff_specializes).mp hab', (Scheme.le_iff_specializes).mp hba⟩))
  have hlt : b < a := ⟨hba, hab⟩
  have h1 : Order.coheight a + 1 ≤ Order.coheight b := Order.coheight_add_one_le hlt
  -- `b` is not the generic point, so it is a closed point.
  have hcl : IsClosed ({b} : Set C.left) := by
    rcases C.eq_genericPoint_or_isClosed b with hb | hb
    · exfalso
      rw [hb] at h1
      rw [C.coheight_genericPoint] at h1
      simp at h1
    · exact hb
  -- `c ≤ b` means `c ∈ closure {b}`, which is `{b}`.
  have hmem : c ∈ closure ({b} : Set C.left) :=
    specializes_iff_mem_closure.mp ((Scheme.le_iff_specializes).mp hcb)
  rw [hcl.closure_eq] at hmem
  exact (Set.mem_singleton_iff.mp hmem).symm

open CategoryTheory Limits AlgebraicGeometry in
theorem range_base_subset_pair {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    (p : Work.SpecLin.CurvePt C R) :
    Set.range (p.left.base) ⊆
      ({(p.left.base) (genericPoint (Spec (CommRingCat.of R))),
        (p.left.base) (IsLocalRing.closedPoint R)} : Set C.left) := by
  -- It suffices to test the single point `IsLocalRing.closedPoint R`; every point of `Spec R`
  -- is squeezed between the generic point and the closed point, and the curve has no chain of
  -- three distinct points.
  suffices ∀ y : ↥(Spec (CommRingCat.of R)),
      (p.left.base) y ∈ ({(p.left.base) (genericPoint (Spec (CommRingCat.of R))),
        (p.left.base) (IsLocalRing.closedPoint R)} : Set C.left) by
    rintro x ⟨y, rfl⟩
    exact this y
  intro y
  have hcont : Continuous (p.left.base) := p.left.continuous
  -- `R` is a domain, so `Spec R` is irreducible and `genericPoint` specialises to every point.
  have h1 : Specializes (genericPoint (Spec (CommRingCat.of R))) y :=
    genericPoint_specializes y
  -- `R` is local, so every point specialises to `IsLocalRing.closedPoint R`.
  have h2 : Specializes y (IsLocalRing.closedPoint R) :=
    IsLocalRing.specializes_closedPoint y
  have h1' : Specializes ((p.left.base) (genericPoint (Spec (CommRingCat.of R))))
      ((p.left.base) y) :=
    h1.map hcont
  have h2' : Specializes ((p.left.base) y)
      ((p.left.base) (IsLocalRing.closedPoint R)) :=
    h2.map hcont
  -- Translated into the specialisation order `≤` on points of `C`.
  have hba : (p.left.base) y ≤ (p.left.base) (genericPoint (Spec (CommRingCat.of R))) :=
    Scheme.le_iff_specializes.mpr h1'
  have hcb : (p.left.base) (IsLocalRing.closedPoint R) ≤ (p.left.base) y :=
    Scheme.le_iff_specializes.mpr h2'
  rcases curve_pair_of_le C (a := (p.left.base) (genericPoint (Spec (CommRingCat.of R))))
    (b := (p.left.base) y) (c := (p.left.base) (IsLocalRing.closedPoint R)) hba hcb with h | h
  · simp [h]
  · simp [h]

end Work.SpecLin.Core
