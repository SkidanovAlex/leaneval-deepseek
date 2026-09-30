import Mathlib
import Submission.Work.SpecLin.Alt.chartMap
import Submission.Work.SpecLin.Alt.chartTensorPointSetup
import Submission.Work.SpecLin.Alt.isLocalization_chartTensorSectionsMap
import Submission.Work.SpecLin.Alt.exists_mul_eq_iff_of_isLocalization
import Submission.Work.SpecLin.Alt.exists_mul_eq_iff_ordAt_of_primeIdealOf
import Submission.Work.SpecLin.Core.linEquiv_of_sections
import Submission.Work.SpecLin.Core.mem_primeIdealOf_ptToPoint_iff
import Submission.Work.SpecLin.Core.ordChart
import Submission.Work.CurveBasics.Place.mem_valuationSubring_iff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.SpecLin.Alt

open CategoryTheory Limits AlgebraicGeometry

/-- **A prime ideal is determined by the fractions whose denominator lies outside it.**

Let `i : A →+* L` be an injective ring homomorphism from a commutative ring `A` into a field
`L`, and let `r, r'` be ideals of `A`.  If the two sets
`{x : L | ∃ a b : A, b ∉ r ∧ x * i b = i a}` and
`{x : L | ∃ a b : A, b ∉ r' ∧ x * i b = i a}` coincide (written pointwise as the hypothesis
`h`), then `r = r'`.

Indeed, `x * i b = i a` with `b ∉ r` is the condition that `x` is a fraction `i a / i b` whose
denominator is not in `r`, i.e. that `x` lies in the image of the localisation `A_r → L`.  An
element `s` of `A` lies in `r` exactly when `(i s)⁻¹` is *not* such a fraction. -/
theorem prime_eq_of_forall_exists_mul_eq
    {A : Type _} [CommRing A] {L : Type _} [Field L]
    (i : A →+* L) (hi : Function.Injective i) (r r' : Ideal A)
    (h : ∀ x : L, (∃ a b : A, b ∉ r ∧ x * i b = i a) ↔
                  (∃ a b : A, b ∉ r' ∧ x * i b = i a)) :
    r = r' := by
  refine le_antisymm (fun s hs => ?_) (fun s hs => ?_)
  · by_cases hs0 : s = 0
    · rw [hs0]; exact r'.zero_mem
    · by_contra hc
      have his : i s ≠ 0 := fun hh => hs0 (hi (by rw [hh, map_zero]))
      have hmem' : (i s)⁻¹ ∈ {x : L | ∃ a b : A, b ∉ r' ∧ x * i b = i a} :=
        ⟨1, s, hc, by rw [map_one, inv_mul_cancel₀ his]⟩
      obtain ⟨a, b, hb, heq⟩ := (h _).mpr hmem'
      have h2 : i s * ((i s)⁻¹ * i b) = i s * i a := by rw [heq]
      rw [mul_inv_cancel_left₀ his (i b)] at h2
      have h1 : i b = i (s * a) := by rw [map_mul]; exact h2
      exact hb (by rw [hi h1]; exact r.mul_mem_right a hs)
  · by_cases hs0 : s = 0
    · rw [hs0]; exact r.zero_mem
    · by_contra hc
      have his : i s ≠ 0 := fun hh => hs0 (hi (by rw [hh, map_zero]))
      have hmem : (i s)⁻¹ ∈ {x : L | ∃ a b : A, b ∉ r ∧ x * i b = i a} :=
        ⟨1, s, hc, by rw [map_one, inv_mul_cancel₀ his]⟩
      obtain ⟨a, b, hb, heq⟩ := (h _).mp hmem
      have h2 : i s * ((i s)⁻¹ * i b) = i s * i a := by rw [heq]
      rw [mul_inv_cancel_left₀ his (i b)] at h2
      have h1 : i b = i (s * a) := by rw [map_mul]; exact h2
      exact hb (by rw [hi h1]; exact r'.mul_mem_right a hs)

theorem pointDict_prime {K : Type _} [Field K] {C : Work.CurveBasics.Curve K}
    (R : Type _) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    (W : C.left.Opens) (hW : AlgebraicGeometry.IsAffineOpen W) [Nonempty W]
    (p : Ideal (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)) (hp : p.IsPrime)
    (hmiss : ∀ r : R, r ≠ 0 →
      (Algebra.TensorProduct.includeRight (R := K)
        (A := C.left.presheaf.obj (Opposite.op W)) (B := R)) r ∉ p)
    (Q : (C.baseChange (FractionRing R)).Place)
    (hQmem : Q.point ∈ C.bcOpens (FractionRing R) W)
    (hQ : ∀ x : (C.baseChange (FractionRing R)).functionField,
      (∃ a b : Work.SpecLin.Core.chartTensor (K := K) (C := C) R W,
          b ∉ p ∧ x * Work.SpecLin.Alt.chartTensorMap R W hW b
            = Work.SpecLin.Alt.chartTensorMap R W hW a)
        ↔ 0 ≤ (C.baseChange (FractionRing R)).ordAt x Q) :
    ((Work.SpecLin.Alt.chartAffineOpen R W hW).primeIdealOf ⟨Q.point, hQmem⟩).asIdeal
      = Work.SpecLin.Alt.chartTensorPrime R W hW p := by
  classical
  haveI : Nonempty (C.bcOpens (FractionRing R) W) := C.bcOpens_nonempty (FractionRing R) W
  letI : Algebra (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W) (chartSections R W) :=
    (chartTensorSectionsMap R W hW).toAlgebra
  letI : Algebra (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)
      ((C.baseChange (FractionRing R)).functionField) :=
    (chartTensorMap R W hW).toAlgebra
  haveI : IsLocalization (chartContentSubmonoid (K := K) (C := C) R W) (chartSections R W) :=
    isLocalization_chartTensorSectionsMap R W hW
  haveI : IsScalarTower (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)
      (chartSections R W) ((C.baseChange (FractionRing R)).functionField) :=
    IsScalarTower.of_algebraMap_eq (fun b => rfl)
  set q : Ideal (chartSections R W) :=
    ((chartAffineOpen R W hW).primeIdealOf ⟨Q.point, hQmem⟩).asIdeal with hqdef
  -- The prime of the point `Q` inside the chart `W_F` is the set of chart sections which are
  -- non-units in the local ring of `C_F` at `Q`, i.e. the fractions with denominator outside it.
  have hCx : ∀ x : (C.baseChange (FractionRing R)).functionField,
      (∃ a b : chartSections R W, b ∉ q ∧
          x * algebraMap (chartSections R W) ((C.baseChange (FractionRing R)).functionField) b
        = algebraMap (chartSections R W) ((C.baseChange (FractionRing R)).functionField) a)
        ↔ 0 ≤ (C.baseChange (FractionRing R)).ordAt x Q := by
    intro x
    exact exists_mul_eq_iff_ordAt_of_primeIdealOf
      (C := C.baseChange (FractionRing R)) (C.bcOpens (FractionRing R) W)
      (chartAffineOpen R W hW) Q hQmem x
  -- The chart dictionary `hQ`, transported from the relative chart `B` to its localisation
  -- `S = Γ(C_F, W_F)`, identifies the same set with the fractions whose denominator lies
  -- outside `p' = p·S`.
  have hBx : ∀ x : (C.baseChange (FractionRing R)).functionField,
      (∃ a b : Work.SpecLin.Core.chartTensor (K := K) (C := C) R W,
          b ∉ p ∧ x * chartTensorMap R W hW b = chartTensorMap R W hW a)
        ↔ (∃ a b : chartSections R W,
            b ∉ chartTensorPrime R W hW p ∧
              x * algebraMap (chartSections R W)
                    ((C.baseChange (FractionRing R)).functionField) b
                = algebraMap (chartSections R W)
                    ((C.baseChange (FractionRing R)).functionField) a) := by
    intro x
    exact exists_mul_eq_iff_of_isLocalization
      (R := Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)
      (S := chartSections R W)
      (K := (C.baseChange (FractionRing R)).functionField)
      (chartContentSubmonoid (K := K) (C := C) R W) p
      (chartContentSubmonoid_disjoint R W p hmiss) x
  -- Both primes are therefore cut out by the same set of fractions.
  have hiff : ∀ x : (C.baseChange (FractionRing R)).functionField,
      (∃ a b : chartSections R W, b ∉ q ∧
          x * algebraMap (chartSections R W) ((C.baseChange (FractionRing R)).functionField) b
        = algebraMap (chartSections R W) ((C.baseChange (FractionRing R)).functionField) a)
        ↔ (∃ a b : chartSections R W,
            b ∉ chartTensorPrime R W hW p ∧
              x * algebraMap (chartSections R W)
                    ((C.baseChange (FractionRing R)).functionField) b
                = algebraMap (chartSections R W)
                    ((C.baseChange (FractionRing R)).functionField) a) := by
    intro x
    exact (hCx x).trans ((hQ x).symm.trans (hBx x))
  exact prime_eq_of_forall_exists_mul_eq
    (algebraMap (chartSections R W) ((C.baseChange (FractionRing R)).functionField))
    (fun a b hab => Scheme.germToFunctionField_injective (C.baseChange (FractionRing R)).left
      (C.bcOpens (FractionRing R) W) hab)
    q (chartTensorPrime R W hW p) hiff

end Work.SpecLin.Alt
