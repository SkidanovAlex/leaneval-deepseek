/-
# The unit step of the affine-chart core of specialisation of linear equivalence

The remaining gap of the affine-chart proof of specialisation of linear equivalence over a
valuation ring `R` (`Work.SpecLin.Alt.chartCoreDiv`, `Work.SpecLin.Setup.chartCoreDivPull`) is a
*local* statement about the relative chart `B = A ⊗[K] R` of a curve over a field `K`.

This file isolates the *provable* part of it.  Let `A` be a `K`-algebra, `R` a valuation ring over
`K`, `B = A ⊗[K] R`, and `P = 𝔪_R · B`.  If `x ∈ B ∖ P` is primitive and if `x` has a *primitive*
"inverse numerator", i.e. there are `b ∈ B ∖ P` and `0 ≠ s ∈ R` with `x · b = s`, then `x` is a
unit of `B`.

The proof is the content-normalisation argument, and it uses only that `B ⧸ P = A ⊗[K] κ` is a
domain (the special fibre is integral); in particular no Noetherianity of `R`, no dimension theory
and no Krull principal ideal theorem is involved.
-/
import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.style.haveILetI false

open scoped TensorProduct

namespace Work.SpecLin.Setup

universe u

/-- **The unit step of the affine-chart core, "special-fibre" form.**

Let `K` be a field, `A` a nontrivial `K`-algebra, `R` a valuation ring which is a `K`-algebra and
`B = A ⊗[K] R` a domain whose special fibre `B ⧸ 𝔪_R·B` is a domain.  If `x ∈ B` is primitive
modulo `P = 𝔪_R·B` and if some *primitive* `b ∈ B` and some `0 ≠ s ∈ R` satisfy `x · b = s`,
then `x` is a unit of `B`.

Indeed, if `s ∈ 𝔪_R` then `x·b ∈ P`, so the images of `x` and `b` in the domain `B ⧸ P` are
nonzero elements with zero product, a contradiction; hence `s ∈ Rˣ` and `x` is invertible. -/
theorem isUnit_of_mul_eq_of_notMem_maximalIdeal_map
    {K : Type u} [Field K] {A : Type u} [CommRing A] [Algebra K A]
    {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    [IsDomain (TensorProduct K A R)]
    (hdom : IsDomain (TensorProduct K A R ⧸
      (IsLocalRing.maximalIdeal R).map
        (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R))))
    (x : TensorProduct K A R)
    (hx : x ∉ (IsLocalRing.maximalIdeal R).map
      (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R)))
    (hb : ∃ (b : TensorProduct K A R) (s : R),
      b ∉ (IsLocalRing.maximalIdeal R).map
        (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R)) ∧ s ≠ 0 ∧
      (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R)) s = x * b) :
    IsUnit x := by
  obtain ⟨b, s, hbP, hs, hEq⟩ := hb
  by_cases hs' : s ∈ IsLocalRing.maximalIdeal R
  · exfalso
    have hmem : (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R)) s ∈
        (IsLocalRing.maximalIdeal R).map
          (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R)) :=
      Ideal.mem_map_of_mem _ hs'
    rw [hEq] at hmem
    have hzero : (Ideal.Quotient.mk _ (x * b) : TensorProduct K A R ⧸ _) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    rw [map_mul] at hzero
    have hx0 : (Ideal.Quotient.mk _ x : TensorProduct K A R ⧸ _) ≠ 0 :=
      fun h => hx (Ideal.Quotient.eq_zero_iff_mem.mp h)
    have hb0 : (Ideal.Quotient.mk _ b : TensorProduct K A R ⧸ _) ≠ 0 :=
      fun h => hbP (Ideal.Quotient.eq_zero_iff_mem.mp h)
    exact mul_ne_zero hx0 hb0 hzero
  · have hunit : IsUnit s := by
      rw [IsLocalRing.mem_maximalIdeal] at hs'
      exact not_not.mp hs'
    obtain ⟨s', hs'⟩ := hunit
    refine IsUnit.of_mul_eq_one
      (b * (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R)) (↑s'⁻¹)) ?_
    rw [← mul_assoc, ← hEq, ← map_mul, show s * (↑s'⁻¹ : R) = 1 from ?_, map_one]
    rw [← hs']
    exact Units.mul_inv s'

end Work.SpecLin.Setup
