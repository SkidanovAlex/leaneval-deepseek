import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry
open scoped Classical

namespace Work.SpecLin.Core

/-- **The order of vanishing in a discrete valuation ring, membership form.**

Let `A` be a discrete valuation ring with field of fractions `K`.  For a nonzero `x : A` the
statement `Ring.ordFrac A (algebraMap A K x) ≥ n` (in the monoid with zero `ℤᵐ⁰`, i.e. after
coercing the integer `n`) is equivalent to `x` lying in the `n`-th power of the maximal ideal
of `A`.

This is the local form of the dictionary between the order of vanishing and the powers of the
prime of a point. -/
theorem le_ordFrac_iff_mem_maximalIdeal_pow {A K : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    (x : A) (hx : x ≠ 0) (n : ℕ) :
    (WithZero.exp (n : ℤ) ≤ Ring.ordFrac A (algebraMap A K x)) ↔
      x ∈ (IsLocalRing.maximalIdeal A) ^ n := by
  have hm : x ∈ (IsLocalRing.maximalIdeal A) ^ n ↔
      (IsDiscreteValuationRing.maximalIdeal A).intValuation x ≤ WithZero.exp (-(n : ℤ)) := by
    rw [show IsLocalRing.maximalIdeal A =
      (IsDiscreteValuationRing.maximalIdeal A).asIdeal from rfl]
    exact (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem _ x n).symm
  rw [hm, Ring.ordFrac_eq_valuation_inv (K := K) (algebraMap A K x),
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDedekindDomain.HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _
        (show x ≠ 0 from hx),
      ← WithZero.exp_neg, WithZero.exp_le_exp, WithZero.exp_le_exp, neg_le_neg_iff]
  simp

/-- **The `n`-th power of the maximal ideal of a localization.**

Let `p` be a maximal prime of a ring `R` and `S` a localization of `R` at `p`.  Then an element
`a : R` maps into the `n`-th power of the maximal ideal of `S` if and only if `a ∈ p ^ n`. -/
theorem algebraMap_mem_maximalIdeal_pow_iff {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] [IsLocalization.AtPrime S p] [IsLocalRing S] [p.IsMaximal]
    (a : R) (n : ℕ) :
    algebraMap R S a ∈ (IsLocalRing.maximalIdeal S) ^ n ↔ a ∈ p ^ n := by
  rw [← IsLocalization.AtPrime.under_maximalIdeal_pow p S n, Ideal.mem_comap]

/-- **Order of vanishing on an affine chart, membership form.** -/
theorem ord_germ_eq_iff_mem_pow {X : AlgebraicGeometry.Scheme} [AlgebraicGeometry.IsIntegral X]
    [AlgebraicGeometry.IsLocallyNoetherian X] (U : X.Opens)
    (hU : AlgebraicGeometry.IsAffineOpen U) [Nonempty U]
    [IsDedekindDomain (X.presheaf.obj (Opposite.op U))]
    (z : X) (hz : z ∈ U) (hz1 : Order.coheight z = 1)
    (a : X.presheaf.obj (Opposite.op U)) (n : ℕ) (ha : a ≠ 0) :
    ((n : ℤ) ≤ X.ord (AlgebraicGeometry.Scheme.germToFunctionField X U a) z)
      ↔ a ∈ (hU.primeIdealOf ⟨z, hz⟩).asIdeal ^ n := by
  letI hAlg : Algebra (X.presheaf.obj (Opposite.op U)) (X.presheaf.stalk z) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨z, hz⟩
  haveI hLoc : IsLocalization.AtPrime (X.presheaf.stalk z) (hU.primeIdealOf ⟨z, hz⟩).asIdeal :=
    hU.isLocalization_stalk ⟨z, hz⟩
  haveI hKrull : Ring.KrullDimLE 1 (X.presheaf.stalk z) := krullDimLE_of_coheight_le hz1.le
  haveI hLR : IsLocalRing (X.presheaf.stalk z) :=
    IsLocalization.AtPrime.isLocalRing (X.presheaf.stalk z) (hU.primeIdealOf ⟨z, hz⟩).asIdeal
  have hf : X.germToFunctionField U a ≠ 0 := fun h =>
    ha (Scheme.germToFunctionField_injective X U (by simpa using h))
  rw [Scheme.le_ord_iff hz1 hf]
  rw [← Scheme.algebraMap_germ_eq_germToFunctionField X hz a]
  change WithZero.exp (n : ℤ) ≤
    Ring.ordFrac (X.presheaf.stalk z) (algebraMap (X.presheaf.stalk z) X.functionField
      (algebraMap (X.presheaf.obj (Opposite.op U)) (X.presheaf.stalk z) a)) ↔
    a ∈ (hU.primeIdealOf ⟨z, hz⟩).asIdeal ^ n
  by_cases hp0 : (hU.primeIdealOf ⟨z, hz⟩).asIdeal = ⊥
  · -- The point `z` is the generic point of the chart: `a` is a unit at `z`.
    have ha' : a ∈ (hU.primeIdealOf ⟨z, hz⟩).asIdeal.primeCompl := by
      rw [Ideal.mem_primeCompl_iff, hp0, Ideal.mem_bot]
      exact ha
    have hunit : IsUnit (algebraMap (X.presheaf.obj (Opposite.op U)) (X.presheaf.stalk z) a) :=
      IsLocalization.map_units _ ⟨a, ha'⟩
    rw [Ring.ordFrac_of_isUnit hunit, hp0]
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    constructor
    · intro h
      have hn : n = 0 := by omega
      subst hn
      simp
    · intro h
      by_cases hn : n = 0
      · subst hn
        omega
      · exfalso
        rw [Ideal.bot_pow hn] at h
        exact ha (Ideal.mem_bot.mp h)
  · -- `p` is a nonzero prime of the Dedekind domain `Γ(X, U)`, so the stalk at `z` is a DVR
    -- and the order of vanishing is the `p`-adic valuation.
    haveI hDVR : IsDiscreteValuationRing (X.presheaf.stalk z) :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain _ hp0 _
    haveI hMax : (hU.primeIdealOf ⟨z, hz⟩).asIdeal.IsMaximal :=
      Ideal.IsPrime.isMaximal (hU.primeIdealOf ⟨z, hz⟩).isPrime hp0
    have hinj : Function.Injective
        (algebraMap (X.presheaf.obj (Opposite.op U)) (X.presheaf.stalk z)) :=
      IsLocalization.injective _
        (Ideal.primeCompl_le_nonZeroDivisors (hU.primeIdealOf ⟨z, hz⟩).asIdeal)
    have hx : algebraMap (X.presheaf.obj (Opposite.op U)) (X.presheaf.stalk z) a ≠ 0 :=
      fun h => ha (hinj (by simpa using h))
    rw [le_ordFrac_iff_mem_maximalIdeal_pow _ hx n,
      algebraMap_mem_maximalIdeal_pow_iff (hU.primeIdealOf ⟨z, hz⟩).asIdeal a n]

end Work.SpecLin.Core
