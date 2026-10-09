import Submission.Work.SSGRoute.ZDataTwo.Mu2Reciprocity
import Submission.Work.SSGRoute.ZDataTwo.Mu2ArithDeps
import Submission.Work.SSGRoute.ZDataTwo.isLocalNorm_ofInfinite_of_isComplex
import Submission.Commons.FieldTheory.Galois.exists_smul_eq_of_comap_eq
import Submission.Commons.RingTheory.Valuation.valuationSubringAtPrime_injective
import Submission.Commons.NumberTheory.NumberField.Valuation.exists_valuationSubring_at_prime
import Submission.Commons.NumberTheory.NumberField.numberField_of_intermediateField
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The reciprocity clause of the `μ₂` local Tate system with archimedean terms

This file assembles the reciprocity identity of `mu2Form` from the two arithmetic inputs

* `finPair_eq_zero_of_kills_inertia` (a finite place, `∤ 2`, at which both Kummer characters kill
  the inertia contributes `0`), and
* `arch_sum_eq_badRealSum` (the sum of the archimedean local invariants over a transversal of the
  conjugacy classes of involutions is the number of real places at which `β` fails to be a local
  norm from `k(√α)`),

using the global product formula `Work.HilbertSymbolGeneral.hilbertReciprocityTwo` and the rigidity
of the Galois action on the finite places (`Commons.FieldTheory.Galois.exists_smul_eq_of_comap_eq`).
-/

namespace Work.SSGRoute.ZDataTwo

open _root_.SSGRoute
open Polynomial
open scoped IntermediateField Pointwise

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

variable (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  [IsAlgClosed Ω]
  (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  [DistribMulAction (K ≃ₐ[k] K) (ZMod 2)] [SMulCommClass (K ≃ₐ[k] K) (ZMod 2) (ZMod 2)]


/-- In `ZMod 2` the only non-zero element is `1`. -/
lemma zmodTwo_eq_one_of_ne_zero (z : ZMod 2) (hz : z ≠ 0) : z = 1 := by
  fin_cases z
  · exact absurd rfl hz
  · rfl

/-- Places with the same trace on `k` have the same trace on the base. -/
lemma comap_eq_of_isConjPlace {A B : ValuationSubring Ω} (h : IsConjPlace k A B) :
    A.comap (algebraMap k Ω) = B.comap (algebraMap k Ω) := by
  obtain ⟨σ, rfl⟩ := h
  exact (Commons.NumberTheory.NumberField.Valuation.comap_smul_algebraMap (K := k) (K' := Ω)
    A σ).symm

/-! ## The quadratic Kummer field `k(√α)` -/

/-- **The Kummer field `k(√α)` of a non-square is quadratic Galois, with an explicit witness.** -/
theorem kummerField_quadratic (α : kˣ) (hnsq : ∀ d : k, d * d ≠ (α : k)) :
    IsGalois k ↥(kummerField k Ω α) ∧
      Nat.card (↥(kummerField k Ω α) ≃ₐ[k] ↥(kummerField k Ω α)) = 2 ∧
      ∃ y : ↥(kummerField k Ω α),
        y * y = algebraMap k ↥(kummerField k Ω α) (α : k) ∧
        y ∉ Set.range (algebraMap k ↥(kummerField k Ω α)) := by
  set y : Ω := ((Work.SSGRoute.kummerSqrt (K := k) (Ω := Ω) α : Ωˣ) : Ω) with hydef
  have hroot : y ^ 2 = algebraMap k Ω (α : k) := by
    rw [hydef, ← Units.val_pow_eq_pow_val, Work.SSGRoute.kummerSqrt_pow, Units.coe_map]
    rfl
  have hroot_mul : y * y = algebraMap k Ω (α : k) := by rw [← pow_two]; exact hroot
  have hfield : kummerField k Ω α = k⟮y⟯ := by rw [hydef]; rfl
  have hint : IsIntegral k y :=
    IsIntegral.of_pow (n := 2) (by norm_num)
      (by rw [hroot]; exact isIntegral_algebraMap)
  have hy_notin_bot : y ∉ (⊥ : IntermediateField k Ω) := by
    intro hmem
    obtain ⟨d, hd⟩ := IntermediateField.mem_bot.mp hmem
    refine hnsq d ?_
    have h2 : algebraMap k Ω (d * d) = algebraMap k Ω (α : k) := by
      rw [map_mul, hd, ← pow_two, hroot]
    exact (algebraMap k Ω).injective h2
  have hle2 : Module.finrank k ↥(kummerField k Ω α) ≤ 2 := by
    rw [hfield]
    exact (NK.NUV2.LC.adjoinSq_normal_finrank_le (K := k) (L := Ω) y (α : k) hroot_mul).2.2
  have hnormal : Normal k ↥(kummerField k Ω α) := by
    rw [hfield]
    exact (NK.NUV2.LC.adjoinSq_normal_finrank_le (K := k) (L := Ω) y (α : k) hroot_mul).1
  have hne0 : (minpoly k y).natDegree ≠ 0 := by
    intro h0
    have hf1 : minpoly k y = 1 := by
      rw [Polynomial.eq_C_of_natDegree_eq_zero h0]
      have hc1 : (minpoly k y).coeff 0 = 1 := by
        rw [← h0, Polynomial.coeff_natDegree, (minpoly.monic hint).leadingCoeff]
      rw [hc1, map_one]
    have hae := minpoly.aeval k y
    rw [hf1] at hae
    simpa using hae
  have hne1 : (minpoly k y).natDegree ≠ 1 := by
    intro h1
    obtain ⟨a, ha0, b, hfab⟩ := Polynomial.natDegree_eq_one.mp h1
    have hrel : algebraMap k Ω a * y + algebraMap k Ω b = 0 := by
      have hae := minpoly.aeval k y
      rw [← hfab] at hae
      simpa using hae
    have ha0' : algebraMap k Ω a ≠ 0 := fun h0 =>
      ha0 ((algebraMap k Ω).injective (by rw [h0, map_zero]))
    have hy_eq : y = (-algebraMap k Ω b) * (algebraMap k Ω a)⁻¹ := by
      have h2 : algebraMap k Ω a * y = -algebraMap k Ω b := by
        rw [add_eq_zero_iff_eq_neg] at hrel
        exact hrel
      calc y = (algebraMap k Ω a)⁻¹ * (algebraMap k Ω a * y) := by
            rw [← mul_assoc, inv_mul_cancel₀ ha0', one_mul]
        _ = (algebraMap k Ω a)⁻¹ * (-algebraMap k Ω b) := by rw [h2]
        _ = (-algebraMap k Ω b) * (algebraMap k Ω a)⁻¹ := by ring
    refine hy_notin_bot (IntermediateField.mem_bot.mpr ⟨(-b) * a⁻¹, ?_⟩)
    rw [map_mul, map_neg, map_inv₀]
    exact hy_eq.symm
  have hnat : (minpoly k y).natDegree = 2 := by
    have hdiv : minpoly k y ∣ (X ^ 2 - C (α : k) : k[X]) := by
      refine minpoly.dvd k y ?_
      rw [map_sub, map_pow, aeval_X, aeval_C, hroot, sub_self]
    have hq : (X ^ 2 - C (α : k) : k[X]) ≠ 0 :=
      Polynomial.X_pow_sub_C_ne_zero (by norm_num) (α : k)
    have hle : (minpoly k y).natDegree ≤ 2 :=
      calc (minpoly k y).natDegree ≤ (X ^ 2 - C (α : k) : k[X]).natDegree :=
            Polynomial.natDegree_le_of_dvd hdiv hq
        _ = 2 := Polynomial.natDegree_X_pow_sub_C (n := 2) (r := (α : k))
    omega
  have hfinrank : Module.finrank k ↥(kummerField k Ω α) = 2 := by
    have hfr : Module.finrank k ↥(kummerField k Ω α) =
        (minpoly k y).natDegree := by
      rw [hfield]
      exact IntermediateField.adjoin.finrank hint
    rw [hfr, hnat]
  have hgal : IsGalois k ↥(kummerField k Ω α) := isGalois_iff.mpr ⟨inferInstance, hnormal⟩
  haveI : IsGalois k ↥(kummerField k Ω α) := hgal
  refine ⟨hgal, ?_, ?_⟩
  · rw [IsGalois.card_aut_eq_finrank k ↥(kummerField k Ω α)]
    exact hfinrank
  · refine ⟨⟨y, ?_⟩, ?_, ?_⟩
    · rw [hfield]
      exact IntermediateField.mem_adjoin_simple_self k y
    · refine Subtype.ext ?_
      rw [IntermediateField.coe_algebraMap_apply]
      change y * y = algebraMap k Ω (α : k)
      exact hroot_mul
    · rintro ⟨d, hd⟩
      refine hnsq d ?_
      have hdy : y = algebraMap k Ω d := by
        have h := congrArg (fun z : ↥(kummerField k Ω α) => (z : Ω)) hd
        simpa using h.symm
      have hd2 : algebraMap k Ω (d * d) = algebraMap k Ω (α : k) := by
        rw [map_mul, ← hdy, ← pow_two, hroot]
      exact (algebraMap k Ω).injective hd2

/-! ## Places: rigidity of the prime below a finite place -/

/-- The prime below a finite place does not depend on the proof of finiteness. -/
lemma primeBelow_irrel (A : ValuationSubring Ω) (h₁ h₂ : IsFinPlace k A) :
    primeBelow k Ω A h₁ = primeBelow k Ω A h₂ := by
  unfold primeBelow
  exact congrArg Exists.choose (Subsingleton.elim _ _)

/-- Two finite places with the same trace on `k` have the same prime below. -/
lemma primeBelow_eq_of_comap_eq {A B : ValuationSubring Ω} (hA : IsFinPlace k A)
    (hB : IsFinPlace k B) (h : A.comap (algebraMap k Ω) = B.comap (algebraMap k Ω)) :
    primeBelow k Ω A hA = primeBelow k Ω B hB := by
  refine Commons.RingTheory.Valuation.valuationSubringAtPrime_injective
    (R := NumberField.RingOfIntegers k) (K := k) ?_
  rw [← primeBelow_spec k Ω A hA, ← primeBelow_spec k Ω B hB, h]

/-- A finite place is determined up to conjugacy by its trace on `k`. -/
lemma isConjPlace_of_comap_eq {A B : ValuationSubring Ω} (hA : IsFinPlace k A)
    (h : A.comap (algebraMap k Ω) = B.comap (algebraMap k Ω)) :
    IsConjPlace k A B :=
  Commons.FieldTheory.Galois.exists_smul_eq_of_comap_eq A B hA h

/-- Two finite places with the same prime below are conjugate. -/
lemma isConjPlace_of_primeBelow_eq {A B : ValuationSubring Ω} (hA : IsFinPlace k A)
    (hB : IsFinPlace k B) (h : primeBelow k Ω A hA = primeBelow k Ω B hB) :
    IsConjPlace k A B := by
  refine isConjPlace_of_comap_eq k Ω hA ?_
  rw [primeBelow_spec k Ω A hA, primeBelow_spec k Ω B hB, h]

end Work.SSGRoute.ZDataTwo
