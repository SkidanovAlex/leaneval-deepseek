import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.Padics.PadicVal.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped BigOperators NumberField
open UniqueFactorizationMonoid

noncomputable section

namespace Commons.NumberTheory.NumberField

/-- `padicValNat` is additive over finite products of non-zero natural numbers. -/
lemma padicValNat_prod (p : ℕ) [Fact (Nat.Prime p)] {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ s, f i ≠ 0) :
    padicValNat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValNat p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      rw [padicValNat.mul (hf a (by simp [ha]))
        (Finset.prod_ne_zero_iff.mpr (fun i hi => hf i (by simp [hi])))]
      rw [ih (fun i hi => hf i (by simp [hi]))]

/-- For a non-zero ideal `I` of a Dedekind domain, the `p`-adic valuation of its absolute
norm equals the sum over the prime-ideal factors of `I` of the multiplicity times the
`p`-adic valuation of the norm of the prime ideal. -/
lemma padicValNat_absNorm_normalizedFactors
    {R : Type*} [CommRing R] [IsDedekindDomain R] [Module.Free ℤ R] [Module.Finite ℤ R] [Infinite R]
    {I : Ideal R} (hI : I ≠ ⊥) (p : ℕ) [Fact (Nat.Prime p)] :
    padicValNat p I.absNorm =
      ((normalizedFactors I).toFinset.sum fun P : Ideal R =>
        (normalizedFactors I).count P * padicValNat p P.absNorm) := by
  classical
  let m : Multiset (Ideal R) := normalizedFactors I
  let s : Finset (Ideal R) := m.toFinset
  have hprod : m.prod = I := by
    dsimp [m]
    exact Ideal.prod_normalizedFactors_eq_self hI
  have hms : m.prod = ∏ P ∈ s, P ^ m.count P := by
    simpa [s] using (Finset.prod_multiset_count m : _)
  have hI_norm : I.absNorm = ∏ P ∈ s, P.absNorm ^ m.count P := by
    rw [← hprod, hms]
    rw [map_prod (Ideal.absNorm)]
    refine Finset.prod_congr rfl ?_
    intro P hP
    exact map_pow (Ideal.absNorm) P (m.count P)
  have hne : ∀ P ∈ s, P.absNorm ^ m.count P ≠ 0 := by
    intro P hP
    have hPm : P ∈ m := by
      simpa [s] using (Multiset.mem_toFinset.mp (by simpa [s] using hP))
    have hPmem : P ∈ normalizedFactors I := by simpa [m] using hPm
    have hPif : P.IsPrime ∧ I ≤ P := (Ideal.mem_normalizedFactors_iff (A := R) hI).mp hPmem
    have hPne : P ≠ ⊥ := by
      intro hbot
      exact hI (le_bot_iff.mp (by simpa [hbot] using hPif.2))
    have habs : P.absNorm ≠ 0 := (Ideal.absNorm_eq_zero_iff.not).mpr hPne
    exact pow_ne_zero (m.count P) habs
  rw [hI_norm]
  rw [padicValNat_prod p s (fun P => P.absNorm ^ m.count P) hne]
  simp only [padicValNat.pow]
  rfl

/-- The `p`-adic valuation of the absolute discriminant of a number field equals the sum over
the prime ideals dividing the different ideal of their multiplicities in the different times
the `p`-adic valuation of their absolute norms. -/
theorem discriminant_valuation_sum
    {K : Type*} [Field K] [NumberField K] (p : ℕ) [Fact (Nat.Prime p)] :
    padicValNat p (NumberField.discr K).natAbs =
      ((normalizedFactors (differentIdeal ℤ (𝓞 K))).toFinset.sum fun P : Ideal (𝓞 K) =>
        (normalizedFactors (differentIdeal ℤ (𝓞 K))).count P * padicValNat p P.absNorm) := by
  classical
  have hnorm : (differentIdeal ℤ (𝓞 K)).absNorm = (NumberField.discr K).natAbs :=
    NumberField.absNorm_differentIdeal K (𝓞 K)
  rw [← hnorm]
  exact padicValNat_absNorm_normalizedFactors (R := 𝓞 K)
    (I := differentIdeal ℤ (𝓞 K)) (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 K)) p

end Commons.NumberTheory.NumberField