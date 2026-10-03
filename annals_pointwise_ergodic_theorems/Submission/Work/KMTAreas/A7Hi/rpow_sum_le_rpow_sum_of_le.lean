import Mathlib

namespace Work.KMTAreas.A7Hi

/-- Superadditivity of `x ↦ x ^ c` (`1 ≤ c`) for finite sums of `ℝ≥0∞`-numbers: the `c`-th power
of a sum dominates the sum of the `c`-th powers. -/
private theorem a7hi_sum_rpow_le_rpow_sum {ι : Type*} (s : Finset ι) {c : ℝ} (hc : 1 ≤ c)
    (y : ι → ENNReal) :
    ∑ i ∈ s, y i ^ c ≤ (∑ i ∈ s, y i) ^ c := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ENNReal.zero_rpow_of_pos (lt_of_lt_of_le zero_lt_one hc)]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      calc y a ^ c + ∑ i ∈ s, y i ^ c
          = (∑ i ∈ s, y i ^ c) + y a ^ c := add_comm _ _
        _ ≤ (∑ i ∈ s, y i) ^ c + y a ^ c := add_le_add ih le_rfl
        _ = y a ^ c + (∑ i ∈ s, y i) ^ c := add_comm _ _
        _ ≤ (y a + ∑ i ∈ s, y i) ^ c := ENNReal.add_rpow_le_rpow_add _ _ hc

/-- For `0 < P ≤ R` the `ℓ^R`-norm of a finite family of `ℝ≥0∞`-numbers is dominated by its
`ℓ^P`-norm.  (Both exponents positive; the family is indexed by a finite type, so this is the
`ℓ^R ⊆ ℓ^P` embedding for counting measure of total mass `≥ 1`.) -/
theorem rpow_sum_le_rpow_sum_of_le {ι : Type*} [Fintype ι] {P R : ℝ} (hP : 0 < P) (hPR : P ≤ R)
    (a : ι → ENNReal) :
    (∑ i, a i ^ R) ^ (1 / R) ≤ (∑ i, a i ^ P) ^ (1 / P) := by
  have hR : 0 < R := lt_of_lt_of_le hP hPR
  have hθ : 1 ≤ R / P := (one_le_div hP).2 hPR
  -- `x^R = (x^P)^(R/P)`
  have hexp₁ : P * (R / P) = R := by field_simp
  -- `(∑ a^P)^(1/P) = ((∑ a^P)^(R/P))^(1/R)`
  have hexp₂ : (R / P) * (1 / R) = 1 / P := by field_simp
  have hpow : ∀ x : ENNReal, (x ^ P) ^ (R / P) = x ^ R := fun x => by
    rw [← ENNReal.rpow_mul, hexp₁]
  -- the `ℓ^θ`-comparison with `x i = a i ^ P`, `θ = R / P`
  have hmain : ∑ i, a i ^ R ≤ (∑ i, a i ^ P) ^ (R / P) := by
    have hL : (∑ i, a i ^ R) = ∑ i, (a i ^ P) ^ (R / P) :=
      Finset.sum_congr rfl fun i _ => (hpow (a i)).symm
    rw [hL]
    simpa using a7hi_sum_rpow_le_rpow_sum (Finset.univ : Finset ι) hθ (fun i => a i ^ P)
  -- raise both sides to the power `1 / R`
  calc (∑ i, a i ^ R) ^ (1 / R)
      ≤ ((∑ i, a i ^ P) ^ (R / P)) ^ (1 / R) :=
        ENNReal.rpow_le_rpow hmain (one_div_pos.mpr hR).le
    _ = (∑ i, a i ^ P) ^ (1 / P) := by
        rw [← ENNReal.rpow_mul, hexp₂]

end Work.KMTAreas.A7Hi
