import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped ComplexConjugate BigOperators

namespace Commons.Analysis.Integral

private lemma norm_ofReal_abs (x : ℝ) : ‖((x : ℝ) : ℂ)‖ = |x| := by simp

/-- `x * x ^ (q - 2) = x ^ (q - 1)` for `x ≥ 0` and `1 < q`. -/
private lemma mul_rpow_sub_two (x : ℝ) (hx : 0 ≤ x) {q : ℝ} (hq : 1 < q) :
    x * x ^ (q - 2) = x ^ (q - 1) := by
  rcases eq_or_lt_of_le hx with h0 | hpos
  · rw [← h0]
    rw [Real.zero_rpow (by linarith : q - 1 ≠ 0)]
    ring
  · have h := Real.rpow_add hpos (1:ℝ) (q - 2)
    rw [Real.rpow_one] at h
    have hqeq : (1:ℝ) + (q - 2) = q - 1 := by ring
    rw [hqeq] at h
    exact h.symm

/-- `x ^ 2 * x ^ (q - 2) = x ^ q` for `x ≥ 0` and `1 < q`. -/
private lemma sq_mul_rpow_sub_two (x : ℝ) (hx : 0 ≤ x) {q : ℝ} (hq : 1 < q) :
    x ^ 2 * x ^ (q - 2) = x ^ q := by
  rcases eq_or_lt_of_le hx with h0 | hpos
  · rw [← h0, Real.zero_rpow (by linarith : q ≠ 0)]
    ring
  · have h := Real.rpow_add hpos (2:ℝ) (q - 2)
    rw [Real.rpow_two] at h
    have hqeq : (2:ℝ) + (q - 2) = q := by ring
    rw [hqeq] at h
    exact h.symm

/-- `S * S ^ (1/q - 1) = S ^ (1/q)` for `0 < S`. -/
private lemma mul_rpow_pred_eq {S : ℝ} (hS : 0 < S) (q : ℝ) :
    S * S ^ (1/q - 1) = S ^ (1/q) := by
  have h : (1:ℝ) + (1/q - 1) = 1/q := by ring
  calc S * S ^ (1 / q - 1)
      = S ^ (1:ℝ) * S ^ (1 / q - 1) := by rw [Real.rpow_one]
    _ = S ^ ((1:ℝ) + (1 / q - 1)) := (Real.rpow_add hS 1 (1/q - 1)).symm
    _ = S ^ (1 / q) := by rw [h]

/-- **Dual witness for the finite `ℓ^q`-norm.**  For a nonzero complex
vector `u` and Hölder-conjugate exponents `q, q' > 1` there is a vector `g`
with `‖g‖_{q'} = 1` whose pairing with `u` realizes the norm `‖u‖_q`.  The
witness is the extremal (equality) case of Hölder's inequality:
`g i = conj (u i) · ‖u i‖ ^ (q - 2) · ‖u‖_q ^ (1 - q)`. -/
theorem exists_dual_witness {ι : Type*} [Fintype ι] {q q' : ℝ} (hq : 1 < q) (hq' : 1 < q')
    (hqq' : 1 / q + 1 / q' = 1) (u : ι → ℂ) (hu : u ≠ 0) :
    ∃ g : ι → ℂ, (∑ i, ‖g i‖ ^ q') ^ (1 / q') = 1 ∧
      (∑ i, ‖u i‖ ^ q) ^ (1 / q) ≤ ‖∑ i, u i * g i‖ := by
  have hq0 : (0:ℝ) < q := by linarith
  have hq'0 : (0:ℝ) < q' := by linarith
  have hq_ne : q ≠ 0 := ne_of_gt hq0
  have hq'_ne : q' ≠ 0 := ne_of_gt hq'0
  -- Conjugate-exponent identities.
  have hmul : (q - 1) * q' = q := by
    have key : q' + q = q * q' := by
      have h := hqq'
      field_simp [hq_ne, hq'_ne] at h
      linarith
    nlinarith
  have hneg : (1 / q - 1) * q' = -1 := by
    have h : 1 / q = 1 - 1 / q' := by linarith
    rw [h]
    field_simp
    ring
  -- Some coordinate of `u` is nonzero.
  obtain ⟨i0, hi0⟩ : ∃ i, u i ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hu (funext h)
  -- The `ℓ^q`-norm of `u`, its reciprocal power, and the dual witness.
  set S : ℝ := ∑ i, ‖u i‖ ^ q with hS_def
  set c : ℝ := S ^ (1 / q - 1) with hc_def
  set g : ι → ℂ := fun i => (starRingEnd ℂ) (u i) * ((‖u i‖ ^ (q - 2) * c : ℝ) : ℂ) with hg_def
  have hS_nonneg : 0 ≤ S := by
    rw [hS_def]
    exact Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) q
  have hS_pos : 0 < S := by
    rw [hS_def]
    have hle : ‖u i0‖ ^ q ≤ ∑ i, ‖u i‖ ^ q :=
      Finset.single_le_sum (fun i _ => Real.rpow_nonneg (norm_nonneg _) q) (Finset.mem_univ i0)
    have hpos : 0 < ‖u i0‖ ^ q :=
      Real.rpow_pos_of_pos (norm_pos_iff.mpr hi0) q
    linarith
  have hc_nonneg : 0 ≤ c := by
    rw [hc_def]
    exact Real.rpow_nonneg hS_nonneg _
  have hcq' : c ^ q' = S⁻¹ := by
    rw [hc_def, (Real.rpow_mul hS_nonneg (1/q - 1) q').symm, hneg,
      Real.rpow_neg hS_nonneg, Real.rpow_one]
  -- Norm of the witness.
  have hgi : ∀ i, ‖g i‖ = ‖u i‖ ^ (q - 1) * c := by
    intro i
    rw [hg_def]
    simp only []
    rw [norm_mul, Complex.norm_conj, norm_ofReal_abs,
      abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (norm_nonneg (u i)) (q - 2)) hc_nonneg),
      ← mul_assoc, mul_rpow_sub_two (‖u i‖) (norm_nonneg (u i)) hq]
  refine ⟨g, ?_, ?_⟩
  · -- `‖g‖_{q'} = 1`.
    have h1 : ∀ i, ‖g i‖ ^ q' = ‖u i‖ ^ q * c ^ q' := by
      intro i
      rw [hgi i, Real.mul_rpow (Real.rpow_nonneg (norm_nonneg (u i)) (q - 1)) hc_nonneg,
        (Real.rpow_mul (norm_nonneg (u i)) (q - 1) q').symm, hmul]
    rw [Finset.sum_congr rfl (fun i _ => h1 i), ← Finset.sum_mul, ← hS_def, hcq',
      mul_inv_cancel₀ (ne_of_gt hS_pos), Real.one_rpow]
  · -- The pairing realizes the norm.
    have h1 : ∀ i, u i * g i = ((‖u i‖ ^ q * c : ℝ) : ℂ) := by
      intro i
      rw [hg_def]
      simp only []
      rw [← mul_assoc, Complex.mul_conj, ← Complex.ofReal_mul, Complex.normSq_eq_norm_sq]
      congr 1
      rw [← mul_assoc, sq_mul_rpow_sub_two (‖u i‖) (norm_nonneg (u i)) hq]
    have hsum : (∑ i, u i * g i) = ((S ^ (1/q) : ℝ) : ℂ) := by
      calc (∑ i, u i * g i)
          = ∑ i, ((‖u i‖ ^ q * c : ℝ) : ℂ) := Finset.sum_congr rfl fun i _ => h1 i
        _ = (((∑ i, ‖u i‖ ^ q * c) : ℝ) : ℂ) :=
              (Complex.ofReal_sum Finset.univ (fun i => ‖u i‖ ^ q * c)).symm
        _ = ((S * c : ℝ) : ℂ) := by
              congr 1
              rw [← Finset.sum_mul, ← hS_def]
        _ = ((S ^ (1/q) : ℝ) : ℂ) := by
              congr 1
              rw [hc_def]
              exact mul_rpow_pred_eq hS_pos q
    have hB : ‖∑ i, u i * g i‖ = S ^ (1/q) := by
      rw [hsum, norm_ofReal_abs, abs_of_nonneg (Real.rpow_nonneg hS_nonneg (1/q))]
    rw [hB]

end Commons.Analysis.Integral