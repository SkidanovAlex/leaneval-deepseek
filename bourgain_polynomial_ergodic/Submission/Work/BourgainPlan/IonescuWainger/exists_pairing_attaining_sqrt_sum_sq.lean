import Mathlib

namespace Work.BourgainPlan.IonescuWainger

/-- For a finite family `z : ι → ℂ`, the linear functional `c ↦ ∑ i, c i * z i` on `ℓ²(ι)`
has operator norm `(∑ i, ‖z i‖ ^ 2) ^ (1 / 2 : ℝ)`, and this norm is attained on the unit ball.

This is the finite-dimensional duality fact that "the norm of the pairing is attained":
the Cauchy–Schwarz upper bound holds for every `c` with `∑ ‖c i‖² ≤ 1`, and the bound is
achieved by the (conjugate) multiple of `z` normalised to have `ℓ²`-norm `1`. -/
theorem exists_pairing_attaining_sqrt_sum_sq {ι : Type*} [Fintype ι] (z : ι → ℂ) :
    (∀ c : ι → ℂ, (∑ i, ‖c i‖ ^ 2) ≤ 1 → ‖∑ i, c i * z i‖ ≤ (∑ i, ‖z i‖ ^ 2) ^ (1 / 2 : ℝ)) ∧
    (∃ c : ι → ℂ, (∑ i, ‖c i‖ ^ 2) ≤ 1 ∧ ‖∑ i, c i * z i‖ = (∑ i, ‖z i‖ ^ 2) ^ (1 / 2 : ℝ)) := by
  have hnorm_real : ∀ r : ℝ, ‖(r : ℂ)‖ = |r| := by
    intro r
    rw [Complex.norm_def, Complex.normSq_ofReal, ← pow_two, Real.sqrt_sq_eq_abs]
  constructor
  · intro c hc
    have h1 : ‖∑ i, c i * z i‖ ≤ ∑ i, ‖c i‖ * ‖z i‖ := by
      calc ‖∑ i, c i * z i‖ ≤ ∑ i, ‖c i * z i‖ := norm_sum_le _ _
        _ = ∑ i, ‖c i‖ * ‖z i‖ := by simp
    have h2 : ∑ i, ‖c i‖ * ‖z i‖ ≤ Real.sqrt (∑ i, ‖c i‖ ^ 2) * Real.sqrt (∑ i, ‖z i‖ ^ 2) := by
      have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => ‖c i‖) (fun i => ‖z i‖)
      simpa using h
    have hA : Real.sqrt (∑ i, ‖c i‖ ^ 2) ≤ 1 := by
      have : Real.sqrt (∑ i, ‖c i‖ ^ 2) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hc
      simpa using this
    have hBnn : 0 ≤ Real.sqrt (∑ i, ‖z i‖ ^ 2) := Real.sqrt_nonneg _
    calc ‖∑ i, c i * z i‖ ≤ ∑ i, ‖c i‖ * ‖z i‖ := h1
      _ ≤ Real.sqrt (∑ i, ‖c i‖ ^ 2) * Real.sqrt (∑ i, ‖z i‖ ^ 2) := h2
      _ ≤ 1 * Real.sqrt (∑ i, ‖z i‖ ^ 2) := mul_le_mul_of_nonneg_right hA hBnn
      _ = (∑ i, ‖z i‖ ^ 2) ^ (1 / 2 : ℝ) := by rw [one_mul, Real.sqrt_eq_rpow]
  · by_cases hB0 : (∑ i, ‖z i‖ ^ 2) = 0
    · refine ⟨fun _ => 0, ?_, ?_⟩
      · simp
      · rw [hB0, Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0)]
        simp
    · set B : ℝ := ∑ i, ‖z i‖ ^ 2 with hB
      have hBpos : 0 < B := by
        rw [hB]
        exact lt_of_le_of_ne (Finset.sum_nonneg (fun i _ => by positivity)) (Ne.symm hB0)
      rw [← Real.sqrt_eq_rpow B]
      set s : ℝ := Real.sqrt B with hs
      have hspos : 0 < s := by rw [hs]; exact Real.sqrt_pos_of_pos hBpos
      have hsnn : 0 ≤ s := hspos.le
      have hs2 : s ^ 2 = B := by rw [hs]; exact Real.sq_sqrt hBpos.le
      refine ⟨fun i => ((s : ℂ))⁻¹ * (starRingEnd ℂ) (z i), ?_, ?_⟩
      · have hcoef : ‖((s : ℂ))⁻¹‖ ^ 2 = B⁻¹ := by
          rw [norm_inv, inv_pow, hnorm_real, sq_abs, hs2]
        have hc_i : ∀ i, ‖((s : ℂ))⁻¹ * (starRingEnd ℂ) (z i)‖ ^ 2 = B⁻¹ * ‖z i‖ ^ 2 := by
          intro i
          rw [norm_mul, Complex.norm_conj, mul_pow, hcoef]
        have hsum : ∑ i, ‖((s : ℂ))⁻¹ * (starRingEnd ℂ) (z i)‖ ^ 2 = 1 := by
          rw [Finset.sum_congr rfl (fun i _ => hc_i i)]
          rw [← Finset.mul_sum]
          rw [← hB]
          exact inv_mul_cancel₀ hBpos.ne'
        rw [hsum]
      · have hconj : ∑ i, (starRingEnd ℂ) (z i) * z i = (B : ℂ) := by
          calc ∑ i, (starRingEnd ℂ) (z i) * z i = ∑ i, ((‖z i‖ ^ 2 : ℝ) : ℂ) := by
                refine Finset.sum_congr rfl (fun i _ => ?_)
                rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
            _ = ((∑ i, ‖z i‖ ^ 2 : ℝ) : ℂ) := (Complex.ofReal_sum Finset.univ _).symm
            _ = (B : ℂ) := by rw [← hB]
        have hsum2 : ∑ i, (((s : ℂ))⁻¹ * (starRingEnd ℂ) (z i)) * z i = (s : ℂ) := by
          calc ∑ i, (((s : ℂ))⁻¹ * (starRingEnd ℂ) (z i)) * z i
              = ((s : ℂ))⁻¹ * ∑ i, (starRingEnd ℂ) (z i) * z i := by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl (fun i _ => ?_)
                ring
            _ = ((s : ℂ))⁻¹ * (B : ℂ) := by rw [hconj]
            _ = (s : ℂ) := by
                rw [← Complex.ofReal_inv, ← Complex.ofReal_mul]
                congr 1
                rw [← hs2, pow_two, ← mul_assoc, inv_mul_cancel₀ hspos.ne', one_mul]
        rw [hsum2, hnorm_real, abs_of_nonneg hsnn]

end Work.BourgainPlan.IonescuWainger
