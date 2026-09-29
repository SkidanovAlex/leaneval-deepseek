import Mathlib
import Submission.Work.C17g.changeOrigin_ofScalars

namespace Work.C17f

/-- A summable sequence of complex numbers is bounded. -/
lemma exists_bound_of_summable (f : ℕ → ℂ) (hf : Summable f) : ∃ M : ℝ, ∀ n, ‖f n‖ ≤ M := by
  have hb : Bornology.IsBounded (Set.range f) :=
    Metric.isBounded_range_of_tendsto f hf.tendsto_atTop_zero
  obtain ⟨M, hM⟩ := hb.subset_closedBall (0 : ℂ)
  exact ⟨M, fun n => by
    have h1 := hM (Set.mem_range_self n)
    simpa only [Metric.mem_closedBall, dist_zero_right] using h1⟩

/-- If a power series `∑ cₙ zⁿ` converges (pointwise) to `F z` on the disc `‖z‖ < r`, then
`F` is complex differentiable there and its derivative is the term-by-term derivative series. -/
theorem deriv_hasSum_powSeries (c : ℕ → ℂ) (r : ℝ) (F : ℂ → ℂ)
    (h : ∀ z : ℂ, ‖z‖ < r → HasSum (fun n : ℕ => c n * z ^ n) (F z)) :
    ∀ z : ℂ, ‖z‖ < r →
      HasSum (fun n : ℕ => ((n : ℂ) + 1) * c (n + 1) * z ^ n) (deriv F z) := by
  intro z hz
  -- choose `ρ` with `‖z‖ < ρ < r`
  obtain ⟨ρ, hzρ, hρr⟩ : ∃ ρ, ‖z‖ < ρ ∧ ρ < r := ⟨(‖z‖ + r) / 2, by linarith, by linarith⟩
  have hρpos : 0 < ρ := lt_of_le_of_lt (norm_nonneg z) hzρ
  -- the series converges at the point `ρ`
  have hρconv : HasSum (fun n => c n * (ρ : ℂ) ^ n) (F (ρ : ℂ)) := by
    refine h (ρ : ℂ) ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρpos]
    exact hρr
  have hsumρ : Summable (fun n => c n * (ρ : ℂ) ^ n) := hρconv.summable
  obtain ⟨M, hM⟩ := exists_bound_of_summable _ hsumρ
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  -- choose `ρ'` with `‖z‖ < ρ' < ρ`
  obtain ⟨ρ', hzρ', hρ'ρ⟩ : ∃ ρ', ‖z‖ < ρ' ∧ ρ' < ρ :=
    ⟨(‖z‖ + ρ) / 2, by linarith, by linarith⟩
  have hρ'pos : 0 < ρ' := lt_of_le_of_lt (norm_nonneg z) hzρ'
  -- geometric ratio
  set t : ℝ := ρ' / ρ with ht
  have ht0 : 0 ≤ t := by rw [ht]; exact div_nonneg hρ'pos.le hρpos.le
  have ht1 : t < 1 := by rw [ht, div_lt_one hρpos]; exact hρ'ρ
  have hu : Summable (fun n => M * t ^ n) := (summable_geometric_of_lt_one ht0 ht1).mul_left M
  have hzU : z ∈ Metric.ball (0 : ℂ) ρ' := by
    simp only [Metric.mem_ball, dist_zero_right]; exact hzρ'
  have hdiff : ∀ i : ℕ, DifferentiableOn ℂ (fun w : ℂ => c i * w ^ i) (Metric.ball (0 : ℂ) ρ') :=
    fun i => DifferentiableOn.mul (differentiableOn_const (c i))
      (DifferentiableOn.pow differentiableOn_id i)
  have hρ't : ρ * t = ρ' := by rw [ht]; exact mul_div_cancel₀ _ (ne_of_gt hρpos)
  -- domination on the disc of radius `ρ'`
  have hbound : ∀ (i : ℕ) (w : ℂ), w ∈ Metric.ball (0 : ℂ) ρ' → ‖c i * w ^ i‖ ≤ M * t ^ i := by
    intro i w hw
    have hw' : ‖w‖ < ρ' := by simpa [Metric.mem_ball, dist_zero_right] using hw
    have hpow : ρ' ^ i = ρ ^ i * t ^ i := by rw [← hρ't, mul_pow]
    calc ‖c i * w ^ i‖ = ‖c i‖ * ‖w‖ ^ i := by rw [norm_mul, norm_pow]
      _ ≤ ‖c i‖ * ρ' ^ i :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg w) hw'.le i) (norm_nonneg _)
      _ = (‖c i‖ * ρ ^ i) * t ^ i := by rw [hpow]; ring
      _ = ‖c i * (ρ : ℂ) ^ i‖ * t ^ i := by
            rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρpos]
      _ ≤ M * t ^ i := mul_le_mul_of_nonneg_right (hM i) (pow_nonneg ht0 i)
  -- differentiation of a uniformly dominated series
  have hmain := Complex.hasSum_deriv_of_summable_norm
      (F := fun i : ℕ => fun w : ℂ => c i * w ^ i) hu hdiff Metric.isOpen_ball hbound hzU
  -- identify the derivative of the sum with `deriv F z`
  have hzr : z ∈ Metric.ball (0 : ℂ) r := by simpa [Metric.mem_ball, dist_zero_right] using hz
  have hEqOn : (fun w : ℂ => ∑' i : ℕ, c i * w ^ i) =ᶠ[nhds z] F := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hzr] with w hw
    exact (h w (by simpa [Metric.mem_ball, dist_zero_right] using hw)).tsum_eq
  have hderiv_eq : deriv (fun w : ℂ => ∑' i : ℕ, c i * w ^ i) z = deriv F z := hEqOn.deriv_eq
  rw [hderiv_eq] at hmain
  -- drop the zeroth term and reindex
  have hf0 : deriv (fun w : ℂ => c 0 * w ^ 0) z = 0 := by simp
  have hmain2 : HasSum (fun n : ℕ => deriv (fun w : ℂ => c (n + 1) * w ^ (n + 1)) z)
      (deriv F z) := by
    have hh := (hasSum_nat_add_iff'
      (f := fun i : ℕ => deriv (fun w : ℂ => c i * w ^ i) z) 1).mpr hmain
    simpa [Finset.sum_range_one, hf0] using hh
  -- identify each term
  refine hmain2.congr_fun ?_
  intro n
  symm
  rw [deriv_const_mul (c (n + 1)) (differentiableAt_id.pow (n + 1))]
  rw [deriv_fun_pow differentiableAt_id (n + 1)]
  simp only [deriv_id'', mul_one]
  rw [show n + 1 - 1 = n from by omega]
  rw [show ((n + 1 : ℕ) : ℂ) = (n : ℂ) + 1 from by push_cast; ring]
  ring

end Work.C17f
