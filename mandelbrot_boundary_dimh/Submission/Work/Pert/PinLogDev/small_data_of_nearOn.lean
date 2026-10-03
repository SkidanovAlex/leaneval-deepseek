import Mathlib
import Submission.Work.Pert.small_of_nearOn
import Submission.Work.Interfaces.Parabolic

namespace Work.Pert.PinLogDev

/-- `‖1 - exp t‖ ≤ (9/8)‖t‖` for `‖t‖ ≤ 1/8`: from `‖exp t - 1 - t‖ ≤ ‖t‖²`. -/
private lemma norm_one_sub_exp_le {t : ℂ} (ht : ‖t‖ ≤ 1/8) : ‖1 - Complex.exp t‖ ≤ 9/8 * ‖t‖ := by
  have h1 : ‖t‖ ≤ 1 := by linarith
  have htri : ‖1 - Complex.exp t‖ ≤ ‖t‖ + ‖Complex.exp t - 1 - t‖ := by
    have heq : 1 - Complex.exp t = -(t + (Complex.exp t - 1 - t)) := by ring
    rw [heq, norm_neg]
    exact norm_add_le t _
  have h2 : ‖Complex.exp t - 1 - t‖ ≤ ‖t‖ ^ 2 := Complex.norm_exp_sub_one_sub_id_le h1
  have h4 : ‖t‖ * ‖t‖ ≤ ‖t‖ * (1/8) :=
    mul_le_mul_of_nonneg_left ht (norm_nonneg t)
  calc ‖1 - Complex.exp t‖ ≤ ‖t‖ + ‖Complex.exp t - 1 - t‖ := htri
    _ ≤ ‖t‖ + ‖t‖^2 := by linarith
    _ = ‖t‖ + ‖t‖ * ‖t‖ := by ring
    _ ≤ ‖t‖ + ‖t‖ * (1/8) := by linarith
    _ = 9/8 * ‖t‖ := by ring

/-- The relation `σ u₀ = 1 - exp t` together with `‖u₀ - 1‖ ≤ 1/8` and `‖t‖ ≤ 1/8` forces
`‖σ‖ ≤ (9/7)‖t‖`: `‖σ‖·(7/8) ≤ ‖σ u₀‖ = ‖1 - exp t‖ ≤ (9/8)‖t‖`. -/
private lemma norm_sigma_le_of_exp {σ u0 t : ℂ} (hu0 : ‖u0 - 1‖ ≤ 1/8)
    (hid : σ * u0 = 1 - Complex.exp t) (ht : ‖t‖ ≤ 1/8) : ‖σ‖ ≤ 9/7 * ‖t‖ := by
  have hu0ge : (7:ℝ)/8 ≤ ‖u0‖ := by
    have h : (1:ℝ) ≤ ‖u0‖ + ‖u0 - 1‖ := by
      have h2 := norm_sub_le u0 (u0 - 1)
      have he : u0 - (u0 - 1) = (1:ℂ) := by ring
      rw [he] at h2
      simpa using h2
    linarith
  have hmul : ‖σ‖ * ‖u0‖ = ‖1 - Complex.exp t‖ := by rw [← norm_mul, hid]
  have h1 : ‖σ‖ * (7/8) ≤ 9/8 * ‖t‖ := by
    have h := mul_le_mul_of_nonneg_left hu0ge (norm_nonneg σ)
    rw [hmul] at h
    linarith [norm_one_sub_exp_le ht]
  have h2 : ‖σ‖ ≤ (9/8 * ‖t‖) / (7/8) := by
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 7/8)]
    linarith
  have h3 : (9/8 * ‖t‖) / (7/8) = 9/7 * ‖t‖ := by ring
  linarith

/-- Uniform smallness of the normal-form data of a perturbation, in terms of `M`: for a parabolic
germ `f₀` on `D₀` and `rr > 0` there are `Ms, C > 0` such that whenever
`NearOn f₀ f Df (closedBall 0 rr) (1/(1000(M+1)))`, `f 0 = 0`, `α = rotOf f` and
`f z = z + z(z-σ)u z` with `u` holomorphic, `1/2 ≤ ‖u‖ ≤ 2` on `ball 0 rr`, and
`1 - σ u 0 = exp (2πiα)`, then (for `M ≥ Ms`) `‖u 0 - 1‖ ≤ 1/8`, `‖σ‖ ≤ 9/7‖2πiα‖` and
`‖α‖ ≤ C/(M+1)`.  Proof: Cauchy on `ball 0 ρ`, `ρ := min rr r₀`, plus `Work.Pert.small_of_nearOn`,
plus `‖1 - exp t‖ ≤ (9/8)‖t‖` for `‖t‖ ≤ 1/8`. -/
theorem small_data_of_nearOn {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (hd : MandelDim.IsParabolicGerm f₀ D₀)
    {rr : ℝ} (hrr : 0 < rr) :
    ∃ (Ms C : ℝ), 0 < Ms ∧ 0 < C ∧
      ∀ M : ℝ, Ms ≤ M → ∀ (f : ℂ → ℂ) (Df : Set ℂ) (u : ℂ → ℂ) (σ α : ℂ),
        MandelDim.NearOn f₀ f Df (Metric.closedBall (0 : ℂ) rr) (1 / (1000 * (M + 1))) →
        f 0 = 0 → α = MandelDim.rotOf f →
        DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr) →
        (∀ z ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2) →
        (∀ z ∈ Metric.ball (0 : ℂ) rr, f z = z + z * (z - σ) * u z) →
        1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α) →
        ‖u 0 - 1‖ ≤ 1 / 8 ∧ ‖σ‖ ≤ 9 / 7 * ‖2 * Real.pi * Complex.I * α‖ ∧
          ‖α‖ ≤ C / (M + 1) := by
  obtain ⟨r₀, hr₀, _hr₀D, C₀, hC₀pos, hC₀⟩ := Work.Pert.small_of_nearOn hd
  -- the radius on which Cauchy's estimate is applied
  set ρ : ℝ := min rr r₀ / 2 with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; linarith [lt_min hrr hr₀]
  have hρr : ρ ≤ r₀ := by rw [hρdef]; linarith [min_le_right rr r₀]
  have hρrr : ρ ≤ rr := by rw [hρdef]; linarith [min_le_left rr r₀]
  set T : ℝ := 1 / ρ ^ 2 + 1 / (ρ * rr) with hTdef
  have hTpos : 0 < T := by rw [hTdef]; positivity
  -- effective Cauchy constant and the constant of the `‖α‖` bound
  set K : ℝ := max C₀ 10 with hKdef
  have hKpos : 0 < K := lt_of_lt_of_le hC₀pos (le_max_left _ _)
  set C : ℝ := max (C₀ / (1000 * ρ)) 1 with hCdef
  have hCpos : 0 < C := lt_of_lt_of_le one_pos (le_max_right _ _)
  set Ms : ℝ := max (max 1 (K * T / 125)) (max (16 * Real.pi * C) (1 / (500 * ρ))) with hMsdef
  have hMspos : 0 < Ms := by
    rw [hMsdef]
    exact lt_of_lt_of_le (lt_of_lt_of_le one_pos (le_max_left 1 (K * T / 125)))
      (le_max_left (max 1 (K * T / 125)) _)
  refine ⟨Ms, C, hMspos, hCpos, ?_⟩
  intro M hM f Df u σ α hnear hf0 hα hdiffu hbnd hform hexp
  -- the four threshold consequences of `Ms ≤ M`
  have hMs1 : (1:ℝ) ≤ Ms := by
    rw [hMsdef]; exact le_trans (le_max_left 1 (K * T / 125)) (le_max_left _ _)
  have hMsK : K * T / 125 ≤ Ms := by
    rw [hMsdef]; exact le_trans (le_max_right 1 (K * T / 125)) (le_max_left _ _)
  have hMs16 : 16 * Real.pi * C ≤ Ms := by
    rw [hMsdef]
    exact le_trans (le_max_left (16 * Real.pi * C) (1 / (500 * ρ))) (le_max_right _ _)
  have hMs500 : 1 / (500 * ρ) ≤ Ms := by
    rw [hMsdef]
    exact le_trans (le_max_right (16 * Real.pi * C) (1 / (500 * ρ))) (le_max_right _ _)
  have hM1 : (0:ℝ) < M + 1 := by linarith
  have hMK : K * T / 125 ≤ M + 1 := by linarith
  have hM16 : 16 * Real.pi * C ≤ M + 1 := by linarith
  have hM500 : 1 / (500 * ρ) ≤ M + 1 := by linarith
  -- admissibility of `δ₀ = 1/(1000(M+1))` and transfer of `NearOn` to the smaller ball
  have hδpos : (0:ℝ) < 1 / (1000 * (M + 1)) := by positivity
  have h2δ : 2 * (1 / (1000 * (M + 1))) ≤ ρ := by
    have h' : (1:ℝ) ≤ ρ * (500 * (M + 1)) := by
      have h := (div_le_iff₀ (by positivity : (0:ℝ) < 500 * ρ)).mp hM500
      nlinarith [h]
    have h2 : 2 * (1 / (1000 * (M + 1))) = 2 / (1000 * (M + 1)) := by ring
    rw [h2, div_le_iff₀ (by positivity : (0:ℝ) < 1000 * (M + 1))]
    nlinarith [h']
  have hnearρ : MandelDim.NearOn f₀ f Df (Metric.closedBall (0:ℂ) ρ) (1 / (1000 * (M + 1))) :=
    ⟨hnear.1, fun z hz => hnear.2.1 (Metric.closedBall_subset_closedBall hρrr hz),
      hnear.2.2.1, fun z hz => hnear.2.2.2 z (Metric.closedBall_subset_closedBall hρrr hz)⟩
  obtain ⟨hu0b, _hσb, hαb⟩ := hC₀ (ρ := ρ) (δ₀ := 1 / (1000 * (M + 1))) (rr := rr)
    hρpos hρr hδpos h2δ hrr hnearρ hf0 hdiffu hbnd hform
  -- `u 0` is close to `1`
  have hu0le : ‖u 0 - 1‖ ≤ 1 / 8 := by
    have hXnn : (0:ℝ) ≤ 1/(1000*(M+1))/ρ^2 + 1/(1000*(M+1))/(ρ*rr) := by positivity
    have h1 : ‖u 0 - 1‖ ≤ K * (1/(1000*(M+1))/ρ^2 + 1/(1000*(M+1))/(ρ*rr)) :=
      le_trans hu0b (mul_le_mul_of_nonneg_right (by rw [hKdef]; exact le_max_left _ _) hXnn)
    have h2 : K * (1/(1000*(M+1))/ρ^2 + 1/(1000*(M+1))/(ρ*rr)) ≤ 1 / 8 := by
      have hXeq : 1/(1000*(M+1))/ρ^2 + 1/(1000*(M+1))/(ρ*rr) = T/(1000*(M+1)) := by
        rw [hTdef]; field_simp
      rw [hXeq, show K * (T/(1000*(M+1))) = K*T/(1000*(M+1)) by ring,
        div_le_iff₀ (by positivity : (0:ℝ) < 1000*(M+1))]
      nlinarith [hMK]
    linarith
  -- the rotation number is `≤ C/(M+1)`
  have hαC : ‖α‖ ≤ C / (M + 1) := by
    have heq : ‖α‖ = ‖MandelDim.rotOf f‖ := by rw [hα]
    rw [heq]
    refine le_trans hαb ?_
    have heq1 : C₀ * (1/(1000*(M+1)))/ρ = (C₀/(1000*ρ)) * (1/(M+1)) := by field_simp
    have heq2 : C / (M+1) = C * (1/(M+1)) := by ring
    rw [heq1, heq2]
    exact mul_le_mul_of_nonneg_right (by rw [hCdef]; exact le_max_left _ _) (by positivity)
  -- hence `‖2πiα‖ ≤ 1/8`, the range of validity of the exponential estimate
  have htc : ‖2 * Real.pi * Complex.I * α‖ ≤ 1 / 8 := by
    have hnorm : ‖2 * Real.pi * Complex.I * α‖ = 2 * Real.pi * ‖α‖ := by
      rw [norm_mul, norm_mul, norm_mul]
      simp [Complex.norm_I, Real.norm_of_nonneg (le_of_lt Real.pi_pos)]
    rw [hnorm]
    have hαM : ‖α‖ * (M + 1) ≤ C := (le_div_iff₀ hM1).mp hαC
    have h1 : (16*Real.pi*‖α‖) * (M+1) ≤ 1 * (M+1) := by nlinarith [hαM, hM16, Real.pi_pos]
    have h2 : 16*Real.pi*‖α‖ ≤ 1 := le_of_mul_le_mul_right h1 hM1
    linarith
  -- `σ` is comparable with `2πiα`
  have hσu : σ * u 0 = 1 - Complex.exp (2 * Real.pi * Complex.I * α) := by
    linear_combination -hexp
  exact ⟨hu0le, norm_sigma_le_of_exp hu0le hσu htc, hαC⟩

end Work.Pert.PinLogDev
