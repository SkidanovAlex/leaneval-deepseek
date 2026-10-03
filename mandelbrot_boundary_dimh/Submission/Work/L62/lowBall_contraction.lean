import Mathlib
import Submission.Work.L62.lowcyl
import Submission.Work.L62.holomorphic_second_order_remainder
import Submission.Work.L62.deriv_lipschitz_of_second_order

namespace Work.L62

open MandelDim

noncomputable section

variable {g₀ : ℂ → ℂ} {D : Set ℂ}

/-- `‖π(w)‖ = exp (-2π Im w)` for the lift coordinate `π w = exp (2πi w)`
(proved locally so that the contraction estimate below does not need an extra import). -/
theorem norm_piExp_lowBall (z : ℂ) : ‖MandelDim.piExp z‖ = Real.exp (-(2 * Real.pi * z.im)) := by
  rw [MandelDim.piExp, Complex.norm_exp]
  congr 1
  rw [Complex.mul_re]
  simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re]

/-- Uniform contraction of the lower-end cylinder family on a small ball: if `H ·` are holomorphic
self-maps of `lowOmega d hd` with `H β 0 = 0` and `deriv (H β) 0 = π (cl - β)` for `β ∈ Λ`, and
`Im β ≤ Im cl - κ` with `κ > 0`, then a *single* radius `r > 0` and factor `μ = 1/2 + e^{-2πκ}/2 < 1`
work for all `β ∈ Λ`.  Route: `‖deriv (H β) 0‖ = e^{2π(Im β - Im cl)} ≤ e^{-2πκ}`, a uniform
second-order Taylor bound from `lowOmega ⊆ closedBall 0 (e^{2πη})` by Cauchy, then choose `r`. -/
theorem lowBall_contraction {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D)
    (hd : MandelDim.HornData d) {cl : ℂ} {H : ℂ → ℂ → ℂ} {Λ : Set ℂ} {κ : ℝ}
    (hκ : 0 < κ) (hΛim : ∀ β ∈ Λ, β.im ≤ cl.im - κ)
    (hHdiff : ∀ β ∈ Λ, DifferentiableOn ℂ (H β) (Work.L62.lowOmega d hd))
    (hHmap : ∀ β ∈ Λ, Set.MapsTo (H β) (Work.L62.lowOmega d hd) (Work.L62.lowOmega d hd))
    (hHfix : ∀ β ∈ Λ, H β 0 = 0)
    (hHder : ∀ β ∈ Λ, deriv (H β) 0 = MandelDim.piExp (cl - β)) :
    ∃ r : ℝ, 0 < r ∧ ∀ β ∈ Λ, ∀ w : ℂ, ‖w‖ ≤ r →
      ‖H β w‖ ≤ (1 / 2 + Real.exp (-(2 * Real.pi * κ)) / 2) * ‖w‖ := by
  -- Radius of the disc on which Cauchy's estimate is applied, and the sup bound `M ≔ e^{2πη}`.
  set ε : ℝ := Real.exp (-(2 * Real.pi * hd.η)) with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; positivity
  set R : ℝ := ε / 2 with hRdef
  have hRpos : 0 < R := by rw [hRdef]; linarith
  have hRlt : R < ε := by rw [hRdef]; linarith
  -- the closed disc of radius `R` is contained in `lowOmega`, which contains the open disc `ε`
  have hclosed_sub : Metric.closedBall (0 : ℂ) R ⊆ Work.L62.lowOmega d hd :=
    (Metric.closedBall_subset_ball hRlt).trans (Work.L62.ball_subset_lowOmega d hd)
  set M : ℝ := Real.exp (2 * Real.pi * hd.η) with hMdef
  have hMpos : 0 < M := by rw [hMdef]; positivity
  -- constant of the second-order remainder, and the derivative bound `lam = e^{-2πκ} < 1`
  set K : ℝ := 2 * M / R ^ 2 with hKdef
  have hKpos : 0 < K := by rw [hKdef]; positivity
  have hKne : K ≠ 0 := ne_of_gt hKpos
  set lam : ℝ := Real.exp (-(2 * Real.pi * κ)) with hlamdef
  have hlamp : 0 < lam := by rw [hlamdef]; positivity
  have hlamlt1 : lam < 1 := by
    rw [hlamdef, Real.exp_lt_one_iff]; nlinarith [Real.pi_pos, hκ]
  -- uniform second-order Taylor bound at the origin
  have hTaylor : ∀ β ∈ Λ, ∀ u : ℂ, ‖u‖ ≤ R / 2 →
      ‖H β u - MandelDim.piExp (cl - β) * u‖ ≤ K * ‖u‖ ^ 2 := by
    intro β hβ u hu
    have hf : DifferentiableOn ℂ (H β) (Metric.closedBall 0 R) :=
      (hHdiff β hβ).mono hclosed_sub
    have hbnd : ∀ z ∈ Metric.sphere (0 : ℂ) R, ‖H β z‖ ≤ M := by
      intro z hz
      have hzΩ : z ∈ Work.L62.lowOmega d hd :=
        hclosed_sub (Metric.sphere_subset_closedBall hz)
      have hmem := Work.L62.lowOmega_subset_closedBall d hd (hHmap β hβ hzΩ)
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hmem
      rw [hMdef]
      exact hmem
    have h := Work.L62.holomorphic_second_order_remainder hRpos hMpos.le hf hbnd u
      (by simpa using hu)
    rw [hHfix β hβ, hHder β hβ, sub_zero, sub_zero] at h
    rw [hKdef]
    exact h
  -- the derivative of `H β` at the origin has norm at most `lam`
  have hderiv_bound : ∀ β ∈ Λ, ‖MandelDim.piExp (cl - β)‖ ≤ lam := by
    intro β hβ
    rw [norm_piExp_lowBall, hlamdef]
    apply Real.exp_le_exp.mpr
    rw [Complex.sub_im]
    nlinarith [Real.pi_pos, hΛim β hβ]
  refine ⟨min (R / 2) ((1 - lam) / (2 * K)),
    lt_min (by linarith) (div_pos (by linarith) (by linarith)), ?_⟩
  intro β hβ w hw
  have hwR : ‖w‖ ≤ R / 2 := le_trans hw (min_le_left _ _)
  have hwK : ‖w‖ ≤ (1 - lam) / (2 * K) := le_trans hw (min_le_right _ _)
  have hT := hTaylor β hβ w hwR
  have hD := hderiv_bound β hβ
  have hsplit : ‖H β w‖ ≤ ‖H β w - MandelDim.piExp (cl - β) * w‖
      + ‖MandelDim.piExp (cl - β)‖ * ‖w‖ := by
    calc ‖H β w‖
        = ‖(H β w - MandelDim.piExp (cl - β) * w) + MandelDim.piExp (cl - β) * w‖ := by
          rw [sub_add_cancel]
      _ ≤ ‖H β w - MandelDim.piExp (cl - β) * w‖ + ‖MandelDim.piExp (cl - β) * w‖ :=
          norm_add_le _ _
      _ = ‖H β w - MandelDim.piExp (cl - β) * w‖ + ‖MandelDim.piExp (cl - β)‖ * ‖w‖ := by
          rw [norm_mul]
  have hKr : K * ‖w‖ ≤ (1 - lam) / 2 := by
    calc K * ‖w‖ ≤ K * ((1 - lam) / (2 * K)) := mul_le_mul_of_nonneg_left hwK hKpos.le
      _ = (1 - lam) / 2 := by field_simp
  have hquad : K * ‖w‖ ^ 2 ≤ ((1 - lam) / 2) * ‖w‖ := by
    rw [pow_two, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hKr (norm_nonneg w)
  calc ‖H β w‖ ≤ ‖H β w - MandelDim.piExp (cl - β) * w‖
        + ‖MandelDim.piExp (cl - β)‖ * ‖w‖ := hsplit
    _ ≤ K * ‖w‖ ^ 2 + lam * ‖w‖ :=
        add_le_add hT (mul_le_mul_of_nonneg_right hD (norm_nonneg w))
    _ ≤ ((1 - lam) / 2) * ‖w‖ + lam * ‖w‖ := add_le_add hquad le_rfl
    _ = (1 / 2 + lam / 2) * ‖w‖ := by ring

end

end Work.L62
