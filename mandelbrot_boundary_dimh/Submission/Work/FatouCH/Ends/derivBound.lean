import Mathlib
import Submission.Work.Interfaces.Fatou
import Submission.Work.FatouCH.Ends.Basic

/-!
# The pointwise derivative bound at the end of the cylinder

Shishikura's Lemma A.2.4(i) (`MandelDim.FatouDerivEstimate`, here in the numerical form `DiffEst`)
says that a Fatou coordinate is `1/v` up to `C₁ (1/R² + ‖v'‖)` on a ball of radius `R` on which the
Abel relation holds.  At a point `z` of height `T = z.im` far up in `Qreg b₁ b₂`, the ball of radius
`T/8` lies in the region (hypothesis `hball`) and the tail `w ↦ F w - w - ρ` is bounded by
`|M| exp (-(7 κ T / 8))` there (hypothesis `htail`).  Cauchy's estimate turns the smallness of the
tail into one for its derivative, and the result is the pointwise bound

  `‖deriv (devFn Φ ρ) z‖ ≤ psi (Kc C₁ M) κ T = 2 K / T² + 2 K exp (-(κ T / 8))`, `K = Kc C₁ M`,

which is integrable in `T`; that is what makes the Fatou coordinate converge to `z/ρ + c` at the end.
-/

namespace Work.FatouCH.Ends

open Set Metric Complex
open scoped Topology

noncomputable section

theorem endsDerivBound {b₁ b₂ : Option ℂ} {F Φ : ℂ → ℂ} {ρ : ℂ} {M κ : ℝ} {R₁ C₁ : ℝ}
    (hDiff : DiffEst R₁ C₁) (hC₁ : 0 ≤ C₁)
    (hNT : MandelDim.NearTranslationOn F (MandelDim.Qreg b₁ b₂))
    (hΦ : MandelDim.IsFatouCoordOn F Φ (MandelDim.Qreg b₁ b₂)) (hκ : 0 < κ)
    (hρ : 1 / 2 ≤ ‖ρ‖) {T : ℝ} (hT1 : 1 ≤ T) (hR : R₁ ≤ T / 16)
    (hsmall : |M| * Real.exp (-(7 * κ * T / 8)) ≤ 1 / 4)
    {z : ℂ} (hball : Metric.ball z (T / 8) ⊆ MandelDim.Qreg b₁ b₂)
    (htail : ∀ ζ ∈ Metric.ball z (T / 8),
      ‖F ζ - (ζ + ρ)‖ ≤ |M| * Real.exp (-(7 * κ * T / 8))) :
    ‖deriv (devFn Φ ρ) z‖ ≤ psi (Kc C₁ M) κ T := by
  have hTpos : 0 < T := by linarith
  have h16pos : (0 : ℝ) < T / 16 := by linarith
  have hMnn : (0 : ℝ) ≤ |M| := abs_nonneg M
  set e1 : ℝ := Real.exp (-(7 * κ * T / 8)) with he1
  set e2 : ℝ := Real.exp (-(κ * T / 8)) with he2
  have he1pos : 0 < e1 := by rw [he1]; positivity
  have he2pos : 0 < e2 := by rw [he2]; positivity
  set b : ℝ := ‖deriv (fun w : ℂ => F w - w - ρ) z‖ with hb
  -- ## Step 0
  have hzball8 : z ∈ Metric.ball z (T / 8) := by
    rw [Metric.mem_ball, dist_self]; linarith
  have hzQ : z ∈ MandelDim.Qreg b₁ b₂ := hball hzball8
  have hΦat : DifferentiableAt ℂ Φ z :=
    hΦ.1.differentiableAt ((isOpen_Qreg b₁ b₂).mem_nhds hzQ)
  have hsub168 : Metric.ball z (T / 16) ⊆ Metric.ball z (T / 8) :=
    Metric.ball_subset_ball (by linarith)
  have hsubQ : Metric.ball z (T / 16) ⊆ MandelDim.Qreg b₁ b₂ := hsub168.trans hball
  -- ## Step 1: the derivative estimate on the ball of radius `T/16`
  have hmain : ‖deriv Φ z - 1 / (F z - z)‖ ≤
      C₁ * (1 / (T / 16) ^ 2 + ‖deriv (fun w : ℂ => F w - w) z‖) := by
    refine hDiff Φ (fun w : ℂ => F w - w) z (T / 16) hR ?_ ?_ ?_ ?_ ?_
    · exact hΦ.1.mono hsubQ
    · exact hΦ.2.1.mono hsubQ
    · exact (hNT.1.mono hsubQ).sub differentiableOn_id
    · intro w hw
      have h := (hNT.2 w (hsubQ hw)).1
      have heq : (fun w : ℂ => F w - w) w - 1 = F w - (w + 1) := by ring
      rw [heq]; linarith
    · intro w hw hw'
      have hwF : F w ∈ Metric.ball z (T / 8) := by
        have heq : w + (F w - w) = F w := by ring
        rw [heq] at hw'; exact hsub168 hw'
      have h := hΦ.2.2 w (hsubQ hw) (hball hwF)
      have heq : w + (F w - w) = F w := by ring
      rwa [heq]
  -- ## Step 2: Cauchy's estimate for the derivative of the tail
  have hGd : DifferentiableOn ℂ (fun w : ℂ => F w - w - ρ) (Metric.ball z (T / 8)) :=
    ((hNT.1.mono hball).sub differentiableOn_id).sub (differentiableOn_const ρ)
  have hsub168c : Metric.closedBall z (T / 16) ⊆ Metric.ball z (T / 8) := by
    intro w hw
    rw [Metric.mem_closedBall, dist_eq_norm] at hw
    rw [Metric.mem_ball, dist_eq_norm]
    linarith
  have hDC : DiffContOnCl ℂ (fun w : ℂ => F w - w - ρ) (Metric.ball z (T / 16)) :=
    hGd.diffContOnCl_ball hsub168c
  have hsph : ∀ w ∈ Metric.sphere z (T / 16),
      ‖F w - w - ρ‖ ≤ |M| * e1 := by
    intro w hw
    have hwb : w ∈ Metric.ball z (T / 8) := by
      rw [Metric.mem_sphere, dist_eq_norm] at hw
      rw [Metric.mem_ball, dist_eq_norm]
      linarith
    have h := htail w hwb
    have heq : ‖F w - w - ρ‖ = ‖F w - (w + ρ)‖ := by congr 1; ring
    rwa [heq]
  have hCau_b : b ≤ 16 * |M| * e1 / T := by
    rw [hb]
    have hCau : ‖deriv (fun w : ℂ => F w - w - ρ) z‖ ≤
        (|M| * e1) / (T / 16) :=
      Complex.norm_deriv_le_of_forall_mem_sphere_norm_le h16pos hDC hsph
    have heq : (|M| * e1) / (T / 16) = 16 * |M| * e1 / T := by
      field_simp
    linarith [hCau, heq.ge]
  -- ## Step 3: `deriv (F - id) = deriv (F - id - ρ)`
  have hveq : deriv (fun w : ℂ => F w - w) z = deriv (fun w : ℂ => F w - w - ρ) z := by
    have hfun : (fun w : ℂ => F w - w) = fun w : ℂ => (F w - w - ρ) + ρ := by
      funext w; ring
    rw [hfun, deriv_add_const]
  -- ## Step 4: the pointwise smallness of the tail at `z`
  have hGz : ‖F z - (z + ρ)‖ ≤ |M| * e1 := htail z hzball8
  have hvz : (1 : ℝ) / 4 ≤ ‖F z - z‖ := by
    have h2 : ‖ρ‖ ≤ ‖F z - z‖ + ‖(F z - z) - ρ‖ := by
      have h := norm_sub_le (F z - z) ((F z - z) - ρ)
      have he : (F z - z) - ((F z - z) - ρ) = ρ := by ring
      rwa [he] at h
    have heq : ‖(F z - z) - ρ‖ = ‖F z - (z + ρ)‖ := by congr 1; ring
    rw [heq] at h2
    linarith
  have hinv : ‖1 / (F z - z) - 1 / ρ‖ ≤ 8 * |M| * e1 := by
    have hvz_ne : F z - z ≠ 0 := by
      intro h; rw [h, norm_zero] at hvz; norm_num at hvz
    have hρ_ne : ρ ≠ 0 := by
      intro h; rw [h, norm_zero] at hρ; norm_num at hρ
    have heq : 1 / (F z - z) - 1 / ρ = -(F z - (z + ρ)) / ((F z - z) * ρ) := by
      field_simp
      ring
    rw [heq, norm_div, norm_neg, norm_mul]
    have hbc : (1 : ℝ) / 8 ≤ ‖F z - z‖ * ‖ρ‖ := by
      have h := mul_le_mul hvz hρ (by norm_num) (by linarith [hvz])
      norm_num at h ⊢
      exact h
    rw [div_le_iff₀ (by positivity)]
    have h1 : 8 * |M| * e1 * (1 / 8) ≤ 8 * |M| * e1 * (‖F z - z‖ * ‖ρ‖) :=
      mul_le_mul_of_nonneg_left hbc (by positivity)
    have h2 : ‖F z - (z + ρ)‖ ≤ 8 * |M| * e1 * (1 / 8) := by
      have he : 8 * |M| * e1 * (1 / 8) = |M| * e1 := by ring
      rw [he]; exact hGz
    exact le_trans h2 h1
  -- ## Step 5: assemble the two pieces
  have hstep : ‖deriv (devFn Φ ρ) z‖ ≤ C₁ * (1 / (T / 16) ^ 2 + b) + 8 * |M| * e1 := by
    rw [deriv_devFn hΦat, hb]
    have hsplit : deriv Φ z - 1 / ρ =
        (deriv Φ z - 1 / (F z - z)) + (1 / (F z - z) - 1 / ρ) := by ring
    rw [hsplit]
    calc ‖(deriv Φ z - 1 / (F z - z)) + (1 / (F z - z) - 1 / ρ)‖
        ≤ ‖deriv Φ z - 1 / (F z - z)‖ + ‖1 / (F z - z) - 1 / ρ‖ := norm_add_le _ _
      _ ≤ C₁ * (1 / (T / 16) ^ 2 + ‖deriv (fun w : ℂ => F w - w) z‖) + 8 * |M| * e1 :=
          add_le_add hmain hinv
      _ = C₁ * (1 / (T / 16) ^ 2 + b) + 8 * |M| * e1 := by rw [hb, hveq]
  -- ## Step 6: numerics
  have hKc : Kc C₁ M = 256 * C₁ + 16 * C₁ * |M| + 16 * |M| := rfl
  have h256 : 1 / (T / 16) ^ 2 = 256 / T ^ 2 := by
    field_simp
    norm_num
  have he12 : e1 ≤ e2 := by
    rw [he1, he2, Real.exp_le_exp]
    nlinarith [hκ, hTpos]
  have hquot : e1 / T ≤ e2 := by
    rw [div_le_iff₀ hTpos]
    have h1 : e1 ≤ 1 := by
      rw [he1, Real.exp_le_one_iff]
      nlinarith [hκ, hTpos]
    nlinarith [he12, h1, hT1, he2pos]
  have hterm1 : 256 * C₁ / T ^ 2 ≤ 2 * Kc C₁ M / T ^ 2 := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    rw [hKc]; nlinarith [hC₁, hMnn]
  have hsum_exp : C₁ * (16 * |M| * e1 / T) + 8 * |M| * e1 ≤ 2 * Kc C₁ M * e2 := by
    have hA : C₁ * (16 * |M| * e1 / T) = (16 * C₁ * |M|) * (e1 / T) := by ring
    have hB : 8 * |M| * e1 = (8 * |M|) * e1 := by ring
    rw [hA, hB]
    have h1 : (16 * C₁ * |M|) * (e1 / T) ≤ (16 * C₁ * |M|) * e2 :=
      mul_le_mul_of_nonneg_left hquot (by positivity)
    have h2 : (8 * |M|) * e1 ≤ (8 * |M|) * e2 :=
      mul_le_mul_of_nonneg_left he12 (by positivity)
    have h3 : 16 * C₁ * |M| + 8 * |M| ≤ 2 * Kc C₁ M := by
      rw [hKc]; nlinarith [hC₁, hMnn]
    calc (16 * C₁ * |M|) * (e1 / T) + (8 * |M|) * e1
        ≤ (16 * C₁ * |M|) * e2 + (8 * |M|) * e2 := add_le_add h1 h2
      _ = (16 * C₁ * |M| + 8 * |M|) * e2 := by ring
      _ ≤ 2 * Kc C₁ M * e2 := mul_le_mul_of_nonneg_right h3 he2pos.le
  have hpsi : psi (Kc C₁ M) κ T = 2 * Kc C₁ M / T ^ 2 + 2 * Kc C₁ M * e2 := by
    rw [psi, he2]
  calc ‖deriv (devFn Φ ρ) z‖
      ≤ C₁ * (1 / (T / 16) ^ 2 + b) + 8 * |M| * e1 := hstep
    _ = C₁ * (256 / T ^ 2) + (C₁ * b + 8 * |M| * e1) := by rw [h256]; ring
    _ ≤ 2 * Kc C₁ M / T ^ 2 + 2 * Kc C₁ M * e2 := by
        have hC1a : C₁ * (256 / T ^ 2) ≤ 2 * Kc C₁ M / T ^ 2 := by
          have h : C₁ * (256 / T ^ 2) = 256 * C₁ / T ^ 2 := by ring
          rw [h]; exact hterm1
        have hC1b : C₁ * b ≤ C₁ * (16 * |M| * e1 / T) :=
          mul_le_mul_of_nonneg_left hCau_b hC₁
        linarith [hC1a, hC1b, hsum_exp]
    _ = psi (Kc C₁ M) κ T := hpsi.symm

end

end Work.FatouCH.Ends
