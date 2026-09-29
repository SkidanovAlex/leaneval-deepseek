import Mathlib
import Submission.Work.ANum2.lune_second_deriv_bound
import Submission.Work.ANum3.lune_deriv2_norm
import Submission.Work.ANum3.luneR_abs_lower
import Submission.Work.APsi.lune_cont_diff

/-! # Analytic bounds for the second derivative of the lune map at `c = 36/5`

* `deriv_lune_differentiableOn`: `lune'` is holomorphic on the unit disc (needed for the
  second-order Taylor estimate).
* `lune_deriv2_le_cauchy`: the crude bound `‖lune''‖ ≤ 2/d²` for `0 < d ≤ 1 − ‖z‖`, from
  Mathlib's Cauchy estimate and `‖lune‖ ≤ 1` on the unit disc.
* `lune_deriv2_le_explicit`: `‖lune''(z)‖ ≤ (2‖R z‖·2(1+c²)² + ‖R' z‖²)/(8(c²−1)‖R z‖^{3/2})`,
  the explicit bound behind the `M2e` branch of the checker. -/

namespace Work.Cert.ACBall
open Work.Cert Complex Submission.CDTPlan Work.APsi

theorem deriv_lune_differentiableOn :
    DifferentiableOn ℂ (deriv (Submission.CDTPlan.lune (36 / 5))) (Metric.ball 0 1) :=
  ((Work.APsi.lune_cont_diff (36 / 5) (by norm_num)).2).deriv Metric.isOpen_ball

/-- `‖lune''(z)‖ = K/(‖R z‖√‖R z‖)` with `K = 8c²(c²−1) = 13177728/625`. -/
lemma lune_deriv2_eq {z : ℂ} (hz : ‖z‖ < 1) :
    ‖deriv (deriv (Submission.CDTPlan.lune (36 / 5))) z‖
      = (13177728 / 625 : ℝ)
        / (‖Work.APsi.luneR (36 / 5) z‖ * Real.sqrt ‖Work.APsi.luneR (36 / 5) z‖) := by
  have h := Work.ANum3.lune_deriv2_norm z hz
  have hK : (8 * (36 / 5 : ℝ) ^ 2 * ((1 + (36 / 5 : ℝ) ^ 2) ^ 2 - 4 * (36 / 5 : ℝ) ^ 2)
      / ((36 / 5 : ℝ) ^ 2 - 1)) = 13177728 / 625 := by norm_num
  rw [hK] at h
  have hlow := Work.ANum3.luneR_abs_lower z
  have hsq : ‖z‖ ^ 2 < 1 := by nlinarith [norm_nonneg z, hz]
  have h1 : 0 < ‖Work.APsi.luneR (36 / 5) z‖ := by nlinarith [norm_nonneg (Work.APsi.luneR (36 / 5) z)]
  have hpos : 0 < ‖Work.APsi.luneR (36 / 5) z‖ * Real.sqrt ‖Work.APsi.luneR (36 / 5) z‖ :=
    mul_pos h1 (Real.sqrt_pos.mpr h1)
  rw [eq_div_iff (ne_of_gt hpos)]
  linarith [h]

theorem lune_deriv2_le_cauchy {z : ℂ} (hz : ‖z‖ < 1) {d : ℝ} (hd : 0 < d) (h : d ≤ 1 - ‖z‖) :
    ‖deriv (deriv (Submission.CDTPlan.lune (36 / 5))) z‖ ≤ 2 / d ^ 2 := by
  have hc := Work.APsi.lune_cont_diff (36 / 5) (by norm_num)
  have htri : ∀ w : ℂ, ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by
    intro w
    calc ‖w‖ = ‖(w - z) + z‖ := by rw [sub_add_cancel]
      _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
  have hb1 : Metric.ball z d ⊆ Metric.ball (0 : ℂ) 1 := by
    intro w hw
    simp only [Metric.mem_ball, dist_eq_norm, sub_zero] at hw ⊢
    linarith [htri w]
  have hb2 : Metric.ball z d ⊆ Metric.closedBall (0 : ℂ) 1 :=
    fun w hw => Metric.ball_subset_closedBall (hb1 hw)
  have hcbd : Metric.closedBall z d ⊆ Metric.closedBall (0 : ℂ) 1 := by
    intro w hw
    simp only [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hw ⊢
    linarith [htri w]
  have hcl : closure (Metric.ball z d) ⊆ Metric.closedBall (0 : ℂ) 1 :=
    fun w hw => hcbd (closure_minimal (fun x hx => Metric.ball_subset_closedBall hx)
      Metric.isClosed_closedBall hw)
  have hbdd : ∀ w ∈ Metric.sphere z d, ‖Submission.CDTPlan.lune (36 / 5) w‖ ≤ 1 := by
    intro w hw
    exact Work.APsi.lune_norm_le_one (36 / 5) (by norm_num) w
      (by simpa [dist_eq_norm] using Metric.mem_closedBall.mp (hcbd (Metric.sphere_subset_closedBall hw)))
  have hDC : DiffContOnCl ℂ (Submission.CDTPlan.lune (36 / 5)) (Metric.ball z d) :=
    ⟨hc.2.mono hb1, hc.1.mono hcl⟩
  have hkey : ‖iteratedDeriv 2 (Submission.CDTPlan.lune (36 / 5)) z‖ ≤ 2 / d ^ 2 := by
    have h := norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
      (f := Submission.CDTPlan.lune (36 / 5)) (c := z) (R := d) (C := 1) 2 hd hDC hbdd
    simpa using h
  have hiter : iteratedDeriv 2 (Submission.CDTPlan.lune (36 / 5)) z
      = deriv (deriv (Submission.CDTPlan.lune (36 / 5))) z := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rwa [hiter] at hkey

lemma lune_quad_const' (z : ℂ) :
    ((4 * (1 + (36 / 5 : ℝ) ^ 2) ^ 2 : ℝ) : ℂ) * Work.APsi.luneR (36 / 5) z
        - (Work.ANum2.luneRd (36 / 5) z) ^ 2
      = ((64 * (36 / 5 : ℝ) ^ 2 *
            ((1 + (36 / 5 : ℝ) ^ 2) ^ 2 - 4 * (36 / 5 : ℝ) ^ 2) : ℝ) : ℂ) := by
  simp only [Work.APsi.luneR, Work.ANum2.luneRd]
  push_cast
  ring

theorem lune_deriv2_le_explicit {z : ℂ} (hz : ‖z‖ < 1) {Rlo Rhi Rp sL : ℝ} (hRlo : 0 < Rlo)
    (hsL : 0 < sL) (hlo : Rlo ≤ ‖Work.APsi.luneR (36 / 5) z‖)
    (hhi : ‖Work.APsi.luneR (36 / 5) z‖ ≤ Rhi)
    (hp : ‖deriv (Work.APsi.luneR (36 / 5)) z‖ ≤ Rp) (hsL2 : sL ^ 2 ≤ Rlo) :
    ‖deriv (deriv (Submission.CDTPlan.lune (36 / 5))) z‖ ≤
      (2 * Rhi * (2 * (1 + (36 / 5 : ℝ) ^ 2) ^ 2) + Rp ^ 2)
        / (8 * ((36 / 5 : ℝ) ^ 2 - 1) * Rlo * sL) := by
  have hRpos : 0 < ‖Work.APsi.luneR (36 / 5) z‖ := lt_of_lt_of_le hRlo hlo
  have hdr : (Work.ANum2.luneRd (36 / 5) z) = deriv (Work.APsi.luneR (36 / 5)) z :=
    (Work.ANum2.deriv_luneR (36 / 5) z).symm
  -- the quadratic identity, in real form
  have hre : 4 * (1 + (36 / 5 : ℝ) ^ 2) ^ 2 * (Work.APsi.luneR (36 / 5) z).re
      - ((Work.ANum2.luneRd (36 / 5) z) ^ 2).re
      = 64 * (36 / 5 : ℝ) ^ 2 * ((1 + (36 / 5 : ℝ) ^ 2) ^ 2 - 4 * (36 / 5 : ℝ) ^ 2) := by
    have h := congrArg Complex.re (lune_quad_const' z)
    simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im, sub_zero,
      mul_zero, zero_mul] at h
    simpa using h
  have hsq : ((Work.ANum2.luneRd (36 / 5) z) ^ 2).re
      = (Work.ANum2.luneRd (36 / 5) z).re ^ 2 - (Work.ANum2.luneRd (36 / 5) z).im ^ 2 := by
    rw [sq, Complex.mul_re]; ring
  have hR'2 : ‖Work.ANum2.luneRd (36 / 5) z‖ ^ 2
      = (Work.ANum2.luneRd (36 / 5) z).re ^ 2 + (Work.ANum2.luneRd (36 / 5) z).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hΛ : 64 * (36 / 5 : ℝ) ^ 2 * ((1 + (36 / 5 : ℝ) ^ 2) ^ 2 - 4 * (36 / 5 : ℝ) ^ 2)
      ≤ 4 * (1 + (36 / 5 : ℝ) ^ 2) ^ 2 * ‖Work.APsi.luneR (36 / 5) z‖
        + ‖Work.ANum2.luneRd (36 / 5) z‖ ^ 2 := by
    have hRge : (Work.APsi.luneR (36 / 5) z).re ≤ ‖Work.APsi.luneR (36 / 5) z‖ :=
      Complex.re_le_norm _
    have hBnn : (0 : ℝ) ≤ 4 * (1 + (36 / 5 : ℝ) ^ 2) ^ 2 := by positivity
    nlinarith [hre, hsq, hR'2, hRge, hBnn, sq_nonneg (Work.ANum2.luneRd (36 / 5) z).re,
      sq_nonneg (Work.ANum2.luneRd (36 / 5) z).im]
  -- assemble
  have hden : (0 : ℝ) < 8 * ((36 / 5 : ℝ) ^ 2 - 1) := by norm_num
  have hnumpos : (0 : ℝ) < 8 * ((36 / 5 : ℝ) ^ 2 - 1) * Rlo * sL := by positivity
  have hKle : (13177728 / 625 : ℝ) * (8 * ((36 / 5 : ℝ) ^ 2 - 1))
      ≤ 2 * Rhi * (2 * (1 + (36 / 5 : ℝ) ^ 2) ^ 2) + Rp ^ 2 := by
    have he : (13177728 / 625 : ℝ) * (8 * ((36 / 5 : ℝ) ^ 2 - 1))
        = 64 * (36 / 5 : ℝ) ^ 2 * ((1 + (36 / 5 : ℝ) ^ 2) ^ 2 - 4 * (36 / 5 : ℝ) ^ 2) := by
      norm_num
    rw [he]
    have h2 : ‖Work.ANum2.luneRd (36 / 5) z‖ ^ 2 ≤ Rp ^ 2 := by
      rw [hdr]
      exact pow_le_pow_left₀ (norm_nonneg _) hp 2
    have h3 : 4 * (1 + (36 / 5 : ℝ) ^ 2) ^ 2 * ‖Work.APsi.luneR (36 / 5) z‖
        ≤ 4 * (1 + (36 / 5 : ℝ) ^ 2) ^ 2 * Rhi :=
      mul_le_mul_of_nonneg_left hhi (by positivity)
    have h4 : 2 * Rhi * (2 * (1 + (36 / 5 : ℝ) ^ 2) ^ 2)
        = 4 * (1 + (36 / 5 : ℝ) ^ 2) ^ 2 * Rhi := by ring
    rw [h4]
    linarith [hΛ, h2, h3]
  have hsLle : sL ≤ Real.sqrt ‖Work.APsi.luneR (36 / 5) z‖ :=
    (Real.le_sqrt (le_of_lt hsL) (le_of_lt hRpos)).mpr (le_trans hsL2 hlo)
  have hR32 : Rlo * sL ≤ ‖Work.APsi.luneR (36 / 5) z‖ * Real.sqrt ‖Work.APsi.luneR (36 / 5) z‖ :=
    mul_le_mul hlo hsLle (le_of_lt hsL) (le_of_lt hRpos)
  rw [lune_deriv2_eq hz, div_le_div_iff₀ (by positivity) hnumpos]
  calc (13177728 / 625 : ℝ) * (8 * ((36 / 5 : ℝ) ^ 2 - 1) * Rlo * sL)
      = ((13177728 / 625 : ℝ) * (8 * ((36 / 5 : ℝ) ^ 2 - 1))) * (Rlo * sL) := by ring
    _ ≤ (2 * Rhi * (2 * (1 + (36 / 5 : ℝ) ^ 2) ^ 2) + Rp ^ 2)
          * (‖Work.APsi.luneR (36 / 5) z‖ * Real.sqrt ‖Work.APsi.luneR (36 / 5) z‖) :=
        mul_le_mul hKle hR32 (by positivity) (by positivity)

end Work.Cert.ACBall
