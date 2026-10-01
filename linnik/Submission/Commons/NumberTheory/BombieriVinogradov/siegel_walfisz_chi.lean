import Mathlib
import Submission.Commons.NumberTheory.Zeta.chebyshevPsi_sub_id_rh_bound
import Submission.Commons.NumberTheory.DirichletCharacter.chebyshevPsiChi_truncatedPerron
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_logDeriv_eq_neg_LSeries_vonMangoldt
import Submission.Commons.Analysis.Asymptotics.poly_mul_exp_neg_sqrtLog_le
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_zeroFree_offAxis_uniform
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_zeroFree_uniform_realAxis
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_realZero_bound_uniform
import Submission.Commons.NumberTheory.DirichletCharacter.chebyshevPsiChi_truncatedPerron_uniform
import Submission.Commons.NumberTheory.DirichletCharacter.completedL_diskZeroCount_explicit
import Submission.Commons.NumberTheory.DirichletCharacter.completedL_window_cover
import Submission.Commons.NumberTheory.Linnik.completedL_ballZeroCount
import Submission.Commons.NumberTheory.DirichletCharacter.completedL_pf_diff_norm_le

open Complex DirichletCharacter Filter Set MeasureTheory intervalIntegral
open scoped Real Topology BigOperators

namespace Commons.NumberTheory.BombieriVinogradov

noncomputable section

set_option maxHeartbeats 64000000

def psiChiIntF {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (x : ℝ) (s : ℂ) : ℂ :=
  logDeriv (DirichletCharacter.LFunction χ) s * (-((x : ℂ) ^ s / s))

def chiPerronRe (x : ℝ) : ℝ := 1 + 1 / Real.log x

def chiPerron {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (x T : ℝ) : ℂ :=
  (1 / (2 * Real.pi)) *
    (∫ t : ℝ in -T..T, psiChiIntF χ x ((chiPerronRe x : ℂ) + Complex.I * (t : ℂ)))

def chiBotInt {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (x δ T : ℝ) : ℂ :=
  ∫ u : ℝ in (1 - δ)..chiPerronRe x,
    psiChiIntF χ x ((u : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)

def chiTopInt {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (x δ T : ℝ) : ℂ :=
  ∫ u : ℝ in (1 - δ)..chiPerronRe x,
    psiChiIntF χ x ((u : ℂ) + (T : ℂ) * Complex.I)

def chiLeftInt {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (x δ T : ℝ) : ℂ :=
  ∫ t : ℝ in -T..T, psiChiIntF χ x (((1 - δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)

def chiRightInt {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (x T : ℝ) : ℂ :=
  ∫ t : ℝ in -T..T, psiChiIntF χ x ((chiPerronRe x : ℂ) + (t : ℂ) * Complex.I)

/-- **Cauchy–Goursat on a zero-free rectangle.** -/
lemma psiChi_boundary_eq_zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    {x : ℝ} (hx : 0 < x) {z w : ℂ}
    (hrect : ∀ s ∈ (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im), s ≠ 0 ∧
        DirichletCharacter.LFunction χ s ≠ 0) :
    (∫ (u : ℝ) in z.re..w.re, psiChiIntF χ x (u + z.im * Complex.I))
      - (∫ (u : ℝ) in z.re..w.re, psiChiIntF χ x (u + w.im * Complex.I))
      + Complex.I • (∫ (y : ℝ) in z.im..w.im, psiChiIntF χ x (w.re + y * Complex.I))
      - Complex.I • (∫ (y : ℝ) in z.im..w.im, psiChiIntF χ x (z.re + y * Complex.I)) = 0 := by
  have hL : Differentiable ℂ (DirichletCharacter.LFunction χ) :=
    DirichletCharacter.differentiable_LFunction hχ
  have hdL : Differentiable ℂ (deriv (DirichletCharacter.LFunction χ)) := hL.deriv
  have h1 : DifferentiableOn ℂ (logDeriv (DirichletCharacter.LFunction χ))
      (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) :=
    (hdL.differentiableOn).div hL.differentiableOn (fun s hs => (hrect s hs).2)
  have h2 : DifferentiableOn ℂ (fun s : ℂ => (x : ℂ) ^ s / s)
      (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) := by
    have hc : Differentiable ℂ (fun s : ℂ => (x : ℂ) ^ s) :=
      Commons.NumberTheory.Zeta.cpow_differentiable hx
    exact hc.differentiableOn.div differentiableOn_id (fun s hs => (hrect s hs).1)
  have h3 : DifferentiableOn ℂ (psiChiIntF χ x)
      (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) :=
    h1.mul h2.neg
  exact Complex.integral_boundary_rect_eq_zero_of_differentiableOn (psiChiIntF χ x) z w h3

/-- `chiPerron` equals `(1/2π)` times the right-edge integral with the `t * I` ordering. -/
lemma chiPerron_eq_right {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (x T : ℝ) :
    chiPerron χ x T = (1 / (2 * Real.pi)) * chiRightInt χ x T := by
  rw [chiPerron, chiRightInt]
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  congr 1
  ring

/-- **Edge relation.** If the Perron rectangle `[1-δ, 1+1/log x] × [-T, T]` is zero-free for
`L(·, χ)`, then the Perron integral is the sum of the three edge integrals. -/
lemma chiPerron_eq_edges {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    {x T δ : ℝ} (hx : 1 < x) (hT : 0 < T) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hrect : ∀ s : ℂ, 1 - δ ≤ s.re → s.re ≤ chiPerronRe x → |s.im| ≤ T →
        s ≠ 0 ∧ DirichletCharacter.LFunction χ s ≠ 0) :
    chiPerron χ x T =
      (1 / (2 * Real.pi)) * (Complex.I * chiBotInt χ x δ T
        - Complex.I * chiTopInt χ x δ T + chiLeftInt χ x δ T) := by
  set z : ℂ := ((1 - δ : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * Complex.I with hz
  set w : ℂ := ((chiPerronRe x : ℝ) : ℂ) + (T : ℝ) * Complex.I with hw
  have hzre : z.re = 1 - δ := by simp [hz]
  have hzim : z.im = -T := by simp [hz]
  have hwre : w.re = chiPerronRe x := by simp [hw]
  have hwim : w.im = T := by simp [hw]
  have hle1 : 1 - δ ≤ chiPerronRe x := by
    have hlog : 0 < Real.log x := Real.log_pos hx
    have hchi : (1 : ℝ) ≤ chiPerronRe x := by
      dsimp [chiPerronRe]; linarith [one_div_pos.mpr hlog]
    linarith
  have hrect' : ∀ s ∈ (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im), s ≠ 0 ∧
      DirichletCharacter.LFunction χ s ≠ 0 := by
    intro s hs
    rw [Complex.mem_reProdIm] at hs
    obtain ⟨hsre, hsim⟩ := hs
    rw [hzre, hwre, Set.uIcc_of_le hle1] at hsre
    rw [hzim, hwim, Set.uIcc_of_le (by linarith : -T ≤ T)] at hsim
    exact hrect s hsre.1 hsre.2 (abs_le.mpr ⟨hsim.1, hsim.2⟩)
  have hzero := psiChi_boundary_eq_zero χ hχ (x := x) (show 0 < x by linarith) (z := z) (w := w) hrect'
  have hb : (∫ (u : ℝ) in z.re..w.re, psiChiIntF χ x (u + z.im * Complex.I))
      = chiBotInt χ x δ T := by
    rw [chiBotInt, hzre, hwre]
    apply intervalIntegral.integral_congr
    intro u _
    congr 1
    rw [hzim]
  have ht : (∫ (u : ℝ) in z.re..w.re, psiChiIntF χ x (u + w.im * Complex.I))
      = chiTopInt χ x δ T := by
    rw [chiTopInt, hzre, hwre]
    apply intervalIntegral.integral_congr
    intro u _
    congr 1
    rw [hwim]
  have hr : (∫ (y : ℝ) in z.im..w.im, psiChiIntF χ x (w.re + y * Complex.I))
      = chiRightInt χ x T := by
    rw [chiRightInt, hzim, hwim, hwre]
  have hl : (∫ (y : ℝ) in z.im..w.im, psiChiIntF χ x (z.re + y * Complex.I))
      = chiLeftInt χ x δ T := by
    rw [chiLeftInt, hzim, hwim, hzre]
  rw [hb, ht, hr, hl] at hzero
  simp only [smul_eq_mul] at hzero
  set BOT := chiBotInt χ x δ T with hBOT
  set TOP := chiTopInt χ x δ T with hTOP
  set LEFT := chiLeftInt χ x δ T with hLEFT
  have h1 : Complex.I * chiRightInt χ x T = TOP - BOT + Complex.I * LEFT := by
    linear_combination hzero
  have hI1 : (-Complex.I) * Complex.I = 1 := by rw [neg_mul, Complex.I_mul_I, neg_neg]
  have h3 := congrArg (fun z' : ℂ => (-Complex.I) * z') h1
  have hL : (-Complex.I) * (Complex.I * chiRightInt χ x T) = chiRightInt χ x T := by
    rw [← mul_assoc, hI1, one_mul]
  have hR : (-Complex.I) * (TOP - BOT + Complex.I * LEFT) = Complex.I * BOT - Complex.I * TOP + LEFT := by
    rw [mul_add, mul_sub, ← mul_assoc, hI1, one_mul]; ring
  rw [hL, hR] at h3
  rw [chiPerron_eq_right, h3, hBOT, hTOP, hLEFT]

/-- Norm of the Perron integrand. -/
lemma norm_psiChiIntF {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {x : ℝ} (hx : 0 < x)
    (s : ℂ) :
    ‖psiChiIntF χ x s‖ =
      ‖logDeriv (DirichletCharacter.LFunction χ) s‖ * x ^ s.re / ‖s‖ := by
  rw [psiChiIntF, norm_mul, norm_neg, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  ring

/-- Generic bound for a horizontal edge integral of the Perron rectangle. -/
private lemma chiHorizInt_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {x δ σ C1 : ℝ} (hx : 1 ≤ x) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hσ : σ ≠ 0)
    (hB : ∀ u ∈ Set.Icc (1 - δ) (chiPerronRe x),
        ‖logDeriv (DirichletCharacter.LFunction χ) ((u : ℂ) + (σ : ℂ) * Complex.I)‖ ≤ C1) :
    ‖(∫ u : ℝ in (1 - δ)..chiPerronRe x,
        psiChiIntF χ x ((u : ℂ) + (σ : ℂ) * Complex.I))‖
      ≤ C1 * x ^ chiPerronRe x * chiPerronRe x / |σ| := by
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have hchi : (1 : ℝ) ≤ chiPerronRe x := by
    dsimp [chiPerronRe]
    have := one_div_nonneg.mpr hlog
    linarith
  have hle1 : 1 - δ ≤ chiPerronRe x := le_trans (by linarith [hδ0]) hchi
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hσabs : 0 < |σ| := abs_pos.mpr hσ
  have hC1' : 0 ≤ C1 := le_trans (norm_nonneg (logDeriv (DirichletCharacter.LFunction χ)
      (((1 - δ : ℝ) : ℂ) + (σ : ℂ) * Complex.I))) (hB (1 - δ) ⟨le_rfl, hle1⟩)
  have hbound : ∀ u ∈ Set.uIoc (1 - δ) (chiPerronRe x),
      ‖psiChiIntF χ x ((u : ℂ) + (σ : ℂ) * Complex.I)‖ ≤ C1 * x ^ chiPerronRe x / |σ| := by
    intro u hu
    rw [Set.uIoc_of_le hle1] at hu
    have huI : u ∈ Set.Icc (1 - δ) (chiPerronRe x) := ⟨le_of_lt hu.1, hu.2⟩
    have hxu : (0 : ℝ) ≤ x ^ u := Real.rpow_nonneg (le_trans zero_le_one hx) u
    have hnum : ‖logDeriv (DirichletCharacter.LFunction χ) ((u : ℂ) + (σ : ℂ) * Complex.I)‖ * x ^ u
        ≤ C1 * x ^ chiPerronRe x := by
      have h2 : x ^ u ≤ x ^ chiPerronRe x := Real.rpow_le_rpow_of_exponent_le hx huI.2
      calc ‖logDeriv (DirichletCharacter.LFunction χ) ((u : ℂ) + (σ : ℂ) * Complex.I)‖ * x ^ u
          ≤ C1 * x ^ u := mul_le_mul_of_nonneg_right (hB u huI) hxu
        _ ≤ C1 * x ^ chiPerronRe x := mul_le_mul_of_nonneg_left h2 hC1'
    have him : |σ| ≤ ‖((u : ℂ) + (σ : ℂ) * Complex.I : ℂ)‖ := by
      have h := Complex.abs_im_le_norm ((u : ℂ) + (σ : ℂ) * Complex.I)
      rwa [show (((u : ℂ) + (σ : ℂ) * Complex.I : ℂ)).im = σ by simp] at h
    have hpos : 0 < ‖((u : ℂ) + (σ : ℂ) * Complex.I : ℂ)‖ := lt_of_lt_of_le hσabs him
    rw [norm_psiChiIntF χ hx0]
    rw [show (((u : ℂ) + (σ : ℂ) * Complex.I : ℂ)).re = u by simp]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    refine mul_le_mul hnum ?_ (inv_nonneg.mpr (norm_nonneg _))
      (mul_nonneg hC1' (Real.rpow_nonneg (le_trans zero_le_one hx) _))
    simpa [one_div] using one_div_le_one_div_of_le hσabs him
  have hmain := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  refine hmain.trans ?_
  have hC1 : 0 ≤ C1 * x ^ chiPerronRe x / |σ| :=
    div_nonneg (mul_nonneg hC1' (Real.rpow_nonneg (le_trans zero_le_one hx) _)) hσabs.le
  have habs : |chiPerronRe x - (1 - δ)| ≤ chiPerronRe x := by
    rw [abs_sub_le_iff]; exact ⟨by linarith, by linarith⟩
  calc C1 * x ^ chiPerronRe x / |σ| * |chiPerronRe x - (1 - δ)|
      ≤ C1 * x ^ chiPerronRe x / |σ| * chiPerronRe x := mul_le_mul_of_nonneg_left habs hC1
    _ = C1 * x ^ chiPerronRe x * chiPerronRe x / |σ| := by ring

/-- Bound for the top edge integral. -/
lemma chiTopInt_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {x δ T C1 : ℝ}
    (hx : 1 ≤ x) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hT : 0 < T)
    (hTop : ∀ u ∈ Set.Icc (1 - δ) (chiPerronRe x),
        ‖logDeriv (DirichletCharacter.LFunction χ) ((u : ℂ) + (T : ℂ) * Complex.I)‖ ≤ C1) :
    ‖chiTopInt χ x δ T‖ ≤ C1 * x ^ chiPerronRe x * chiPerronRe x / T := by
  rw [chiTopInt]
  simpa [abs_of_nonneg hT.le] using
    chiHorizInt_bound χ (δ := δ) (σ := T) (C1 := C1) hx hδ0 hδ1 (ne_of_gt hT) hTop

/-- Bound for the bottom edge integral. -/
lemma chiBotInt_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {x δ T C1 : ℝ}
    (hx : 1 ≤ x) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hT : 0 < T)
    (hBot : ∀ u ∈ Set.Icc (1 - δ) (chiPerronRe x),
        ‖logDeriv (DirichletCharacter.LFunction χ) ((u : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)‖ ≤ C1) :
    ‖chiBotInt χ x δ T‖ ≤ C1 * x ^ chiPerronRe x * chiPerronRe x / T := by
  rw [chiBotInt]
  simpa [abs_neg, abs_of_nonneg hT.le] using
    chiHorizInt_bound χ (δ := δ) (σ := -T) (C1 := C1) hx hδ0 hδ1 (by linarith) hBot

/-- Bound for the left edge integral of the Perron rectangle. -/
lemma chiLeftInt_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    {x δ T C1 C2 : ℝ} (hx : 1 ≤ x) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2) (hT : 2 ≤ T)
    (hne : ∀ t ∈ Set.Icc (-T) T,
        DirichletCharacter.LFunction χ (((1 - δ : ℝ) : ℂ) + (t : ℂ) * Complex.I) ≠ 0)
    (hC2 : ∀ t : ℝ, |t| ≤ 2 →
        ‖logDeriv (DirichletCharacter.LFunction χ)
          (((1 - δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C2)
    (hC1 : ∀ t : ℝ, 2 ≤ |t| → |t| ≤ T →
        ‖logDeriv (DirichletCharacter.LFunction χ)
          (((1 - δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C1) :
    ‖chiLeftInt χ x δ T‖ ≤
      x ^ (1 - δ) * (8 * C2 + 2 * C1 * (Real.log (T + 2) + 1)) := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hσpos : 0 < 1 - δ := by linarith
  have hxpow : 0 ≤ x ^ (1 - δ) := Real.rpow_nonneg (le_trans zero_le_one hx) _
  have hC2nn : 0 ≤ C2 := le_trans (norm_nonneg _) (hC2 0 (by norm_num))
  have hC1nn : 0 ≤ C1 := le_trans (norm_nonneg _)
    (hC1 2 (by norm_num) (by rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]; exact hT))
  set F : ℝ → ℂ := fun t => psiChiIntF χ x (((1 - δ : ℝ) : ℂ) + (t : ℂ) * Complex.I) with hFdef
  have hnormF : ∀ t : ℝ, ‖F t‖
      = ‖logDeriv (DirichletCharacter.LFunction χ)
          (((1 - δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ * x ^ (1 - δ)
        / ‖(((1 - δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ := by
    intro t
    rw [hFdef, norm_psiChiIntF χ hxpos]
    simp
  have hline : Continuous fun t : ℝ => (((1 - δ : ℝ) : ℂ) + (t : ℂ) * Complex.I) := by fun_prop
  have hneT : ∀ t ∈ Set.uIcc (-T) T,
      DirichletCharacter.LFunction χ (((1 - δ : ℝ) : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro t ht
    rw [Set.uIcc_of_le (by linarith : -T ≤ T)] at ht
    exact hne t ht
  have hseg : ∀ t : ℝ, (((1 - δ : ℝ) : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro t h
    have h2 : ((((1 - δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re = 0 := by rw [h]; simp
    simp at h2
    linarith
  have hcont : ContinuousOn F (Set.uIcc (-T) T) := by
    have hdL : Differentiable ℂ (DirichletCharacter.LFunction χ) := differentiable_LFunction hχ
    have hnum : ContinuousOn (fun t : ℝ =>
        deriv (DirichletCharacter.LFunction χ) (((1 - δ : ℝ) : ℂ) + (t : ℂ) * Complex.I))
        (Set.uIcc (-T) T) := (hdL.deriv.continuous.comp hline).continuousOn
    have hden : ContinuousOn (fun t : ℝ =>
        DirichletCharacter.LFunction χ (((1 - δ : ℝ) : ℂ) + (t : ℂ) * Complex.I))
        (Set.uIcc (-T) T) := (hdL.continuous.comp hline).continuousOn
    have hlog : ContinuousOn (fun t : ℝ => logDeriv (DirichletCharacter.LFunction χ)
        (((1 - δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)) (Set.uIcc (-T) T) := by
      have hh := hnum.div hden hneT
      refine hh.congr (fun t _ => ?_)
      simp only [logDeriv_apply, Pi.div_apply]
    have hcpow : Continuous fun t : ℝ => (x : ℂ) ^ (((1 - δ : ℝ) : ℂ) + (t : ℂ) * Complex.I) :=
      (Commons.NumberTheory.Zeta.cpow_differentiable hxpos).continuous.comp hline
    have hquot : ContinuousOn (fun t : ℝ =>
        (x : ℂ) ^ (((1 - δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)
          / (((1 - δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)) (Set.uIcc (-T) T) :=
      hcpow.continuousOn.div hline.continuousOn (fun t _ => hseg t)
    rw [hFdef]
    exact hlog.mul hquot.neg
  have hsubA : Set.uIcc (-T) (-2) ⊆ Set.uIcc (-T) T := by
    intro t ht
    rw [Set.uIcc_of_le (by linarith : -T ≤ (-2:ℝ))] at ht
    rw [Set.uIcc_of_le (by linarith : -T ≤ T)]
    exact ⟨ht.1, by linarith [ht.2]⟩
  have hsubB : Set.uIcc (-2) 2 ⊆ Set.uIcc (-T) T := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (-2:ℝ) ≤ 2)] at ht
    rw [Set.uIcc_of_le (by linarith : -T ≤ T)]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hsubC : Set.uIcc (2:ℝ) T ⊆ Set.uIcc (-T) T := by
    intro t ht
    rw [Set.uIcc_of_le hT] at ht
    rw [Set.uIcc_of_le (by linarith : -T ≤ T)]
    exact ⟨by linarith [ht.1], ht.2⟩
  have hsubBC : Set.uIcc (-2) T ⊆ Set.uIcc (-T) T := by
    intro t ht
    rw [Set.uIcc_of_le (by linarith : (-2:ℝ) ≤ T)] at ht
    rw [Set.uIcc_of_le (by linarith : -T ≤ T)]
    exact ⟨by linarith [ht.1], ht.2⟩
  have hIntA : IntervalIntegrable F volume (-T) (-2) := (hcont.mono hsubA).intervalIntegrable
  have hIntB : IntervalIntegrable F volume (-2) 2 := (hcont.mono hsubB).intervalIntegrable
  have hIntC : IntervalIntegrable F volume (2:ℝ) T := (hcont.mono hsubC).intervalIntegrable
  have hIntBC : IntervalIntegrable F volume (-2) T := (hcont.mono hsubBC).intervalIntegrable
  have hsplit1 := intervalIntegral.integral_add_adjacent_intervals hIntA hIntBC
  have hsplit2 := intervalIntegral.integral_add_adjacent_intervals hIntB hIntC
  have hBmid : ‖∫ t in (-2:ℝ)..2, F t‖ ≤ 8 * C2 * x ^ (1 - δ) := by
    have hb : ∀ t ∈ Set.uIoc (-2:ℝ) 2, ‖F t‖ ≤ C2 * x ^ (1 - δ) / (1 - δ) := by
      intro t ht
      rw [Set.uIoc_of_le (by norm_num : (-2:ℝ) ≤ 2)] at ht
      have htabs : |t| ≤ 2 := abs_le.mpr ⟨le_of_lt ht.1, ht.2⟩
      rw [hnormF t]
      have h1 : ‖logDeriv (DirichletCharacter.LFunction χ)
          (((1 - δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C2 := hC2 t htabs
      have hden : (1 - δ) ≤ ‖(((1 - δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ := by
        have hh := Complex.re_le_norm (((1 - δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)
        simpa using hh
      have hdenpos : 0 < ‖(((1 - δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ := lt_of_lt_of_le hσpos hden
      rw [div_le_div_iff₀ hdenpos hσpos]
      have hle : ‖logDeriv (DirichletCharacter.LFunction χ)
          (((1 - δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ * (1 - δ)
          ≤ C2 * ‖(((1 - δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ := by
        calc ‖logDeriv (DirichletCharacter.LFunction χ)
              (((1 - δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ * (1 - δ)
            ≤ C2 * (1 - δ) := mul_le_mul_of_nonneg_right h1 hσpos.le
          _ ≤ C2 * ‖(((1 - δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ :=
              mul_le_mul_of_nonneg_left hden hC2nn
      calc ‖logDeriv (DirichletCharacter.LFunction χ)
            (((1 - δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ * x ^ (1 - δ) * (1 - δ)
          = (‖logDeriv (DirichletCharacter.LFunction χ)
            (((1 - δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ * (1 - δ)) * x ^ (1 - δ) := by ring
        _ ≤ (C2 * ‖(((1 - δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖) * x ^ (1 - δ) :=
            mul_le_mul_of_nonneg_right hle hxpow
        _ = C2 * x ^ (1 - δ) * ‖(((1 - δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ := by ring
    have hmain := intervalIntegral.norm_integral_le_of_norm_le_const hb
    have habs : |(2:ℝ) - (-2)| = 4 := by norm_num
    rw [habs] at hmain
    have h4 : C2 * x ^ (1 - δ) / (1 - δ) * 4 ≤ 8 * C2 * x ^ (1 - δ) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hσpos]
      have h2 : (4:ℝ) ≤ 8 * (1 - δ) := by linarith
      calc C2 * x ^ (1 - δ) * 4 ≤ C2 * x ^ (1 - δ) * (8 * (1 - δ)) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = 8 * C2 * x ^ (1 - δ) * (1 - δ) := by ring
    linarith [hmain, h4]
  have hptC : ∀ᵐ t ∂volume, t ∈ Set.Ioc (2:ℝ) T → ‖F t‖ ≤ x ^ (1 - δ) * C1 / t := by
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    rw [hnormF t]
    have h1 : ‖logDeriv (DirichletCharacter.LFunction χ)
        (((1 - δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C1 :=
      hC1 t (by rw [abs_of_nonneg (by linarith [ht.1] : (0:ℝ) ≤ t)]; exact le_of_lt ht.1)
        (by rw [abs_of_nonneg (by linarith [ht.1] : (0:ℝ) ≤ t)]; exact ht.2)
    have hden : t ≤ ‖(((1 - δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ := by
      have hh := Complex.abs_im_le_norm (((1 - δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)
      have him : ((((1 - δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)).im = t := by simp
      rw [him, abs_of_nonneg (by linarith [ht.1] : (0:ℝ) ≤ t)] at hh
      exact hh
    have hdenpos : 0 < ‖(((1 - δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ :=
      lt_of_lt_of_le (by linarith [ht.1]) hden
    have htpos : 0 < t := by linarith [ht.1]
    rw [div_le_div_iff₀ hdenpos htpos]
    calc ‖logDeriv (DirichletCharacter.LFunction χ)
          (((1 - δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ * x ^ (1 - δ) * t
        ≤ ‖logDeriv (DirichletCharacter.LFunction χ)
          (((1 - δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ * x ^ (1 - δ)
            * ‖(((1 - δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ :=
          mul_le_mul_of_nonneg_left hden (by positivity)
      _ ≤ (C1 * x ^ (1 - δ)) * ‖(((1 - δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hxpow) (norm_nonneg _)
      _ = x ^ (1 - δ) * C1 * ‖(((1 - δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ := by ring
  have hCright : ‖∫ t in (2:ℝ)..T, F t‖ ≤ C1 * x ^ (1 - δ) * (Real.log (T + 2) + 1) := by
    have hgint : IntervalIntegrable (fun t : ℝ => x ^ (1 - δ) * C1 / t) volume (2:ℝ) T := by
      refine ContinuousOn.intervalIntegrable ?_
      refine ContinuousOn.div ?_ continuousOn_id ?_
      · fun_prop
      · intro t ht
        rw [Set.uIcc_of_le hT] at ht
        linarith [ht.1]
    have hmain := intervalIntegral.norm_integral_le_of_norm_le hT hptC hgint
    have hcompute : (∫ t in (2:ℝ)..T, x ^ (1 - δ) * C1 / t)
        = x ^ (1 - δ) * C1 * Real.log (T / 2) := by
      rw [show (fun t : ℝ => x ^ (1 - δ) * C1 / t)
          = (fun t : ℝ => (x ^ (1 - δ) * C1) * (1 / t)) by
        funext t; ring]
      rw [intervalIntegral.integral_const_mul,
        integral_one_div_of_pos (by norm_num : (0:ℝ) < 2) (by linarith)]
    rw [hcompute] at hmain
    refine hmain.trans ?_
    have hlog : Real.log (T / 2) ≤ Real.log (T + 2) + 1 := by
      rw [Real.log_div (by linarith : T ≠ 0) (by norm_num : (2:ℝ) ≠ 0)]
      have h2 : Real.log T ≤ Real.log (T + 2) := Real.log_le_log (by linarith) (by linarith)
      have h3 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      linarith
    calc x ^ (1 - δ) * C1 * Real.log (T / 2)
        ≤ x ^ (1 - δ) * C1 * (Real.log (T + 2) + 1) :=
          mul_le_mul_of_nonneg_left hlog (mul_nonneg hxpow hC1nn)
      _ = C1 * x ^ (1 - δ) * (Real.log (T + 2) + 1) := by ring
  have hCleft : ‖∫ t in (-T)..(-2:ℝ), F t‖ ≤ C1 * x ^ (1 - δ) * (Real.log (T + 2) + 1) := by
    have hcomp : (∫ t in (-T)..(-2:ℝ), F t) = ∫ t in (2:ℝ)..T, F (-t) := by
      have hh := intervalIntegral.integral_comp_neg (f := F) (a := (2:ℝ)) (b := T)
      simpa using hh.symm
    rw [hcomp]
    have hptC' : ∀ᵐ t ∂volume, t ∈ Set.Ioc (2:ℝ) T → ‖F (-t)‖ ≤ x ^ (1 - δ) * C1 / t := by
      refine Filter.Eventually.of_forall (fun t ht => ?_)
      rw [hnormF (-t)]
      have h1 : ‖logDeriv (DirichletCharacter.LFunction χ)
          (((1 - δ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)‖ ≤ C1 := by
        refine hC1 (-t) (by
          rw [abs_neg, abs_of_nonneg (by linarith [ht.1] : (0:ℝ) ≤ t)]
          exact le_of_lt ht.1) ?_
        rw [abs_neg, abs_of_nonneg (by linarith [ht.1] : (0:ℝ) ≤ t)]
        exact ht.2
      have hden : t ≤ ‖(((1 - δ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)‖ := by
        have hh := Complex.abs_im_le_norm (((1 - δ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)
        have him : ((((1 - δ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)).im = -t := by simp
        rw [him, abs_neg, abs_of_nonneg (by linarith [ht.1] : (0:ℝ) ≤ t)] at hh
        exact hh
      have hdenpos : 0 < ‖(((1 - δ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)‖ :=
        lt_of_lt_of_le (by linarith [ht.1]) hden
      have htpos : 0 < t := by linarith [ht.1]
      rw [div_le_div_iff₀ hdenpos htpos]
      calc ‖logDeriv (DirichletCharacter.LFunction χ)
            (((1 - δ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)‖ * x ^ (1 - δ) * t
          ≤ ‖logDeriv (DirichletCharacter.LFunction χ)
            (((1 - δ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)‖ * x ^ (1 - δ)
              * ‖(((1 - δ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)‖ :=
            mul_le_mul_of_nonneg_left hden (by positivity)
        _ ≤ (C1 * x ^ (1 - δ)) * ‖(((1 - δ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hxpow) (norm_nonneg _)
        _ = x ^ (1 - δ) * C1 * ‖(((1 - δ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)‖ := by ring
    have hgint : IntervalIntegrable (fun t : ℝ => x ^ (1 - δ) * C1 / t) volume (2:ℝ) T := by
      refine ContinuousOn.intervalIntegrable ?_
      refine ContinuousOn.div ?_ continuousOn_id ?_
      · fun_prop
      · intro t ht
        rw [Set.uIcc_of_le hT] at ht
        linarith [ht.1]
    have hmain := intervalIntegral.norm_integral_le_of_norm_le hT hptC' hgint
    have hcompute : (∫ t in (2:ℝ)..T, x ^ (1 - δ) * C1 / t)
        = x ^ (1 - δ) * C1 * Real.log (T / 2) := by
      rw [show (fun t : ℝ => x ^ (1 - δ) * C1 / t)
          = (fun t : ℝ => (x ^ (1 - δ) * C1) * (1 / t)) by
        funext t; ring]
      rw [intervalIntegral.integral_const_mul,
        integral_one_div_of_pos (by norm_num : (0:ℝ) < 2) (by linarith)]
    rw [hcompute] at hmain
    refine hmain.trans ?_
    have hlog : Real.log (T / 2) ≤ Real.log (T + 2) + 1 := by
      rw [Real.log_div (by linarith : T ≠ 0) (by norm_num : (2:ℝ) ≠ 0)]
      have h2 : Real.log T ≤ Real.log (T + 2) := Real.log_le_log (by linarith) (by linarith)
      have h3 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      linarith
    calc x ^ (1 - δ) * C1 * Real.log (T / 2)
        ≤ x ^ (1 - δ) * C1 * (Real.log (T + 2) + 1) :=
          mul_le_mul_of_nonneg_left hlog (mul_nonneg hxpow hC1nn)
      _ = C1 * x ^ (1 - δ) * (Real.log (T + 2) + 1) := by ring
  have htotal : ‖chiLeftInt χ x δ T‖
      ≤ ‖∫ t in (-T)..(-2:ℝ), F t‖ + ‖∫ t in (-2:ℝ)..(2:ℝ), F t‖
        + ‖∫ t in (2:ℝ)..T, F t‖ := by
    have e1 : chiLeftInt χ x δ T = ∫ t in (-T)..T, F t := rfl
    rw [e1, ← hsplit1, ← hsplit2]
    have h1 := norm_add_le (∫ t in (-T)..(-2:ℝ), F t)
      ((∫ t in (-2:ℝ)..(2:ℝ), F t) + ∫ t in (2:ℝ)..T, F t)
    have h2 := norm_add_le (∫ t in (-2:ℝ)..(2:ℝ), F t) (∫ t in (2:ℝ)..T, F t)
    linarith
  have hident : C1 * x ^ (1 - δ) * (Real.log (T + 2) + 1) + 8 * C2 * x ^ (1 - δ)
      + C1 * x ^ (1 - δ) * (Real.log (T + 2) + 1)
      = x ^ (1 - δ) * (8 * C2 + 2 * C1 * (Real.log (T + 2) + 1)) := by ring
  linarith [htotal, hBmid, hCright, hCleft, hident]


lemma sum_range_eq_sum_Icc (f : ℕ → ℂ) (x : ℕ) (h0 : f 0 = 0) :
    ∑ n ∈ Finset.range (x + 1), f n = ∑ n ∈ Finset.Icc 1 x, f n := by
  have hset : Finset.Ico 0 (x + 1) = insert 0 (Finset.Icc 1 x) := by
    ext n
    simp only [Finset.mem_Ico, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [Finset.range_eq_Ico, hset, Finset.sum_insert (by simp [Finset.mem_Icc]), h0, zero_add]


/-! ## Auxiliary asymptotic estimates for the final assembly -/

/-- `exp (-c √(log x)) ≤ (log x)^{-A}` eventually, for `c > 0`, `A > 0`. -/
private lemma eventually_exp_neg_sqrtLog_le_inv_pow (c : ℝ) (hc : 0 < c) (A : ℝ) (hA : 0 < A) :
    ∀ᶠ x : ℝ in Filter.atTop,
      Real.exp (-c * Real.sqrt (Real.log x)) ≤ 1 / (Real.log x) ^ A := by
  obtain ⟨N, hN⟩ := exists_nat_ge A
  have hpoly : ∀ᶠ x : ℝ in Filter.atTop,
      (Real.log x) ^ N * Real.exp (-c * Real.sqrt (Real.log x)) ≤ 1 := by
    have h := Commons.Analysis.Asymptotics.poly_mul_exp_neg_sqrtLog_le c hc N 1 (by norm_num)
    filter_upwards [h] with x hx
    have h2 : Real.exp (-(c / 2) * Real.sqrt (Real.log x)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [Real.sqrt_nonneg (Real.log x), hc]
    linarith [hx, h2]
  filter_upwards [hpoly, Filter.eventually_ge_atTop (Real.exp 1)] with x hx hx1
  have hL1 : 1 ≤ Real.log x := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hx1
  have hLpos : 0 < Real.log x := lt_of_lt_of_le one_pos hL1
  have hLN : 0 < (Real.log x) ^ N := pow_pos hLpos N
  have hkey : Real.exp (-c * Real.sqrt (Real.log x)) ≤ 1 / (Real.log x) ^ N := by
    rw [le_div_iff₀ hLN]
    calc Real.exp (-c * Real.sqrt (Real.log x)) * (Real.log x) ^ N
        = (Real.log x) ^ N * Real.exp (-c * Real.sqrt (Real.log x)) := by ring
      _ ≤ 1 := hx
  refine hkey.trans ?_
  have hpow : (Real.log x) ^ A ≤ (Real.log x) ^ N := by
    have h' : (Real.log x) ^ A ≤ (Real.log x) ^ ((N : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by exact_mod_cast hN)
    rwa [Real.rpow_natCast] at h'
  exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hLpos A) hpow

/-- `C (log x)^k exp(-c √(log x)) ≤ (log x)^{-A}` eventually. -/
private lemma eventually_pow_log_mul_exp_neg_sqrtLog_le (k : ℕ) (c : ℝ) (hc : 0 < c)
    (C : ℝ) (hC : 0 ≤ C) (A : ℝ) (hA : 0 < A) :
    ∀ᶠ x : ℝ in Filter.atTop,
      C * (Real.log x) ^ k * Real.exp (-c * Real.sqrt (Real.log x)) ≤
        1 / (Real.log x) ^ A := by
  have h1 := Commons.Analysis.Asymptotics.poly_mul_exp_neg_sqrtLog_le c hc k C hC
  have h2 := eventually_exp_neg_sqrtLog_le_inv_pow (c / 2) (by linarith) A hA
  filter_upwards [h1, h2] with x hx1 hx2
  exact le_trans hx1 hx2

/-- `C (log x)^k ≤ x` eventually. -/
private lemma eventually_pow_log_mul_le_self (k : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ x : ℝ in Filter.atTop, C * (Real.log x) ^ k ≤ x := by
  rcases eq_or_lt_of_le hC with h0 | hpos
  · filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with x hx
    rw [← h0, zero_mul]; exact hx
  · have hε : (0:ℝ) < 1 / max C 1 := by positivity
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 k one_ne_zero).eventually_le_const hε
    filter_upwards [h, Filter.eventually_ge_atTop (1:ℝ)] with x hx hx1
    have hxpos : 0 < x := lt_of_lt_of_le one_pos hx1
    have hdiv : (Real.log x) ^ k / (1 * x + 0) ≤ 1 / max C 1 := hx
    rw [one_mul, add_zero, div_le_iff₀ hxpos] at hdiv
    have hCmax : C * (1 / max C 1) ≤ 1 := by
      rw [mul_one_div, div_le_one (by positivity)]
      exact le_max_left C 1
    calc C * (Real.log x) ^ k ≤ C * (1 / max C 1 * x) := mul_le_mul_of_nonneg_left hdiv hC
      _ = C * (1 / max C 1) * x := by ring
      _ ≤ 1 * x := mul_le_mul_of_nonneg_right hCmax hxpos.le
      _ = x := one_mul x

/-- `(log x)^A ≤ (log x)^N` for `N ≥ A` and `x ≥ e`. -/
private lemma rpow_le_rpow_log {x A : ℝ} (N : ℕ) (hx : 1 ≤ Real.log x)
    (hAN : A ≤ (N : ℝ)) : (Real.log x) ^ A ≤ (Real.log x) ^ N :=
  Real.rpow_natCast (Real.log x) N ▸ Real.rpow_le_rpow_of_exponent_le hx hAN


/-- `m log log x + m ≤ √(log x)` eventually. -/
private lemma eventually_sqrtLog_ge (m : ℝ) :
    ∀ᶠ x : ℝ in Filter.atTop,
      m * Real.log (Real.log x) + m ≤ Real.sqrt (Real.log x) := by
  set M : ℝ := |m| with hMdef
  have hM0 : 0 ≤ M := abs_nonneg m
  have hcomp : (fun x : ℝ => Real.log (Real.log x)) =o[Filter.atTop]
      (fun x : ℝ => (Real.log x) ^ (1 / 2 : ℝ)) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ) < 1/2)).comp_tendsto Real.tendsto_log_atTop
  have hε : (0:ℝ) < 1 / (M + 1) := by positivity
  have hmain := (Asymptotics.isLittleO_iff.mp hcomp) hε
  filter_upwards [hmain, Filter.eventually_ge_atTop (Real.exp ((M * (M + 1)) ^ 2 + 1))]
    with x hx hx1
  have hL1 : 1 ≤ Real.log x := by
    have h : (M * (M + 1)) ^ 2 + 1 ≤ Real.log x := by
      rw [← Real.log_exp ((M * (M + 1)) ^ 2 + 1)]
      exact Real.log_le_log (Real.exp_pos _) hx1
    linarith [sq_nonneg (M * (M + 1))]
  have hLnn : 0 ≤ Real.log x := le_trans zero_le_one hL1
  have hroot : ‖(Real.log x) ^ (1 / 2 : ℝ)‖ = Real.sqrt (Real.log x) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hLnn _), Real.sqrt_eq_rpow]
  have hlogabs : |Real.log (Real.log x)| ≤ (1 / (M + 1)) * Real.sqrt (Real.log x) := by
    have hx' : |Real.log (Real.log x)| ≤ (1 / (M + 1)) * Real.sqrt (Real.log x) := by
      rw [hroot, Real.norm_eq_abs] at hx
      exact hx
    rw [abs_le]
    exact ⟨by linarith [neg_abs_le (Real.log (Real.log x)), hx'],
      by linarith [le_abs_self (Real.log (Real.log x)), hx']⟩
  have hsq : M * (M + 1) ≤ Real.sqrt (Real.log x) := by
    have h : (M * (M + 1)) ^ 2 ≤ Real.log x := by
      have h' : (M * (M + 1)) ^ 2 + 1 ≤ Real.log x := by
        rw [← Real.log_exp ((M * (M + 1)) ^ 2 + 1)]
        exact Real.log_le_log (Real.exp_pos _) hx1
      linarith
    calc M * (M + 1) = Real.sqrt ((M * (M + 1)) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt (Real.log x) := Real.sqrt_le_sqrt h
  have hmul : m * Real.log (Real.log x) ≤ M * |Real.log (Real.log x)| := by
    calc m * Real.log (Real.log x) ≤ |m * Real.log (Real.log x)| := le_abs_self _
      _ = M * |Real.log (Real.log x)| := by rw [abs_mul, hMdef]
  have hmM : m ≤ M := by rw [hMdef]; exact le_abs_self m
  have h3 : M ≤ (1 / (M + 1)) * Real.sqrt (Real.log x) := by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by linarith : (0:ℝ) < M + 1)]
    exact hsq
  have hstep1 : m * Real.log (Real.log x) + m ≤
      M * |Real.log (Real.log x)| + M := by linarith [hmul, hmM]
  have hstep2 : M * |Real.log (Real.log x)| ≤ M * ((1 / (M + 1)) * Real.sqrt (Real.log x)) :=
    mul_le_mul_of_nonneg_left hlogabs hM0
  have hfinal : (M / (M + 1)) * Real.sqrt (Real.log x) + (1 / (M + 1)) * Real.sqrt (Real.log x)
      = Real.sqrt (Real.log x) := by
    rw [← add_mul]
    have : M / (M + 1) + 1 / (M + 1) = 1 := by
      rw [← add_div]
      exact div_self (by linarith : (M + 1) ≠ 0)
    rw [this, one_mul]
  calc m * Real.log (Real.log x) + m
      ≤ M * |Real.log (Real.log x)| + M := hstep1
    _ ≤ M * ((1 / (M + 1)) * Real.sqrt (Real.log x)) + (1 / (M + 1)) * Real.sqrt (Real.log x) := by
        linarith [hstep2, h3]
    _ = (M / (M + 1)) * Real.sqrt (Real.log x) + (1 / (M + 1)) * Real.sqrt (Real.log x) := by ring
    _ = Real.sqrt (Real.log x) := hfinal


/-- **The contour-shift engine with an explicit truncated-Perron constant.**  This is
`psiChi_le_engine'` with the constant supplied by the caller (so that it can be taken
uniform in the character). -/
theorem psiChi_le_engine_of_perron {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    {Ctr : ℝ} (hCtr : 0 < Ctr)
    (hper : ∀ (x : ℝ), 3 ≤ x → ∀ T : ℝ, 2 ≤ T →
      ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
            χ ((n : ℕ) : ZMod N) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
          - chiPerron χ x T‖ ≤ Ctr * (x * (Real.log x) ^ 2 / T + Real.log x)) :
    ∀ {x T δ C1 C2 : ℝ}, 3 ≤ x → 2 ≤ T → 0 < δ → δ ≤ 1 / 2 →
      (∀ s : ℂ, 1 - δ ≤ s.re → s.re ≤ chiPerronRe x → |s.im| ≤ T →
          s ≠ 0 ∧ DirichletCharacter.LFunction χ s ≠ 0) →
      (∀ u ∈ Set.Icc (1 - δ) (chiPerronRe x),
          ‖logDeriv (DirichletCharacter.LFunction χ) ((u : ℂ) + (T : ℂ) * Complex.I)‖ ≤ C1) →
      (∀ u ∈ Set.Icc (1 - δ) (chiPerronRe x),
          ‖logDeriv (DirichletCharacter.LFunction χ) ((u : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)‖ ≤ C1) →
      (∀ t ∈ Set.Icc (-T) T,
          DirichletCharacter.LFunction χ (((1 - δ : ℝ) : ℂ) + (t : ℂ) * Complex.I) ≠ 0) →
      (∀ t : ℝ, |t| ≤ 2 →
          ‖logDeriv (DirichletCharacter.LFunction χ)
            (((1 - δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C2) →
      (∀ t : ℝ, 2 ≤ |t| → |t| ≤ T →
          ‖logDeriv (DirichletCharacter.LFunction χ)
            (((1 - δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C1) →
      ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
            χ ((n : ℕ) : ZMod N) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))‖ ≤
        Ctr * (x * (Real.log x) ^ 2 / T + Real.log x) +
          (1 / (2 * Real.pi)) *
            (2 * (C1 * x ^ chiPerronRe x * chiPerronRe x / T)
              + x ^ (1 - δ) * (8 * C2 + 2 * C1 * (Real.log (T + 2) + 1))) := by
  intro x T δ C1 C2 hx hT hδ0 hδ1 hrect hTop hBot hleft hC2b hC1b
  have hx1 : (1 : ℝ) < x := by linarith
  have htrunc := hper x hx T hT
  have hedges := chiPerron_eq_edges χ hχ (x := x) (T := T) (δ := δ) hx1 (by linarith)
    hδ0.le (by linarith) hrect
  have htop := chiTopInt_bound χ (x := x) (δ := δ) (T := T) (C1 := C1) (by linarith)
    hδ0.le (by linarith) (by linarith) hTop
  have hbot := chiBotInt_bound χ (x := x) (δ := δ) (T := T) (C1 := C1) (by linarith)
    hδ0.le (by linarith) (by linarith) hBot
  have hleftb := chiLeftInt_bound χ hχ (x := x) (δ := δ) (T := T) (C1 := C1) (C2 := C2)
    (by linarith) hδ0.le hδ1 (by linarith) hleft hC2b hC1b
  have hnorm : ‖chiPerron χ x T‖ ≤
      (1 / (2 * Real.pi)) * (2 * (C1 * x ^ chiPerronRe x * chiPerronRe x / T)
        + x ^ (1 - δ) * (8 * C2 + 2 * C1 * (Real.log (T + 2) + 1))) := by
    rw [hedges]
    have hc : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
      simp only [norm_div, norm_one]
      congr 1
      simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [norm_mul, hc]
    have hI1 : ‖Complex.I * chiBotInt χ x δ T‖ = ‖chiBotInt χ x δ T‖ := by
      rw [norm_mul, Complex.norm_I, one_mul]
    have hI2 : ‖Complex.I * chiTopInt χ x δ T‖ = ‖chiTopInt χ x δ T‖ := by
      rw [norm_mul, Complex.norm_I, one_mul]
    have h1 := norm_add_le (Complex.I * chiBotInt χ x δ T - Complex.I * chiTopInt χ x δ T)
      (chiLeftInt χ x δ T)
    have h2 := norm_sub_le (Complex.I * chiBotInt χ x δ T) (Complex.I * chiTopInt χ x δ T)
    rw [hI1, hI2] at h2
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    linarith [h1, h2, htop, hbot, hleftb]
  have hmain : ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        χ ((n : ℕ) : ZMod N) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))‖
      ≤ ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
          χ ((n : ℕ) : ZMod N) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
          - chiPerron χ x T‖ + ‖chiPerron χ x T‖ := by
    have hsum := norm_add_le ((∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        χ ((n : ℕ) : ZMod N) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
          - chiPerron χ x T) (chiPerron χ x T)
    simpa using hsum
  linarith [hmain, htrunc, hnorm]


/-- **Reduction of the Siegel–Walfisz target to five uniform analytic inputs.** -/
theorem siegel_walfisz_chi_of_uniform_inputs
    (hPerron : ∃ C : ℝ, 0 < C ∧ ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
        (x : ℝ), 3 ≤ x → ∀ T : ℝ, 2 ≤ T →
        ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
              χ ((n : ℕ) : ZMod N) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
            - chiPerron χ x T‖ ≤ C * (x * (Real.log x) ^ 2 / T + Real.log x))
    (hOff : ∃ c : ℝ, 0 < c ∧ ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N),
      χ.IsPrimitive → χ ≠ 1 → ∀ σ t : ℝ, t ≠ 0 →
        1 - c / Real.log ((N : ℝ) * (|t| + 2)) ≤ σ →
        DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0)
    (hReal : ∃ c : ℝ, 0 < c ∧ ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N),
      χ.IsPrimitive → χ ≠ 1 → χ * χ ≠ 1 → ∀ σ : ℝ,
        1 - c / Real.log (2 * (N : ℝ)) ≤ σ →
        DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0)
    (hZero : ∃ c : ℝ, 0 < c ∧ ∃ K : ℝ, 0 < K ∧ ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N),
      χ.IsPrimitive → χ ≠ 1 → χ * χ = 1 → ∀ β : ℝ, 0 < β → β < 1 →
        DirichletCharacter.LFunction χ (β : ℂ) = 0 → c / (N : ℝ) ^ K ≤ 1 - β)
    (hLog : ∃ C : ℝ, 0 < C ∧
      ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N),
      χ.IsPrimitive → χ ≠ 1 → ∀ σ t r : ℝ, 1 / 2 ≤ σ → σ ≤ 5 / 4 → 0 < r → r ≤ 1 →
        (∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 →
          r ≤ ‖((σ : ℂ) + (t : ℂ) * Complex.I) - ρ‖) →
        ‖logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          C * (1 + 1 / r) * (Real.log ((N : ℝ) * (|t| + 2)) + 1)) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧
    ∀ᶠ x : ℕ in Filter.atTop,
      ∀ {q : ℕ} [NeZero q], q ≤ ⌊(Real.log (x:ℝ)) ^ C⌋₊ →
      ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → χ ≠ 1 →
        ‖∑ n ∈ Finset.range (x+1),
            ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q)‖ ≤
          (x:ℝ) / (Real.log (x:ℝ))^A := by
  intro A hA
  obtain ⟨CtrP, hCtrP, hPerron⟩ := hPerron
  obtain ⟨cOff, hcOff, hOff⟩ := hOff
  obtain ⟨cReal, hcReal, hReal⟩ := hReal
  obtain ⟨cZero, hcZero, K, hK, hZero⟩ := hZero
  obtain ⟨CL, hCL, hLog⟩ := hLog
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge A
  let c₁ : ℝ := min cOff cReal
  let c₂ : ℝ := min (c₁ / 16) (cZero / 4)
  let Cexp : ℝ := min 1 (1 / (2 * K))
  let CLb : ℝ := CL * (9 + 18 / c₁ + 6 / cZero)
  have hc₁pos : 0 < c₁ := lt_min hcOff hcReal
  have hc₁off : c₁ ≤ cOff := min_le_left _ _
  have hc₁real : c₁ ≤ cReal := min_le_right _ _
  have hc₂pos : 0 < c₂ := lt_min (by positivity) (by positivity)
  have hc₂le1 : c₂ ≤ c₁ / 16 := min_le_left _ _
  have hc₂le2 : c₂ ≤ cZero / 4 := min_le_right _ _
  have hCLb : 0 < CLb := by
    have h3 : 0 < 9 + 18 / c₁ + 6 / cZero := by positivity
    exact mul_pos hCL h3
  have hCexppos : 0 < Cexp := lt_min one_pos (by positivity)
  have hCexpK : Cexp * K ≤ 1 / 2 := by
    have h1 : Cexp ≤ 1 / (2 * K) := min_le_right _ _
    have h3 : Cexp * K ≤ (1 / (2 * K)) * K := mul_le_mul_of_nonneg_right h1 hK.le
    have h4 : (1 / (2 * K)) * K = 1 / 2 := by field_simp
    rw [h4] at h3
    linarith
  let m₀ : ℝ := max (max Cexp 3) (c₁ / 4)
  have hm₀Cexp : Cexp ≤ m₀ := le_trans (le_max_left _ _) (le_max_left _ _)
  have hm₀3 : (3:ℝ) ≤ m₀ := le_trans (le_max_right _ _) (le_max_left _ _)
  have hm₀c₁ : c₁ / 4 ≤ m₀ := le_max_right _ _
  refine ⟨Cexp, hCexppos, ?_⟩
  have hEv1 : ∀ᶠ x : ℕ in Filter.atTop, (3:ℝ) ≤ (x:ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (Filter.eventually_ge_atTop (3:ℝ))
  have hEv2 : ∀ᶠ x : ℕ in Filter.atTop, (4:ℝ) ≤ Real.log (x:ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (Real.tendsto_log_atTop.eventually_ge_atTop 4)
  have hEv3 : ∀ᶠ x : ℕ in Filter.atTop,
      m₀ * Real.log (Real.log (x:ℝ)) + m₀ ≤ Real.sqrt (Real.log (x:ℝ)) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_sqrtLog_ge m₀)
  have hEv4 : ∀ᶠ x : ℕ in Filter.atTop,
      6 * CtrP * (Real.log (x:ℝ)) ^ 2 * Real.exp (-1 * Real.sqrt (Real.log (x:ℝ))) ≤
        1 / (Real.log (x:ℝ)) ^ A :=
    tendsto_natCast_atTop_atTop.eventually
      (eventually_pow_log_mul_exp_neg_sqrtLog_le 2 1 one_pos (6 * CtrP) (by positivity) A hA)
  have hEv5 : ∀ᶠ x : ℕ in Filter.atTop,
      6 * CtrP * (Real.log (x:ℝ)) ^ (N₀ + 1) ≤ (x:ℝ) :=
    tendsto_natCast_atTop_atTop.eventually
      (eventually_pow_log_mul_le_self (N₀ + 1) (6 * CtrP) (by positivity))
  have hEv6 : ∀ᶠ x : ℕ in Filter.atTop,
      6 * CLb * Real.exp 1 / Real.pi * (Real.log (x:ℝ)) ^ 1 *
        Real.exp (-1 * Real.sqrt (Real.log (x:ℝ))) ≤ 1 / (Real.log (x:ℝ)) ^ A :=
    tendsto_natCast_atTop_atTop.eventually
      (eventually_pow_log_mul_exp_neg_sqrtLog_le 1 1 one_pos (6 * CLb * Real.exp 1 / Real.pi)
        (by positivity) A hA)
  have hEv7 : ∀ᶠ x : ℕ in Filter.atTop,
      21 * CLb / Real.pi * (Real.log (x:ℝ)) ^ 2 * Real.exp (-c₂ * Real.sqrt (Real.log (x:ℝ))) ≤
        1 / (Real.log (x:ℝ)) ^ A :=
    tendsto_natCast_atTop_atTop.eventually
      (eventually_pow_log_mul_exp_neg_sqrtLog_le 2 c₂ hc₂pos (21 * CLb / Real.pi)
        (by positivity) A hA)
  filter_upwards [hEv1, hEv2, hEv3, hEv4, hEv5, hEv6, hEv7]
    with x hx3 hL4 hsl hdec1 hdec2 hdec3 hdec4
  intro q _ hq χ hχprim hχ1
  let L : ℝ := Real.log (x:ℝ)
  let T : ℝ := Real.exp (Real.sqrt L)
  have hLpos : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hLnonneg : 0 ≤ L := le_trans zero_le_one hL1
  have hx1 : (1:ℝ) ≤ (x:ℝ) := by linarith
  have hqpos : 0 < (q:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hq1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hq2 : 2 ≤ q := by
    have hne1 : q ≠ 1 := by
      intro h1; subst h1; exact hχ1 (Subsingleton.elim χ 1)
    have hne0 : q ≠ 0 := NeZero.ne q
    omega
  have hqK : 1 < (q:ℝ) ^ K := Real.one_lt_rpow (by exact_mod_cast hq2 : (1:ℝ) < (q:ℝ)) hK
  have hT2 : 2 ≤ T := by
    have hlog2 : Real.log 2 ≤ Real.sqrt L := by
      have h1 : (2:ℝ) ≤ Real.sqrt L := by
        rw [← Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
        exact Real.sqrt_le_sqrt (by norm_num; linarith : ((2:ℝ)) ^ 2 ≤ L)
      linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)]
    calc (2:ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp (Real.sqrt L) := Real.exp_le_exp.mpr hlog2
      _ = T := by rw [show T = Real.exp (Real.sqrt L) from rfl]
  have hTpos : 0 < T := Real.exp_pos _
  have hT1 : (1:ℝ) ≤ T := by
    have h := Real.exp_le_exp.mpr (Real.sqrt_nonneg L)
    rw [Real.exp_zero] at h
    exact h
  have hlogT : Real.log (T + 2) ≤ Real.sqrt L + 2 := by
    have h1 : T + 2 ≤ 3 * T := by linarith
    have h2 : Real.log (3 * T) = Real.log 3 + Real.log T :=
      Real.log_mul (by norm_num) (ne_of_gt hTpos)
    have h3 : Real.log T = Real.sqrt L := by
      rw [show T = Real.exp (Real.sqrt L) from rfl, Real.log_exp]
    have h4 : Real.log 3 ≤ 2 := by
      have h5 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 3)
      linarith
    have h5 : Real.log (T + 2) ≤ Real.log 3 + Real.log T := by
      rw [← h2]
      exact Real.log_le_log (by linarith) h1
    rw [h3] at h5
    linarith
  have hsqrtlogeq : Real.sqrt L ≤ Real.log (T + 2) := by
    calc Real.sqrt L = Real.log (Real.exp (Real.sqrt L)) := (Real.log_exp _).symm
      _ ≤ Real.log (T + 2) := Real.log_le_log (Real.exp_pos _) (by
          rw [show T = Real.exp (Real.sqrt L) from rfl]; linarith)
  have hqR : (q:ℝ) ≤ L ^ Cexp := by
    have hfl : (⌊L ^ Cexp⌋₊ : ℝ) ≤ L ^ Cexp :=
      Nat.floor_le (Real.rpow_nonneg hLnonneg _)
    have h2 : (q:ℝ) ≤ (⌊L ^ Cexp⌋₊ : ℝ) := by exact_mod_cast hq
    linarith
  have hlogq : Real.log (q:ℝ) ≤ Cexp * Real.log L := by
    calc Real.log (q:ℝ) ≤ Real.log (L ^ Cexp) := Real.log_le_log hqpos hqR
      _ = Cexp * Real.log L := Real.log_rpow hLpos Cexp
  have hlogq_bound : Real.log ((q:ℝ) * (T + 2)) + 1 ≤ 3 * Real.sqrt L := by
    have h3 : Real.log ((q:ℝ) * (T + 2)) = Real.log (q:ℝ) + Real.log (T + 2) :=
      Real.log_mul (ne_of_gt hqpos) (by linarith)
    have h4 : Cexp * Real.log L + 3 ≤ Real.sqrt L := by
      have h5 : m₀ * Real.log L + m₀ ≤ Real.sqrt L := hsl
      have h6 : Cexp * Real.log L ≤ m₀ * Real.log L :=
        mul_le_mul_of_nonneg_right hm₀Cexp (Real.log_nonneg (by linarith : (1:ℝ) ≤ L))
      linarith [h5, h6, hm₀3]
    have h5 : Real.log ((q:ℝ) * (T + 2)) ≤ 2 * Real.sqrt L := by
      rw [h3]
      linarith [hlogq, h4, hlogT]
    linarith [h5, Real.sqrt_nonneg L]
  have hsqrtL_le_logqT : Real.sqrt L ≤ Real.log ((q:ℝ) * (T + 2)) := by
    have h3 : Real.log (T + 2) ≤ Real.log ((q:ℝ) * (T + 2)) :=
      Real.log_le_log (by linarith) (by nlinarith [hq1, hT2])
    linarith [hsqrtlogeq, h3]
  let δ : ℝ := min (c₁ / (8 * Real.log ((q:ℝ) * (T + 2)))) (cZero / (4 * (q:ℝ) ^ K))
  have hlogqT_pos : 0 < Real.log ((q:ℝ) * (T + 2)) := by
    apply Real.log_pos; nlinarith [hq1, hT2]
  have hδpos : 0 < δ := lt_min (by positivity) (by positivity)
  have hδhalf : δ ≤ 1 / 2 := by
    have h5 : c₁ / 4 ≤ Real.sqrt L := by
      have h6 : m₀ ≤ m₀ * Real.log L + m₀ := by
        have h7 : 0 ≤ m₀ * Real.log L :=
          mul_nonneg (by linarith [hm₀3]) (Real.log_nonneg (by linarith : (1:ℝ) ≤ L))
        linarith
      linarith [hm₀c₁, h6, hsl]
    calc δ ≤ c₁ / (8 * Real.log ((q:ℝ) * (T + 2))) := min_le_left _ _
      _ ≤ 1 / 2 := by
          rw [div_le_iff₀ (by positivity : (0:ℝ) < 8 * Real.log ((q:ℝ) * (T + 2)))]
          nlinarith [hsqrtL_le_logqT, h5, hc₁pos]
  have hδoff : ∀ t : ℝ, |t| ≤ T → δ ≤ cOff / Real.log ((q:ℝ) * (|t| + 2)) := by
    intro t ht
    have h00 : (0:ℝ) < (q:ℝ) * (|t| + 2) := mul_pos hqpos (by linarith [abs_nonneg t])
    have h2 : Real.log ((q:ℝ) * (|t| + 2)) ≤ Real.log ((q:ℝ) * (T + 2)) :=
      Real.log_le_log h00 (by
        have := abs_le.mp ht; nlinarith [hqpos, this.1, this.2])
    have h3 : 0 < Real.log ((q:ℝ) * (|t| + 2)) := by
      apply Real.log_pos; nlinarith [hq1, abs_nonneg t]
    have h4 : δ ≤ c₁ / (8 * Real.log ((q:ℝ) * (T + 2))) := min_le_left _ _
    calc δ ≤ c₁ / (8 * Real.log ((q:ℝ) * (T + 2))) := h4
      _ ≤ c₁ / (8 * Real.log ((q:ℝ) * (|t| + 2))) := by
          rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 8 * Real.log ((q:ℝ) * (T + 2)))
            (by positivity : (0:ℝ) < 8 * Real.log ((q:ℝ) * (|t| + 2)))]
          nlinarith [h2]
      _ ≤ cOff / Real.log ((q:ℝ) * (|t| + 2)) := by
          rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 8 * Real.log ((q:ℝ) * (|t| + 2))) h3]
          nlinarith [hc₁off, h3]
  have hδreal : δ ≤ cReal / Real.log (2 * (q:ℝ)) := by
    have h2 : Real.log (2 * (q:ℝ)) ≤ Real.log ((q:ℝ) * (T + 2)) :=
      Real.log_le_log (by positivity) (by nlinarith [hqpos, hT2])
    have h3 : 0 < Real.log (2 * (q:ℝ)) := by
      apply Real.log_pos; linarith [hq1]
    have h4 : δ ≤ c₁ / (8 * Real.log ((q:ℝ) * (T + 2))) := min_le_left _ _
    calc δ ≤ c₁ / (8 * Real.log ((q:ℝ) * (T + 2))) := h4
      _ ≤ c₁ / (8 * Real.log (2 * (q:ℝ))) := by
          rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 8 * Real.log ((q:ℝ) * (T + 2)))
            (by positivity : (0:ℝ) < 8 * Real.log (2 * (q:ℝ)))]
          nlinarith [h2]
      _ ≤ cReal / Real.log (2 * (q:ℝ)) := by
          rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 8 * Real.log (2 * (q:ℝ))) h3]
          nlinarith [hc₁real, h3]
  have hδzero : δ ≤ cZero / (q:ℝ) ^ K := by
    have h4 : δ ≤ cZero / (4 * (q:ℝ) ^ K) := min_le_right _ _
    have h5 : 0 < (q:ℝ) ^ K := by positivity
    have h6 : cZero / (4 * (q:ℝ) ^ K) ≤ cZero / (q:ℝ) ^ K := by
      rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 4 * (q:ℝ) ^ K) h5]
      nlinarith [hqK, hcZero, h5]
    linarith
  have hδL : c₂ * Real.sqrt L ≤ δ * L := by
    have hlog2 : Real.log ((q:ℝ) * (T + 2)) ≤ 2 * Real.sqrt L := by
      have h3 : Cexp * Real.log L + 3 ≤ Real.sqrt L := by
        have h5 : m₀ * Real.log L + m₀ ≤ Real.sqrt L := hsl
        have h6 : Cexp * Real.log L ≤ m₀ * Real.log L :=
          mul_le_mul_of_nonneg_right hm₀Cexp (Real.log_nonneg (by linarith : (1:ℝ) ≤ L))
        linarith [h5, h6, hm₀3]
      have h4 : Real.log ((q:ℝ) * (T + 2)) = Real.log (q:ℝ) + Real.log (T + 2) :=
        Real.log_mul (ne_of_gt hqpos) (by linarith)
      rw [h4]
      linarith [hlogq, h3, hlogT]
    have ha : c₁ / 16 * Real.sqrt L ≤ c₁ / (8 * Real.log ((q:ℝ) * (T + 2))) * L := by
      have hsq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hLnonneg
      have h1 : Real.sqrt L * Real.log ((q:ℝ) * (T + 2)) ≤ 2 * L := by
        calc Real.sqrt L * Real.log ((q:ℝ) * (T + 2))
            ≤ Real.sqrt L * (2 * Real.sqrt L) :=
              mul_le_mul_of_nonneg_left hlog2 (Real.sqrt_nonneg L)
          _ = 2 * L := by
              rw [show Real.sqrt L * (2 * Real.sqrt L) = 2 * (Real.sqrt L * Real.sqrt L)
                by ring, hsq]
      rw [show c₁ / 16 * Real.sqrt L = c₁ * Real.sqrt L / 16 by ring,
        show c₁ / (8 * Real.log ((q:ℝ) * (T + 2))) * L
          = c₁ * L / (8 * Real.log ((q:ℝ) * (T + 2))) by ring]
      rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 16)
        (by positivity : (0:ℝ) < 8 * Real.log ((q:ℝ) * (T + 2)))]
      nlinarith [h1, hc₁pos]
    have hb : cZero / 4 * Real.sqrt L ≤ cZero / (4 * (q:ℝ) ^ K) * L := by
      have hqKle : (q:ℝ) ^ K ≤ L ^ (Cexp * K) := by
        calc (q:ℝ) ^ K ≤ (L ^ Cexp) ^ K := Real.rpow_le_rpow (by positivity) hqR hK.le
          _ = L ^ (Cexp * K) := (Real.rpow_mul hLnonneg Cexp K).symm
      have hpow : L ^ (Cexp * K) ≤ Real.sqrt L := by
        rw [Real.sqrt_eq_rpow]
        exact Real.rpow_le_rpow_of_exponent_le hL1 hCexpK
      have h6 : Real.sqrt L * ((q:ℝ) ^ K) ≤ L := by
        calc Real.sqrt L * (q:ℝ) ^ K ≤ Real.sqrt L * L ^ (Cexp * K) :=
              mul_le_mul_of_nonneg_left hqKle (Real.sqrt_nonneg L)
          _ ≤ Real.sqrt L * Real.sqrt L := mul_le_mul_of_nonneg_left hpow (Real.sqrt_nonneg L)
          _ = L := Real.mul_self_sqrt hLnonneg
      rw [show cZero / 4 * Real.sqrt L = cZero * Real.sqrt L / 4 by ring,
        show cZero / (4 * (q:ℝ) ^ K) * L = cZero * L / (4 * (q:ℝ) ^ K) by ring]
      rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 4)
        (by positivity : (0:ℝ) < 4 * (q:ℝ) ^ K)]
      nlinarith [h6, hcZero]
    have hmul : ∀ a b : ℝ, min a b * L = min (a * L) (b * L) := by
      intro a b
      rcases le_total a b with h | h
      · rw [min_eq_left h, min_eq_left (mul_le_mul_of_nonneg_right h hLnonneg)]
      · rw [min_eq_right h, min_eq_right (mul_le_mul_of_nonneg_right h hLnonneg)]
    have hmulmin : min (c₁ / (8 * Real.log ((q:ℝ) * (T + 2))))
          (cZero / (4 * (q:ℝ) ^ K)) * L
        = min (c₁ / (8 * Real.log ((q:ℝ) * (T + 2))) * L)
            (cZero / (4 * (q:ℝ) ^ K) * L) := by
      rw [hmul]
    have hδeq : δ * L = min (c₁ / (8 * Real.log ((q:ℝ) * (T + 2))))
        (cZero / (4 * (q:ℝ) ^ K)) * L := rfl
    rw [hδeq, hmulmin]
    exact le_min
      (le_trans (mul_le_mul_of_nonneg_right hc₂le1 (Real.sqrt_nonneg L)) ha)
      (le_trans (mul_le_mul_of_nonneg_right hc₂le2 (Real.sqrt_nonneg L)) hb)
  have hperre : chiPerronRe x = 1 + 1 / L := by
    rw [chiPerronRe, show Real.log x = L from rfl]
  have hrect : ∀ s : ℂ, 1 - δ ≤ s.re → s.re ≤ chiPerronRe x → |s.im| ≤ T →
      s ≠ 0 ∧ DirichletCharacter.LFunction χ s ≠ 0 := by
    intro s hs1 hs2 hs3
    have hsre_pos : 0 < s.re := by linarith [hs1, hδhalf]
    constructor
    · intro h0
      have h00 : s.re = 0 := by rw [h0]; simp
      linarith
    · by_cases him : s.im = 0
      · have hs_eq : s = ((s.re : ℝ) : ℂ) := by
          apply Complex.ext
          · simp
          · simpa using him
        rw [hs_eq]
        by_cases h1 : (1:ℝ) ≤ s.re
        · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) (by simpa using h1)
        · push_neg at h1
          intro hzero
          by_cases hsq : χ * χ = 1
          · have hz := hZero χ hχprim hχ1 hsq s.re (by linarith [hs1, hδhalf]) h1 hzero
            have h4 : 1 - s.re ≤ δ := by linarith
            have h5 : 0 < (q:ℝ) ^ K := by positivity
            have h6 : δ ≤ cZero / (4 * (q:ℝ) ^ K) := min_le_right _ _
            have h7 : cZero / (4 * (q:ℝ) ^ K) < cZero / (q:ℝ) ^ K := by
              rw [div_lt_div_iff₀ (by positivity : (0:ℝ) < 4 * (q:ℝ) ^ K) h5]
              nlinarith [hqK, hcZero, h5]
            linarith [hz, h4, h6, h7]
          · have h8 : δ ≤ cReal / Real.log (2 * (q:ℝ)) := hδreal
            have h9 : 1 - cReal / Real.log (2 * (q:ℝ)) ≤ s.re := by linarith [h8, hs1]
            exact hReal χ hχprim hχ1 hsq s.re h9 hzero
      · have h7 : δ ≤ cOff / Real.log ((q:ℝ) * (|s.im| + 2)) := hδoff s.im hs3
        have hz := hOff χ hχprim hχ1 s.re s.im him (by linarith [h7, hs1])
        rwa [Complex.re_add_im] at hz
  let rad : ℝ := min (1/2) (min (c₁ / (2 * (Real.log ((q:ℝ) * (T + 2)) + 1)))
    (cZero / (2 * (q:ℝ) ^ K)))
  have hradpos : 0 < rad := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hradhalf : rad ≤ 1/2 := min_le_left _ _
  have hrad1 : rad ≤ 1 := by linarith
  have hrad_le_c₁ : rad ≤ c₁ / (2 * (Real.log ((q:ℝ) * (T + 2)) + 1)) :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hrad_le_cZero : rad ≤ cZero / (2 * (q:ℝ) ^ K) :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  have hqT1 : (1:ℝ) ≤ Real.log ((q:ℝ) * (T + 2)) := by
    have hq2R : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq2
    have h1 : (8:ℝ) ≤ (q:ℝ) * (T + 2) := by nlinarith [hq2R, hT2]
    have h2 : 1 ≤ Real.log 8 := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
    exact le_trans h2 (Real.log_le_log (by norm_num) h1)
  have hqKle_sqrt : (q:ℝ) ^ K ≤ Real.sqrt L := by
    calc (q:ℝ) ^ K ≤ L ^ (Cexp * K) := by
          calc (q:ℝ) ^ K ≤ (L ^ Cexp) ^ K := Real.rpow_le_rpow (by positivity) hqR hK.le
            _ = L ^ (Cexp * K) := (Real.rpow_mul hLnonneg Cexp K).symm
      _ ≤ Real.sqrt L := by
          rw [Real.sqrt_eq_rpow]
          exact Real.rpow_le_rpow_of_exponent_le hL1 hCexpK
  have hsqrtself : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hLnonneg
  have hsqrtle : Real.sqrt L ≤ L := by
    have h2a : 1 ≤ Real.sqrt L := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt hL1
    calc Real.sqrt L = Real.sqrt L * 1 := by ring
      _ ≤ Real.sqrt L * Real.sqrt L := mul_le_mul_of_nonneg_left h2a (Real.sqrt_nonneg L)
      _ = L := hsqrtself
  have hloginv : 1 + 1 / rad ≤ 3 + 2 * (Real.log ((q:ℝ) * (T + 2)) + 1) / c₁
      + 2 * (q:ℝ) ^ K / cZero := by
    have hb : 0 < c₁ / (2 * (Real.log ((q:ℝ) * (T + 2)) + 1)) := by positivity
    have hc : 0 < cZero / (2 * (q:ℝ) ^ K) := by positivity
    have hr : rad = 1/2 ∨ rad = c₁ / (2 * (Real.log ((q:ℝ) * (T + 2)) + 1))
        ∨ rad = cZero / (2 * (q:ℝ) ^ K) := by
      rw [show rad = min (1/2) (min (c₁ / (2 * (Real.log ((q:ℝ) * (T + 2)) + 1)))
        (cZero / (2 * (q:ℝ) ^ K))) from rfl]
      by_cases h1 : (1/2 : ℝ) ≤ min (c₁ / (2 * (Real.log ((q:ℝ) * (T + 2)) + 1)))
          (cZero / (2 * (q:ℝ) ^ K))
      · rw [min_eq_left h1]; exact Or.inl rfl
      · rw [min_eq_right (le_of_lt (not_le.mp h1))]
        by_cases h2 : c₁ / (2 * (Real.log ((q:ℝ) * (T + 2)) + 1)) ≤ cZero / (2 * (q:ℝ) ^ K)
        · rw [min_eq_left h2]; exact Or.inr (Or.inl rfl)
        · rw [min_eq_right (le_of_lt (not_le.mp h2))]; exact Or.inr (Or.inr rfl)
    rcases hr with h | h | h
    · rw [h]
      have h5 : 0 ≤ 2 * (Real.log ((q:ℝ) * (T + 2)) + 1) / c₁ := by positivity
      have h6 : 0 ≤ 2 * (q:ℝ) ^ K / cZero := by positivity
      have h7 : (1:ℝ)/(1/2) = 2 := by norm_num
      rw [h7]
      linarith
    · rw [h]
      have h4 : 1 / (c₁ / (2 * (Real.log ((q:ℝ) * (T + 2)) + 1)))
          = 2 * (Real.log ((q:ℝ) * (T + 2)) + 1) / c₁ := by field_simp
      rw [h4]
      have h5 : 0 ≤ 2 * (q:ℝ) ^ K / cZero := by positivity
      linarith
    · rw [h]
      have h4 : 1 / (cZero / (2 * (q:ℝ) ^ K)) = 2 * (q:ℝ) ^ K / cZero := by field_simp
      rw [h4]
      have h5 : 0 ≤ 2 * (Real.log ((q:ℝ) * (T + 2)) + 1) / c₁ := by positivity
      linarith
  have hdelta_le_off : δ ≤ cOff / (8 * Real.log ((q:ℝ) * (T + 2))) := by
    have h4 : δ ≤ c₁ / (8 * Real.log ((q:ℝ) * (T + 2))) := min_le_left _ _
    have h5 : c₁ / (8 * Real.log ((q:ℝ) * (T + 2))) ≤ cOff / (8 * Real.log ((q:ℝ) * (T + 2))) :=
      div_le_div_of_nonneg_right hc₁off (by positivity)
    linarith
  have hlogb : ∀ σ t : ℝ, 1 - δ ≤ σ → σ ≤ chiPerronRe x → |t| ≤ T →
      ‖logDeriv (DirichletCharacter.LFunction χ) ((σ:ℂ) + (t:ℂ) * Complex.I)‖ ≤ CLb * L := by
    intro σ t h1 h2 h3
    have hσ12 : 1 / 2 ≤ σ := by linarith [h1, hδhalf]
    have hσ54 : σ ≤ 5 / 4 := by
      rw [hperre] at h2
      have hq : 1 / L ≤ 1 / 4 := by
        rw [div_le_div_iff₀ hLpos (by norm_num : (0:ℝ) < 4)]
        linarith
      linarith
    have hlogt_le : Real.log ((q:ℝ) * (|t| + 2)) + 1 ≤ 3 * Real.sqrt L := by
      have h4 : Real.log ((q:ℝ) * (|t| + 2)) ≤ Real.log ((q:ℝ) * (T + 2)) :=
        Real.log_le_log (mul_pos hqpos (by linarith [abs_nonneg t])) (by
          have := abs_le.mp h3; nlinarith [hqpos, this.1, this.2])
      linarith [h4, hlogq_bound]
    have hdist' : ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 →
        rad ≤ ‖((σ:ℂ) + (t:ℂ) * Complex.I) - ρ‖ := by
      intro ρ hρ
      have hre_le : σ - ρ.re ≤ ‖((σ:ℂ) + (t:ℂ) * Complex.I) - ρ‖ := by
        have h := Complex.re_le_norm (((σ:ℂ) + (t:ℂ) * Complex.I) - ρ)
        simp at h
        linarith
      by_cases hre0 : ρ.re ≤ 0
      · have h5 : (1:ℝ)/2 ≤ σ - ρ.re := by linarith
        linarith [hradhalf]
      · push Not at hre0
        by_cases him : ρ.im = 0
        · have hρ' : ρ = ((ρ.re : ℝ) : ℂ) := by
            apply Complex.ext <;> simp [him]
          have hρzero : DirichletCharacter.LFunction χ ((ρ.re : ℝ) : ℂ) = 0 := by
            rw [← hρ']; exact hρ
          have hρlt1 : ρ.re < 1 := by
            by_contra hc
            push Not at hc
            exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1)
              (by simpa using hc)) hρzero
          by_cases hsq : χ * χ = 1
          · have hz := hZero χ hχprim hχ1 hsq ρ.re hre0 hρlt1 hρzero
            have h5 : cZero / (2 * (q:ℝ) ^ K) ≤ σ - ρ.re := by
              have h6 : δ ≤ cZero / (4 * (q:ℝ) ^ K) := min_le_right _ _
              have h7 : 0 < (q:ℝ) ^ K := by positivity
              have h8 : cZero / (2 * (q:ℝ) ^ K) + cZero / (4 * (q:ℝ) ^ K)
                  ≤ cZero / (q:ℝ) ^ K := by
                have h9 : cZero / (2 * (q:ℝ) ^ K) + cZero / (4 * (q:ℝ) ^ K)
                    = 3 * cZero / (4 * (q:ℝ) ^ K) := by field_simp; ring
                rw [h9, div_le_div_iff₀ (by positivity) h7]
                nlinarith [hcZero]
              have h10 : cZero / (q:ℝ) ^ K - δ ≤ σ - ρ.re := by linarith
              linarith [h8, h6, h10]
            exact le_trans hrad_le_cZero (le_trans h5 hre_le)
          · have hz : ρ.re < 1 - cReal / Real.log (2 * (q:ℝ)) := by
              by_contra hc
              push Not at hc
              exact (hReal χ hχprim hχ1 hsq ρ.re (by linarith)) hρzero
            have hYpos : 0 < Real.log (2 * (q:ℝ)) := Real.log_pos (by linarith [hq1])
            have hXY : Real.log (2 * (q:ℝ)) ≤ Real.log ((q:ℝ) * (T + 2)) := by
              apply Real.log_le_log (by positivity)
              nlinarith [hqpos, hT2]
            have hδc : δ ≤ cReal / (8 * Real.log (2 * (q:ℝ))) := by
              calc δ ≤ c₁ / (8 * Real.log ((q:ℝ) * (T + 2))) := min_le_left _ _
                _ ≤ cReal / (8 * Real.log ((q:ℝ) * (T + 2))) :=
                    div_le_div_of_nonneg_right hc₁real (by positivity)
                _ ≤ cReal / (8 * Real.log (2 * (q:ℝ))) := by
                    apply div_le_div_of_nonneg_left hcReal.le (by positivity)
                    linarith [hXY]
            have h5 : c₁ / (2 * (Real.log ((q:ℝ) * (T + 2)) + 1)) ≤ σ - ρ.re := by
              have hstep1 : c₁ / (2 * (Real.log ((q:ℝ) * (T + 2)) + 1))
                  ≤ c₁ / (2 * Real.log (2 * (q:ℝ))) := by
                rw [div_le_div_iff₀ (by positivity) (by positivity)]
                nlinarith [hc₁pos, hXY, hYpos]
              have haux : c₁ / (2 * Real.log (2 * (q:ℝ)))
                  ≤ cReal / Real.log (2 * (q:ℝ)) - cReal / (8 * Real.log (2 * (q:ℝ))) := by
                have h1 : cReal / (2 * Real.log (2 * (q:ℝ)))
                    ≤ cReal / Real.log (2 * (q:ℝ)) - cReal / (8 * Real.log (2 * (q:ℝ))) := by
                  rw [show cReal / Real.log (2 * (q:ℝ)) - cReal / (8 * Real.log (2 * (q:ℝ)))
                      = 7 * cReal / (8 * Real.log (2 * (q:ℝ))) by field_simp; ring]
                  rw [div_le_div_iff₀ (by positivity) (by positivity)]
                  nlinarith [hcReal]
                have h2 : c₁ / (2 * Real.log (2 * (q:ℝ)))
                    ≤ cReal / (2 * Real.log (2 * (q:ℝ))) := by
                  rw [div_le_div_iff₀ (by positivity) (by positivity)]
                  nlinarith [hc₁real]
                linarith [h1, h2]
              have hstep2 : c₁ / (2 * Real.log (2 * (q:ℝ)))
                  ≤ cReal / Real.log (2 * (q:ℝ)) - δ := by linarith [haux, hδc]
              have hstep3 : cReal / Real.log (2 * (q:ℝ)) - δ ≤ σ - ρ.re := by
                have h9 : cReal / Real.log (2 * (q:ℝ)) - δ ≤ (1 - δ) - ρ.re := by linarith [hz]
                have h10 : (1 - δ) - ρ.re ≤ σ - ρ.re := by linarith
                linarith [h9, h10]
              linarith [hstep1, hstep2, hstep3]
            exact le_trans hrad_le_c₁ (le_trans h5 hre_le)
        · by_cases hfar : rad ≤ |t - ρ.im|
          · have h5 : |t - ρ.im| ≤ ‖((σ:ℂ) + (t:ℂ) * Complex.I) - ρ‖ := by
              have h := Complex.abs_im_le_norm (((σ:ℂ) + (t:ℂ) * Complex.I) - ρ)
              simpa using h
            linarith
          · have hlt : |t - ρ.im| < rad := not_le.mp hfar
            have him2 : |ρ.im| ≤ T + 1 := by
              have h5 : |ρ.im| ≤ |t| + |ρ.im - t| := by
                have h6 := abs_add_le t (ρ.im - t)
                have h7 : t + (ρ.im - t) = ρ.im := by ring
                rwa [h7] at h6
              have h7 : |ρ.im - t| ≤ rad := by
                rw [abs_sub_comm]; exact hlt.le
              have h8 := abs_le.mp h3
              linarith
            have hz : ρ.re < 1 - cOff / Real.log ((q:ℝ) * (|ρ.im| + 2)) := by
              by_contra hc
              push Not at hc
              exact (hOff χ hχprim hχ1 ρ.re ρ.im him (by linarith)
                (by rw [show ((ρ.re : ℂ) + (ρ.im : ℂ) * Complex.I) = ρ from Complex.re_add_im ρ]
                    exact hρ))
            have hLpos2 : 0 < Real.log ((q:ℝ) * (|ρ.im| + 2)) :=
              Real.log_pos (by nlinarith [hq1, abs_nonneg ρ.im])
            have hLle : Real.log ((q:ℝ) * (|ρ.im| + 2))
                ≤ Real.log ((q:ℝ) * (T + 2)) + 1 := by
              have h8 : (q:ℝ) * (|ρ.im| + 2) ≤ Real.exp 1 * ((q:ℝ) * (T + 2)) := by
                have h9 : Real.exp 1 ≥ 2 := le_of_lt (by linarith [Real.exp_one_gt_two])
                have h8a : |ρ.im| + 2 ≤ T + 3 := by linarith [him2]
                have h8b : (T:ℝ) + 3 ≤ 2 * (T + 2) := by linarith [hT2]
                have h8c : (q:ℝ) * (|ρ.im| + 2) ≤ (q:ℝ) * (T + 3) :=
                  mul_le_mul_of_nonneg_left h8a hqpos.le
                have h8d : (q:ℝ) * (T + 3) ≤ 2 * ((q:ℝ) * (T + 2)) := by nlinarith [hqpos, h8b]
                have h8e : 2 * ((q:ℝ) * (T + 2)) ≤ Real.exp 1 * ((q:ℝ) * (T + 2)) :=
                  mul_le_mul_of_nonneg_right h9 (by positivity)
                linarith [h8c, h8d, h8e]
              have h10 := Real.log_le_log (by positivity) h8
              rw [Real.log_mul (by positivity : (Real.exp 1) ≠ 0)
                (by positivity : ((q:ℝ) * (T + 2)) ≠ 0), Real.log_exp] at h10
              linarith
            have hBig : cOff / (Real.log ((q:ℝ) * (T + 2)) + 1) - δ ≤ σ - ρ.re := by
              have h9 : cOff / (Real.log ((q:ℝ) * (T + 2)) + 1)
                  ≤ cOff / Real.log ((q:ℝ) * (|ρ.im| + 2)) := by
                rw [div_le_div_iff₀ (by positivity) hLpos2]
                nlinarith [hcOff, hLle]
              have h10 : cOff / Real.log ((q:ℝ) * (|ρ.im| + 2)) - δ ≤ (1 - δ) - ρ.re := by
                linarith [hz]
              linarith
            have hKey : c₁ / (2 * (Real.log ((q:ℝ) * (T + 2)) + 1))
                + c₁ / (8 * Real.log ((q:ℝ) * (T + 2)))
                ≤ cOff / (Real.log ((q:ℝ) * (T + 2)) + 1) := by
              set X : ℝ := Real.log ((q:ℝ) * (T + 2)) with hXdef
              have hX1 : 1 ≤ X := by rw [hXdef]; exact hqT1
              have hXpos : 0 < X := by linarith
              have h1 : c₁ / (2 * (X + 1)) + c₁ / (8 * X)
                  = c₁ * (5 * X + 1) / (8 * X * (X + 1)) := by
                field_simp <;> ring
              have h2 : cOff / (X + 1) = cOff * (8 * X) / (8 * X * (X + 1)) := by
                field_simp <;> ring
              rw [h1, h2, div_le_div_iff₀ (by nlinarith [hXpos]) (by nlinarith [hXpos])]
              have hA : c₁ * (5 * X + 1) ≤ cOff * (5 * X + 1) :=
                mul_le_mul_of_nonneg_right hc₁off (by linarith)
              have hB : cOff * (5 * X + 1) ≤ cOff * (8 * X) :=
                mul_le_mul_of_nonneg_left (by linarith) hcOff.le
              have hC : c₁ * (5 * X + 1) ≤ cOff * (8 * X) := le_trans hA hB
              exact mul_le_mul_of_nonneg_right hC (by nlinarith [hXpos])
            have hδX : δ ≤ c₁ / (8 * Real.log ((q:ℝ) * (T + 2))) := min_le_left _ _
            have h5 : c₁ / (2 * (Real.log ((q:ℝ) * (T + 2)) + 1)) ≤ σ - ρ.re := by
              linarith [hBig, hKey, hδX]
            exact le_trans hrad_le_c₁ (le_trans h5 hre_le)
    have hb := hLog χ hχprim hχ1 σ t rad hσ12 hσ54 hradpos hrad1 hdist'
    have hfin : (1 + 1/rad) * (Real.log ((q:ℝ) * (|t| + 2)) + 1)
        ≤ (9 + 18 / c₁ + 6 / cZero) * L := by
      have hlognn : 0 ≤ Real.log ((q:ℝ) * (|t| + 2)) + 1 := by
        have h2 : 0 ≤ Real.log ((q:ℝ) * (|t| + 2)) :=
          Real.log_nonneg (by nlinarith [hq1, abs_nonneg t])
        linarith
      have hBnn : 0 ≤ 3 + 2 * (Real.log ((q:ℝ) * (T + 2)) + 1) / c₁
          + 2 * (q:ℝ) ^ K / cZero := by
        have h2 : 0 < Real.log ((q:ℝ) * (T + 2)) := by linarith [hqT1]
        positivity
      have h5 : (1 + 1/rad) * (Real.log ((q:ℝ) * (|t| + 2)) + 1)
          ≤ (3 + 2 * (Real.log ((q:ℝ) * (T + 2)) + 1) / c₁ + 2 * (q:ℝ) ^ K / cZero)
            * (3 * Real.sqrt L) :=
        mul_le_mul hloginv hlogt_le hlognn hBnn
      have h6 : (3 + 2 * (Real.log ((q:ℝ) * (T + 2)) + 1) / c₁ + 2 * (q:ℝ) ^ K / cZero)
            * (3 * Real.sqrt L)
          ≤ (9 + 18 / c₁ + 6 / cZero) * L := by
        have h7 : (Real.log ((q:ℝ) * (T + 2)) + 1) * Real.sqrt L ≤ 3 * L := by
          calc (Real.log ((q:ℝ) * (T + 2)) + 1) * Real.sqrt L
              ≤ (3 * Real.sqrt L) * Real.sqrt L :=
                mul_le_mul_of_nonneg_right hlogq_bound (Real.sqrt_nonneg L)
            _ = 3 * L := by rw [show (3 * Real.sqrt L) * Real.sqrt L
                = 3 * (Real.sqrt L * Real.sqrt L) by ring, hsqrtself]
        have h8 : (q:ℝ) ^ K * Real.sqrt L ≤ L := by
          calc (q:ℝ) ^ K * Real.sqrt L ≤ Real.sqrt L * Real.sqrt L :=
                mul_le_mul_of_nonneg_right hqKle_sqrt (Real.sqrt_nonneg L)
            _ = L := hsqrtself
        have h9 : 0 < c₁ := hc₁pos
        have h10 : 0 < cZero := hcZero
        have h11 : Real.sqrt L ≤ L := hsqrtle
        rw [show (3 + 2 * (Real.log ((q:ℝ) * (T + 2)) + 1) / c₁ + 2 * (q:ℝ) ^ K / cZero)
              * (3 * Real.sqrt L)
            = 9 * Real.sqrt L + 6 * ((Real.log ((q:ℝ) * (T + 2)) + 1) * Real.sqrt L) / c₁
              + 6 * ((q:ℝ) ^ K * Real.sqrt L) / cZero by ring]
        rw [show (9 + 18 / c₁ + 6 / cZero) * L = 9 * L + 18 * L / c₁ + 6 * L / cZero by ring]
        have h12 : 9 * Real.sqrt L ≤ 9 * L := by linarith
        have h13 : 6 * ((Real.log ((q:ℝ) * (T + 2)) + 1) * Real.sqrt L) / c₁ ≤ 18 * L / c₁ := by
          apply div_le_div_of_nonneg_right _ h9.le
          linarith [h7]
        have h14 : 6 * ((q:ℝ) ^ K * Real.sqrt L) / cZero ≤ 6 * L / cZero := by
          apply div_le_div_of_nonneg_right _ h10.le
          linarith [h8]
        linarith [h12, h13, h14]
      linarith [h5, h6]
    calc ‖logDeriv (DirichletCharacter.LFunction χ) ((σ:ℂ) + (t:ℂ) * Complex.I)‖
        ≤ CL * (1 + 1/rad) * (Real.log ((q:ℝ) * (|t| + 2)) + 1) := hb
      _ = CL * ((1 + 1/rad) * (Real.log ((q:ℝ) * (|t| + 2)) + 1)) := by ring
      _ ≤ CL * ((9 + 18 / c₁ + 6 / cZero) * L) := mul_le_mul_of_nonneg_left hfin hCL.le
      _ = CLb * L := by
          rw [show CLb = CL * (9 + 18 / c₁ + 6 / cZero) from rfl]; ring

  have hTinv : T⁻¹ = Real.exp (-1 * Real.sqrt L) := by
    rw [show T = Real.exp (Real.sqrt L) from rfl, ← Real.exp_neg]
    congr 1
    ring
  have hxlog : Real.log (x:ℝ) = L := rfl
  have hxlpow : (x:ℝ) ^ chiPerronRe x = (x:ℝ) * Real.exp 1 := by
    rw [hperre, Real.rpow_def_of_pos (by linarith : (0:ℝ) < (x:ℝ)), hxlog]
    have h : L * (1 + 1 / L) = L + 1 := by field_simp
    rw [h, Real.exp_add, Real.exp_log (by linarith : (0:ℝ) < (x:ℝ))]
  have hxpowδ : (x:ℝ) ^ (1 - δ) = (x:ℝ) * Real.exp (-δ * L) := by
    rw [Real.rpow_def_of_pos (by linarith : (0:ℝ) < (x:ℝ)), hxlog]
    have h : L * (1 - δ) = L + (-δ * L) := by ring
    rw [h, Real.exp_add, Real.exp_log (by linarith : (0:ℝ) < (x:ℝ))]
  have hsqrtLle : Real.sqrt L ≤ L := by
    have h2a : 1 ≤ Real.sqrt L := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt hL1
    calc Real.sqrt L = Real.sqrt L * 1 := by ring
      _ ≤ Real.sqrt L * Real.sqrt L := mul_le_mul_of_nonneg_left h2a (Real.sqrt_nonneg L)
      _ = L := Real.mul_self_sqrt hLnonneg
  have hmain := (psiChi_le_engine_of_perron χ hχ1 hCtrP
      (fun y hy T' hT' => hPerron χ y hy T' hT'))
      hx3 hT2 hδpos hδhalf hrect
      (fun u hu => hlogb u T hu.1 hu.2 (by rw [abs_of_nonneg hTpos.le]))
      (fun u hu => hlogb u (-T) hu.1 hu.2
        (by rw [abs_neg, abs_of_nonneg hTpos.le]))
      (fun t ht => (hrect _ (by simp)
        (by rw [hperre]; simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
              Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero]
            linarith [hδpos, one_div_pos.mpr hLpos])
        (by simpa using abs_le.mpr ⟨ht.1, ht.2⟩)).2)
      (fun t ht => hlogb (1 - δ) t le_rfl (by rw [hperre]; linarith [hδpos, one_div_pos.mpr hLpos])
        (le_trans ht hT2))
      (fun t ht ht2 => hlogb (1 - δ) t le_rfl
        (by rw [hperre]; linarith [hδpos, one_div_pos.mpr hLpos]) ht2)
  have hterm1 : CtrP * ((x:ℝ) * L ^ 2 / T + L) ≤ (1/3) * ((x:ℝ) / L ^ A) := by
    have h1 : (x:ℝ) * L ^ 2 / T = (x:ℝ) * (L ^ 2 * Real.exp (-1 * Real.sqrt L)) := by
      rw [div_eq_mul_inv, hTinv]
      ring
    have h3 : CtrP * L ^ 2 * Real.exp (-1 * Real.sqrt L) ≤ 1 / (6 * L ^ A) := by
      have h4 : 6 * (CtrP * L ^ 2 * Real.exp (-1 * Real.sqrt L)) ≤ 1 / L ^ A := by
        rw [show 6 * (CtrP * L ^ 2 * Real.exp (-1 * Real.sqrt L))
          = 6 * CtrP * L ^ 2 * Real.exp (-1 * Real.sqrt L) by ring]
        exact hdec1
      rw [show (1:ℝ) / (6 * L ^ A) = (1 / L ^ A) / 6 by ring]
      rw [le_div_iff₀ (by norm_num : (0:ℝ) < 6)]
      linarith [h4]
    have h5 : L ^ A ≤ L ^ N₀ := by
      have h6 : L ^ A ≤ L ^ ((N₀ : ℝ)) := Real.rpow_le_rpow_of_exponent_le hL1 hN₀
      rwa [Real.rpow_natCast] at h6
    have h7 : CtrP * L ≤ (x:ℝ) / (6 * L ^ A) := by
      have h8 : 6 * (CtrP * L * L ^ N₀) ≤ (x:ℝ) := by
        rw [show 6 * (CtrP * L * L ^ N₀) = 6 * CtrP * L ^ (N₀ + 1) by rw [pow_succ']; ring]
        exact hdec2
      have h9 : CtrP * L * L ^ A ≤ CtrP * L * L ^ N₀ :=
        mul_le_mul_of_nonneg_left h5 (by positivity)
      rw [le_div_iff₀ (by positivity : (0:ℝ) < 6 * L ^ A)]
      nlinarith [h8, h9]
    have h10 : (x:ℝ) * (1 / (6 * L ^ A)) + (x:ℝ) / (6 * L ^ A) ≤ (1/3) * ((x:ℝ) / L ^ A) := by
      have h11 : (x:ℝ) * (1 / (6 * L ^ A)) = (x:ℝ) / (6 * L ^ A) := by ring
      rw [h11]
      have h12 : (1/3 : ℝ) * ((x:ℝ) / L ^ A) = 2 * ((x:ℝ) / (6 * L ^ A)) := by ring
      rw [h12]
      linarith
    calc CtrP * ((x:ℝ) * L ^ 2 / T + L)
        = (x:ℝ) * (CtrP * L ^ 2 * Real.exp (-1 * Real.sqrt L)) + CtrP * L := by
          rw [h1]; ring
      _ ≤ (x:ℝ) * (1 / (6 * L ^ A)) + (x:ℝ) / (6 * L ^ A) := by
          have ha : (x:ℝ) * (CtrP * L ^ 2 * Real.exp (-1 * Real.sqrt L))
              ≤ (x:ℝ) * (1 / (6 * L ^ A)) :=
            mul_le_mul_of_nonneg_left h3 (by linarith : (0:ℝ) ≤ (x:ℝ))
          linarith [ha, h7]
      _ ≤ (1/3) * ((x:ℝ) / L ^ A) := h10
  have hterm2 : (1 / (2 * Real.pi)) * (2 * (CLb * L * (x:ℝ) ^ chiPerronRe x
        * chiPerronRe x / T)) ≤ (1/3) * ((x:ℝ) / L ^ A) := by
    have h1 : chiPerronRe x ≤ 2 := by
      rw [hperre]
      have h1' : 1 / L ≤ 1 := by rw [div_le_one hLpos]; exact hL1
      linarith
    have h2 : (1 / (2 * Real.pi)) * (2 * (CLb * L * (x:ℝ) ^ chiPerronRe x
          * chiPerronRe x / T))
        ≤ (x:ℝ) * (2 * Real.exp 1 * CLb / Real.pi * L * Real.exp (-1 * Real.sqrt L)) := by
      have hgoal : (1 / (2 * Real.pi)) * (2 * (CLb * L * (x:ℝ) ^ chiPerronRe x
            * chiPerronRe x / T))
          = (x:ℝ) * (2 * Real.exp 1 * CLb / Real.pi * L * Real.exp (-1 * Real.sqrt L))
            * (chiPerronRe x / 2) := by
        have h1 : CLb * L * (x:ℝ) ^ chiPerronRe x * chiPerronRe x / T
            = CLb * L * ((x:ℝ) * Real.exp 1) * chiPerronRe x * Real.exp (-1 * Real.sqrt L) := by
          rw [hxlpow, div_eq_mul_inv (CLb * L * ((x:ℝ) * Real.exp 1) * chiPerronRe x) T, hTinv]
        rw [h1]
        ring
      rw [hgoal]
      have h2' : chiPerronRe x / 2 ≤ 1 := by linarith
      have hpos : 0 ≤ (x:ℝ) * (2 * Real.exp 1 * CLb / Real.pi * L
          * Real.exp (-1 * Real.sqrt L)) := by
        have h3 : 0 < Real.exp 1 := Real.exp_pos 1
        have h4 : 0 < CLb := hCLb
        positivity
      nlinarith [h2', hpos]
    have h3 : (x:ℝ) * (2 * Real.exp 1 * CLb / Real.pi * L * Real.exp (-1 * Real.sqrt L))
        ≤ (1/3) * ((x:ℝ) / L ^ A) := by
      have h4 : 6 * CLb * Real.exp 1 / Real.pi * L ^ 1 * Real.exp (-1 * Real.sqrt L)
          ≤ 1 / L ^ A := hdec3
      rw [pow_one] at h4
      have h6 : 2 * Real.exp 1 * CLb / Real.pi * L * Real.exp (-1 * Real.sqrt L)
          ≤ (1/3) / L ^ A := by
        have h7 : 3 * (2 * Real.exp 1 * CLb / Real.pi * L * Real.exp (-1 * Real.sqrt L))
            = 6 * CLb * Real.exp 1 / Real.pi * L * Real.exp (-1 * Real.sqrt L) := by ring
        have h8 : 3 * (2 * Real.exp 1 * CLb / Real.pi * L * Real.exp (-1 * Real.sqrt L))
            ≤ 1 / L ^ A := by rw [h7]; exact h4
        have h9 : ((1:ℝ)/3) / L ^ A = (1/3) * (1 / L ^ A) := by ring
        rw [h9]
        have h10 : 0 < L ^ A := Real.rpow_pos_of_pos hLpos A
        linarith
      rw [show (1/3) * ((x:ℝ) / L ^ A) = (x:ℝ) * ((1/3) / L ^ A) by ring]
      exact mul_le_mul_of_nonneg_left h6 (by linarith)
    linarith [h2, h3]
  have hterm3 : (1 / (2 * Real.pi)) * ((x:ℝ) ^ (1 - δ) *
        (8 * (CLb * L) + 2 * (CLb * L) * (Real.log (T + 2) + 1)))
      ≤ (1/3) * ((x:ℝ) / L ^ A) := by
    have h1 : Real.log (T + 2) + 1 ≤ 3 * Real.sqrt L := by
      have h1a : Real.log (T + 2) ≤ Real.log ((q:ℝ) * (T + 2)) :=
        Real.log_le_log (by linarith) (by nlinarith [hq1, hT2])
      linarith [h1a, hlogq_bound]
    have h2 : 8 * (CLb * L) + 2 * (CLb * L) * (Real.log (T + 2) + 1)
        ≤ 14 * (CLb * L ^ 2) := by
      have hlog : Real.log (T + 2) + 1 ≤ 3 * L := by
        have h3 : Real.sqrt L ≤ L := hsqrtLle
        linarith [h1, h3]
      have h6 : 2 * (CLb * L) * (Real.log (T + 2) + 1) ≤ 6 * (CLb * L ^ 2) := by
        have h6a : 2 * (CLb * L) * (Real.log (T + 2) + 1) ≤ 2 * (CLb * L) * (3 * L) :=
          mul_le_mul_of_nonneg_left hlog (by positivity)
        have h6b : 2 * (CLb * L) * (3 * L) = 6 * (CLb * L ^ 2) := by ring
        linarith [h6a, h6b.le]
      have h7 : 8 * (CLb * L) ≤ 8 * (CLb * L ^ 2) := by
        have h7a : L ≤ L ^ 2 := by nlinarith [hL1]
        have h7b : CLb * L ≤ CLb * L ^ 2 := mul_le_mul_of_nonneg_left h7a hCLb.le
        linarith [h7b]
      linarith [h6, h7]
    have h4 : (x:ℝ) ^ (1 - δ) * (14 * (CLb * L ^ 2))
        ≤ (x:ℝ) * (14 * (CLb * L ^ 2) * Real.exp (-c₂ * Real.sqrt L)) := by
      rw [hxpowδ]
      have h5 : Real.exp (-δ * L) ≤ Real.exp (-c₂ * Real.sqrt L) :=
        Real.exp_le_exp.mpr (by linarith [hδL])
      have h6 : 0 ≤ 14 * (CLb * L ^ 2) := by positivity
      calc (x:ℝ) * Real.exp (-δ * L) * (14 * (CLb * L ^ 2))
          ≤ (x:ℝ) * Real.exp (-c₂ * Real.sqrt L) * (14 * (CLb * L ^ 2)) := by
            apply mul_le_mul_of_nonneg_right _ h6
            exact mul_le_mul_of_nonneg_left h5 (by linarith)
        _ = (x:ℝ) * (14 * (CLb * L ^ 2) * Real.exp (-c₂ * Real.sqrt L)) := by ring
    have h5 : (1 / (2 * Real.pi)) * ((x:ℝ) * (14 * (CLb * L ^ 2) * Real.exp (-c₂ * Real.sqrt L)))
        ≤ (1/3) * ((x:ℝ) / L ^ A) := by
      have h6 : 21 * CLb / Real.pi * L ^ 2 * Real.exp (-c₂ * Real.sqrt L) ≤ 1 / L ^ A := hdec4
      have h7 : (1 / (2 * Real.pi)) * (14 * (CLb * L ^ 2) * Real.exp (-c₂ * Real.sqrt L))
          ≤ (1/3) / L ^ A := by
        have h7a : 3 * ((1 / (2 * Real.pi)) * (14 * (CLb * L ^ 2) * Real.exp (-c₂ * Real.sqrt L)))
            ≤ 1 / L ^ A := by
          have h8 : 3 * ((1 / (2 * Real.pi)) * (14 * (CLb * L ^ 2) * Real.exp (-c₂ * Real.sqrt L)))
              = 21 * CLb / Real.pi * L ^ 2 * Real.exp (-c₂ * Real.sqrt L) := by
            have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
            field_simp
            ring
          rw [h8]; exact h6
        have h7b : (1 / L ^ A) / 3 = (1/3) / L ^ A := by ring
        rw [← h7b]
        exact (le_div_iff₀ (by norm_num : (0:ℝ) < 3)).mpr (by rw [mul_comm]; exact h7a)
      rw [show (1 / (2 * Real.pi)) * ((x:ℝ) * (14 * (CLb * L ^ 2) * Real.exp (-c₂ * Real.sqrt L)))
          = (x:ℝ) * ((1 / (2 * Real.pi)) * (14 * (CLb * L ^ 2) * Real.exp (-c₂ * Real.sqrt L))) by ring]
      rw [show (1/3) * ((x:ℝ) / L ^ A) = (x:ℝ) * ((1/3) / L ^ A) by ring]
      exact mul_le_mul_of_nonneg_left h7 (by linarith [hx3])
    calc (1 / (2 * Real.pi)) * ((x:ℝ) ^ (1 - δ) *
          (8 * (CLb * L) + 2 * (CLb * L) * (Real.log (T + 2) + 1)))
        ≤ (1 / (2 * Real.pi)) * ((x:ℝ) ^ (1 - δ) * (14 * (CLb * L ^ 2))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ (1 / (2 * Real.pi)) * ((x:ℝ) * (14 * (CLb * L ^ 2) * Real.exp (-c₂ * Real.sqrt L))) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ ≤ (1/3) * ((x:ℝ) / L ^ A) := h5
  have hfin : ‖(∑ n ∈ Finset.Icc 1 ⌊(x:ℝ)⌋₊,
        χ ((n : ℕ) : ZMod q) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))‖ ≤
      (x:ℝ) / L ^ A := by
    linarith [hmain, hterm1, hterm2, hterm3]
  have hbridge : (∑ n ∈ Finset.range (x+1),
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q))
      = ∑ n ∈ Finset.Icc 1 ⌊(x:ℝ)⌋₊,
          χ ((n : ℕ) : ZMod q) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) := by
    rw [sum_range_eq_sum_Icc _ x (by simp), Nat.floor_natCast]
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [hbridge]
  exact hfin


/-- **The target from the two remaining uniform inputs** (`hPerron` for the truncated Perron
approximation and `hLog` for the logarithmic-derivative bound in the zero-free region), using
the published commons lemmas for the two zero-free regions and for the uniform real-zero
bound. -/
theorem siegel_walfisz_chi_of_two_inputs
    (hPerron : ∃ C : ℝ, 0 < C ∧ ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
        (x : ℝ), 3 ≤ x → ∀ T : ℝ, 2 ≤ T →
        ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
              χ ((n : ℕ) : ZMod N) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
            - chiPerron χ x T‖ ≤ C * (x * (Real.log x) ^ 2 / T + Real.log x))
    (hLog : ∃ C : ℝ, 0 < C ∧
      ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N),
      χ.IsPrimitive → χ ≠ 1 → ∀ σ t r : ℝ, 1 / 2 ≤ σ → σ ≤ 5 / 4 → 0 < r → r ≤ 1 →
        (∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 →
          r ≤ ‖((σ : ℂ) + (t : ℂ) * Complex.I) - ρ‖) →
        ‖logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          C * (1 + 1 / r) * (Real.log ((N : ℝ) * (|t| + 2)) + 1)) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧
    ∀ᶠ x : ℕ in Filter.atTop,
      ∀ {q : ℕ} [NeZero q], q ≤ ⌊(Real.log (x:ℝ)) ^ C⌋₊ →
      ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → χ ≠ 1 →
        ‖∑ n ∈ Finset.range (x+1),
            ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q)‖ ≤
          (x:ℝ) / (Real.log (x:ℝ))^A := by
  obtain ⟨c₁, hc₁, hOff⟩ := Commons.NumberTheory.DirichletCharacter.LFunction_zeroFree_offAxis_uniform
  obtain ⟨c₂, hc₂, hReal⟩ := Commons.NumberTheory.DirichletCharacter.LFunction_zeroFree_uniform_realAxis
  obtain ⟨c₃, hc₃, K, hK, hZero⟩ :=
    Commons.NumberTheory.DirichletCharacter.LFunction_realZero_bound_uniform
  refine siegel_walfisz_chi_of_uniform_inputs hPerron ⟨c₁, hc₁, hOff⟩ ?_
    ⟨c₃, hc₃, K, hK, hZero⟩ hLog
  refine ⟨c₂, hc₂, ?_⟩
  intro N _ χ hχp hχ hχ2 σ hσ
  exact hReal N χ hχp hχ hχ2 σ hσ

/-- `psiChiIntF` is the integrand of the Perron formula for `χ·Λ`. -/
lemma psiChiIntF_eq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (x : ℝ) {s : ℂ}
    (hs : 1 < s.re) :
    psiChiIntF χ x s =
      LSeries (fun n : ℕ => χ ((n : ℕ) : ZMod N) *
          ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) s * (x : ℂ) ^ s / s := by
  have h1 := Commons.NumberTheory.DirichletCharacter.LFunction_logDeriv_eq_neg_LSeries_vonMangoldt χ hs
  have hfun : (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ))
      = (fun n : ℕ => χ ((n : ℕ) : ZMod N) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) := by
    funext n; push_cast; ring
  rw [psiChiIntF, h1, hfun]
  ring

/-- **Uniform truncated-Perron bound** in the `chiPerron` normalisation, from the
published commons lemma. -/
theorem chiPerron_uniform_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (x : ℝ),
      3 ≤ x → ∀ T : ℝ, 2 ≤ T →
      ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
            χ ((n : ℕ) : ZMod N) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
          - chiPerron χ x T‖ ≤ C * (x * (Real.log x) ^ 2 / T + Real.log x) := by
  obtain ⟨C, hCpos, hC⟩ :=
    Commons.NumberTheory.DirichletCharacter.chebyshevPsiChi_truncatedPerron_uniform
  refine ⟨C, hCpos, ?_⟩
  intro N _ χ x hx T hT
  have hx1 : (1 : ℝ) < x := by linarith
  have hlogpos : 0 < Real.log x := Real.log_pos hx1
  have hper : (1 : ℝ) < chiPerronRe x := by
    dsimp [chiPerronRe]; linarith [one_div_pos.mpr hlogpos]
  have hcongr : (∫ t : ℝ in -T..T, psiChiIntF χ x ((chiPerronRe x : ℂ) + Complex.I * (t : ℂ)))
      = ∫ t : ℝ in -T..T,
          (LSeries (fun n : ℕ => χ ((n : ℕ) : ZMod N) *
              ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
            ((chiPerronRe x : ℂ) + Complex.I * (t : ℂ))) *
            ((x : ℂ) ^ ((chiPerronRe x : ℂ) + Complex.I * (t : ℂ))) /
            ((chiPerronRe x : ℂ) + Complex.I * (t : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro t _
    have hre : (((chiPerronRe x : ℂ) + Complex.I * (t : ℂ))).re = chiPerronRe x := by simp
    exact psiChiIntF_eq χ x (s := (chiPerronRe x : ℂ) + Complex.I * (t : ℂ))
      (by rw [hre]; exact hper)
  have hCx := hC χ x hx T hT
  rw [chiPerron, hcongr]
  simpa [chiPerronRe] using hCx

open Complex DirichletCharacter Metric Filter Set
open scoped Real BigOperators Topology
variable {N : ℕ} [NeZero N]

def phiK (x : ℝ) : ℝ := 2 / (x * max 1 (x - 2))

lemma phi_pos {x : ℝ} (hx : 0 < x) : 0 < phiK x := by
  unfold phiK
  have h : 0 < x * max 1 (x - 2) :=
    mul_pos hx (lt_of_lt_of_le one_pos (le_max_left _ _))
  exact div_pos (by norm_num) h

lemma phi_nonneg {x : ℝ} (hx : 0 < x) : 0 ≤ phiK x := le_of_lt (phi_pos hx)

lemma phi_antitoneOn : AntitoneOn phiK (Set.Ioi 0) := by
  intro x hx y hy hxy
  unfold phiK
  have hx0 : 0 < x := hx
  have hp1 : 0 < x * max 1 (x - 2) :=
    mul_pos hx0 (lt_of_lt_of_le one_pos (le_max_left _ _))
  have hle : x * max 1 (x - 2) ≤ y * max 1 (y - 2) :=
    mul_le_mul hxy (max_le_max (le_refl 1) (by linarith)) (by positivity) hy.le
  exact div_le_div_of_nonneg_left (by norm_num) hp1 hle

lemma phi_le_two_div {x : ℝ} (hx : 0 < x) : phiK x ≤ 2 / x := by
  unfold phiK
  have h : x ≤ x * max 1 (x - 2) := by
    have h1 : (1:ℝ) ≤ max 1 (x - 2) := le_max_left _ _
    nlinarith
  exact div_le_div_of_nonneg_left (by norm_num) hx h

lemma phi_le_quad {x : ℝ} (h3 : 3 ≤ x) : phiK x ≤ 6 / x ^ 2 := by
  unfold phiK
  have hx0 : 0 < x := by linarith
  have hm : max 1 (x - 2) = x - 2 := by
    apply max_eq_right; linarith
  rw [hm]
  have hpos : 0 < x * (x - 2) := by nlinarith
  have h3x : x / 3 ≤ x - 2 := by linarith
  have hprod : x * (x / 3) ≤ x * (x - 2) := mul_le_mul_of_nonneg_left h3x hx0.le
  have hsq : x * (x / 3) = x ^ 2 / 3 := by ring
  rw [hsq] at hprod
  rw [div_le_div_iff₀ hpos (by positivity : (0:ℝ) < x ^ 2)]
  nlinarith

lemma sum_Ico_sub_dyadic (g : ℕ → ℝ) : ∀ a b : ℕ, a ≤ b →
    ∑ j ∈ Finset.Ico a b, (g j - g (j+1)) = g a - g b := by
  intro a b hab
  induction b with
  | zero => simp at hab; subst hab; simp
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le hab with h | h
    · rw [h]; simp
    · have han : a ≤ n := by omega
      rw [Finset.sum_Ico_succ_top han, ih han]
      ring

/-- **Layer cake.** If `r ≤ d` and `2^(J+1)*r > d` then `phiK d` is bounded by the
`J`-truncated telescoping sum of `phiK` at the dyadic scale `2^j r`, plus the top term. -/
lemma layer_cake_phi {r d : ℝ} (hr : 0 < r) (hd : r ≤ d) {J : ℕ}
    (hJ : d < 2^(J+1) * r) :
    phiK d ≤ (∑ j ∈ Finset.range J, (phiK (2^j * r) - phiK (2^(j+1) * r)) *
        (if d < 2^(j+1) * r then (1:ℝ) else 0)) + phiK (2^J * r) := by
  have hpowpos : ∀ j : ℕ, 0 < (2:ℝ)^j * r := fun j => by positivity
  have hex : ∃ j : ℕ, d < (2:ℝ)^(j+1) * r := ⟨J, hJ⟩
  set j₀ := Nat.find hex with hj₀
  have hspec : d < (2:ℝ)^(j₀+1) * r := by rw [hj₀]; exact Nat.find_spec hex
  have hmin : ∀ j : ℕ, j < j₀ → ¬ (d < (2:ℝ)^(j+1) * r) := by
    intro j hj
    have hj' : j < Nat.find hex := hj
    exact Nat.find_min hex hj'
  have hle : (2:ℝ)^j₀ * r ≤ d := by
    rcases Nat.eq_zero_or_pos j₀ with h0 | h0
    · rw [h0]; simpa using hd
    · have hprev := hmin (j₀ - 1) (by omega)
      have hprev' : d ≥ (2:ℝ)^(j₀ - 1 + 1) * r := le_of_not_gt hprev
      have he : (2:ℝ)^(j₀ - 1 + 1) = (2:ℝ)^j₀ := by congr 1; omega
      rwa [he] at hprev'
  have hj₀J : j₀ ≤ J := by
    by_contra hcon
    have hcon' : J < j₀ := not_le.mp hcon
    have h1 : (2:ℝ)^(J+1) * r ≤ (2:ℝ)^j₀ * r :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) hr.le
    linarith
  have hind : ∀ j ∈ Finset.range J,
      (if d < (2:ℝ)^(j+1) * r then (1:ℝ) else 0) =
        (if j₀ ≤ j then (1:ℝ) else 0) := by
    intro j hj
    rw [Finset.mem_range] at hj
    by_cases h : d < (2:ℝ)^(j+1) * r
    · have hge : j₀ ≤ j := by
        by_contra hc
        exact absurd h (hmin j (not_le.mp hc))
      rw [if_pos h, if_pos hge]
    · have hlt : j < j₀ := by
        by_contra hc
        have h1 : (2:ℝ)^(j₀+1) * r ≤ (2:ℝ)^(j+1) * r :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) hr.le
        exact absurd (lt_of_lt_of_le hspec h1) h
      rw [if_neg h, if_neg (by omega)]
  have hsum_eq : (∑ j ∈ Finset.range J, (phiK (2^j * r) - phiK (2^(j+1) * r)) *
        (if d < 2^(j+1) * r then (1:ℝ) else 0)) =
      ∑ j ∈ (Finset.range J).filter (fun j => j₀ ≤ j),
        (phiK (2^j * r) - phiK (2^(j+1) * r)) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [hind j hj]
    by_cases h : j₀ ≤ j <;> simp [h]
  rw [hsum_eq]
  rcases Nat.eq_or_lt_of_le hj₀J with heq | hlt
  · rw [← heq]
    have hemp : (Finset.range j₀).filter (fun j => j₀ ≤ j) = ∅ := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false, not_and]
      omega
    rw [hemp, Finset.sum_empty, zero_add]
    exact phi_antitoneOn (hpowpos j₀) (show (0:ℝ) < d by linarith) hle
  · have hfilter : (Finset.range J).filter (fun j => j₀ ≤ j) = Finset.Ico j₀ J := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      omega
    rw [hfilter, sum_Ico_sub_dyadic (fun j => phiK ((2:ℝ)^j * r)) j₀ J hj₀J]
    have h1 : phiK d ≤ phiK ((2:ℝ)^j₀ * r) :=
      phi_antitoneOn (hpowpos j₀) (show (0:ℝ) < d by linarith) hle
    have h2 : 0 ≤ phiK ((2:ℝ)^J * r) := phi_nonneg (hpowpos J)
    linarith

lemma geom_sum_range_le_one {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (N : ℕ) :
    ∑ j ∈ Finset.range N, q^j ≤ 1/(1-q) := by
  have h0 : 0 < 1 - q := by linarith
  have hm := geom_sum_mul q N
  have h2 : (∑ j ∈ Finset.range N, q^j) * (1 - q) = 1 - q^N := by
    have h3 : (∑ j ∈ Finset.range N, q^j) * (q - 1) = q^N - 1 := hm
    linarith [h3]
  have h4 : 1 - q^N ≤ 1 := by
    have := pow_nonneg hq0 N; linarith
  rw [le_div_iff₀ h0]
  linarith [h2, h4]

lemma log_le_two_mul_sqrt {x : ℝ} (hx : 1 ≤ x) : Real.log x ≤ 2 * Real.sqrt x := by
  have hx0 : 0 < x := by linarith
  have hs1 : 1 ≤ Real.sqrt x := Real.one_le_sqrt.mpr hx
  have h1 : Real.log x = 2 * Real.log (Real.sqrt x) := by
    have := Real.log_sqrt hx0.le
    linarith
  rw [h1]
  have h2 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 :=
    Real.log_le_sub_one_of_pos (by linarith)
  linarith

/-- **Dyadic sum estimate.**  If `C j` is bounded by a linear (in the dyadic radius)
count bound, then the dyadic sum of `φ`-increments weighted by `C` is `≪ c L / r`. -/
theorem dyadic_sum_bound_phi {r L c : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hL : 1 ≤ L) (hc : 0 ≤ c)
    {C : ℕ → ℝ} (hC0 : ∀ j, 0 ≤ C j)
    (hC1 : ∀ j, (2:ℝ)^(j+1) * r ≤ 1 → C j ≤ 4 * c * L)
    (hC2 : ∀ j, 1 ≤ (2:ℝ)^(j+1) * r →
        C j ≤ c * ((2:ℝ)^(j+1) * r + 1) * (L + Real.log ((2:ℝ)^(j+1) * r + 1))) :
    ∀ N, ∑ j ∈ Finset.range N, (phiK ((2:ℝ)^j * r) - phiK ((2:ℝ)^(j+1) * r)) * C j
      ≤ 2000 * c * L * (1 + 1 / r) := by
  intro N
  have hlog7 : Real.log 7 ≤ 3 := by
    have h1 : Real.log 7 ≤ Real.log 8 := Real.log_le_log (by norm_num) (by norm_num)
    have h2 : Real.log (8:ℝ) = 3 * Real.log 2 := by
      rw [show (8:ℝ) = 2^3 by norm_num, Real.log_pow]; norm_num
    have h3 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
    rw [h2] at h1; linarith
  have hpt : ∀ j, (phiK ((2:ℝ)^j * r) - phiK ((2:ℝ)^(j+1) * r)) * C j
      ≤ c * L * (1024 / ((2:ℝ)^(j+1) * r) + 192 / Real.sqrt ((2:ℝ)^(j+1) * r)) := by
    intro j
    have huv : (2:ℝ)^j * r = ((2:ℝ)^(j+1) * r) / 2 := by
      rw [pow_succ]; ring
    have hmono : phiK ((2:ℝ)^(j+1) * r) ≤ phiK ((2:ℝ)^j * r) := by
      refine phi_antitoneOn (show (0:ℝ) < (2:ℝ)^j * r by positivity)
        (show (0:ℝ) < (2:ℝ)^(j+1) * r by positivity) ?_
      have hp : (2:ℝ)^j ≤ (2:ℝ)^(j+1) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      exact mul_le_mul_of_nonneg_right hp hr.le
    have hdnn : 0 ≤ phiK ((2:ℝ)^j * r) - phiK ((2:ℝ)^(j+1) * r) := by linarith
    by_cases hu : (2:ℝ)^(j+1) * r ≤ 1
    · have hupos : 0 < (2:ℝ)^(j+1) * r := by positivity
      have hCu := hC1 j hu
      have ha : phiK ((2:ℝ)^j * r) - phiK ((2:ℝ)^(j+1) * r) ≤ 4 / ((2:ℝ)^(j+1) * r) := by
        have h2 : phiK ((2:ℝ)^j * r) ≤ 2 / ((2:ℝ)^j * r) := phi_le_two_div (by positivity)
        have h3 : 2 / ((2:ℝ)^j * r) = 4 / ((2:ℝ)^(j+1) * r) := by
          rw [huv]; field_simp; norm_num
        have hb : 0 ≤ phiK ((2:ℝ)^(j+1) * r) := phi_nonneg (by positivity)
        linarith [hmono, h2, h3.le]
      have hfin : (4 / ((2:ℝ)^(j+1) * r)) * (4 * c * L)
          ≤ c * L * (1024 / ((2:ℝ)^(j+1) * r) + 192 / Real.sqrt ((2:ℝ)^(j+1) * r)) := by
        have h1 : 0 ≤ c * L := mul_nonneg hc (by linarith)
        have h2 : 0 ≤ 192 * c * L / Real.sqrt ((2:ℝ)^(j+1) * r) := by positivity
        have h3 : (4 / ((2:ℝ)^(j+1) * r)) * (4 * c * L)
            = 16 * c * L / ((2:ℝ)^(j+1) * r) := by ring
        have h4 : 16 * c * L / ((2:ℝ)^(j+1) * r) ≤ 1024 * c * L / ((2:ℝ)^(j+1) * r) :=
          div_le_div_of_nonneg_right (by linarith) hupos.le
        have h5 : 1024 * c * L / ((2:ℝ)^(j+1) * r)
            = c * L * (1024 / ((2:ℝ)^(j+1) * r)) := by ring
        have h6 : c * L * (1024 / ((2:ℝ)^(j+1) * r))
            ≤ c * L * (1024 / ((2:ℝ)^(j+1) * r) + 192 / Real.sqrt ((2:ℝ)^(j+1) * r)) := by
          have h7 : 0 ≤ c * L * (192 / Real.sqrt ((2:ℝ)^(j+1) * r)) := by positivity
          linarith
        linarith [h3.le, h4, h5.le, h6]
      calc (phiK ((2:ℝ)^j * r) - phiK ((2:ℝ)^(j+1) * r)) * C j
          ≤ (4 / ((2:ℝ)^(j+1) * r)) * (4 * c * L) :=
            mul_le_mul ha hCu (hC0 j) (by positivity)
        _ ≤ _ := hfin
    · have hu1 : 1 ≤ (2:ℝ)^(j+1) * r := le_of_lt (not_le.mp hu)
      have hupos : 0 < (2:ℝ)^(j+1) * r := by linarith
      have hCU := hC2 j hu1
      by_cases h6 : (2:ℝ)^(j+1) * r ≤ 6
      · -- linear regime
        have ha : phiK ((2:ℝ)^j * r) - phiK ((2:ℝ)^(j+1) * r) ≤ 4 / ((2:ℝ)^(j+1) * r) := by
          have h2 : phiK ((2:ℝ)^j * r) ≤ 2 / ((2:ℝ)^j * r) := phi_le_two_div (by positivity)
          have h3 : 2 / ((2:ℝ)^j * r) = 4 / ((2:ℝ)^(j+1) * r) := by
            rw [huv]; field_simp; norm_num
          have hb : 0 ≤ phiK ((2:ℝ)^(j+1) * r) := phi_nonneg (by positivity)
          linarith [hmono, h2, h3.le]
        have hCu : C j ≤ 112 * c * L := by
          refine le_trans hCU ?_
          have h1 : (2:ℝ)^(j+1) * r + 1 ≤ 7 := by linarith
          have h2 : Real.log ((2:ℝ)^(j+1) * r + 1) ≤ Real.log 7 :=
            Real.log_le_log (by linarith) h1
          have h3 : L + Real.log ((2:ℝ)^(j+1) * r + 1) ≤ 4 * L := by linarith
          have h4 : 0 ≤ L + Real.log ((2:ℝ)^(j+1) * r + 1) := by
            have := Real.log_nonneg (show (1:ℝ) ≤ (2:ℝ)^(j+1) * r + 1 by linarith)
            linarith
          calc c * ((2:ℝ)^(j+1) * r + 1) * (L + Real.log ((2:ℝ)^(j+1) * r + 1))
              ≤ c * 7 * (4 * L) := by
                refine mul_le_mul (mul_le_mul_of_nonneg_left h1 hc) h3 h4 (by positivity)
            _ = 28 * c * L := by ring
            _ ≤ 112 * c * L := by nlinarith [hc, hL]
        have hfin : 4 / ((2:ℝ)^(j+1) * r) * (112 * c * L)
            ≤ c * L * (1024 / ((2:ℝ)^(j+1) * r) + 192 / Real.sqrt ((2:ℝ)^(j+1) * r)) := by
          have h1 : 4 / ((2:ℝ)^(j+1) * r) * (112 * c * L)
              = 448 * c * L / ((2:ℝ)^(j+1) * r) := by ring
          rw [h1]
          have h2 : 448 * c * L / ((2:ℝ)^(j+1) * r)
              ≤ 1024 * c * L / ((2:ℝ)^(j+1) * r) :=
            div_le_div_of_nonneg_right (by nlinarith [hc, hL]) hupos.le
          have h3 : 1024 * c * L / ((2:ℝ)^(j+1) * r)
              = c * L * (1024 / ((2:ℝ)^(j+1) * r)) := by ring
          have h4 : 0 ≤ c * L * (192 / Real.sqrt ((2:ℝ)^(j+1) * r)) := by positivity
          linarith [h2, h4]
        calc (phiK ((2:ℝ)^j * r) - phiK ((2:ℝ)^(j+1) * r)) * C j
            ≤ (4 / ((2:ℝ)^(j+1) * r)) * (112 * c * L) :=
              mul_le_mul ha hCu (hC0 j) (by positivity)
          _ ≤ _ := hfin
      · -- quadratic regime
        have hu6 : 6 ≤ (2:ℝ)^(j+1) * r := le_of_lt (not_le.mp h6)
        have ha : phiK ((2:ℝ)^j * r) - phiK ((2:ℝ)^(j+1) * r)
            ≤ 24 / ((2:ℝ)^(j+1) * r) ^ 2 := by
          have h2 : phiK ((2:ℝ)^j * r) ≤ 6 / ((2:ℝ)^j * r) ^ 2 := by
            apply phi_le_quad
            rw [huv]; linarith
          have h3 : 6 / ((2:ℝ)^j * r) ^ 2 = 24 / ((2:ℝ)^(j+1) * r) ^ 2 := by
            rw [huv]; field_simp; norm_num
          have hb : 0 ≤ phiK ((2:ℝ)^(j+1) * r) := phi_nonneg (by positivity)
          linarith [hmono, h2, h3.le]
        have hlogu : Real.log ((2:ℝ)^(j+1) * r) ≤ 2 * Real.sqrt ((2:ℝ)^(j+1) * r) :=
          log_le_two_mul_sqrt (by linarith)
        have hlog2u : Real.log ((2:ℝ)^(j+1) * r + 1)
            ≤ 1 + Real.log ((2:ℝ)^(j+1) * r) := by
          have h1 : (2:ℝ)^(j+1) * r + 1 ≤ 2 * ((2:ℝ)^(j+1) * r) := by linarith
          have h2 : Real.log ((2:ℝ)^(j+1) * r + 1)
              ≤ Real.log (2 * ((2:ℝ)^(j+1) * r)) := Real.log_le_log (by linarith) h1
          rw [Real.log_mul (by norm_num) (ne_of_gt hupos)] at h2
          have h3 : Real.log 2 ≤ 1 := by
            have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
          linarith
        have hsq1 : 1 ≤ Real.sqrt ((2:ℝ)^(j+1) * r) := Real.one_le_sqrt.mpr hu1
        have hkey : L + 1 + Real.log ((2:ℝ)^(j+1) * r)
            ≤ 4 * L * Real.sqrt ((2:ℝ)^(j+1) * r) := by
          have h1 : L + 1 + Real.log ((2:ℝ)^(j+1) * r)
              ≤ L + 1 + 2 * Real.sqrt ((2:ℝ)^(j+1) * r) := by linarith
          have h2 : L + 1 ≤ 2 * L * Real.sqrt ((2:ℝ)^(j+1) * r) := by nlinarith
          have h3 : 2 * Real.sqrt ((2:ℝ)^(j+1) * r)
              ≤ 2 * L * Real.sqrt ((2:ℝ)^(j+1) * r) := by nlinarith
          linarith
        have hCu2 : C j ≤ 8 * c * L * ((2:ℝ)^(j+1) * r) * Real.sqrt ((2:ℝ)^(j+1) * r) := by
          have hA : C j ≤ c * (2 * ((2:ℝ)^(j+1) * r)) * (L + 1 + Real.log ((2:ℝ)^(j+1) * r)) := by
            refine le_trans hCU ?_
            have hlt2 : ((2:ℝ)^(j+1) * r + 1) ≤ 2 * ((2:ℝ)^(j+1) * r) := by linarith
            have hnn : 0 ≤ L + Real.log ((2:ℝ)^(j+1) * r + 1) := by
              have := Real.log_nonneg (show (1:ℝ) ≤ (2:ℝ)^(j+1) * r + 1 by linarith)
              linarith
            calc c * ((2:ℝ)^(j+1) * r + 1) * (L + Real.log ((2:ℝ)^(j+1) * r + 1))
                ≤ c * (2 * ((2:ℝ)^(j+1) * r)) * (L + Real.log ((2:ℝ)^(j+1) * r + 1)) :=
                  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlt2 hc) hnn
              _ ≤ c * (2 * ((2:ℝ)^(j+1) * r)) * (L + 1 + Real.log ((2:ℝ)^(j+1) * r)) := by
                  apply mul_le_mul_of_nonneg_left _ (by positivity)
                  linarith [hlog2u]
          have h1 : c * (2 * ((2:ℝ)^(j+1) * r)) * (L + 1 + Real.log ((2:ℝ)^(j+1) * r))
              ≤ c * (2 * ((2:ℝ)^(j+1) * r)) * (4 * L * Real.sqrt ((2:ℝ)^(j+1) * r)) :=
            mul_le_mul_of_nonneg_left hkey (by positivity)
          have h2 : c * (2 * ((2:ℝ)^(j+1) * r)) * (4 * L * Real.sqrt ((2:ℝ)^(j+1) * r))
              = 8 * c * L * ((2:ℝ)^(j+1) * r) * Real.sqrt ((2:ℝ)^(j+1) * r) := by ring
          linarith [hA, h1, h2.le]
        have hsq : Real.sqrt ((2:ℝ)^(j+1) * r) * Real.sqrt ((2:ℝ)^(j+1) * r)
            = (2:ℝ)^(j+1) * r := Real.mul_self_sqrt hupos.le
        have hfin : 24 / ((2:ℝ)^(j+1) * r) ^ 2
              * (8 * c * L * ((2:ℝ)^(j+1) * r) * Real.sqrt ((2:ℝ)^(j+1) * r))
            ≤ c * L * (1024 / ((2:ℝ)^(j+1) * r) + 192 / Real.sqrt ((2:ℝ)^(j+1) * r)) := by
          have h1 : 24 / ((2:ℝ)^(j+1) * r) ^ 2
              * (8 * c * L * ((2:ℝ)^(j+1) * r) * Real.sqrt ((2:ℝ)^(j+1) * r))
              = 192 * c * L / Real.sqrt ((2:ℝ)^(j+1) * r) := by
            field_simp
            rw [sq, hsq]; ring
          rw [h1]
          have h2 : 192 * c * L / Real.sqrt ((2:ℝ)^(j+1) * r)
              = c * L * (192 / Real.sqrt ((2:ℝ)^(j+1) * r)) := by ring
          have h3 : 0 ≤ c * L * (1024 / ((2:ℝ)^(j+1) * r)) := by positivity
          rw [h2]
          linarith [h3]
        calc (phiK ((2:ℝ)^j * r) - phiK ((2:ℝ)^(j+1) * r)) * C j
            ≤ (24 / ((2:ℝ)^(j+1) * r) ^ 2)
              * (8 * c * L * ((2:ℝ)^(j+1) * r) * Real.sqrt ((2:ℝ)^(j+1) * r)) :=
              mul_le_mul ha hCu2 (hC0 j) (by positivity)
          _ ≤ _ := hfin
  have hsum1 : ∑ j ∈ Finset.range N, (1 / ((2:ℝ)^(j+1) * r)) ≤ 1 / r := by
    have hrw : ∀ j : ℕ, (1 : ℝ) / ((2:ℝ)^(j+1) * r) = (1 / (2*r)) * ((1:ℝ)/2)^j := by
      intro j
      rw [pow_succ]
      field_simp
      rw [← mul_pow]
      norm_num
    have hg : ∑ j ∈ Finset.range N, ((1:ℝ)/2)^j ≤ 2 := by
      have h := geom_sum_range_le_one (q := ((1:ℝ)/2)) (by norm_num) (by norm_num) N
      norm_num at h
      exact h
    calc ∑ j ∈ Finset.range N, (1 / ((2:ℝ)^(j+1) * r))
        = ∑ j ∈ Finset.range N, (1 / (2*r)) * ((1:ℝ)/2)^j :=
          Finset.sum_congr rfl (fun j _ => hrw j)
      _ = (1 / (2*r)) * ∑ j ∈ Finset.range N, ((1:ℝ)/2)^j := by rw [Finset.mul_sum]
      _ ≤ (1 / (2*r)) * 2 := mul_le_mul_of_nonneg_left hg (by positivity)
      _ = 1 / r := by field_simp
  have hsqrtpow : ∀ k : ℕ, Real.sqrt ((2:ℝ)^k) = Real.sqrt 2 ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ m ih =>
        rw [pow_succ, Real.sqrt_mul (by positivity) (2:ℝ), ih, pow_succ]
  have hsum2 : ∑ j ∈ Finset.range N, (1 / Real.sqrt ((2:ℝ)^(j+1) * r)) ≤ 3 / r := by
    have hrw : ∀ j : ℕ, (1 : ℝ) / Real.sqrt ((2:ℝ)^(j+1) * r)
        = (1 / Real.sqrt (2*r)) * ((1:ℝ)/Real.sqrt 2)^j := by
      intro j
      rw [Real.sqrt_mul (by positivity) r, hsqrtpow (j+1), pow_succ]
      rw [show Real.sqrt (2*r) = Real.sqrt 2 * Real.sqrt r by
        rw [Real.sqrt_mul (by norm_num)]]
      have hA : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
      have hB : (0:ℝ) < Real.sqrt r := Real.sqrt_pos.mpr hr
      field_simp
      rw [← mul_pow]
      norm_num
    have hq0 : 0 ≤ (1:ℝ)/Real.sqrt 2 := by positivity
    have hq1 : (1:ℝ)/Real.sqrt 2 < 1 := by
      rw [div_lt_one (Real.sqrt_pos.mpr (by norm_num))]
      exact Real.one_lt_sqrt_two
    have hg : ∑ j ∈ Finset.range N, ((1:ℝ)/Real.sqrt 2)^j ≤ 4 := by
      have h := geom_sum_range_le_one hq0 hq1 N
      have hqle : (1:ℝ)/(1 - 1/Real.sqrt 2) ≤ 4 := by
        have hA : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
        have h2 : (4/3:ℝ) ≤ Real.sqrt 2 := by
          rw [Real.le_sqrt (by norm_num) (by norm_num)]
          norm_num
        have h3 : 1/Real.sqrt 2 ≤ (3:ℝ)/4 := by
          rw [div_le_div_iff₀ hA (by norm_num : (0:ℝ) < 4)]
          nlinarith
        have h4 : 0 < 1 - 1/Real.sqrt 2 := by nlinarith
        rw [div_le_iff₀ h4]
        nlinarith
      linarith
    calc ∑ j ∈ Finset.range N, (1 / Real.sqrt ((2:ℝ)^(j+1) * r))
        = ∑ j ∈ Finset.range N, (1 / Real.sqrt (2*r)) * ((1:ℝ)/Real.sqrt 2)^j :=
          Finset.sum_congr rfl (fun j _ => hrw j)
      _ = (1 / Real.sqrt (2*r)) * ∑ j ∈ Finset.range N, ((1:ℝ)/Real.sqrt 2)^j := by
          rw [Finset.mul_sum]
      _ ≤ (1 / Real.sqrt (2*r)) * 4 := mul_le_mul_of_nonneg_left hg (by positivity)
      _ ≤ 3 / r := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (Real.sqrt_pos.mpr (by positivity)) hr]
          have h1 : (4*r/3)^2 ≤ 2*r := by nlinarith [hr1, hr]
          have h2 : 4*r/3 ≤ Real.sqrt (2*r) := by
            have h3 : (4*r/3)^2 ≤ (Real.sqrt (2*r))^2 := by
              rw [Real.sq_sqrt (show (0:ℝ) ≤ 2*r by positivity)]; exact h1
            calc 4*r/3 = Real.sqrt ((4*r/3)^2) := (Real.sqrt_sq (by positivity)).symm
              _ ≤ Real.sqrt ((Real.sqrt (2*r))^2) := Real.sqrt_le_sqrt h3
              _ = Real.sqrt (2*r) := Real.sqrt_sq (by positivity)
          linarith
  have hcomb : ∑ j ∈ Finset.range N, (1024 / ((2:ℝ)^(j+1) * r)
        + 192 / Real.sqrt ((2:ℝ)^(j+1) * r)) ≤ 1024*(1/r) + 192*(3/r) := by
    rw [Finset.sum_add_distrib]
    have e1 : ∑ j ∈ Finset.range N, 1024 / ((2:ℝ)^(j+1) * r)
        = 1024 * ∑ j ∈ Finset.range N, 1/((2:ℝ)^(j+1) * r) := by
      rw [Finset.mul_sum]; simp [div_eq_mul_inv]
    have e2 : ∑ j ∈ Finset.range N, 192 / Real.sqrt ((2:ℝ)^(j+1) * r)
        = 192 * ∑ j ∈ Finset.range N, 1/Real.sqrt ((2:ℝ)^(j+1) * r) := by
      rw [Finset.mul_sum]; simp [div_eq_mul_inv]
    rw [e1, e2]
    nlinarith [hsum1, hsum2]
  calc ∑ j ∈ Finset.range N, (phiK ((2:ℝ)^j * r) - phiK ((2:ℝ)^(j+1) * r)) * C j
      ≤ ∑ j ∈ Finset.range N, c * L * (1024 / ((2:ℝ)^(j+1) * r)
          + 192 / Real.sqrt ((2:ℝ)^(j+1) * r)) := Finset.sum_le_sum (fun j _ => hpt j)
    _ = c * L * ∑ j ∈ Finset.range N, (1024 / ((2:ℝ)^(j+1) * r)
          + 192 / Real.sqrt ((2:ℝ)^(j+1) * r)) := by rw [Finset.mul_sum]
    _ ≤ c * L * (1024*(1/r) + 192*(3/r)) := mul_le_mul_of_nonneg_left hcomb (by positivity)
    _ ≤ 2000 * c * L * (1 + 1 / r) := by
        have h1 : 0 ≤ c * L := mul_nonneg hc (by linarith)
        have h2 : 0 < 1/r := one_div_pos.mpr hr
        have hA : (1024:ℝ)*(1/r) + 192*(3*(1/r)) ≤ 2000*(1 + 1/r) := by linarith
        calc c * L * (1024*(1/r) + 192*(3/r)) = c * L * (1024*(1/r) + 192*(3*(1/r))) := by ring
          _ ≤ c * L * (2000*(1 + 1/r)) := mul_le_mul_of_nonneg_left hA h1
          _ = 2000 * c * L * (1 + 1 / r) := by ring







/-! ### Divisor basics for an entire function -/

lemma divisor_eq_orderNatL {f : ℂ → ℂ} {U : Set ℂ} {u : ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hu : u ∈ U) :
    MeromorphicOn.divisor f U u = (analyticOrderNatAt f u : ℤ) := by
  rw [MeromorphicOn.divisor_apply hf.meromorphicOn hu, (hf u hu).meromorphicOrderAt_eq]
  rcases eq_or_ne (analyticOrderAt f u) ⊤ with h | h
  · rw [h]; simp [analyticOrderNatAt, h]
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp h
    have h2 : analyticOrderNatAt f u = n := by rw [analyticOrderNatAt, ← hn]; simp
    rw [h2, ← hn]; simp

lemma divisor_nonnegL {f : ℂ → ℂ} {U : Set ℂ} {z : ℂ} (hf : AnalyticOnNhd ℂ f U) :
    (0 : ℤ) ≤ MeromorphicOn.divisor f U z := by
  by_cases hz : z ∈ U
  · rw [MeromorphicOn.divisor_apply hf.meromorphicOn hz]
    have hAn : AnalyticAt ℂ f z := hf z hz
    have hord : (0 : WithTop ℤ) ≤ meromorphicOrderAt f z :=
      (MeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt hAn.meromorphicNFAt).2 hAn
    exact (WithTop.untop₀_nonneg (α := ℤ) (a := meromorphicOrderAt f z)).mpr hord
  · rw [MeromorphicOn.divisor_def]
    rw [if_neg]
    intro h
    exact hz h.2

lemma divisor_ne_zero_imp_eq_zeroL {f : ℂ → ℂ} {U : Set ℂ} {u : ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hu : u ∈ U)
    (h : MeromorphicOn.divisor f U u ≠ 0) : f u = 0 := by
  rw [divisor_eq_orderNatL hf hu] at h
  by_contra hne
  apply h
  have : analyticOrderNatAt f u = 0 := by
    rw [analyticOrderNatAt, analyticOrderAt_eq_zero.mpr (Or.inr hne)]
    rfl
  rw [this]; simp

lemma analyticOnNhd_completedLL (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (U : Set ℂ) :
    AnalyticOnNhd ℂ (completedLFunction χ) U :=
  fun z _ => (differentiable_completedLFunction hχ).analyticAt z

/-- Multiplicity-weighted zero count of `Λ(χ,·)` in a disk. -/
def cntK (χ : DirichletCharacter ℂ N) (s : ℂ) (x : ℝ) : ℝ :=
  ∑ᶠ u : ℂ, (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall s x)) u : ℤ) : ℝ)

lemma cnt_finite (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (s : ℂ) (x : ℝ) :
    Function.HasFiniteSupport
      (fun u : ℂ => (((MeromorphicOn.divisor (completedLFunction χ)
        (Metric.closedBall s x)) u : ℤ) : ℝ)) := by
  have h1 : (MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall s x)).support.Finite :=
    MeromorphicOn.divisor_support_finite_of_subset (analyticOnNhd_completedLL χ hχ _).meromorphicOn
      (isCompact_closedBall s x) (Subset.refl _)
  refine h1.subset ?_
  intro u hu
  simp only [Function.mem_support] at hu ⊢
  intro h0
  exact hu (by rw [h0]; simp)

lemma cnt_nonneg (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (s : ℂ) (x : ℝ) :
    0 ≤ cntK χ s x := by
  unfold cntK
  apply finsum_nonneg
  intro u
  exact_mod_cast divisor_nonnegL (analyticOnNhd_completedLL χ hχ _)

lemma cnt_mono (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (s : ℂ) {x y : ℝ} (hxy : x ≤ y) :
    cntK χ s x ≤ cntK χ s y := by
  have hsub : Metric.closedBall s x ⊆ Metric.closedBall s y :=
    Metric.closedBall_subset_closedBall (by linarith)
  refine finsum_le_finsum' (cnt_finite χ hχ s x) (cnt_finite χ hχ s y) (fun u => ?_)
  by_cases hu : u ∈ Metric.closedBall s x
  · rw [divisor_eq_orderNatL (analyticOnNhd_completedLL χ hχ _) hu,
      divisor_eq_orderNatL (analyticOnNhd_completedLL χ hχ _) (hsub hu)]
  · have h0 : MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall s x) u = 0 :=
      (MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall s x)).apply_eq_zero_of_notMem hu
    rw [h0]
    have := divisor_nonnegL (analyticOnNhd_completedLL χ hχ (Metric.closedBall s y) : _) (z := u)
    simp only [Int.cast_zero]
    exact_mod_cast this

/-- **Uniform local zero count** (disk centred on `Re = 2`). -/
theorem local_zeroCount_uniformL :
    ∃ c : ℝ, 0 < c ∧ ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
      (hχprim : χ.IsPrimitive), ∀ R : ℝ, 2 ≤ R → ∀ t : ℝ,
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (completedLFunction χ)
          (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) R)) u : ℤ) : ℝ)) ≤
        c * R * (Real.log (2 + |t| + R) + Real.log (N : ℝ) + 2) := by
  classical
  refine ⟨4 * (9 / 2) * (1 + Real.log 3 / 2), by positivity, ?_⟩
  intro N _ χ hχ hχprim R hR t
  let n : ℕ := Nat.ceil (2 * R + 2)
  let J : Finset ℕ := Finset.range (n + 1)
  let m : ℕ → ℝ := fun j => t - (R + 1) + (j : ℝ)
  let X : ℝ := Real.log (2 + |t| + R) + Real.log (N : ℝ) + 2
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N)))
  have hN0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  have hX2 : 2 ≤ X := by
    dsimp [X]
    have h1 : 0 ≤ Real.log (2 + |t| + R) := Real.log_nonneg (by linarith [abs_nonneg t])
    linarith
  have hn_le : (n : ℝ) ≤ 2 * R + 3 := by
    dsimp [n]
    have hc : (Nat.ceil (2 * R + 2) : ℝ) < 2 * R + 2 + 1 :=
      Nat.ceil_lt_add_one (a := 2 * R + 2) (by positivity : 0 ≤ 2 * R + 2)
    nlinarith
  have hcard : ((n + 1 : ℕ) : ℝ) ≤ 4 * R := by
    dsimp [n]
    exact Commons.NumberTheory.Linnik.window_count_bound hR
  have h25 : (2.5 : ℝ) = (5:ℝ)/2 := by norm_num
  have hwin' : ∀ j : ℕ, j ≤ n →
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (completedLFunction χ)
          (Metric.closedBall ((2 : ℂ) + Complex.I * ((m j) : ℂ)) ((5:ℝ)/2))) u : ℤ) : ℝ)) ≤
        (9 / 2) * (Real.log (2 + |m j|) + Real.log (N : ℝ) + 2) := by
    intro j hj
    have h0 := Commons.NumberTheory.DirichletCharacter.completedL_diskZeroCount_explicit
      χ hχ hχprim (m j)
    have hX2' : 2 ≤ Real.log (2 + |m j|) + Real.log (N : ℝ) + 2 := by
      have h1 : 0 ≤ Real.log (2 + |m j|) := Real.log_nonneg (by linarith [abs_nonneg (m j)])
      linarith
    have hlog4 : Real.log (2 + |m j| + 2) ≤ Real.log (2 + |m j|) + 2 := by
      have h1 : 2 + |m j| + 2 ≤ 4 * (2 + |m j|) := by nlinarith [abs_nonneg (m j)]
      have h2 := Real.log_le_log (by positivity : (0:ℝ) < 2 + |m j| + 2) h1
      rw [Real.log_mul (by norm_num) (by positivity : (2 + |m j|) ≠ 0)] at h2
      have h3 : Real.log 4 ≤ 2 := by
        rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
        have h4 : Real.log 2 ≤ 1 := by
          have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
        push_cast; linarith
      linarith
    have h5 : (3/2) * (Real.log (N : ℝ) + Real.log (2 + |m j| + 2)) + 6
        ≤ (3/2) * (Real.log (N : ℝ) + (Real.log (2 + |m j|) + 2)) + 6 := by linarith
    have h6 : (3/2) * (Real.log (N : ℝ) + (Real.log (2 + |m j|) + 2)) + 6
        ≤ (9/2) * (Real.log (2 + |m j|) + Real.log (N : ℝ) + 2) := by linarith [hX2']
    exact le_trans (le_trans h0 h5) h6
  have hlogm : ∀ j : ℕ, j ≤ n → Real.log (2 + |m j|) ≤ Real.log (2 + |t| + R) + Real.log 3 := by
    intro j hj
    have hpos1 : 0 < 2 + |m j| := by positivity
    have hle : 2 + |m j| ≤ 3 * (2 + |t| + R) := by
      have hb := Commons.NumberTheory.Linnik.window_center_le (R := R) (t := t) (j := j) (n := n) hR hj hn_le
      simpa [m] using hb
    have h := Real.log_le_log hpos1 hle
    rw [show 3 * (2 + |t| + R) = (2 + |t| + R) * 3 by ring] at h
    rw [Real.log_mul (ne_of_gt (by positivity : 0 < 2 + |t| + R))
        (ne_of_gt (by norm_num : 0 < (3 : ℝ)))] at h
    exact h
  have hEj : ∀ j : ℕ, j ≤ n →
      (Real.log (2 + |m j|) + Real.log (N : ℝ) + 2) ≤ X + Real.log 3 := by
    intro j hj
    have h0 := hlogm j hj
    dsimp [X]
    linarith
  have hsum1 : (∑ j ∈ J, (9 / 2 : ℝ) * (Real.log (2 + |m j|) + Real.log (N : ℝ) + 2)) ≤
      ((n + 1 : ℕ) : ℝ) * ((9 / 2 : ℝ) * (X + Real.log 3)) := by
    have h1 : ∀ j ∈ J, (9 / 2 : ℝ) * (Real.log (2 + |m j|) + Real.log (N : ℝ) + 2) ≤
        (9 / 2 : ℝ) * (X + Real.log 3) := by
      intro j hj
      exact mul_le_mul_of_nonneg_left (hEj j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))) (by norm_num)
    have h2 : (∑ j ∈ J, (9 / 2 : ℝ) * (X + Real.log 3))
        = ((n + 1 : ℕ) : ℝ) * ((9 / 2 : ℝ) * (X + Real.log 3)) := by
      rw [Finset.sum_const]
      simp [J, nsmul_eq_mul]
    exact le_trans (Finset.sum_le_sum h1) (le_of_eq h2)
  have hsum2 : ((n + 1 : ℕ) : ℝ) * ((9 / 2 : ℝ) * (X + Real.log 3)) ≤
      (4 * (9 / 2) * (1 + Real.log 3 / 2)) * R * X := by
    have h2 : 0 ≤ (9 / 2 : ℝ) * (X + Real.log 3) := by positivity
    have h3 : (9 / 2 : ℝ) * (X + Real.log 3) ≤ ((9 / 2 : ℝ) * (1 + Real.log 3 / 2)) * X := by
      have hX : 0 ≤ X := by linarith
      have hx1 : X + Real.log 3 ≤ (1 + Real.log 3 / 2) * X := by
        have hposlog : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
        nlinarith [hX2]
      nlinarith [hx1]
    calc ((n + 1 : ℕ) : ℝ) * ((9 / 2 : ℝ) * (X + Real.log 3))
        ≤ (4 * R) * ((9 / 2 : ℝ) * (X + Real.log 3)) :=
          mul_le_mul_of_nonneg_right hcard h2
      _ ≤ (4 * R) * (((9 / 2 : ℝ) * (1 + Real.log 3 / 2)) * X) :=
          mul_le_mul_of_nonneg_left h3 (by positivity : (0:ℝ) ≤ 4 * R)
      _ = (4 * (9 / 2) * (1 + Real.log 3 / 2)) * R * X := by ring
  have hcover := Commons.NumberTheory.DirichletCharacter.completedL_window_cover χ hχ hχprim
    (R := R) (t := t) hR
  have hgoal : (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (completedLFunction χ)
      (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) R)) u : ℤ) : ℝ)) ≤
      (4 * (9 / 2) * (1 + Real.log 3 / 2)) * R * X := by
    have hcvr : (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (completedLFunction χ)
        (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) R)) u : ℤ) : ℝ)) ≤
        ∑ j ∈ Finset.range (Nat.ceil (2 * R + 2) + 1), (∑ᶠ u : ℂ,
          (((MeromorphicOn.divisor (completedLFunction χ)
            (Metric.closedBall ((2 : ℂ) + Complex.I * ((m j : ℝ) : ℂ)) ((5:ℝ)/2))) u : ℤ) : ℝ)) := by
      have h := hcover
      rw [h25] at h
      refine le_trans h ?_
      apply Finset.sum_le_sum
      intro j hj
      exact le_of_eq (Commons.NumberTheory.Linnik.sum_divisor_center_eq (f := completedLFunction χ)
        (ρ := (5:ℝ)/2) (by
          rw [show m j = t - (R + 1) + (j : ℝ) from rfl]
          push_cast
          ring))
    calc (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (completedLFunction χ)
            (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) R)) u : ℤ) : ℝ))
        ≤ ∑ j ∈ Finset.range (Nat.ceil (2 * R + 2) + 1), (∑ᶠ u : ℂ,
            (((MeromorphicOn.divisor (completedLFunction χ)
              (Metric.closedBall ((2 : ℂ) + Complex.I * ((m j : ℝ) : ℂ)) ((5:ℝ)/2))) u : ℤ) : ℝ)) := hcvr
      _ ≤ ∑ j ∈ Finset.range (Nat.ceil (2 * R + 2) + 1),
            (9 / 2 : ℝ) * (Real.log (2 + |m j|) + Real.log (N : ℝ) + 2) := by
          refine Finset.sum_le_sum (fun j hj => ?_)
          exact hwin' j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
      _ = ∑ j ∈ J, (9 / 2 : ℝ) * (Real.log (2 + |m j|) + Real.log (N : ℝ) + 2) := by rfl
      _ ≤ ((n + 1 : ℕ) : ℝ) * ((9 / 2 : ℝ) * (X + Real.log 3)) := hsum1
      _ ≤ (4 * (9 / 2) * (1 + Real.log 3 / 2)) * R * X := hsum2
  simpa [X] using hgoal

/-- **Uniform zero count in an arbitrary disk.** -/
theorem ball_zeroCount_uniformL :
    ∃ c : ℝ, 0 < c ∧ ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
      (hχprim : χ.IsPrimitive), ∀ a : ℂ, ∀ ρ : ℝ, 1 ≤ ρ →
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (completedLFunction χ)
          (Metric.closedBall a ρ)) u : ℤ) : ℝ)) ≤
        c * (ρ + 1) * (Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2) := by
  obtain ⟨c0, hc0, hlocal⟩ := local_zeroCount_uniformL
  refine ⟨4 * max c0 0 + 4, by positivity, ?_⟩
  intro N _ χ hχ hχprim a ρ hρ
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N)))
  have hN0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  have hnorm : 0 ≤ ‖a‖ := norm_nonneg a
  have hρ0 : 0 ≤ ρ := by linarith
  have h2 := hlocal χ hχ hχprim (ρ + 2) (by linarith : 2 ≤ ρ + 2) a.im
  have h2' : (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (completedLFunction χ)
        (Metric.closedBall ((2 : ℂ) + Complex.I * (a.im : ℂ)) (ρ + 2))) u : ℤ) : ℝ)) ≤
      c0 * (ρ + 2) * (Real.log (4 + |a.im| + ρ) + Real.log (N : ℝ) + 2) := by
    have harg : (2 + |a.im| + (ρ + 2)) = (4 + |a.im| + ρ) := by ring
    simpa [harg] using h2
  have h12 : (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (completedLFunction χ)
        (Metric.closedBall a ρ)) u : ℤ) : ℝ)) ≤
      c0 * (ρ + 2) * (Real.log (4 + |a.im| + ρ) + Real.log (N : ℝ) + 2) :=
    le_trans (Commons.NumberTheory.Linnik.divisor_sum_le_divisor_sum_big χ hχ hχprim a ρ) h2'
  have hIm : |a.im| ≤ ‖a‖ := Complex.abs_im_le_norm a
  have hposLog : 0 < 4 + |a.im| + ρ := by nlinarith [abs_nonneg a.im]
  have hleSq : 4 + ‖a‖ + ρ ≤ (‖a‖ + ρ + 2) ^ 2 := by nlinarith [sq_nonneg (‖a‖ + ρ), hnorm]
  have hlog1 : Real.log (4 + |a.im| + ρ) ≤ 2 * Real.log (‖a‖ + ρ + 2) := by
    have hmono : Real.log (4 + |a.im| + ρ) ≤ Real.log (4 + ‖a‖ + ρ) :=
      Real.log_le_log hposLog (by nlinarith)
    have hpos2 : 0 < 4 + ‖a‖ + ρ := by nlinarith
    have hlog2 : Real.log (4 + ‖a‖ + ρ) ≤ Real.log ((‖a‖ + ρ + 2) ^ 2) :=
      Real.log_le_log hpos2 hleSq
    have hsq : Real.log ((‖a‖ + ρ + 2) ^ 2) = 2 * Real.log (‖a‖ + ρ + 2) := by
      rw [Real.log_pow]; ring
    linarith
  have hXlog : 0 ≤ Real.log (‖a‖ + ρ + 2) := Real.log_nonneg (by nlinarith)
  have hsmall : 2 * Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2 ≤
      2 * (Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2) := by nlinarith [hN0, hXlog]
  have hposT : 0 ≤ Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2 := by linarith
  have hposC : 0 ≤ max c0 0 := le_max_right c0 0
  have hRhoFact : (ρ + 2) * (2 * Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2) ≤
      4 * (ρ + 1) * (Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2) := by
    have hρ2 : ρ + 2 ≤ 2 * (ρ + 1) := by nlinarith
    have hleft : 0 ≤ 2 * Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2 := by linarith
    calc (ρ + 2) * (2 * Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2)
        ≤ (2 * (ρ + 1)) * (2 * (Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2)) :=
          mul_le_mul hρ2 hsmall hleft (by linarith)
      _ = 4 * (ρ + 1) * (Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2) := by ring
  have hposArg : 0 ≤ Real.log (4 + |a.im| + ρ) + Real.log (N : ℝ) + 2 := by
    have h1pos : 0 ≤ Real.log (4 + |a.im| + ρ) := Real.log_nonneg (by linarith [abs_nonneg a.im])
    linarith
  have hstepA : c0 * (ρ + 2) * (Real.log (4 + |a.im| + ρ) + Real.log (N : ℝ) + 2) ≤
      (max c0 0) * (ρ + 2) * (2 * Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2) := by
    have hle0 : c0 ≤ max c0 0 := le_max_left c0 0
    have hprod1 : c0 * (ρ + 2) * (Real.log (4 + |a.im| + ρ) + Real.log (N : ℝ) + 2) ≤
        (max c0 0) * (ρ + 2) * (Real.log (4 + |a.im| + ρ) + Real.log (N : ℝ) + 2) := by
      have hfact : 0 ≤ (ρ + 2) * (Real.log (4 + |a.im| + ρ) + Real.log (N : ℝ) + 2) := by positivity
      calc c0 * (ρ + 2) * (Real.log (4 + |a.im| + ρ) + Real.log (N : ℝ) + 2)
          = c0 * ((ρ + 2) * (Real.log (4 + |a.im| + ρ) + Real.log (N : ℝ) + 2)) := by ring
        _ ≤ (max c0 0) * ((ρ + 2) * (Real.log (4 + |a.im| + ρ) + Real.log (N : ℝ) + 2)) :=
            mul_le_mul_of_nonneg_right hle0 hfact
        _ = (max c0 0) * (ρ + 2) * (Real.log (4 + |a.im| + ρ) + Real.log (N : ℝ) + 2) := by ring
    have hArg : Real.log (4 + |a.im| + ρ) + Real.log (N : ℝ) + 2 ≤
        2 * Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2 := by linarith [hlog1]
    have hpos2 : 0 ≤ (max c0 0) * (ρ + 2) := by positivity
    exact le_trans hprod1 (mul_le_mul_of_nonneg_left hArg hpos2)
  have hstepB : (max c0 0) * (ρ + 2) * (2 * Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2) ≤
      (max c0 0) * (4 * (ρ + 1)) * (Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2) := by
    calc (max c0 0) * (ρ + 2) * (2 * Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2)
        = (max c0 0) * ((ρ + 2) * (2 * Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2)) := by ring
      _ ≤ (max c0 0) * (4 * (ρ + 1) * (Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2)) :=
          mul_le_mul_of_nonneg_left hRhoFact hposC
      _ = (max c0 0) * (4 * (ρ + 1)) * (Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2) := by ring
  have hfinal : (max c0 0) * (4 * (ρ + 1)) * (Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2) ≤
      (4 * max c0 0 + 4) * (ρ + 1) * (Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2) := by
    have hleC : 4 * max c0 0 ≤ 4 * max c0 0 + 4 := by linarith
    have hposR : 0 ≤ (ρ + 1) * (Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2) := by positivity
    calc (max c0 0) * (4 * (ρ + 1)) * (Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2)
        = (4 * max c0 0) * ((ρ + 1) * (Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2)) := by ring
      _ ≤ (4 * max c0 0 + 4) * ((ρ + 1) * (Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2)) :=
          mul_le_mul_of_nonneg_right hleC hposR
      _ = (4 * max c0 0 + 4) * (ρ + 1) * (Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2) := by ring
  exact le_trans h12 (le_trans hstepA (le_trans hstepB hfinal))


lemma log_arg_posL (s : ℂ) : (0:ℝ) < ‖s‖ + 2 := by positivity
lemma log_arg_ge1L (s : ℂ) : (1:ℝ) ≤ ‖s‖ + 2 := by linarith [norm_nonneg s]
lemma logN_nonnegL : (0:ℝ) ≤ Real.log (N : ℝ) :=
  Real.log_nonneg (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)))

lemma cnt_le_ball :
    ∃ c : ℝ, 0 < c ∧ ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
      (hχprim : χ.IsPrimitive), ∀ s : ℂ, ∀ x : ℝ, 1 ≤ x →
      cntK χ s x ≤ c * (x + 1) * (Real.log (‖s‖ + x + 2) + Real.log (N : ℝ) + 2) := by
  obtain ⟨c₀, hc₀, hb⟩ := ball_zeroCount_uniformL
  refine ⟨c₀, hc₀, ?_⟩
  intro N _ χ hχ hχprim s x hx
  simpa [cntK] using hb χ hχ hχprim s x hx

lemma cnt_bounds :
    ∃ c : ℝ, 0 < c ∧ ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
      (hχprim : χ.IsPrimitive), ∀ s : ℂ, ∀ x : ℝ,
      (x ≤ 1 → cntK χ s x ≤ 4 * c * (Real.log (‖s‖ + 2) + Real.log (N : ℝ) + 2)) ∧
      (1 ≤ x → cntK χ s x ≤ c * (x + 1) *
        (Real.log (‖s‖ + 2) + Real.log (N : ℝ) + 2 + Real.log (x + 1))) := by
  obtain ⟨c, hc, hcnt⟩ := cnt_le_ball
  refine ⟨c, hc, ?_⟩
  intro N _ χ hχ hχprim s x
  have hcnt := hcnt χ hχ hχprim
  have hLpos : 0 < Real.log (‖s‖ + 2) := by
    refine Real.log_pos ?_; linarith [norm_nonneg s]
  constructor
  · intro hx
    have h1 : cntK χ s x ≤ cntK χ s 1 := cnt_mono χ hχ s hx
    have h2 := hcnt s 1 le_rfl
    have h3 : Real.log (‖s‖ + 1 + 2) ≤ Real.log (‖s‖ + 2) + 1 := by
      have he : ‖s‖ + 1 + 2 = ‖s‖ + 3 := by ring
      rw [he]
      have h : ‖s‖ + 3 ≤ (‖s‖ + 2) * 2 := by linarith [norm_nonneg s]
      have h4 := Real.log_le_log (by positivity : (0:ℝ) < ‖s‖ + 3) h
      rw [Real.log_mul (x := (‖s‖ + 2)) (y := 2) (by positivity) (by norm_num)] at h4
      have h5 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
      linarith
    have hL2 : 2 ≤ Real.log (‖s‖ + 2) + Real.log (N : ℝ) + 2 := by linarith [hLpos.le, logN_nonnegL (N := N)]
    have hnn : 0 ≤ Real.log (‖s‖ + 2) + Real.log (N : ℝ) + 2 := by linarith
    calc cntK χ s x ≤ cntK χ s 1 := h1
      _ ≤ c * (1 + 1) * (Real.log (‖s‖ + 1 + 2) + Real.log (N : ℝ) + 2) := h2
      _ ≤ 4 * c * (Real.log (‖s‖ + 2) + Real.log (N : ℝ) + 2) := by
          have hA : Real.log (‖s‖ + 1 + 2) + Real.log (N : ℝ) + 2
              ≤ 2 * (Real.log (‖s‖ + 2) + Real.log (N : ℝ) + 2) := by linarith
          have h2' : c * (1 + 1) * (Real.log (‖s‖ + 1 + 2) + Real.log (N : ℝ) + 2)
              ≤ c * (1 + 1) * (2 * (Real.log (‖s‖ + 2) + Real.log (N : ℝ) + 2)) :=
            mul_le_mul_of_nonneg_left hA (by positivity)
          have h3' : c * (1 + 1) * (2 * (Real.log (‖s‖ + 2) + Real.log (N : ℝ) + 2))
              = 4 * c * (Real.log (‖s‖ + 2) + Real.log (N : ℝ) + 2) := by ring
          linarith [h2', h3'.le]
  · intro hx
    have h1 := hcnt s x hx
    have h2 : Real.log (‖s‖ + x + 2) ≤ Real.log (‖s‖ + 2) + Real.log (x + 1) := by
      have h : ‖s‖ + x + 2 ≤ (‖s‖ + 2) * (x + 1) := by nlinarith [norm_nonneg s, hx]
      have h4 := Real.log_le_log (by positivity : (0:ℝ) < ‖s‖ + x + 2) h
      rw [Real.log_mul (x := (‖s‖ + 2)) (y := (x + 1)) (by positivity) (by linarith)] at h4
      exact h4
    have hnn : 0 ≤ x + 1 := by linarith
    calc cntK χ s x ≤ c * (x + 1) * (Real.log (‖s‖ + x + 2) + Real.log (N : ℝ) + 2) := h1
      _ ≤ c * (x + 1) * (Real.log (‖s‖ + 2) + Real.log (N : ℝ) + 2 + Real.log (x + 1)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith

/-- `D u ≠ 0` for the divisor of `Λ` on a ball means `u` is a zero of `Λ`. -/
lemma zero_of_divisor_neL {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {R : ℝ} {u : ℂ}
    (h : ((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R) u : ℤ) : ℝ) ≠ 0) :
    completedLFunction χ u = 0 := by
  have hmem : u ∈ Metric.closedBall (0:ℂ) R := by
    by_contra hc
    exact h (by simp [(MeromorphicOn.divisor _ _).apply_eq_zero_of_notMem hc])
  have hne : MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R) u ≠ 0 := by
    intro h0; exact h (by simp [h0])
  exact divisor_ne_zero_imp_eq_zeroL (analyticOnNhd_completedLL χ hχ _) hmem hne

lemma lfunction_zero_of_divisor_neLL {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive)
    {R : ℝ} {u : ℂ}
    (h : ((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R) u : ℤ) : ℝ) ≠ 0) :
    LFunction χ u = 0 := by
  have hN1 : N ≠ 1 := by
    intro h1; subst h1; exact hχ (Subsingleton.elim χ 1)
  rw [LFunction_eq_completed_div_gammaFactor χ u (Or.inr hN1), zero_of_divisor_neL hχ h, zero_div]

/-- Membership in the closed ball from a nonzero divisor value. -/
lemma mem_ball_of_divisor_neL {χ : DirichletCharacter ℂ N} {R : ℝ} {u : ℂ}
    (h : ((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R) u : ℤ) : ℝ) ≠ 0) :
    u ∈ Metric.closedBall (0:ℂ) R := by
  by_contra hc
  exact h (by simp [(MeromorphicOn.divisor _ _).apply_eq_zero_of_notMem hc])

lemma norm_sub_sqL {σ t : ℝ} (hσ : σ ≤ 2) :
    ‖((2:ℂ) + (t:ℂ)*I) - ((σ:ℂ) + (t:ℂ)*I)‖ = 2 - σ := by
  have h : ((2:ℂ) + (t:ℂ)*I) - ((σ:ℂ) + (t:ℂ)*I) = ((2-σ : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  rw [h, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  linarith

lemma re_le_norm_subL (σ t : ℝ) (u : ℂ) (hu : u.re ≤ 1) :
    (1:ℝ) ≤ ‖((2:ℂ) + (t:ℂ)*I) - u‖ := by
  have h : (((2:ℂ) + (t:ℂ)*I) - u).re = 2 - u.re := by simp
  calc (1:ℝ) ≤ 2 - u.re := by linarith
    _ = (((2:ℂ) + (t:ℂ)*I) - u).re := h.symm
    _ ≤ ‖((2:ℂ) + (t:ℂ)*I) - u‖ := Complex.re_le_norm _

/-- **Kernel-sum bound.** -/
theorem kernel_sum_boundL :
    ∃ C : ℝ, 0 < C ∧ ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
      (hχprim : χ.IsPrimitive), ∀ σ t r R : ℝ, 1/2 ≤ σ → σ ≤ 5/4 → 0 < r → r ≤ 1 → 2 ≤ R →
      (∀ ρ : ℂ, LFunction χ ρ = 0 → r ≤ ‖((σ:ℂ) + (t:ℂ)*I) - ρ‖) →
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) u : ℤ) : ℝ)
          * ‖1/(((σ:ℂ)+(t:ℂ)*I) - u) - 1/(((2:ℂ)+(t:ℂ)*I) - u)‖)
        ≤ C * (1 + 1/r) * (Real.log (‖((σ:ℂ)+(t:ℂ)*I)‖ + 2) + Real.log (N:ℝ) + 2) := by
  obtain ⟨c, hc, hcnt⟩ := cnt_bounds
  have hc0 : 0 ≤ c := hc.le
  refine ⟨3000 * c, by positivity, ?_⟩
  intro N _ χ hχ hχprim σ t r R hσ1 hσ2 hr hr1 hR hdist
  set s : ℂ := (σ:ℂ) + (t:ℂ)*I with hsdef
  set s₀ : ℂ := (2:ℂ) + (t:ℂ)*I with hs₀def
  set L : ℝ := Real.log (‖s‖ + 2) + Real.log (N:ℝ) + 2 with hLdef
  have hsne : (0:ℝ) < ‖s‖ := by
    rw [hsdef]
    have h2 : |(((σ:ℂ) + (t:ℂ)*I).re)| ≤ ‖((σ:ℂ) + (t:ℂ)*I)‖ := Complex.abs_re_le_norm _
    have h3 : (((σ:ℂ) + (t:ℂ)*I).re) = σ := by simp
    rw [h3, abs_of_nonneg (by linarith : (0:ℝ) ≤ σ)] at h2
    linarith
  have hLpos : 0 < Real.log (‖s‖ + 2) := by
    refine Real.log_pos ?_
    linarith
  have hL1 : 1 ≤ L := by
    have := logN_nonnegL (N := N); rw [hLdef]; linarith
  set D : ℂ → ℝ := fun u => (((MeromorphicOn.divisor (completedLFunction χ)
    (Metric.closedBall 0 R)) u : ℤ) : ℝ) with hDdef
  have hDnn : ∀ u, 0 ≤ D u := fun u => by
    have h1 := divisor_nonnegL (analyticOnNhd_completedLL χ hχ (Metric.closedBall 0 R)) (z := u)
    show (0:ℝ) ≤ (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) u : ℤ) : ℝ)
    exact_mod_cast h1
  have hDfin : (Function.support D).Finite := by
    have h1 : (MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)).support.Finite :=
      MeromorphicOn.divisor_support_finite_of_subset (analyticOnNhd_completedLL χ hχ _).meromorphicOn
        (isCompact_closedBall (0:ℂ) R) (Subset.refl _)
    refine h1.subset ?_
    intro u hu
    simp only [Function.mem_support] at hu ⊢
    intro h0
    refine hu ?_
    show (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) u : ℤ) : ℝ) = 0
    rw [h0]; simp
  have hDfs : Function.HasFiniteSupport D := hDfin
  have hSmem : ∀ u, u ∈ hDfin.toFinset ↔ D u ≠ 0 := fun u =>
    hDfin.mem_toFinset.trans (by simp [Function.mem_support])
  -- bounds valid for the support elements
  have hLf : ∀ u, D u ≠ 0 → LFunction χ u = 0 := by
    intro u hu
    exact lfunction_zero_of_divisor_neLL hχ hχprim hu
  have hre : ∀ u, D u ≠ 0 → u.re ≤ 1 := by
    intro u hu
    exact (Commons.NumberTheory.DirichletCharacter.zerosInStrip χ hχ hχprim u
      (zero_of_divisor_neL hχ hu)).2.le
  have hnormR : ∀ u, D u ≠ 0 → ‖u‖ ≤ R := by
    intro u hu
    simpa [Metric.mem_closedBall, dist_eq_norm] using mem_ball_of_divisor_neL (χ := χ) hu
  -- the kernel bound
  have hker : ∀ u, D u ≠ 0 → ‖1/(s-u) - 1/(s₀-u)‖ ≤ phiK (‖s-u‖) := by
    intro u hu
    have hd : r ≤ ‖s - u‖ := hdist u (hLf u hu)
    have hnu : (1:ℝ) ≤ ‖s₀ - u‖ := re_le_norm_subL σ t u (hre u hu)
    have hΔ : ‖s₀ - s‖ = 2 - σ := by
      rw [hs₀def, hsdef]
      exact norm_sub_sqL (by linarith : σ ≤ 2)
    have hge : ‖s - u‖ - (2 - σ) ≤ ‖s₀ - u‖ := by
      have h := norm_sub_le (s₀ - u) (s₀ - s)
      have h2 : (s₀ - u) - (s₀ - s) = s - u := by ring
      rw [h2, hΔ] at h
      linarith
    have hmax : max 1 (‖s - u‖ - 2) ≤ ‖s₀ - u‖ := by
      apply max_le hnu
      linarith [hge, hσ1]
    have hpos : 0 < ‖s - u‖ := lt_of_lt_of_le hr hd
    have hspos : 0 < ‖s₀ - u‖ := lt_of_lt_of_le zero_lt_one hnu
    have hkey : ‖1/(s-u) - 1/(s₀-u)‖ = (2 - σ) / (‖s - u‖ * ‖s₀ - u‖) := by
      have h1 : s - u ≠ 0 := by
        intro h0
        have : ‖s - u‖ = 0 := by rw [h0]; simp
        linarith
      have h2 : s₀ - u ≠ 0 := by
        intro h0
        have : ‖s₀ - u‖ = 0 := by rw [h0]; simp
        linarith
      rw [show 1/(s-u) - 1/(s₀-u) = (s₀ - s)/((s-u)*(s₀-u)) by
        field_simp; ring]
      rw [norm_div, norm_mul, hΔ]
    rw [hkey]
    unfold phiK
    have h2σ : 2 - σ ≤ 2 := by linarith
    have hden : 0 < ‖s - u‖ * max 1 (‖s - u‖ - 2) := mul_pos hpos (by positivity)
    rw [div_le_div_iff₀ (mul_pos hpos hspos) hden]
    have h1 : (2 - σ) * (‖s - u‖ * max 1 (‖s - u‖ - 2))
        ≤ 2 * (‖s - u‖ * max 1 (‖s - u‖ - 2)) :=
      mul_le_mul_of_nonneg_right h2σ (by positivity)
    have h2 : 2 * (‖s - u‖ * max 1 (‖s - u‖ - 2)) ≤ 2 * (‖s - u‖ * ‖s₀ - u‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmax (norm_nonneg _)) (by norm_num)
    linarith
  -- choose `J` so that `2^(J+1) r` exceeds `R + ‖s‖`
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, R + ‖s‖ < (2:ℝ)^(J+1) * r := by
    obtain ⟨m, hm⟩ : ∃ m : ℕ, (R + ‖s‖)/r < (2:ℝ)^m := by
      obtain ⟨k, hk⟩ := exists_nat_gt ((R + ‖s‖)/r)
      exact ⟨k, lt_of_lt_of_le hk (by exact_mod_cast (Nat.lt_two_pow_self (n := k)).le)⟩
    refine ⟨m, ?_⟩
    have hrw : (R + ‖s‖) < (2:ℝ)^m * r := by
      rw [div_lt_iff₀ hr] at hm; exact hm
    have h2m : (2:ℝ)^m ≤ (2:ℝ)^(m+1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have := mul_le_mul_of_nonneg_right h2m hr.le
    linarith
  have hsupp_lt : ∀ u, D u ≠ 0 → ‖s - u‖ < (2:ℝ)^(J+1) * r := by
    intro u hu
    have h1 : ‖s - u‖ ≤ ‖s‖ + ‖u‖ := norm_sub_le _ _
    have h2 := hnormR u hu
    linarith
  -- counting comparison
  have hcnt_comp : ∀ X : ℝ, (∑ u ∈ hDfin.toFinset, D u * (if ‖s - u‖ < X then (1:ℝ) else 0))
      ≤ cntK χ s X := by
    intro X
    have hls : Function.HasFiniteSupport (fun u : ℂ => D u * (if ‖s - u‖ < X then (1:ℝ) else 0)) :=
      hDfs.subset (fun u hu => by
        simp only [Function.mem_support] at hu ⊢
        intro h0; exact hu (by rw [h0, zero_mul]))
    have hls' : (Function.support (fun u : ℂ => D u * (if ‖s - u‖ < X then (1:ℝ) else 0))).Finite :=
      hls
    rw [← finsum_eq_sum_of_support_subset (fun u : ℂ => D u * (if ‖s - u‖ < X then (1:ℝ) else 0))
      (s := hDfin.toFinset) (by
        intro u hu
        simp only [Function.mem_support] at hu
        exact hDfin.mem_toFinset.mpr (by
          rw [Function.mem_support]
          intro h0
          exact hu (by rw [h0, zero_mul])))]
    refine finsum_le_finsum' hls (cnt_finite χ hχ s X) (fun u => ?_)
    by_cases hu : D u = 0
    · rw [hu, zero_mul]
      have h1 := divisor_nonnegL (analyticOnNhd_completedLL χ hχ (Metric.closedBall s X)) (z := u)
      change (0:ℝ) ≤ ((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall s X) u : ℤ) : ℝ)
      exact_mod_cast h1
    · by_cases hX : ‖s - u‖ < X
      · rw [if_pos hX, mul_one]
        have huX : u ∈ Metric.closedBall s X := by
          rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev]; exact hX.le
        have hmem : u ∈ Metric.closedBall (0:ℂ) R := mem_ball_of_divisor_neL (χ := χ) hu
        show (((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall 0 R)) u : ℤ) : ℝ)
          ≤ ((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall s X) u : ℤ) : ℝ)
        rw [divisor_eq_orderNatL (analyticOnNhd_completedLL χ hχ _) hmem,
          divisor_eq_orderNatL (analyticOnNhd_completedLL χ hχ _) huX]
      · rw [if_neg hX, mul_zero]
        have h1 := divisor_nonnegL (analyticOnNhd_completedLL χ hχ (Metric.closedBall s X)) (z := u)
        change (0:ℝ) ≤ ((MeromorphicOn.divisor (completedLFunction χ) (Metric.closedBall s X) u : ℤ) : ℝ)
        exact_mod_cast h1
  -- main chain
  have hsecond : (∑ u ∈ hDfin.toFinset, D u * phiK (‖s-u‖)) ≤
      (∑ j ∈ Finset.range J, (phiK (2^j * r) - phiK (2^(j+1) * r)) * cntK χ s ((2:ℝ)^(j+1) * r))
        + phiK ((2:ℝ)^J * r) * cntK χ s ((2:ℝ)^(J+1) * r) := by
    have hpt : ∀ u ∈ hDfin.toFinset, D u * phiK (‖s-u‖) ≤ D u *
        ((∑ j ∈ Finset.range J, (phiK (2^j * r) - phiK (2^(j+1) * r)) *
            (if ‖s-u‖ < (2:ℝ)^(j+1) * r then (1:ℝ) else 0)) + phiK ((2:ℝ)^J * r)) := by
      intro u hu
      have hu' : D u ≠ 0 := (hSmem u).mp hu
      exact mul_le_mul_of_nonneg_left
        (layer_cake_phi hr (hdist u (hLf u hu')) (hsupp_lt u hu')) (hDnn u)
    calc (∑ u ∈ hDfin.toFinset, D u * phiK (‖s-u‖))
        ≤ ∑ u ∈ hDfin.toFinset, D u * ((∑ j ∈ Finset.range J, (phiK (2^j * r) - phiK (2^(j+1) * r)) *
            (if ‖s-u‖ < (2:ℝ)^(j+1) * r then (1:ℝ) else 0)) + phiK ((2:ℝ)^J * r)) :=
          Finset.sum_le_sum hpt
      _ = (∑ j ∈ Finset.range J, (phiK (2^j * r) - phiK (2^(j+1) * r)) *
              (∑ u ∈ hDfin.toFinset, D u * (if ‖s-u‖ < (2:ℝ)^(j+1) * r then (1:ℝ) else 0)))
            + phiK ((2:ℝ)^J * r) * (∑ u ∈ hDfin.toFinset, D u) := by
          have h0 : ∀ u : ℂ, D u * ((∑ j ∈ Finset.range J, (phiK (2^j * r) - phiK (2^(j+1) * r)) *
                (if ‖s-u‖ < (2:ℝ)^(j+1) * r then (1:ℝ) else 0)) + phiK ((2:ℝ)^J * r))
              = D u * (∑ j ∈ Finset.range J, (phiK (2^j * r) - phiK (2^(j+1) * r)) *
                (if ‖s-u‖ < (2:ℝ)^(j+1) * r then (1:ℝ) else 0))
                + D u * phiK ((2:ℝ)^J * r) := fun u => by ring
          rw [Finset.sum_congr rfl (fun u _ => h0 u), Finset.sum_add_distrib]
          congr 1
          · have h1 : ∀ u : ℂ, D u * (∑ j ∈ Finset.range J, (phiK (2^j * r) - phiK (2^(j+1) * r)) *
                (if ‖s-u‖ < (2:ℝ)^(j+1) * r then (1:ℝ) else 0))
                = ∑ j ∈ Finset.range J, D u * ((phiK (2^j * r) - phiK (2^(j+1) * r)) *
                    (if ‖s-u‖ < (2:ℝ)^(j+1) * r then (1:ℝ) else 0)) := by
              intro u; rw [Finset.mul_sum]
            rw [Finset.sum_congr rfl (fun u _ => h1 u), Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro j hj
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro u hu
            ring
          · rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro u hu
            ring
      _ ≤ (∑ j ∈ Finset.range J, (phiK (2^j * r) - phiK (2^(j+1) * r)) *
              cntK χ s ((2:ℝ)^(j+1) * r))
            + phiK ((2:ℝ)^J * r) * cntK χ s ((2:ℝ)^(J+1) * r) := by
          apply add_le_add
          · apply Finset.sum_le_sum
            intro j hj
            have hnn : 0 ≤ phiK (2^j * r) - phiK (2^(j+1) * r) := by
              have h1 : phiK ((2:ℝ)^(j+1) * r) ≤ phiK ((2:ℝ)^j * r) :=
                phi_antitoneOn (show (0:ℝ) < (2:ℝ)^j * r by positivity)
                  (show (0:ℝ) < (2:ℝ)^(j+1) * r by positivity)
                  (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) hr.le)
              linarith
            exact mul_le_mul_of_nonneg_left (hcnt_comp _) hnn
          · have hnn : 0 ≤ phiK ((2:ℝ)^J * r) := phi_nonneg (by positivity)
            have hsum : (∑ u ∈ hDfin.toFinset, D u) ≤ cntK χ s ((2:ℝ)^(J+1) * r) := by
              have h := hcnt_comp ((2:ℝ)^(J+1) * r)
              have h1 : (∑ u ∈ hDfin.toFinset,
                    D u * (if ‖s - u‖ < (2:ℝ)^(J+1) * r then (1:ℝ) else 0))
                  = ∑ u ∈ hDfin.toFinset, D u := by
                apply Finset.sum_congr rfl
                intro u hu
                rw [if_pos (hsupp_lt u ((hSmem u).mp hu)), mul_one]
              rw [h1] at h
              exact h
            exact mul_le_mul_of_nonneg_left hsum hnn
  -- dyadic estimate
  have hdy := dyadic_sum_bound_phi hr hr1 hL1 hc0 (fun j => cnt_nonneg χ hχ s _)
      (fun j hj => (hcnt χ hχ hχprim s ((2:ℝ)^(j+1) * r)).1 hj)
      (fun j hj => (hcnt χ hχ hχprim s ((2:ℝ)^(j+1) * r)).2 hj) J
  -- padding term
  have hpad : phiK ((2:ℝ)^J * r) * cntK χ s ((2:ℝ)^(J+1) * r) ≤ 100 * c * L := by
    set u : ℝ := (2:ℝ)^J * r with hudef
    have hu2 : (2:ℝ)^(J+1) * r = 2 * u := by rw [hudef, pow_succ]; ring
    have hX2 : 2 ≤ 2 * u := by
      rw [hu2] at hJ
      have h1 : R + ‖s‖ < 2 * u := hJ
      have h2 : 0 ≤ ‖s‖ := norm_nonneg s
      linarith
    have hupos : 0 < u := by linarith
    rw [hu2]
    have hcnt2 : cntK χ s (2 * u) ≤ c * (2*u + 1) * (L + Real.log (2*u + 1)) := by
      have h0 := (hcnt χ hχ hχprim s (2*u)).2 (by linarith)
      have hL' : L = Real.log (‖s‖ + 2) + Real.log (N:ℝ) + 2 := hLdef
      rw [hL']
      exact h0
    have hvarphi : phiK u ≤ 2 / u := phi_le_two_div hupos
    have hphi0 : 0 ≤ phiK u := phi_nonneg hupos
    have hlog : Real.log (2*u + 1) ≤ 3*u := by
      have h1 : Real.log (2*u + 1) ≤ 2*u := by
        have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2*u+1 by linarith)
        linarith
      linarith
    have hLnn : 0 ≤ L := le_trans zero_le_one hL1
    have hlog7 : Real.log 7 ≤ 3 := by
      have h1 : Real.log (7:ℝ) ≤ Real.log 8 := Real.log_le_log (by norm_num) (by norm_num)
      have h2 : Real.log (8:ℝ) = 3 * Real.log 2 := by
        rw [show (8:ℝ) = 2^3 by norm_num, Real.log_pow]; norm_num
      have h3 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
      rw [h2] at h1; linarith
    by_cases h3 : u ≤ 3
    · have hcnt3 : cntK χ s (2*u) ≤ c * (3*u) * (L + Real.log 7) := by
        refine le_trans hcnt2 ?_
        have hA : c * (2*u + 1) ≤ c * (3*u) :=
          mul_le_mul_of_nonneg_left (by linarith) hc0
        have hB : L + Real.log (2*u + 1) ≤ L + Real.log 7 := by
          have h5 : Real.log (2*u + 1) ≤ Real.log 7 := Real.log_le_log (by linarith) (by linarith)
          linarith
        have hC : 0 ≤ L + Real.log (2*u + 1) := by
          have h6 : 0 ≤ Real.log (2*u+1) := Real.log_nonneg (by linarith)
          linarith
        exact mul_le_mul hA hB hC (by positivity)
      calc phiK u * cntK χ s (2*u) ≤ (2/u) * (c * (3*u) * (L + Real.log 7)) :=
            mul_le_mul hvarphi hcnt3 (cnt_nonneg χ hχ s _) (by positivity)
        _ = 6 * c * (L + Real.log 7) := by field_simp; ring
        _ ≤ 100 * c * L := by nlinarith [hc0, hLnn, hlog7]
    · have hu3 : 3 ≤ u := le_of_lt (not_le.mp h3)
      have hquad : phiK u ≤ 6 / u^2 := phi_le_quad hu3
      have hcnt3 : cntK χ s (2*u) ≤ c * (3*u) * (L + 3*u) := by
        refine le_trans hcnt2 ?_
        have hA : c * (2*u + 1) ≤ c * (3*u) :=
          mul_le_mul_of_nonneg_left (by linarith) hc0
        have hB : L + Real.log (2*u + 1) ≤ L + 3*u := by linarith
        have hC : 0 ≤ L + Real.log (2*u + 1) := by
          have h6 : 0 ≤ Real.log (2*u+1) := Real.log_nonneg (by linarith)
          linarith
        exact mul_le_mul hA hB hC (by positivity)
      calc phiK u * cntK χ s (2*u) ≤ (6/u^2) * (c * (3*u) * (L + 3*u)) :=
            mul_le_mul hquad hcnt3 (cnt_nonneg χ hχ s _) (by positivity)
        _ = 18 * c * (L + 3*u)/u := by field_simp; ring
        _ ≤ 100 * c * L := by
            have h2 : (L + 3*u)/u ≤ 4 * L := by
              rw [div_le_iff₀ hupos]
              nlinarith [hu3, hupos, hLnn, sq_nonneg u]
            have h4 : 18 * c * ((L + 3*u)/u) ≤ 18 * c * (4*L) :=
              mul_le_mul_of_nonneg_left h2 (by positivity)
            have h5 : 18 * c * (L + 3*u)/u = 18 * c * ((L+3*u)/u) := by ring
            nlinarith [h4, hc0, h5]
  -- assemble
  have hmain : (∑ᶠ u : ℂ, D u * ‖1/(s-u) - 1/(s₀-u)‖) ≤ 3000 * c * (1 + 1/r) * L := by
    rw [finsum_eq_sum_of_support_subset _
      (s := hDfin.toFinset) (by
        intro u hu
        simp only [Function.mem_support] at hu
        exact hDfin.mem_toFinset.mpr (by
          rw [Function.mem_support]
          intro h0
          exact hu (by rw [h0, zero_mul])))]
    calc (∑ u ∈ hDfin.toFinset, D u * ‖1/(s-u) - 1/(s₀-u)‖)
        ≤ ∑ u ∈ hDfin.toFinset, D u * phiK (‖s-u‖) :=
          Finset.sum_le_sum (fun u hu => mul_le_mul_of_nonneg_left (hker u ((hSmem u).mp hu)) (hDnn u))
      _ ≤ _ := hsecond
      _ ≤ 2000 * c * L * (1 + 1/r) + 100 * c * L := add_le_add hdy hpad
      _ ≤ 3000 * c * (1 + 1/r) * L := by
          have hcL : 0 ≤ c * L := mul_nonneg hc0 (le_trans zero_le_one hL1)
          have h1 : (1:ℝ) ≤ 1 + 1/r := by have := one_div_pos.mpr hr; linarith
          have h2 : 2000 * c * L * (1 + 1/r) + 100 * c * L
              = c * L * (2000 * (1 + 1/r) + 100) := by ring
          rw [h2]
          have h3 : 2000 * (1 + 1/r) + 100 ≤ 3000 * (1 + 1/r) := by linarith
          calc c * L * (2000 * (1 + 1/r) + 100) ≤ c * L * (3000 * (1 + 1/r)) :=
                mul_le_mul_of_nonneg_left h3 hcL
            _ = 3000 * c * (1 + 1/r) * L := by ring
  rw [hLdef] at hmain
  exact hmain

lemma completedL_eq_mul_gammaFactorL {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 0 < s.re) : completedLFunction χ s = LFunction χ s * gammaFactor χ s := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    simp at hs
  have hL := LFunction_eq_completed_div_gammaFactor χ s (Or.inl hs0)
  have hg : gammaFactor χ s ≠ 0 :=
    Commons.NumberTheory.DirichletCharacter.gammaFactor_ne_zero_of_re_pos χ s hs
  rw [hL]
  field_simp

/-- **Logarithmic-derivative bound** for `L(·,χ)` off its zeros. -/
theorem logDeriv_bound_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N),
      χ.IsPrimitive → χ ≠ 1 → ∀ σ t r : ℝ, 1/2 ≤ σ → σ ≤ 5/4 → 0 < r → r ≤ 1 →
      (∀ ρ : ℂ, LFunction χ ρ = 0 → r ≤ ‖((σ:ℂ) + (t:ℂ)*I) - ρ‖) →
      ‖logDeriv (LFunction χ) ((σ:ℂ) + (t:ℂ)*I)‖ ≤
        C * (1 + 1/r) * (Real.log ((N:ℝ) * (|t| + 2)) + 1) := by
  obtain ⟨Ck, hCk, hkernel⟩ := kernel_sum_boundL
  refine ⟨4 * Ck + 50, by positivity, ?_⟩
  intro N _ χ hχprim hχ1 σ t r hσ1 hσ2 hr hr1 hdist
  have hχ : χ ≠ 1 := hχ1
  set s : ℂ := (σ:ℂ) + (t:ℂ)*I with hsdef
  set s₀ : ℂ := (2:ℂ) + (t:ℂ)*I with hs₀def
  have hsre : 0 < s.re := by rw [hsdef]; simp; linarith
  have hLs : LFunction χ s ≠ 0 := by
    intro h0
    have h1 := hdist s h0
    have h2 : ‖s - s‖ = 0 := by simp
    rw [h2] at h1
    linarith
  have hΛs : completedLFunction χ s ≠ 0 := by
    have h1 : completedLFunction χ s = LFunction χ s * gammaFactor χ s :=
      completedL_eq_mul_gammaFactorL χ hsre
    rw [h1]
    exact mul_ne_zero hLs
      (Commons.NumberTheory.DirichletCharacter.gammaFactor_ne_zero_of_re_pos χ s hsre)
  have hΛs₀ : completedLFunction χ s₀ ≠ 0 := by
    intro h0
    have h1 := (Commons.NumberTheory.DirichletCharacter.zerosInStrip χ hχ hχprim s₀ h0).2
    rw [hs₀def] at h1
    simp at h1
  set L' : ℝ := Real.log (‖s‖ + 2) + Real.log (N:ℝ) + 2 with hL'def
  have hpf : ‖logDeriv (completedLFunction χ) s - logDeriv (completedLFunction χ) s₀‖
      ≤ Ck * (1 + 1/r) * L' := by
    refine Commons.NumberTheory.DirichletCharacter.completedL_pf_diff_norm_le χ hχ hχprim s s₀
      hΛs hΛs₀ _ (fun R hR => ?_)
    have h := hkernel χ hχ hχprim σ t r R hσ1 hσ2 hr hr1 hR hdist
    rw [hsdef, hs₀def, hL'def]
    exact h
  have htwo : ‖logDeriv (completedLFunction χ) s₀‖ ≤ Real.log (2 + |t|) + 20 := by
    rw [hs₀def]
    have h := Commons.NumberTheory.DirichletCharacter.completedLogDeriv_two_le χ hχ t
    simpa [mul_comm] using h
  have hgam : ‖logDeriv (gammaFactor χ) s‖
      ≤ Real.log Real.pi / 2 + (1/2 : ℝ) * (Real.log (2 + |t|) + 8) := by
    rcases χ.even_or_odd with hE | hO
    · have hfun : gammaFactor χ = Complex.Gammaℝ := by funext z; exact hE.gammaFactor_def z
      have h := Commons.NumberTheory.DirichletCharacter.norm_logDeriv_Gammaℝ_le σ t hσ1
        (by linarith : σ ≤ 16)
      rw [hfun, hsdef]
      rw [mul_comm (t:ℂ) Complex.I]
      exact h
    · have hfun : gammaFactor χ = fun z : ℂ => Complex.Gammaℝ (z + 1) := by
        funext z; exact hO.gammaFactor_def z
      have hcomp : logDeriv (fun z : ℂ => Complex.Gammaℝ (z + 1)) s
          = logDeriv Complex.Gammaℝ (s + 1) := by
        rw [show (fun z : ℂ => Complex.Gammaℝ (z + 1))
            = Complex.Gammaℝ ∘ (fun z : ℂ => z + 1) from rfl]
        rw [logDeriv_comp (f := Complex.Gammaℝ) (g := fun z : ℂ => z + 1) (x := s)]
        · simp
        · exact Commons.NumberTheory.DirichletCharacter.differentiableAt_Gammaℝ (s+1) (by
            rw [Complex.add_re]; simp; linarith [hsre])
        · fun_prop
      have hstream : s + 1 = ((σ+1 : ℝ) : ℂ) + (t:ℂ)*I := by
        rw [hsdef]
        apply Complex.ext <;> simp <;> ring
      rw [hfun, hcomp, hstream, mul_comm (t:ℂ) Complex.I]
      exact Commons.NumberTheory.DirichletCharacter.norm_logDeriv_Gammaℝ_le (σ+1) t
        (by linarith) (by linarith)
  have hdec : logDeriv (completedLFunction χ) s
      = logDeriv (LFunction χ) s + logDeriv (gammaFactor χ) s :=
    Commons.NumberTheory.DirichletCharacter.logDeriv_completedLFunction_eq_add χ hχ s hsre hLs
  have hnormΛ : ‖logDeriv (completedLFunction χ) s‖
      ≤ (Real.log (2 + |t|) + 20) + Ck * (1 + 1/r) * L' := by
    have h1 : logDeriv (completedLFunction χ) s
        = logDeriv (completedLFunction χ) s₀
          + (logDeriv (completedLFunction χ) s - logDeriv (completedLFunction χ) s₀) := by ring
    rw [h1]
    have h2 : ‖logDeriv (completedLFunction χ) s₀
            + (logDeriv (completedLFunction χ) s - logDeriv (completedLFunction χ) s₀)‖
        ≤ ‖logDeriv (completedLFunction χ) s₀‖
            + ‖logDeriv (completedLFunction χ) s - logDeriv (completedLFunction χ) s₀‖ :=
      norm_add_le _ _
    linarith [h2, htwo, hpf]
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hlogN1 : 0 ≤ Real.log ((N:ℝ) * (|t| + 2)) := by
    apply Real.log_nonneg; nlinarith [abs_nonneg t, hN1]
  have hℓ1 : 1 ≤ Real.log ((N:ℝ) * (|t| + 2)) + 1 := by linarith
  have hsle : ‖s‖ ≤ |t| + 5/4 := by
    rw [hsdef]
    have h1 : ‖(σ:ℂ) + (t:ℂ)*I‖ ≤ |σ| + |t| := by
      calc ‖(σ:ℂ) + (t:ℂ)*I‖ ≤ ‖(σ:ℂ)‖ + ‖(t:ℂ)*I‖ := norm_add_le _ _
        _ = |σ| + |t| := by simp
    have h2 : |σ| = σ := abs_of_nonneg (by linarith)
    linarith
  have hlogs : Real.log (‖s‖ + 2) ≤ Real.log ((N:ℝ) * (|t| + 2)) + 1 := by
    have h2 : ‖s‖ + 2 ≤ 2 * ((N:ℝ) * (|t| + 2)) := by nlinarith [abs_nonneg t, hN1]
    have h3 := Real.log_le_log (by positivity : (0:ℝ) < ‖s‖ + 2) h2
    rw [Real.log_mul (by norm_num) (by positivity : ((N:ℝ) * (|t|+2)) ≠ 0)] at h3
    have h4 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
    linarith
  have hlogN : Real.log (N:ℝ) ≤ Real.log ((N:ℝ) * (|t| + 2)) := by
    apply Real.log_le_log (by positivity)
    nlinarith [abs_nonneg t, hN1]
  have hL'le : L' ≤ 4 * (Real.log ((N:ℝ) * (|t| + 2)) + 1) := by
    rw [hL'def]; linarith
  have hlogt : Real.log (2 + |t|) ≤ Real.log ((N:ℝ) * (|t| + 2)) + 1 := by
    have h1 : Real.log (2 + |t|) ≤ Real.log ((N:ℝ) * (|t| + 2)) := by
      apply Real.log_le_log (by linarith [abs_nonneg t])
      nlinarith [abs_nonneg t, hN1]
    linarith
  have h1 : logDeriv (LFunction χ) s
      = logDeriv (completedLFunction χ) s - logDeriv (gammaFactor χ) s := by
    rw [hdec]; ring
  rw [h1]
  have h2 : ‖logDeriv (completedLFunction χ) s - logDeriv (gammaFactor χ) s‖
      ≤ ‖logDeriv (completedLFunction χ) s‖ + ‖logDeriv (gammaFactor χ) s‖ := norm_sub_le _ _
  have h3 : ‖logDeriv (completedLFunction χ) s‖ + ‖logDeriv (gammaFactor χ) s‖
      ≤ (4 * Ck + 50) * (1 + 1/r) * (Real.log ((N:ℝ) * (|t| + 2)) + 1) := by
    have hA : Ck * (1 + 1/r) * L' ≤ Ck * (1 + 1/r) * (4 * (Real.log ((N:ℝ) * (|t| + 2)) + 1)) :=
      mul_le_mul_of_nonneg_left hL'le (by positivity)
    have hB : Real.log (2 + |t|) + 20 ≤ 25 * (Real.log ((N:ℝ) * (|t| + 2)) + 1) := by
      linarith [hlogt, hℓ1]
    have hC : Real.log Real.pi / 2 + (1/2 : ℝ) * (Real.log (2 + |t|) + 8)
        ≤ 20 * (Real.log ((N:ℝ) * (|t| + 2)) + 1) := by
      have hpi : Real.log Real.pi ≤ 4 := by
        have h1 := Real.log_le_sub_one_of_pos Real.pi_pos
        linarith [Real.pi_lt_four]
      linarith [hlogt, hℓ1]
    have hD : (Real.log (2 + |t|) + 20) + Ck * (1 + 1/r) * L'
        ≤ (Real.log (2 + |t|) + 20)
          + Ck * (1 + 1/r) * (4 * (Real.log ((N:ℝ) * (|t| + 2)) + 1)) := by linarith [hA]
    have key : Ck * (1 + 1/r) * (4 * (Real.log ((N:ℝ) * (|t| + 2)) + 1))
          + 25 * (Real.log ((N:ℝ) * (|t| + 2)) + 1)
          + 20 * (Real.log ((N:ℝ) * (|t| + 2)) + 1)
        ≤ (4 * Ck + 50) * (1 + 1/r) * (Real.log ((N:ℝ) * (|t| + 2)) + 1) := by
      have hp1 : (1:ℝ) ≤ 1 + 1/r := by
        have := one_div_pos.mpr hr; linarith
      have h45 : (45:ℝ) * (Real.log ((N:ℝ) * (|t| + 2)) + 1)
          ≤ 50 * (1 + 1/r) * (Real.log ((N:ℝ) * (|t| + 2)) + 1) := by
        apply mul_le_mul_of_nonneg_right _ (le_trans zero_le_one hℓ1)
        linarith
      nlinarith [h45]
    have hsum : ‖logDeriv (completedLFunction χ) s‖ + ‖logDeriv (gammaFactor χ) s‖
        ≤ Ck * (1 + 1/r) * (4 * (Real.log ((N:ℝ) * (|t| + 2)) + 1))
          + 25 * (Real.log ((N:ℝ) * (|t| + 2)) + 1)
          + 20 * (Real.log ((N:ℝ) * (|t| + 2)) + 1) := by
      have hD' : ‖logDeriv (completedLFunction χ) s‖
          ≤ 25 * (Real.log ((N:ℝ) * (|t| + 2)) + 1)
            + Ck * (1 + 1/r) * (4 * (Real.log ((N:ℝ) * (|t| + 2)) + 1)) := by
        linarith [hnormΛ, hD, hB]
      linarith [hD', hC]
    linarith [hsum, key]
  linarith [h2, h3]



/-! ## The target statement

The Siegel–Walfisz estimate for primitive non-principal characters, proved from the
engine above, the uniform logarithmic-derivative bound `logDeriv_bound_uniform`, and the
published uniform zero-free inputs. -/

theorem siegel_walfisz_chi :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧
    ∀ᶠ x : ℕ in Filter.atTop,
      ∀ {q : ℕ} [NeZero q], q ≤ ⌊(Real.log (x:ℝ)) ^ C⌋₊ →
      ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → χ ≠ 1 →
        ‖∑ n ∈ Finset.range (x+1),
            ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q)‖ ≤
          (x:ℝ) / (Real.log (x:ℝ))^A := by
  obtain ⟨C, hC, hPerr⟩ := chiPerron_uniform_bound
  exact siegel_walfisz_chi_of_two_inputs ⟨C, hC, hPerr⟩ logDeriv_bound_uniform

end

end Commons.NumberTheory.BombieriVinogradov
