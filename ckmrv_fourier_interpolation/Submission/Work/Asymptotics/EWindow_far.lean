import Mathlib
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.EWindowAux
import Submission.Work.Asymptotics.Xi8_bound_E
import Submission.Work.Asymptotics.Xi24_bound_E
import Submission.Work.Asymptotics.Xi8_eq
import Submission.Work.Asymptotics.Xi24_eq
import Submission.Work.Asymptotics.Xi8_low_bound
import Submission.Work.Asymptotics.Xi24_low_bound
import Submission.Work.Asymptotics.KMinusCuspBallDefs
import Submission.Work.Asymptotics.DeltaFun_imagAxis_atZero
import Submission.Work.Asymptotics.E_jdiff_large
import Submission.Work.Asymptotics.DeltaFun_imagAxis_lower_sharp
import Submission.Work.Asymptotics.EpolyWindowE_Ncusp

namespace Work.Asymptotics

noncomputable section

open UpperHalfPlane ModularGroup
open scoped MatrixGroups UpperHalfPlane

set_option maxHeartbeats 20000000

/-! ## Auxiliary facts -/

/-- `imagAxis` depends on its real parameter only. -/
lemma imagAxis_eq_of_eq (r : ℝ) (h₁ h₂ : 0 < r) :
    Work.Kernels.imagAxis r h₁ = Work.Kernels.imagAxis r h₂ := rfl

/-- A positive lower bound for the divisor forces the non-coincidence `j w ≠ j z`. -/
lemma jInvariantFun_ne_of_divisor_pos {w z : UpperHalfPlane} {c : ℝ} (hc : 0 < c)
    (h : c ≤ ‖Work.Kernels.DeltaFun z *
      (Work.Kernels.jInvariantFun w - Work.Kernels.jInvariantFun z)‖) :
    Work.Kernels.jInvariantFun w ≠ Work.Kernels.jInvariantFun z := by
  intro hEq
  rw [hEq, sub_self, mul_zero, norm_zero] at h
  linarith

/-- The norm of `imagAxis s` is `s`. -/
lemma norm_imagAxis' (s : ℝ) (hs : 0 < s) :
    ‖((Work.Kernels.imagAxis s hs : UpperHalfPlane) : ℂ)‖ = s := by
  show ‖(s : ℂ) * Complex.I‖ = s
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]

/-- `S • (i/t) = i t`. -/
lemma S_smul_imagAxis_inv' (t : ℝ) (ht : 0 < t) :
    ModularGroup.S • Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht)
      = Work.Kernels.imagAxis t ht := by
  apply UpperHalfPlane.ext
  rw [Work.Kernels.S_smul_coe]
  show (-(((Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht) : UpperHalfPlane)) : ℂ)⁻¹)
      = ((Work.Kernels.imagAxis t ht : UpperHalfPlane) : ℂ)
  simp only [Work.Kernels.imagAxis]
  rw [mul_inv, Complex.inv_I, ← Complex.ofReal_inv, inv_inv]
  push_cast
  ring

/-- **The divisor stays away from `0` on the contour `i/t` for `1 ≤ t ≤ Im(S•w) − 1`.**

For `w ∈ E = KEpsilon` and `1 ≤ t ≤ Im (S • w) − 1` the CKMRV divisor `Δ(i/t)·(j w − j(i/t))` is
bounded below by a positive constant.  This is the "below the pole" twin of
`Work.Asymptotics.divisor_lower_E` (which covers `t ≤ 1` under a separation hypothesis): the
contour point `i/t` has height `1/t ≤ 1`, while the only orbit points of `w` of height `> 1/2`
are the translates of `S • w` of height `≥ t + 1`, so no separation hypothesis is needed.

The proof combines `Work.Asymptotics.E_jdiff_large`
(`c·e^{2π Im(S•w)}·‖1 − e^{2πi((S•w) − i t)}‖ ≤ ‖j w − j (i t)‖`) with
`‖1 − e^{2πi((S•w) − i t)}‖ ≥ 1/2` (the modulus of that exponential is `e^{2π(t − Im(S•w))} ≤ e^{−2π}`)
and `Work.Asymptotics.DeltaFun_imagAxis_lower_sharp` (`‖Δ(i t)‖ ≥ e^{−2πt}/2`), reading the
divisor through the `S`-laws `Δ(i/t) = t^{12}Δ(i t)` and `j (i/t) = j (i t)`. -/
lemma divisor_lower_lowIm :
    ∃ c : ℝ, 0 < c ∧ ∀ (w : UpperHalfPlane) (t : ℝ) (ht : 0 < t),
      w ∈ KEpsilon → 1 ≤ t → t ≤ (ModularGroup.S • w).im - 1 →
        c ≤ ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht)) *
              (Work.Kernels.jInvariantFun w -
                Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht)))‖ := by
  obtain ⟨c, hc, hD⟩ := Work.Asymptotics.E_jdiff_large
  refine ⟨c / 4, by positivity, ?_⟩
  intro w t ht hw ht1 hfar
  -- the `S`-laws identifying the divisor at `i/t` with the one at `i t`
  have hSzi : ModularGroup.S • Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht)
      = Work.Kernels.imagAxis t ht := S_smul_imagAxis_inv' t ht
  have hjz : Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht))
      = Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) := by
    have h := (Work.Kernels.KernelFacts.jInvariantFun_S_smul
      (Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht))).symm
    rw [hSzi] at h; exact h
  have hΔ : Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)
      = (((Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht) : UpperHalfPlane)) : ℂ) ^ 12 *
          Work.Kernels.DeltaFun (Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht)) := by
    have h := Work.Kernels.KernelFacts.smul_of_slash_inv Work.Kernels.KernelFacts.DeltaFun_S_slash
      (Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht))
    rwa [hSzi] at h
  have hΔn : ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht))‖
      = t ^ 12 * ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ := by
    have h2 : ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖
        = (t⁻¹ : ℝ) ^ 12 *
            ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht))‖ := by
      rw [hΔ, norm_mul, norm_pow, norm_imagAxis' t⁻¹ (inv_pos.mpr ht)]
    have h5 : (t⁻¹ : ℝ) ^ 12 = (t ^ 12)⁻¹ := by rw [inv_pow]
    rw [h5] at h2
    have h6 : (t ^ 12 : ℝ) * ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖
        = ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht))‖ := by
      rw [h2]; field_simp
    exact h6.symm
  -- the exponential factor `‖1 − e^{2πi((S•w) − i t)}‖ ≥ 1/2`
  set z : ℂ := Complex.exp (2 * Real.pi * Complex.I *
    ((((ModularGroup.S • w : UpperHalfPlane)) : ℂ) - ((t : ℂ) * Complex.I))) with hz
  have hExp : (1 : ℝ) / 2 ≤ ‖1 - z‖ := by
    have hzn : ‖z‖ = Real.exp (2 * Real.pi * (t - (ModularGroup.S • w).im)) := by
      rw [hz, Complex.norm_exp]
      congr 1
      simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, Complex.sub_re, Complex.sub_im, UpperHalfPlane.coe_im,
        UpperHalfPlane.coe_re]
      norm_num
      ring
    have hle : ‖z‖ ≤ Real.exp (-(2 * Real.pi)) := by
      rw [hzn]
      apply Real.exp_le_exp.mpr
      nlinarith [Real.pi_pos, hfar]
    have h2 : Real.exp (-(2 * Real.pi)) ≤ 1 / 2 := by
      have h6 : (2 : ℝ) ≤ Real.exp (2 * Real.pi) := by
        have h4 : (7 : ℝ) ≤ Real.exp 2 := by
          have h5 : (2.7182818283 : ℝ) ≤ Real.exp 1 := le_of_lt Real.exp_one_gt_d9
          calc (7 : ℝ) ≤ (2.7182818283 : ℝ) ^ 2 := by norm_num
            _ ≤ (Real.exp 1) ^ 2 := pow_le_pow_left₀ (by norm_num) h5 2
            _ = Real.exp 2 := by
                rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
        have h5' : Real.exp 2 ≤ Real.exp (2 * Real.pi) :=
          Real.exp_le_exp.mpr (by nlinarith [Real.pi_gt_three])
        linarith
      have h7 : (Real.exp (2 * Real.pi))⁻¹ ≤ (2 : ℝ)⁻¹ :=
        (inv_le_inv₀ (Real.exp_pos _) (by norm_num : (0 : ℝ) < 2)).mpr h6
      rw [Real.exp_neg]
      simpa using h7
    have h8 : (1 : ℝ) - ‖z‖ ≤ ‖(1 : ℂ) - z‖ := by
      have h := norm_sub_norm_le (1 : ℂ) z
      rwa [norm_one] at h
    linarith
  -- the `j`-difference lower bound
  have hJ := hD w t ht hw ht1
  rw [← hz] at hJ
  have hJ' : c / 2 * Real.exp (2 * Real.pi * (ModularGroup.S • w).im)
      ≤ ‖Work.Kernels.jInvariantFun w -
          Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖ := by
    have h1 : c * Real.exp (2 * Real.pi * (ModularGroup.S • w).im) * (1 / 2)
        ≤ c * Real.exp (2 * Real.pi * (ModularGroup.S • w).im) * ‖1 - z‖ :=
      mul_le_mul_of_nonneg_left hExp (by positivity)
    have h2 : c * Real.exp (2 * Real.pi * (ModularGroup.S • w).im) * (1 / 2)
        = c / 2 * Real.exp (2 * Real.pi * (ModularGroup.S • w).im) := by ring
    rw [h2] at h1
    exact h1.trans hJ
  -- the `Δ`-lower bound, and the assembly
  have hΔl : (1 : ℝ) / 2 * Real.exp (-(2 * Real.pi * t))
      ≤ ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ :=
    Work.Asymptotics.DeltaFun_imagAxis_lower_sharp t ht ht1
  have hprod : (1 : ℝ) / 2 * Real.exp (-(2 * Real.pi * t)) * (c / 2 *
        Real.exp (2 * Real.pi * (ModularGroup.S • w).im))
      ≤ ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht) *
          (Work.Kernels.jInvariantFun w -
            Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht))‖ := by
    have h1 : (1 : ℝ) / 2 * Real.exp (-(2 * Real.pi * t)) * (c / 2 *
          Real.exp (2 * Real.pi * (ModularGroup.S • w).im))
        ≤ ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ *
          ‖Work.Kernels.jInvariantFun w -
            Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖ := by
      have hA : (0 : ℝ) ≤ (1 : ℝ) / 2 * Real.exp (-(2 * Real.pi * t)) := by positivity
      have hB : (0 : ℝ) ≤ c / 2 * Real.exp (2 * Real.pi * (ModularGroup.S • w).im) := by
        positivity
      have hC : (0 : ℝ) ≤ ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ :=
        norm_nonneg _
      have hD : (0 : ℝ) ≤ ‖Work.Kernels.jInvariantFun w -
          Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖ := norm_nonneg _
      nlinarith [hΔl, hJ', hA, hB, hC, hD]
    rw [norm_mul]
    exact h1
  have hexp2 : (1 : ℝ) ≤ Real.exp (2 * Real.pi * ((ModularGroup.S • w).im - t)) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, hfar])
  have hge : c / 4 ≤ (1 : ℝ) / 2 * Real.exp (-(2 * Real.pi * t)) * (c / 2 *
      Real.exp (2 * Real.pi * (ModularGroup.S • w).im)) := by
    have he : Real.exp (-(2 * Real.pi * t)) * Real.exp (2 * Real.pi * (ModularGroup.S • w).im)
        = Real.exp (2 * Real.pi * ((ModularGroup.S • w).im - t)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [show (1 : ℝ) / 2 * Real.exp (-(2 * Real.pi * t)) * (c / 2 *
        Real.exp (2 * Real.pi * (ModularGroup.S • w).im))
        = c / 4 * (Real.exp (-(2 * Real.pi * t)) *
            Real.exp (2 * Real.pi * (ModularGroup.S • w).im)) from by ring, he]
    nlinarith [hexp2, hc]
  have hform : ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht)) *
        (Work.Kernels.jInvariantFun w -
          Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht)))‖
      = t ^ 12 * ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht) *
          (Work.Kernels.jInvariantFun w -
            Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht))‖ := by
    rw [hjz, norm_mul, norm_mul, hΔn]
    ring
  rw [hform]
  have ht12 : (1 : ℝ) ≤ t ^ 12 := one_le_pow₀ ht1
  calc c / 4
      ≤ (1 : ℝ) / 2 * Real.exp (-(2 * Real.pi * t)) * (c / 2 *
          Real.exp (2 * Real.pi * (ModularGroup.S • w).im)) := hge
    _ ≤ ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht) *
          (Work.Kernels.jInvariantFun w -
            Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht))‖ := hprod
    _ ≤ t ^ 12 * ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht) *
          (Work.Kernels.jInvariantFun w -
            Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht))‖ :=
        le_mul_of_one_le_left (norm_nonneg _) ht12

/-! ## From the cleared numerators to the contour values -/

/-- **`K₊` on the contour from its cleared numerator.**

If `Ξ` is the CKMRV numerator of `K₊` (an identity of the shape of `Xi8_eq`/`Xi24_eq`, with the
factor `z^k`, `k = d/2 - 2`), if `Ξ` is polynomially bounded at the points `i s` with `s ≤ 1`, and
if the divisor `Δ z · (j w − j z)` is bounded below by `c > 0` on the range `1 ≤ t ≤ Im(S•w) − 1`,
then `K₊` is polynomially bounded there: the `k`-th power `s^k = t^{−k}` of the contour point
becomes a factor `t^k`, absorbed into `(1+t)^{M+k}`. -/
lemma KPlus_bound_of_cleared
    (d k : ℕ) {Ξ : UpperHalfPlane → UpperHalfPlane → ℂ} {kc : ℂ}
    (hid : ∀ (τ z : UpperHalfPlane), Work.Kernels.jInvariantFun τ ≠
        Work.Kernels.jInvariantFun z →
      kc * (Work.Kernels.DeltaFun z *
          (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)) *
        ((z : ℂ) ^ k * Work.Kernels.KPlus d τ (ModularGroup.S • z)) = Ξ τ z)
    (hkc : kc ≠ 0)
    (hΞ : ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane) (s : ℝ) (hs : 0 < s), w ∈ KEpsilon → s ≤ 1 →
        s⁻¹ ≤ (ModularGroup.S • w).im - 1 →
        ‖Ξ w (Work.Kernels.imagAxis s hs)‖
          ≤ C * (Work.Kernels.scale w) ^ N * (1 + s⁻¹) ^ M)
    {c : ℝ} (hc : 0 < c)
    (hdiv : ∀ (w : UpperHalfPlane) (t : ℝ) (ht : 0 < t), w ∈ KEpsilon → 1 ≤ t →
        t ≤ (ModularGroup.S • w).im - 1 →
        c ≤ ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht)) *
              (Work.Kernels.jInvariantFun w -
                Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht)))‖) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane) (t : ℝ) (ht : 0 < t), w ∈ KEpsilon → 1 ≤ t →
        t ≤ (ModularGroup.S • w).im - 1 →
        ‖Work.Kernels.KPlus d w (Work.Kernels.imagAxis t ht)‖
          ≤ C * (Work.Kernels.scale w) ^ N * (1 + t) ^ M := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := hΞ
  have hkcn : 0 < ‖kc‖ := norm_pos_iff.mpr hkc
  have hden : 0 < ‖kc‖ * c := mul_pos hkcn hc
  refine ⟨C / (‖kc‖ * c), N, M + k, div_pos hC hden, hN, by positivity, ?_⟩
  intro w t ht hw ht1 hfar
  -- the small parameter `s = 1/t` and the contour point `z = i s`
  have hs : 0 < t⁻¹ := inv_pos.mpr ht
  have hst : t⁻¹ ≤ 1 := (inv_le_one₀ ht).mpr ht1
  have hsinv : (t⁻¹)⁻¹ = t := inv_inv t
  have hfar' : (t⁻¹)⁻¹ ≤ (ModularGroup.S • w).im - 1 := by rw [hsinv]; exact hfar
  have hzS := S_smul_imagAxis_inv' t ht
  -- the divisor bound at the contour point
  have hdivz : c ≤ ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t⁻¹ hs) *
      (Work.Kernels.jInvariantFun w -
        Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t⁻¹ hs))‖ := by
    have h := hdiv w t ht hw ht1 hfar
    rwa [imagAxis_eq_of_eq (t⁻¹) (inv_pos.mpr ht) hs] at h
  have hjne : Work.Kernels.jInvariantFun w ≠
      Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t⁻¹ hs) :=
    jInvariantFun_ne_of_divisor_pos hc hdivz
  -- the CKMRV identity at `w` and the contour point
  have hid' := hid w (Work.Kernels.imagAxis t⁻¹ hs) hjne
  rw [hzS] at hid'
  set D : ℝ := ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t⁻¹ hs) *
      (Work.Kernels.jInvariantFun w -
        Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t⁻¹ hs))‖ with hD
  have hDpos : 0 < D := lt_of_lt_of_le hc hdivz
  have hDc : c ≤ D := hdivz
  have hzk : ‖((Work.Kernels.imagAxis t⁻¹ hs : UpperHalfPlane) : ℂ) ^ k‖ = (t⁻¹) ^ k := by
    rw [norm_pow, norm_imagAxis' t⁻¹ hs]
  have hzpos : 0 < ‖((Work.Kernels.imagAxis t⁻¹ hs : UpperHalfPlane) : ℂ) ^ k‖ := by
    rw [hzk]; positivity
  have hprod : ‖((Work.Kernels.imagAxis t⁻¹ hs : UpperHalfPlane) : ℂ) ^ k *
        Work.Kernels.KPlus d w (Work.Kernels.imagAxis t ht)‖
      ≤ ‖Ξ w (Work.Kernels.imagAxis t⁻¹ hs)‖ / (‖kc‖ * D) := by
    have h1 : ‖kc * (Work.Kernels.DeltaFun (Work.Kernels.imagAxis t⁻¹ hs) *
        (Work.Kernels.jInvariantFun w -
          Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t⁻¹ hs)))‖ = ‖kc‖ * D := by
      rw [norm_mul, hD]
    have h2 : ‖kc * (Work.Kernels.DeltaFun (Work.Kernels.imagAxis t⁻¹ hs) *
        (Work.Kernels.jInvariantFun w -
          Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t⁻¹ hs))) *
        (((Work.Kernels.imagAxis t⁻¹ hs : UpperHalfPlane) : ℂ) ^ k *
          Work.Kernels.KPlus d w (Work.Kernels.imagAxis t ht))‖
        = ‖Ξ w (Work.Kernels.imagAxis t⁻¹ hs)‖ := by rw [hid']
    rw [norm_mul, h1] at h2
    have h3 : ‖((Work.Kernels.imagAxis t⁻¹ hs : UpperHalfPlane) : ℂ) ^ k *
        Work.Kernels.KPlus d w (Work.Kernels.imagAxis t ht)‖ * (‖kc‖ * D)
        = ‖Ξ w (Work.Kernels.imagAxis t⁻¹ hs)‖ := by rw [← h2]; ring
    rw [le_div_iff₀ (mul_pos hkcn hDpos)]
    exact le_of_eq h3
  have hmain : ‖((Work.Kernels.imagAxis t⁻¹ hs : UpperHalfPlane) : ℂ) ^ k *
        Work.Kernels.KPlus d w (Work.Kernels.imagAxis t ht)‖
      ≤ C / (‖kc‖ * c) * (Work.Kernels.scale w) ^ N * (1 + t) ^ M := by
    refine hprod.trans ?_
    have hnum : ‖Ξ w (Work.Kernels.imagAxis t⁻¹ hs)‖
        ≤ C * (Work.Kernels.scale w) ^ N * (1 + t) ^ M := by
      have h := hb w t⁻¹ hs hw hst hfar'
      rwa [hsinv] at h
    calc ‖Ξ w (Work.Kernels.imagAxis t⁻¹ hs)‖ / (‖kc‖ * D)
        ≤ (C * (Work.Kernels.scale w) ^ N * (1 + t) ^ M) / (‖kc‖ * D) :=
          div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ (C * (Work.Kernels.scale w) ^ N * (1 + t) ^ M) / (‖kc‖ * c) :=
          div_le_div_of_nonneg_left
            (mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg (Work.Kernels.scale_pos w).le N))
              (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ 1 + t) M)) hden
            (mul_le_mul_of_nonneg_left hDc hkcn.le)
      _ = C / (‖kc‖ * c) * (Work.Kernels.scale w) ^ N * (1 + t) ^ M := by ring
  calc ‖Work.Kernels.KPlus d w (Work.Kernels.imagAxis t ht)‖
      = ‖((Work.Kernels.imagAxis t⁻¹ hs : UpperHalfPlane) : ℂ) ^ k *
          Work.Kernels.KPlus d w (Work.Kernels.imagAxis t ht)‖ /
          ‖((Work.Kernels.imagAxis t⁻¹ hs : UpperHalfPlane) : ℂ) ^ k‖ := by
        rw [norm_mul, mul_div_cancel_left₀ _ (ne_of_gt hzpos)]
    _ ≤ (C / (‖kc‖ * c) * (Work.Kernels.scale w) ^ N * (1 + t) ^ M) /
          ‖((Work.Kernels.imagAxis t⁻¹ hs : UpperHalfPlane) : ℂ) ^ k‖ :=
        div_le_div_of_nonneg_right hmain hzpos.le
    _ = C / (‖kc‖ * c) * (Work.Kernels.scale w) ^ N * (1 + t) ^ M * t ^ k := by
        rw [hzk, div_eq_mul_inv]
        rw [show (((t⁻¹ : ℝ) ^ k))⁻¹ = t ^ k from by rw [inv_pow, inv_inv]]
    _ ≤ C / (‖kc‖ * c) * (Work.Kernels.scale w) ^ N * (1 + t) ^ M * (1 + t) ^ k := by
        refine mul_le_mul_of_nonneg_left ?_
          (mul_nonneg (mul_nonneg (div_nonneg hC.le hden.le)
            (Real.rpow_nonneg (Work.Kernels.scale_pos w).le N))
            (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ 1 + t) M))
        exact pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ t) (by linarith) k
    _ = C / (‖kc‖ * c) * (Work.Kernels.scale w) ^ N * (1 + t) ^ (M + k) := by
        rw [← Real.rpow_natCast (1 + t) k,
          Real.rpow_add (by linarith : (0 : ℝ) < 1 + t) M (k : ℝ)]
        ring

/-- **`K₋` on the contour from its cleared numerator.**  Same as `KPlus_bound_of_cleared` with
the `Ncusp`-identity `Ncusp_ident` (no constant prefactor). -/
lemma KMinus_bound_of_cleared
    (ℓ : Work.Kernels.LogLambdaData) (d k : ℕ) {Ξ : UpperHalfPlane → UpperHalfPlane → ℂ}
    (hid : ∀ (τ z : UpperHalfPlane), Work.Kernels.jInvariantFun τ ≠
        Work.Kernels.jInvariantFun z →
      (Work.Kernels.DeltaFun z *
          (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)) *
        ((z : ℂ) ^ k * Work.Kernels.KMinus ℓ d τ (ModularGroup.S • z)) = Ξ τ z)
    (hΞ : ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane) (s : ℝ) (hs : 0 < s), w ∈ KEpsilon → s ≤ 1 →
        s⁻¹ ≤ (ModularGroup.S • w).im - 1 →
        ‖Ξ w (Work.Kernels.imagAxis s hs)‖
          ≤ C * (Work.Kernels.scale w) ^ N * (1 + s⁻¹) ^ M)
    {c : ℝ} (hc : 0 < c)
    (hdiv : ∀ (w : UpperHalfPlane) (t : ℝ) (ht : 0 < t), w ∈ KEpsilon → 1 ≤ t →
        t ≤ (ModularGroup.S • w).im - 1 →
        c ≤ ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht)) *
              (Work.Kernels.jInvariantFun w -
                Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht)))‖) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane) (t : ℝ) (ht : 0 < t), w ∈ KEpsilon → 1 ≤ t →
        t ≤ (ModularGroup.S • w).im - 1 →
        ‖Work.Kernels.KMinus ℓ d w (Work.Kernels.imagAxis t ht)‖
          ≤ C * (Work.Kernels.scale w) ^ N * (1 + t) ^ M := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := hΞ
  have hpos : 0 < c := hc
  refine ⟨C / c, N, M + k, div_pos hC hpos, hN, by positivity, ?_⟩
  intro w t ht hw ht1 hfar
  have hs : 0 < t⁻¹ := inv_pos.mpr ht
  have hst : t⁻¹ ≤ 1 := (inv_le_one₀ ht).mpr ht1
  have hsinv : (t⁻¹)⁻¹ = t := inv_inv t
  have hfar' : (t⁻¹)⁻¹ ≤ (ModularGroup.S • w).im - 1 := by rw [hsinv]; exact hfar
  have hzS := S_smul_imagAxis_inv' t ht
  have hdivz : c ≤ ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t⁻¹ hs) *
      (Work.Kernels.jInvariantFun w -
        Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t⁻¹ hs))‖ := by
    have h := hdiv w t ht hw ht1 hfar
    rwa [imagAxis_eq_of_eq (t⁻¹) (inv_pos.mpr ht) hs] at h
  have hjne : Work.Kernels.jInvariantFun w ≠
      Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t⁻¹ hs) :=
    jInvariantFun_ne_of_divisor_pos hc hdivz
  have hid' := hid w (Work.Kernels.imagAxis t⁻¹ hs) hjne
  rw [hzS] at hid'
  set D : ℝ := ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t⁻¹ hs) *
      (Work.Kernels.jInvariantFun w -
        Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t⁻¹ hs))‖ with hD
  have hDpos : 0 < D := lt_of_lt_of_le hc hdivz
  have hDc : c ≤ D := hdivz
  have hzk : ‖((Work.Kernels.imagAxis t⁻¹ hs : UpperHalfPlane) : ℂ) ^ k‖ = (t⁻¹) ^ k := by
    rw [norm_pow, norm_imagAxis' t⁻¹ hs]
  have hzpos : 0 < ‖((Work.Kernels.imagAxis t⁻¹ hs : UpperHalfPlane) : ℂ) ^ k‖ := by
    rw [hzk]; positivity
  have hprod : ‖((Work.Kernels.imagAxis t⁻¹ hs : UpperHalfPlane) : ℂ) ^ k *
        Work.Kernels.KMinus ℓ d w (Work.Kernels.imagAxis t ht)‖
      ≤ ‖Ξ w (Work.Kernels.imagAxis t⁻¹ hs)‖ / D := by
    have h1 : ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t⁻¹ hs) *
        (Work.Kernels.jInvariantFun w -
          Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t⁻¹ hs))‖ = D := by rw [← hD]
    have h2 : ‖(Work.Kernels.DeltaFun (Work.Kernels.imagAxis t⁻¹ hs) *
        (Work.Kernels.jInvariantFun w -
          Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t⁻¹ hs))) *
        (((Work.Kernels.imagAxis t⁻¹ hs : UpperHalfPlane) : ℂ) ^ k *
          Work.Kernels.KMinus ℓ d w (Work.Kernels.imagAxis t ht))‖
        = ‖Ξ w (Work.Kernels.imagAxis t⁻¹ hs)‖ := by rw [hid']
    rw [norm_mul, h1] at h2
    have h3 : ‖((Work.Kernels.imagAxis t⁻¹ hs : UpperHalfPlane) : ℂ) ^ k *
        Work.Kernels.KMinus ℓ d w (Work.Kernels.imagAxis t ht)‖ * D
        = ‖Ξ w (Work.Kernels.imagAxis t⁻¹ hs)‖ := by rw [← h2]; ring
    rw [le_div_iff₀ hDpos]
    exact le_of_eq h3
  have hmain : ‖((Work.Kernels.imagAxis t⁻¹ hs : UpperHalfPlane) : ℂ) ^ k *
        Work.Kernels.KMinus ℓ d w (Work.Kernels.imagAxis t ht)‖
      ≤ C / c * (Work.Kernels.scale w) ^ N * (1 + t) ^ M := by
    refine hprod.trans ?_
    have hnum : ‖Ξ w (Work.Kernels.imagAxis t⁻¹ hs)‖
        ≤ C * (Work.Kernels.scale w) ^ N * (1 + t) ^ M := by
      have h := hb w t⁻¹ hs hw hst hfar'
      rwa [hsinv] at h
    calc ‖Ξ w (Work.Kernels.imagAxis t⁻¹ hs)‖ / D
        ≤ (C * (Work.Kernels.scale w) ^ N * (1 + t) ^ M) / D :=
          div_le_div_of_nonneg_right hnum hDpos.le
      _ ≤ (C * (Work.Kernels.scale w) ^ N * (1 + t) ^ M) / c :=
          div_le_div_of_nonneg_left
            (mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg (Work.Kernels.scale_pos w).le N))
              (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ 1 + t) M)) hc hDc
      _ = C / c * (Work.Kernels.scale w) ^ N * (1 + t) ^ M := by ring
  calc ‖Work.Kernels.KMinus ℓ d w (Work.Kernels.imagAxis t ht)‖
      = ‖((Work.Kernels.imagAxis t⁻¹ hs : UpperHalfPlane) : ℂ) ^ k *
          Work.Kernels.KMinus ℓ d w (Work.Kernels.imagAxis t ht)‖ /
          ‖((Work.Kernels.imagAxis t⁻¹ hs : UpperHalfPlane) : ℂ) ^ k‖ := by
        rw [norm_mul, mul_div_cancel_left₀ _ (ne_of_gt hzpos)]
    _ ≤ (C / c * (Work.Kernels.scale w) ^ N * (1 + t) ^ M) /
          ‖((Work.Kernels.imagAxis t⁻¹ hs : UpperHalfPlane) : ℂ) ^ k‖ :=
        div_le_div_of_nonneg_right hmain hzpos.le
    _ = C / c * (Work.Kernels.scale w) ^ N * (1 + t) ^ M * t ^ k := by
        rw [hzk, div_eq_mul_inv]
        rw [show (((t⁻¹ : ℝ) ^ k))⁻¹ = t ^ k from by rw [inv_pow, inv_inv]]
    _ ≤ C / c * (Work.Kernels.scale w) ^ N * (1 + t) ^ M * (1 + t) ^ k := by
        refine mul_le_mul_of_nonneg_left ?_
          (mul_nonneg (mul_nonneg (div_nonneg hC.le hc.le)
            (Real.rpow_nonneg (Work.Kernels.scale_pos w).le N))
            (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ 1 + t) M))
        exact pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ t) (by linarith) k
    _ = C / c * (Work.Kernels.scale w) ^ N * (1 + t) ^ (M + k) := by
        rw [← Real.rpow_natCast (1 + t) k,
          Real.rpow_add (by linarith : (0 : ℝ) < 1 + t) M (k : ℝ)]
        ring

/-! ## The assembly -/

/-- **The assembly.**  From the three low-`Im` numerator bounds (`Xi8_low_bound`,
`Xi24_low_bound`, `Ncusp_low_bound`) and the divisor lower bound (`divisor_lower_lowIm`) one gets
`Work.Asymptotics.EWindow_far` by splitting `Kfun = (K₊ + K₋)/2` and reading the two CKMRV
divisor identities (`Xi8_eq`, `Xi24_eq`, `Ncusp_ident`) on the contour `S • z = i t`, i.e. at
`z = i/t`. -/
theorem EWindow_far_of (ℓ : Work.Kernels.LogLambdaData)
    (hXi8 : ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane) (s : ℝ) (hs : 0 < s), w ∈ KEpsilon → s ≤ 1 →
        s⁻¹ ≤ (ModularGroup.S • w).im - 1 →
        ‖Xi8 w (Work.Kernels.imagAxis s hs)‖
          ≤ C * (Work.Kernels.scale w) ^ N * (1 + s⁻¹) ^ M)
    (hXi24 : ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane) (s : ℝ) (hs : 0 < s), w ∈ KEpsilon → s ≤ 1 →
        s⁻¹ ≤ (ModularGroup.S • w).im - 1 →
        ‖Xi24 w (Work.Kernels.imagAxis s hs)‖
          ≤ C * (Work.Kernels.scale w) ^ N * (1 + s⁻¹) ^ M)
    (hNc : ∀ (d : ℕ), d = 8 ∨ d = 24 → ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane) (s : ℝ) (hs : 0 < s), w ∈ KEpsilon → s ≤ 1 →
        s⁻¹ ≤ (ModularGroup.S • w).im - 1 →
        ‖Ncusp ℓ d w (Work.Kernels.imagAxis s hs)‖
          ≤ C * (Work.Kernels.scale w) ^ N * (1 + s⁻¹) ^ M)
    (hdiv : ∃ c : ℝ, 0 < c ∧ ∀ (w : UpperHalfPlane) (t : ℝ) (ht : 0 < t),
      w ∈ KEpsilon → 1 ≤ t → t ≤ (ModularGroup.S • w).im - 1 →
        c ≤ ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht)) *
              (Work.Kernels.jInvariantFun w -
                Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht)))‖) :
    ∀ (d : ℕ), d = 8 ∨ d = 24 →
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane) (t : ℝ), w ∈ KEpsilon → 1 ≤ t →
        t ≤ (ModularGroup.S • w).im - 1 →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t‖
          ≤ C * (Work.Kernels.scale w) ^ N * (1 + t) ^ M := by
  obtain ⟨c, hc, hdiv⟩ := hdiv
  have hc8 : ((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num)
      (zpow_ne_zero _ (by exact_mod_cast Real.pi_ne_zero))) Complex.I_ne_zero
  have hc24 : ((36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) *
      Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (by simp [Work.Kernels.c1728]))
      (zpow_ne_zero _ (by exact_mod_cast Real.pi_ne_zero))) Complex.I_ne_zero
  intro d hd
  -- the two contour bounds
  have hkp : ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane) (t : ℝ) (ht : 0 < t), w ∈ KEpsilon → 1 ≤ t →
        t ≤ (ModularGroup.S • w).im - 1 →
        ‖Work.Kernels.KPlus d w (Work.Kernels.imagAxis t ht)‖
          ≤ C * (Work.Kernels.scale w) ^ N * (1 + t) ^ M := by
    rcases hd with rfl | rfl
    · exact KPlus_bound_of_cleared 8 2 Xi8_eq hc8 hXi8 hc hdiv
    · exact KPlus_bound_of_cleared 24 10 Xi24_eq hc24 hXi24 hc hdiv
  have hkm : ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane) (t : ℝ) (ht : 0 < t), w ∈ KEpsilon → 1 ≤ t →
        t ≤ (ModularGroup.S • w).im - 1 →
        ‖Work.Kernels.KMinus ℓ d w (Work.Kernels.imagAxis t ht)‖
          ≤ C * (Work.Kernels.scale w) ^ N * (1 + t) ^ M := by
    rcases hd with rfl | rfl
    · refine KMinus_bound_of_cleared ℓ 8 2 ?_ (hNc 8 (Or.inl rfl)) hc hdiv
      intro τ z h
      rw [Ncusp_ident ℓ 8 (Or.inl rfl) τ z h]
      congr 1
    · refine KMinus_bound_of_cleared ℓ 24 10 ?_ (hNc 24 (Or.inr rfl)) hc hdiv
      intro τ z h
      rw [Ncusp_ident ℓ 24 (Or.inr rfl) τ z h]
      congr 1
  obtain ⟨C1, N1, M1, hC1, hN1, hM1, hb1⟩ := hkp
  obtain ⟨C2, N2, M2, hC2, hN2, hM2, hb2⟩ := hkm
  refine ⟨C1 + C2 + 2, max N1 N2, max M1 M2, by linarith, le_trans hN1 (le_max_left _ _),
    le_trans hM1 (le_max_left _ _), ?_⟩
  intro w t hw ht1 hfar
  have ht : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  have hsw : (1 : ℝ) ≤ Work.Kernels.scale w := Work.Kernels.one_le_scale w
  have hsw0 : (0 : ℝ) ≤ Work.Kernels.scale w := le_trans zero_le_one hsw
  have h1t : (1 : ℝ) ≤ 1 + t := by linarith
  have h1t0 : (0 : ℝ) ≤ 1 + t := by linarith
  have hSN1 : (Work.Kernels.scale w) ^ N1 ≤ (Work.Kernels.scale w) ^ (max N1 N2) :=
    Real.rpow_le_rpow_of_exponent_le hsw (le_max_left _ _)
  have hSN2 : (Work.Kernels.scale w) ^ N2 ≤ (Work.Kernels.scale w) ^ (max N1 N2) :=
    Real.rpow_le_rpow_of_exponent_le hsw (le_max_right _ _)
  have hSM1 : (1 + t) ^ M1 ≤ (1 + t) ^ (max M1 M2) :=
    Real.rpow_le_rpow_of_exponent_le h1t (le_max_left _ _)
  have hSM2 : (1 + t) ^ M2 ≤ (1 + t) ^ (max M1 M2) :=
    Real.rpow_le_rpow_of_exponent_le h1t (le_max_right _ _)
  have hSN0 : (0 : ℝ) ≤ (Work.Kernels.scale w) ^ (max N1 N2) :=
    Real.rpow_nonneg hsw0 _
  have hSM10 : (0 : ℝ) ≤ (1 + t) ^ M1 := Real.rpow_nonneg h1t0 M1
  have hSM0 : (0 : ℝ) ≤ (1 + t) ^ (max M1 M2) := Real.rpow_nonneg h1t0 _
  have key1 : C1 * (Work.Kernels.scale w) ^ N1 * (1 + t) ^ M1
      ≤ (C1 + C2 + 2) * (Work.Kernels.scale w) ^ (max N1 N2) * (1 + t) ^ (max M1 M2) := by
    calc C1 * (Work.Kernels.scale w) ^ N1 * (1 + t) ^ M1
        = C1 * ((Work.Kernels.scale w) ^ N1 * (1 + t) ^ M1) := by ring
      _ ≤ (C1 + C2 + 2) *
            ((Work.Kernels.scale w) ^ (max N1 N2) * (1 + t) ^ (max M1 M2)) :=
          mul_le_mul (by linarith) (mul_le_mul hSN1 hSM1 hSM10 hSN0) (by positivity)
            (by linarith)
      _ = (C1 + C2 + 2) * (Work.Kernels.scale w) ^ (max N1 N2) * (1 + t) ^ (max M1 M2) := by
          ring
  have key2 : C2 * (Work.Kernels.scale w) ^ N2 * (1 + t) ^ M2
      ≤ (C1 + C2 + 2) * (Work.Kernels.scale w) ^ (max N1 N2) * (1 + t) ^ (max M1 M2) := by
    calc C2 * (Work.Kernels.scale w) ^ N2 * (1 + t) ^ M2
        = C2 * ((Work.Kernels.scale w) ^ N2 * (1 + t) ^ M2) := by ring
      _ ≤ (C1 + C2 + 2) *
            ((Work.Kernels.scale w) ^ (max N1 N2) * (1 + t) ^ (max M1 M2)) :=
          mul_le_mul (by linarith) (mul_le_mul hSN2 hSM2 (Real.rpow_nonneg h1t0 M2) hSN0)
            (by positivity) (by linarith)
      _ = (C1 + C2 + 2) * (Work.Kernels.scale w) ^ (max N1 N2) * (1 + t) ^ (max M1 M2) := by
          ring
  have hmain : ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t‖
      ≤ ((C1 * (Work.Kernels.scale w) ^ N1 * (1 + t) ^ M1)
          + (C2 * (Work.Kernels.scale w) ^ N2 * (1 + t) ^ M2)) / 2 := by
    rw [Work.Kernels.Kaxis, dif_pos ht, Work.Kernels.Kfun, norm_div,
      show ‖(2 : ℂ)‖ = 2 from by norm_num]
    exact div_le_div_of_nonneg_right
      (le_trans (norm_add_le _ _)
        (add_le_add (hb1 w t ht hw ht1 hfar) (hb2 w t ht hw ht1 hfar))) (by norm_num)
  refine hmain.trans ?_
  rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
  nlinarith [key1, key2]

/-- **The CKMRV kernel on the cusp-`0` tile `E` strictly below the pole height.**

For `w ∈ E = KEpsilon` (so `H := Im (S • w) ≥ 2`) and `1 ≤ t ≤ H - 1`, the kernel
`t ↦ Kaxis (Kfun ℓ d) w t` is bounded polynomially in `scale w` and `t`.  This is the
"below-the-pole" brick of `E_window_exp`, whose range `1 ≤ t ≤ Im(S•w)+1` splits as
`[1, Im-1] ∪ [Im-1, Im+1]` (companion piece: `Work.Asymptotics.EWindow_pole`).

The proof splits `K = (K₊ + K₋)/2` and uses the two *divisor identities* of CKMRV, read on the
contour `S • z = i t` (i.e. `z = i/t`, the point of height `1/t ≤ 1`):

* `Xi8_eq`/`Xi24_eq`: `c_d·Δ(z)(j w − j z)·(z^{d/2−2}·K₊^{(d)}(w, S·z)) = Ξ_d(w,z)`;
* `Ncusp_ident`: `Δ(z)(j w − j z)·(z^{d/2−2}·K₋^{(d)}(w, S·z)) = Ncusp ℓ d w z`.

On the range `1 ≤ t ≤ Im(S•w) − 1` the divisor `Δ(z)(j w − j z)` stays bounded away from `0`
(`Work.Asymptotics.divisor_lower_lowIm`), while the two numerators stay polynomially bounded
even though `Im z = 1/t ≤ 1` (`Work.Asymptotics.Xi8_low_bound`, `Xi24_low_bound`,
`Ncusp_low_bound`).  This is exactly the bookkeeping by which the factor `e^{2πt}` hidden in
`1/‖Δ(i t)‖` is cancelled by the factor `e^{2π Im(S•w)}` of `‖j w − j(i t)‖`. -/
theorem EWindow_far (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane) (t : ℝ), w ∈ Work.Asymptotics.KEpsilon → 1 ≤ t →
        t ≤ (ModularGroup.S • w).im - 1 →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t‖
          ≤ C * (Work.Kernels.scale w) ^ N * (1 + t) ^ M := by
  exact EWindow_far_of ℓ Xi8_low_bound Xi24_low_bound
    (fun e he => EpolyWindowE_ncusp_low_bound ℓ e he) divisor_lower_lowIm d hd

end

end Work.Asymptotics
