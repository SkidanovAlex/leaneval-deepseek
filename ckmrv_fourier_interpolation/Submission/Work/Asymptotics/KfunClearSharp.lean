
/-
# The sharp cusp bound for the cleared CKMRV kernel `K^{(d)}`, `d ∈ {8,24}`

`Work.Asymptotics.KfunClearSharp` is the cusp-`0` estimate for the (pole-cleared) CKMRV
kernel: for `w` in the funnel `𝓕 = {τ ∈ 𝒟 : 2 ≤ Im τ}` and `z = i t` with `0 < t ≤ 1`, off the
coincidence set `j w = j (i t)`,

`‖K^Clear(w, i t)‖ ≤ C (1+‖w‖)^A (1+1/t)^N e^{-c/t} e^{-2π Im w}`,  `c = π` (`d = 8`), `c = 3π` (`d = 24`).

The two pieces `K_±^Clear` are treated separately.  Writing `z₀ = i t` and `w₂ = S z₀ = i/t`
(so `S w₂ = z₀`, `j w₂ = j z₀`, `Δ w₂ = z₀^{12}Δ z₀`) and using the proven slash bounds
`KPlus_slash_bound_funnel` / `KMinusFunnelSlash` at `(τ,z) = (w,w₂)`, the divisor
`‖Δ w₂ (j w − j w₂)‖` cancels the prefactor `Δ w Δ z₀^e (j w − j z₀)` exactly (one power of `Δ z₀`
surviving because `e − 1 ∈ {0,1}`), leaving `e^{-2π/t}` from the `q`-term of `K_+` and `e^{-π/t}`
from the cusp numerator of `K_-`.  For `d = 24` the surviving factor
`‖Δ(i t)‖ ≤ 2 t^{-12}e^{-2π/t}` converts the `π/t` of `K_-` into `3π/t`.
-/
import Mathlib
import Submission.Work.Asymptotics.KPlus_slash_bound_funnel
import Submission.Work.Asymptotics.KMinusFunnelSlash
import Submission.Work.Asymptotics.Funnel24Aux
import Submission.Work.Kernels.ClearLink.KPlusClear_eq_smul
import Submission.Work.Kernels.ClearLink.KMinusClear_eq_smul
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Asymptotics.SpikeCircle.DeltaFunBoundsHalf
import Submission.Work.Asymptotics.EtailE.Atoms

namespace Work.Asymptotics

open UpperHalfPlane ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

noncomputable section

set_option maxHeartbeats 400000

/-! ## Elementary facts about the contour point `i t` -/

private lemma ia_im (t : ℝ) (ht : 0 < t) : (Work.Kernels.imagAxis t ht).im = t := by
  simp [Work.Kernels.imagAxis]

private lemma ia_coe (t : ℝ) (ht : 0 < t) :
    ((Work.Kernels.imagAxis t ht : ℍ) : ℂ) = (t : ℂ) * Complex.I := rfl

private lemma ia_S (t : ℝ) (ht : 0 < t) :
    ModularGroup.S • Work.Kernels.imagAxis t ht = Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht) := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.modular_S_smul]
  simp only [Work.Kernels.imagAxis, UpperHalfPlane.coe_mk]
  rw [inv_neg, mul_inv, Complex.inv_I, ← Complex.ofReal_inv]
  ring

private lemma S_invol (τ : ℍ) : ModularGroup.S • (ModularGroup.S • τ) = τ := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.modular_S_smul]
  simp

/-- `1 ≤ t⁻¹` for `0 < t ≤ 1`. -/
private lemma one_le_inv {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) : (1 : ℝ) ≤ t⁻¹ := by
  rw [one_le_inv₀ ht]; exact ht1

/-- Monotone multiplication of a two-factor left block. -/
private lemma absorb_mul {X a b c d : ℝ} (hX : 0 ≤ X) (hac : a ≤ c) (hbd : b ≤ d)
    (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) : X * a * b ≤ X * c * d := by
  calc X * a * b = X * (a * b) := by ring
    _ ≤ X * (c * d) := mul_le_mul_of_nonneg_left (mul_le_mul hac hbd hb0 hc0) hX
    _ = X * c * d := by ring

/-! ## Pure arithmetic: the cancellations in the divisor -/

private lemma arith_cancel (a b c t Y : ℝ) (e : ℕ) (s : ℤ)
    (ht : t ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    a * b ^ e * c * t ^ s * (Y / (t ^ 12 * b * c)) = Y * a * b ^ e * t ^ s / (t ^ 12 * b) := by
  field_simp
  try ring

private lemma arith_conv_eight (Y a b t : ℝ) (ht : t ≠ 0) (hb : b ≠ 0) :
    Y * a * b ^ 1 * t ^ (2 : ℤ) / (t ^ 12 * b) = Y * a * (t⁻¹) ^ 10 := by
  have hzpow : t ^ (2 : ℤ) = t ^ 2 := by norm_num
  rw [hzpow, pow_one]
  field_simp
  try ring

private lemma arith_conv_twentyfour (Y a b t : ℝ) (ht : t ≠ 0) (hb : b ≠ 0) :
    Y * a * b ^ 2 * t ^ (10 : ℤ) / (t ^ 12 * b) = Y * a * b * (t⁻¹) ^ 2 := by
  have hzpow : t ^ (10 : ℤ) = t ^ 10 := by norm_num
  rw [hzpow]
  field_simp
  try ring

/-! ## The core: transferring a slash bound to the cleared kernel -/

private lemma kclear_slash_le (d : ℕ) (w z₀ w₂ : ℍ) (t : ℝ) (s : ℤ) (e : ℕ) (C A Q : ℝ)
    (K : ℍ → ℍ → ℂ) (KC : ℍ → ℍ → ℂ)
    (ht : 0 < t)
    (hz₀ : (z₀ : ℂ) = (t : ℂ) * Complex.I)
    (hw₂ : ‖(w₂ : ℂ)‖ = t⁻¹)
    (hΔ : Work.Kernels.DeltaFun w₂ = (z₀ : ℂ) ^ 12 * Work.Kernels.DeltaFun z₀)
    (hj : Work.Kernels.jInvariantFun w₂ = Work.Kernels.jInvariantFun z₀)
    (hne : Work.Kernels.jInvariantFun w ≠ Work.Kernels.jInvariantFun z₀)
    (hclear : KC w z₀ = Work.Kernels.growthPrefactor d w z₀ * K w z₀)
    (hgp : ‖Work.Kernels.growthPrefactor d w z₀‖
        = ‖Work.Kernels.DeltaFun w‖ * ‖Work.Kernels.DeltaFun z₀‖ ^ e
          * ‖Work.Kernels.jInvariantFun w - Work.Kernels.jInvariantFun z₀‖)
    (hsl : ‖(w₂ : ℂ) ^ s * K w z₀‖
        ≤ C * (1 + ‖(w : ℂ)‖) ^ A * Q
            / ‖Work.Kernels.DeltaFun w₂ * (Work.Kernels.jInvariantFun w - Work.Kernels.jInvariantFun w₂)‖) :
    ‖KC w z₀‖
      ≤ C * (1 + ‖(w : ℂ)‖) ^ A * Q * ‖Work.Kernels.DeltaFun w‖
          * ‖Work.Kernels.DeltaFun z₀‖ ^ e * t ^ s / (t ^ 12 * ‖Work.Kernels.DeltaFun z₀‖) := by
  have hz₀n : ‖(z₀ : ℂ)‖ = t := Work.Asymptotics.ft_norm_coe hz₀ ht.le
  have hΔn : ‖Work.Kernels.DeltaFun w₂‖ = t ^ 12 * ‖Work.Kernels.DeltaFun z₀‖ := by
    rw [hΔ, norm_mul, norm_pow, hz₀n]
  have hjd : ‖Work.Kernels.jInvariantFun w - Work.Kernels.jInvariantFun w₂‖
      = ‖Work.Kernels.jInvariantFun w - Work.Kernels.jInvariantFun z₀‖ := by rw [hj]
  have hz₀D : ‖Work.Kernels.DeltaFun z₀‖ ≠ 0 := by
    rw [norm_ne_zero_iff]; exact Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z₀
  have hjd_ne : ‖Work.Kernels.jInvariantFun w - Work.Kernels.jInvariantFun z₀‖ ≠ 0 := by
    rw [norm_ne_zero_iff]; exact sub_ne_zero.mpr hne
  have hDn : ‖Work.Kernels.DeltaFun w₂
        * (Work.Kernels.jInvariantFun w - Work.Kernels.jInvariantFun w₂)‖
      = t ^ 12 * ‖Work.Kernels.DeltaFun z₀‖
        * ‖Work.Kernels.jInvariantFun w - Work.Kernels.jInvariantFun z₀‖ := by
    simp only [norm_mul]
    rw [hΔn, hjd]
  have ht_ne : t ≠ 0 := ht.ne'
  have h1 : ‖(w₂ : ℂ) ^ s * K w z₀‖ = t ^ (-s) * ‖K w z₀‖ := by
    rw [norm_mul, norm_zpow, hw₂, _root_.inv_zpow, ← _root_.zpow_neg]
  have hK : ‖K w z₀‖ = t ^ s * ‖(w₂ : ℂ) ^ s * K w z₀‖ := by
    rw [h1, ← mul_assoc, ← zpow_add₀ ht_ne, add_neg_cancel, zpow_zero, one_mul]
  have hstep : ‖KC w z₀‖ = ‖Work.Kernels.DeltaFun w‖ * ‖Work.Kernels.DeltaFun z₀‖ ^ e
      * ‖Work.Kernels.jInvariantFun w - Work.Kernels.jInvariantFun z₀‖ * t ^ s
      * ‖(w₂ : ℂ) ^ s * K w z₀‖ := by
    rw [hclear, norm_mul, hgp, hK]; ring
  have harith : ‖Work.Kernels.DeltaFun w‖ * ‖Work.Kernels.DeltaFun z₀‖ ^ e
        * ‖Work.Kernels.jInvariantFun w - Work.Kernels.jInvariantFun z₀‖ * t ^ s
        * (C * (1 + ‖(w : ℂ)‖) ^ A * Q
            / (t ^ 12 * ‖Work.Kernels.DeltaFun z₀‖
                * ‖Work.Kernels.jInvariantFun w - Work.Kernels.jInvariantFun z₀‖))
      = C * (1 + ‖(w : ℂ)‖) ^ A * Q * ‖Work.Kernels.DeltaFun w‖
          * ‖Work.Kernels.DeltaFun z₀‖ ^ e * t ^ s / (t ^ 12 * ‖Work.Kernels.DeltaFun z₀‖) := by
    rw [arith_cancel (‖Work.Kernels.DeltaFun w‖) (‖Work.Kernels.DeltaFun z₀‖)
      (‖Work.Kernels.jInvariantFun w - Work.Kernels.jInvariantFun z₀‖) t
      (C * (1 + ‖(w : ℂ)‖) ^ A * Q) e s ht_ne hz₀D hjd_ne]
  calc ‖KC w z₀‖
      = ‖Work.Kernels.DeltaFun w‖ * ‖Work.Kernels.DeltaFun z₀‖ ^ e
          * ‖Work.Kernels.jInvariantFun w - Work.Kernels.jInvariantFun z₀‖ * t ^ s
          * ‖(w₂ : ℂ) ^ s * K w z₀‖ := hstep
    _ ≤ ‖Work.Kernels.DeltaFun w‖ * ‖Work.Kernels.DeltaFun z₀‖ ^ e
          * ‖Work.Kernels.jInvariantFun w - Work.Kernels.jInvariantFun z₀‖ * t ^ s
          * (C * (1 + ‖(w : ℂ)‖) ^ A * Q
              / ‖Work.Kernels.DeltaFun w₂
                  * (Work.Kernels.jInvariantFun w - Work.Kernels.jInvariantFun w₂)‖) := by
        refine mul_le_mul_of_nonneg_left hsl ?_
        exact mul_nonneg (mul_nonneg (mul_nonneg (norm_nonneg _)
          (pow_nonneg (norm_nonneg _) e)) (norm_nonneg _)) (zpow_nonneg ht.le s)
    _ = ‖Work.Kernels.DeltaFun w‖ * ‖Work.Kernels.DeltaFun z₀‖ ^ e
          * ‖Work.Kernels.jInvariantFun w - Work.Kernels.jInvariantFun z₀‖ * t ^ s
          * (C * (1 + ‖(w : ℂ)‖) ^ A * Q
              / (t ^ 12 * ‖Work.Kernels.DeltaFun z₀‖
                  * ‖Work.Kernels.jInvariantFun w - Work.Kernels.jInvariantFun z₀‖)) := by
        rw [hDn]
    _ = C * (1 + ‖(w : ℂ)‖) ^ A * Q * ‖Work.Kernels.DeltaFun w‖
          * ‖Work.Kernels.DeltaFun z₀‖ ^ e * t ^ s / (t ^ 12 * ‖Work.Kernels.DeltaFun z₀‖) := harith

/-! ## The `K_+` half, `d = 8` -/

private lemma KPlusClearSharp_eight :
    ∃ C A N : ℝ, 0 < C ∧ 0 ≤ A ∧ 0 ≤ N ∧
      ∀ (w : ℍ) (t : ℝ) (ht : 0 < t), Funnel w → t ≤ 1 →
        Work.Kernels.jInvariantFun w ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) →
        ‖Work.Kernels.KPlusClear 8 w (Work.Kernels.imagAxis t ht)‖
          ≤ C * (1 + ‖(w : ℂ)‖) ^ A * (1 + 1 / t) ^ N
              * Real.exp (-(2 * Real.pi * t⁻¹)) * Real.exp (-(2 * Real.pi * w.im)) := by
  obtain ⟨C, A, hC, hA, hbound⟩ := KPlus_slash_bound_funnel 8 (Or.inl rfl)
  refine ⟨2 * C, A, 10, by positivity, hA, by norm_num, ?_⟩
  intro w t ht hF ht1 hne
  rw [show (1 + 1 / t) ^ (10 : ℝ) = (1 + 1 / t) ^ 10 from Real.rpow_natCast _ _]
  set z₀ : ℍ := Work.Kernels.imagAxis t ht with hz₀def
  set w₂ : ℍ := ModularGroup.S • z₀ with hw₂def
  have hw₂im : w₂.im = t⁻¹ := by
    rw [hw₂def, hz₀def, ia_S t ht]; exact ia_im t⁻¹ (inv_pos.mpr ht)
  have hw₂1 : (1 : ℝ) ≤ w₂.im := by rw [hw₂im]; exact one_le_inv ht ht1
  have hSw₂ : ModularGroup.S • w₂ = z₀ := by rw [hw₂def]; exact S_invol z₀
  have hjw₂ : Work.Kernels.jInvariantFun w₂ = Work.Kernels.jInvariantFun z₀ := by
    rw [hw₂def]; exact Work.Kernels.KernelFacts.jInvariantFun_S_smul z₀
  have hz₀coe : (z₀ : ℂ) = (t : ℂ) * Complex.I := by rw [hz₀def]; exact ia_coe t ht
  have hw₂norm : ‖(w₂ : ℂ)‖ = t⁻¹ := by
    rw [hw₂def, hz₀def, ia_S t ht]
    exact Work.Asymptotics.ft_norm_coe (ia_coe t⁻¹ (inv_pos.mpr ht)) (inv_pos.mpr ht).le
  have hΔ : Work.Kernels.DeltaFun w₂ = (z₀ : ℂ) ^ 12 * Work.Kernels.DeltaFun z₀ := by
    rw [hw₂def]; exact Work.Asymptotics.EtailE.DeltaFun_Ssmul z₀
  have ht_ne : t ≠ 0 := ht.ne'
  have hz₀D : ‖Work.Kernels.DeltaFun z₀‖ ≠ 0 := by
    rw [norm_ne_zero_iff]; exact Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z₀
  have hq : ‖Work.Kernels.qParamFun w₂‖ = Real.exp (-(2 * Real.pi * t⁻¹)) := by
    rw [Work.Asymptotics.norm_qParamFun, hw₂im]
  have hgp : ‖Work.Kernels.growthPrefactor 8 w z₀‖
      = ‖Work.Kernels.DeltaFun w‖ * ‖Work.Kernels.DeltaFun z₀‖ ^ 1
        * ‖Work.Kernels.jInvariantFun w - Work.Kernels.jInvariantFun z₀‖ := by
    simp only [Work.Kernels.growthPrefactor, norm_mul, norm_pow, ↓reduceIte]
  have hsl : ‖(w₂ : ℂ) ^ (2 : ℤ) * Work.Kernels.KPlus 8 w z₀‖
      ≤ C * (1 + ‖(w : ℂ)‖) ^ A * Real.exp (-(2 * Real.pi * t⁻¹))
          / ‖Work.Kernels.DeltaFun w₂
              * (Work.Kernels.jInvariantFun w - Work.Kernels.jInvariantFun w₂)‖ := by
    have h := hbound w w₂ hF.1 hF.2 (le_trans (by norm_num) hw₂1)
      (by rw [hjw₂]; exact hne)
    rw [show (((8 : ℕ) : ℤ) / 2 - 2) = (2 : ℤ) by norm_num, _root_.zpow_ofNat, hSw₂] at h
    rwa [hq] at h
  have h1 := kclear_slash_le 8 w z₀ w₂ t (2 : ℤ) 1 C A (Real.exp (-(2 * Real.pi * t⁻¹)))
    (fun τ z => Work.Kernels.KPlus 8 τ z) (fun τ z => Work.Kernels.KPlusClear 8 τ z)
    ht hz₀coe hw₂norm hΔ hjw₂ hne
    (Work.Kernels.ClearLink.KPlusClear_eq_smul 8 (Or.inl rfl) w z₀ hne) hgp hsl
  have hconv : C * (1 + ‖(w : ℂ)‖) ^ A * Real.exp (-(2 * Real.pi * t⁻¹))
        * ‖Work.Kernels.DeltaFun w‖ * ‖Work.Kernels.DeltaFun z₀‖ ^ 1 * t ^ (2 : ℤ)
        / (t ^ 12 * ‖Work.Kernels.DeltaFun z₀‖)
      = C * (1 + ‖(w : ℂ)‖) ^ A * Real.exp (-(2 * Real.pi * t⁻¹))
        * ‖Work.Kernels.DeltaFun w‖ * (t⁻¹) ^ 10 := by
    rw [arith_conv_eight (C * (1 + ‖(w : ℂ)‖) ^ A * Real.exp (-(2 * Real.pi * t⁻¹)))
      (‖Work.Kernels.DeltaFun w‖) (‖Work.Kernels.DeltaFun z₀‖) t ht_ne hz₀D]
  rw [hconv] at h1
  have hΔw : ‖Work.Kernels.DeltaFun w‖ ≤ 2 * Real.exp (-(2 * Real.pi * w.im)) := by
    have h := Work.Asymptotics.DeltaFun_funnel_le w hF
    rwa [Work.Asymptotics.norm_qParamFun w] at h
  have hpow : (t⁻¹) ^ 10 ≤ (1 + 1 / t) ^ 10 := by
    rw [one_div]
    exact pow_le_pow_left₀ (by positivity) (by linarith [inv_pos.mpr ht]) 10
  have hmul : ‖Work.Kernels.DeltaFun w‖ * (t⁻¹) ^ 10
      ≤ (2 * Real.exp (-(2 * Real.pi * w.im))) * (1 + 1 / t) ^ 10 :=
    mul_le_mul hΔw hpow (by positivity) (by positivity)
  have hX : (0 : ℝ) ≤ C * (1 + ‖(w : ℂ)‖) ^ A * Real.exp (-(2 * Real.pi * t⁻¹)) := by
    positivity
  calc ‖Work.Kernels.KPlusClear 8 w z₀‖
      ≤ C * (1 + ‖(w : ℂ)‖) ^ A * Real.exp (-(2 * Real.pi * t⁻¹)) * ‖Work.Kernels.DeltaFun w‖
          * (t⁻¹) ^ 10 := h1
    _ = (C * (1 + ‖(w : ℂ)‖) ^ A * Real.exp (-(2 * Real.pi * t⁻¹)))
          * (‖Work.Kernels.DeltaFun w‖ * (t⁻¹) ^ 10) := by ring
    _ ≤ (C * (1 + ‖(w : ℂ)‖) ^ A * Real.exp (-(2 * Real.pi * t⁻¹)))
          * ((2 * Real.exp (-(2 * Real.pi * w.im))) * (1 + 1 / t) ^ 10) :=
        mul_le_mul_of_nonneg_left hmul hX
    _ = 2 * C * (1 + ‖(w : ℂ)‖) ^ A * (1 + 1 / t) ^ 10
          * Real.exp (-(2 * Real.pi * t⁻¹)) * Real.exp (-(2 * Real.pi * w.im)) := by ring

/-! ## The `K_+` half, `d = 24` -/

private lemma KPlusClearSharp_twentyfour :
    ∃ C A N : ℝ, 0 < C ∧ 0 ≤ A ∧ 0 ≤ N ∧
      ∀ (w : ℍ) (t : ℝ) (ht : 0 < t), Funnel w → t ≤ 1 →
        Work.Kernels.jInvariantFun w ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) →
        ‖Work.Kernels.KPlusClear 24 w (Work.Kernels.imagAxis t ht)‖
          ≤ C * (1 + ‖(w : ℂ)‖) ^ A * (1 + 1 / t) ^ N
              * Real.exp (-(4 * Real.pi * t⁻¹)) * Real.exp (-(2 * Real.pi * w.im)) := by
  obtain ⟨C, A, hC, hA, hbound⟩ := KPlus_slash_bound_funnel 24 (Or.inr rfl)
  refine ⟨4 * C, A, 14, by positivity, hA, by norm_num, ?_⟩
  intro w t ht hF ht1 hne
  rw [show (1 + 1 / t) ^ (14 : ℝ) = (1 + 1 / t) ^ 14 from Real.rpow_natCast _ _]
  set z₀ : ℍ := Work.Kernels.imagAxis t ht with hz₀def
  set w₂ : ℍ := ModularGroup.S • z₀ with hw₂def
  have hw₂im : w₂.im = t⁻¹ := by
    rw [hw₂def, hz₀def, ia_S t ht]; exact ia_im t⁻¹ (inv_pos.mpr ht)
  have hw₂1 : (1 : ℝ) ≤ w₂.im := by rw [hw₂im]; exact one_le_inv ht ht1
  have hSw₂ : ModularGroup.S • w₂ = z₀ := by rw [hw₂def]; exact S_invol z₀
  have hjw₂ : Work.Kernels.jInvariantFun w₂ = Work.Kernels.jInvariantFun z₀ := by
    rw [hw₂def]; exact Work.Kernels.KernelFacts.jInvariantFun_S_smul z₀
  have hz₀coe : (z₀ : ℂ) = (t : ℂ) * Complex.I := by rw [hz₀def]; exact ia_coe t ht
  have hw₂norm : ‖(w₂ : ℂ)‖ = t⁻¹ := by
    rw [hw₂def, hz₀def, ia_S t ht]
    exact Work.Asymptotics.ft_norm_coe (ia_coe t⁻¹ (inv_pos.mpr ht)) (inv_pos.mpr ht).le
  have hΔ : Work.Kernels.DeltaFun w₂ = (z₀ : ℂ) ^ 12 * Work.Kernels.DeltaFun z₀ := by
    rw [hw₂def]; exact Work.Asymptotics.EtailE.DeltaFun_Ssmul z₀
  have ht_ne : t ≠ 0 := ht.ne'
  have hz₀D : ‖Work.Kernels.DeltaFun z₀‖ ≠ 0 := by
    rw [norm_ne_zero_iff]; exact Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z₀
  have hq : ‖Work.Kernels.qParamFun w₂‖ = Real.exp (-(2 * Real.pi * t⁻¹)) := by
    rw [Work.Asymptotics.norm_qParamFun, hw₂im]
  have h248 : ¬ ((24 : ℕ) = 8) := by norm_num
  have hgp : ‖Work.Kernels.growthPrefactor 24 w z₀‖
      = ‖Work.Kernels.DeltaFun w‖ * ‖Work.Kernels.DeltaFun z₀‖ ^ 2
        * ‖Work.Kernels.jInvariantFun w - Work.Kernels.jInvariantFun z₀‖ := by
    simp only [Work.Kernels.growthPrefactor, norm_mul, norm_pow, if_neg h248]
  have hsl : ‖(w₂ : ℂ) ^ (10 : ℤ) * Work.Kernels.KPlus 24 w z₀‖
      ≤ C * (1 + ‖(w : ℂ)‖) ^ A * Real.exp (-(2 * Real.pi * t⁻¹))
          / ‖Work.Kernels.DeltaFun w₂
              * (Work.Kernels.jInvariantFun w - Work.Kernels.jInvariantFun w₂)‖ := by
    have h := hbound w w₂ hF.1 hF.2 (le_trans (by norm_num) hw₂1)
      (by rw [hjw₂]; exact hne)
    rw [show (((24 : ℕ) : ℤ) / 2 - 2) = (10 : ℤ) by norm_num, _root_.zpow_ofNat, hSw₂] at h
    rwa [hq] at h
  have h1 := kclear_slash_le 24 w z₀ w₂ t (10 : ℤ) 2 C A (Real.exp (-(2 * Real.pi * t⁻¹)))
    (fun τ z => Work.Kernels.KPlus 24 τ z) (fun τ z => Work.Kernels.KPlusClear 24 τ z)
    ht hz₀coe hw₂norm hΔ hjw₂ hne
    (Work.Kernels.ClearLink.KPlusClear_eq_smul 24 (Or.inr rfl) w z₀ hne) hgp hsl
  have hconv : C * (1 + ‖(w : ℂ)‖) ^ A * Real.exp (-(2 * Real.pi * t⁻¹))
        * ‖Work.Kernels.DeltaFun w‖ * ‖Work.Kernels.DeltaFun z₀‖ ^ 2 * t ^ (10 : ℤ)
        / (t ^ 12 * ‖Work.Kernels.DeltaFun z₀‖)
      = C * (1 + ‖(w : ℂ)‖) ^ A * Real.exp (-(2 * Real.pi * t⁻¹))
        * ‖Work.Kernels.DeltaFun w‖ * ‖Work.Kernels.DeltaFun z₀‖ * (t⁻¹) ^ 2 := by
    rw [arith_conv_twentyfour (C * (1 + ‖(w : ℂ)‖) ^ A * Real.exp (-(2 * Real.pi * t⁻¹)))
      (‖Work.Kernels.DeltaFun w‖) (‖Work.Kernels.DeltaFun z₀‖) t ht_ne hz₀D]
  rw [hconv] at h1
  have hΔw : ‖Work.Kernels.DeltaFun w‖ ≤ 2 * Real.exp (-(2 * Real.pi * w.im)) := by
    have h := Work.Asymptotics.DeltaFun_funnel_le w hF
    rwa [Work.Asymptotics.norm_qParamFun w] at h
  have hΔz₀ : ‖Work.Kernels.DeltaFun z₀‖ ≤ 2 * (t⁻¹) ^ 12 * Real.exp (-(2 * Real.pi * t⁻¹)) := by
    have hb : ‖Work.Kernels.DeltaFun w₂‖ ≤ 2 * Real.exp (-(2 * Real.pi * w₂.im)) :=
      Work.Asymptotics.DeltaFun_le_two_exp w₂ hw₂1
    rw [hw₂im] at hb
    have h2 : ‖Work.Kernels.DeltaFun w₂‖ = t ^ 12 * ‖Work.Kernels.DeltaFun z₀‖ := by
      rw [hΔ, norm_mul, norm_pow]
      have hz : ‖(z₀ : ℂ)‖ = t := Work.Asymptotics.ft_norm_coe hz₀coe ht.le
      rw [hz]
    have h3 : ‖Work.Kernels.DeltaFun z₀‖ = ‖Work.Kernels.DeltaFun w₂‖ * (t⁻¹) ^ 12 := by
      rw [h2]
      field_simp
      try ring
    rw [h3]
    calc ‖Work.Kernels.DeltaFun w₂‖ * (t⁻¹) ^ 12
        = (t⁻¹) ^ 12 * ‖Work.Kernels.DeltaFun w₂‖ := by ring
      _ ≤ (t⁻¹) ^ 12 * (2 * Real.exp (-(2 * Real.pi * t⁻¹))) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = 2 * (t⁻¹) ^ 12 * Real.exp (-(2 * Real.pi * t⁻¹)) := by ring
  have hpow : (t⁻¹) ^ 14 ≤ (1 + 1 / t) ^ 14 := by
    rw [one_div]
    exact pow_le_pow_left₀ (by positivity) (by linarith [inv_pos.mpr ht]) 14
  have hmul : ‖Work.Kernels.DeltaFun w‖ * ‖Work.Kernels.DeltaFun z₀‖
      ≤ (2 * Real.exp (-(2 * Real.pi * w.im)))
        * (2 * (t⁻¹) ^ 12 * Real.exp (-(2 * Real.pi * t⁻¹))) :=
    mul_le_mul hΔw hΔz₀ (by positivity) (by positivity)
  have hX : (0 : ℝ)
      ≤ C * (1 + ‖(w : ℂ)‖) ^ A * Real.exp (-(2 * Real.pi * t⁻¹)) * (t⁻¹) ^ 2 := by positivity
  have h14 : (t⁻¹) ^ 14 * Real.exp (-(4 * Real.pi * t⁻¹)) * Real.exp (-(2 * Real.pi * w.im))
      ≤ (1 + 1 / t) ^ 14 * Real.exp (-(4 * Real.pi * t⁻¹)) * Real.exp (-(2 * Real.pi * w.im)) := by
    have h2 : (0 : ℝ) ≤ Real.exp (-(4 * Real.pi * t⁻¹)) * Real.exp (-(2 * Real.pi * w.im)) := by
      positivity
    calc (t⁻¹) ^ 14 * Real.exp (-(4 * Real.pi * t⁻¹)) * Real.exp (-(2 * Real.pi * w.im))
        = (t⁻¹) ^ 14 * (Real.exp (-(4 * Real.pi * t⁻¹))
            * Real.exp (-(2 * Real.pi * w.im))) := by ring
      _ ≤ (1 + 1 / t) ^ 14 * (Real.exp (-(4 * Real.pi * t⁻¹))
            * Real.exp (-(2 * Real.pi * w.im))) := mul_le_mul_of_nonneg_right hpow h2
      _ = (1 + 1 / t) ^ 14 * Real.exp (-(4 * Real.pi * t⁻¹))
            * Real.exp (-(2 * Real.pi * w.im)) := by ring
  calc ‖Work.Kernels.KPlusClear 24 w z₀‖
      ≤ C * (1 + ‖(w : ℂ)‖) ^ A * Real.exp (-(2 * Real.pi * t⁻¹)) * ‖Work.Kernels.DeltaFun w‖
          * ‖Work.Kernels.DeltaFun z₀‖ * (t⁻¹) ^ 2 := h1
    _ = (C * (1 + ‖(w : ℂ)‖) ^ A * Real.exp (-(2 * Real.pi * t⁻¹)) * (t⁻¹) ^ 2)
          * (‖Work.Kernels.DeltaFun w‖ * ‖Work.Kernels.DeltaFun z₀‖) := by ring
    _ ≤ (C * (1 + ‖(w : ℂ)‖) ^ A * Real.exp (-(2 * Real.pi * t⁻¹)) * (t⁻¹) ^ 2)
          * ((2 * Real.exp (-(2 * Real.pi * w.im)))
              * (2 * (t⁻¹) ^ 12 * Real.exp (-(2 * Real.pi * t⁻¹)))) :=
        mul_le_mul_of_nonneg_left hmul hX
    _ = 4 * C * (1 + ‖(w : ℂ)‖) ^ A * ((t⁻¹) ^ 14 * (Real.exp (-(2 * Real.pi * t⁻¹))
          * Real.exp (-(2 * Real.pi * t⁻¹))) * Real.exp (-(2 * Real.pi * w.im))) := by ring
    _ = 4 * C * (1 + ‖(w : ℂ)‖) ^ A * ((t⁻¹) ^ 14 * Real.exp (-(4 * Real.pi * t⁻¹))
          * Real.exp (-(2 * Real.pi * w.im))) := by
        have hexp2 : Real.exp (-(2 * Real.pi * t⁻¹)) * Real.exp (-(2 * Real.pi * t⁻¹))
            = Real.exp (-(4 * Real.pi * t⁻¹)) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [hexp2]
    _ ≤ 4 * C * (1 + ‖(w : ℂ)‖) ^ A * ((1 + 1 / t) ^ 14 * Real.exp (-(4 * Real.pi * t⁻¹))
          * Real.exp (-(2 * Real.pi * w.im))) :=
        mul_le_mul_of_nonneg_left h14 (by positivity)
    _ = 4 * C * (1 + ‖(w : ℂ)‖) ^ A * (1 + 1 / t) ^ 14
          * Real.exp (-(4 * Real.pi * t⁻¹)) * Real.exp (-(2 * Real.pi * w.im)) := by ring

/-! ## The `K_-` half, `d = 8` -/

private lemma KMinusClearSharp_eight (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C A N : ℝ, 0 < C ∧ 0 ≤ A ∧ 0 ≤ N ∧
      ∀ (w : ℍ) (t : ℝ) (ht : 0 < t), Funnel w → t ≤ 1 →
        Work.Kernels.jInvariantFun w ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) →
        ‖Work.Kernels.KMinusClear ℓ 8 w (Work.Kernels.imagAxis t ht)‖
          ≤ C * (1 + ‖(w : ℂ)‖) ^ A * (1 + 1 / t) ^ N
              * Real.exp (-(Real.pi * t⁻¹)) * Real.exp (-(2 * Real.pi * w.im)) := by
  obtain ⟨C, A, hC, hA, hbound⟩ := KMinusFunnelSlash ℓ 8 (Or.inl rfl)
  refine ⟨2 * C, A, 12, by positivity, hA, by norm_num, ?_⟩
  intro w t ht hF ht1 hne
  rw [show (1 + 1 / t) ^ (12 : ℝ) = (1 + 1 / t) ^ 12 from Real.rpow_natCast _ _]
  set z₀ : ℍ := Work.Kernels.imagAxis t ht with hz₀def
  set w₂ : ℍ := ModularGroup.S • z₀ with hw₂def
  have hw₂im : w₂.im = t⁻¹ := by
    rw [hw₂def, hz₀def, ia_S t ht]; exact ia_im t⁻¹ (inv_pos.mpr ht)
  have hw₂1 : (1 : ℝ) ≤ w₂.im := by rw [hw₂im]; exact one_le_inv ht ht1
  have hSw₂ : ModularGroup.S • w₂ = z₀ := by rw [hw₂def]; exact S_invol z₀
  have hjw₂ : Work.Kernels.jInvariantFun w₂ = Work.Kernels.jInvariantFun z₀ := by
    rw [hw₂def]; exact Work.Kernels.KernelFacts.jInvariantFun_S_smul z₀
  have hz₀coe : (z₀ : ℂ) = (t : ℂ) * Complex.I := by rw [hz₀def]; exact ia_coe t ht
  have hw₂norm : ‖(w₂ : ℂ)‖ = t⁻¹ := by
    rw [hw₂def, hz₀def, ia_S t ht]
    exact Work.Asymptotics.ft_norm_coe (ia_coe t⁻¹ (inv_pos.mpr ht)) (inv_pos.mpr ht).le
  have hΔ : Work.Kernels.DeltaFun w₂ = (z₀ : ℂ) ^ 12 * Work.Kernels.DeltaFun z₀ := by
    rw [hw₂def]; exact Work.Asymptotics.EtailE.DeltaFun_Ssmul z₀
  have ht_ne : t ≠ 0 := ht.ne'
  have hz₀D : ‖Work.Kernels.DeltaFun z₀‖ ≠ 0 := by
    rw [norm_ne_zero_iff]; exact Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z₀
  have hgp : ‖Work.Kernels.growthPrefactor 8 w z₀‖
      = ‖Work.Kernels.DeltaFun w‖ * ‖Work.Kernels.DeltaFun z₀‖ ^ 1
        * ‖Work.Kernels.jInvariantFun w - Work.Kernels.jInvariantFun z₀‖ := by
    simp only [Work.Kernels.growthPrefactor, norm_mul, norm_pow, ↓reduceIte]
  have hsl : ‖(w₂ : ℂ) ^ (2 : ℤ) * Work.Kernels.KMinus ℓ 8 w z₀‖
      ≤ C * (1 + ‖(w : ℂ)‖) ^ A * ((1 + t⁻¹) ^ 2 * Real.exp (-(Real.pi * t⁻¹)))
          / ‖Work.Kernels.DeltaFun w₂
              * (Work.Kernels.jInvariantFun w - Work.Kernels.jInvariantFun w₂)‖ := by
    have h := hbound w w₂ hF.1 hF.2 (le_trans (by norm_num) hw₂1)
      (by rw [hjw₂]; exact hne)
    rw [show (((8 : ℕ) : ℤ) / 2 - 2) = (2 : ℤ) by norm_num, _root_.zpow_ofNat, hSw₂,
      hw₂norm, hw₂im] at h
    refine le_trans h (le_of_eq ?_)
    ring
  have h1 := kclear_slash_le 8 w z₀ w₂ t (2 : ℤ) 1 C A
    ((1 + t⁻¹) ^ 2 * Real.exp (-(Real.pi * t⁻¹)))
    (fun τ z => Work.Kernels.KMinus ℓ 8 τ z) (fun τ z => Work.Kernels.KMinusClear ℓ 8 τ z)
    ht hz₀coe hw₂norm hΔ hjw₂ hne
    (Work.Kernels.ClearLink.KMinusClear_eq_smul ℓ 8 (Or.inl rfl) w z₀ hne) hgp hsl
  have hconv : C * (1 + ‖(w : ℂ)‖) ^ A * ((1 + t⁻¹) ^ 2 * Real.exp (-(Real.pi * t⁻¹)))
        * ‖Work.Kernels.DeltaFun w‖ * ‖Work.Kernels.DeltaFun z₀‖ ^ 1 * t ^ (2 : ℤ)
        / (t ^ 12 * ‖Work.Kernels.DeltaFun z₀‖)
      = C * (1 + ‖(w : ℂ)‖) ^ A * ((1 + t⁻¹) ^ 2 * Real.exp (-(Real.pi * t⁻¹)))
        * ‖Work.Kernels.DeltaFun w‖ * (t⁻¹) ^ 10 := by
    rw [arith_conv_eight
      (C * (1 + ‖(w : ℂ)‖) ^ A * ((1 + t⁻¹) ^ 2 * Real.exp (-(Real.pi * t⁻¹))))
      (‖Work.Kernels.DeltaFun w‖) (‖Work.Kernels.DeltaFun z₀‖) t ht_ne hz₀D]
  rw [hconv] at h1
  have hΔw : ‖Work.Kernels.DeltaFun w‖ ≤ 2 * Real.exp (-(2 * Real.pi * w.im)) := by
    have h := Work.Asymptotics.DeltaFun_funnel_le w hF
    rwa [Work.Asymptotics.norm_qParamFun w] at h
  have hpow : (t⁻¹) ^ 10 ≤ (1 + 1 / t) ^ 10 := by
    rw [one_div]
    exact pow_le_pow_left₀ (by positivity) (by linarith [inv_pos.mpr ht]) 10
  have hcombo : (1 + t⁻¹) ^ 2 * (1 + 1 / t) ^ 10 ≤ (1 + 1 / t) ^ 12 := by
    have h1t : (1 : ℝ) + t⁻¹ = 1 + 1 / t := by rw [one_div]
    rw [h1t, ← pow_add]
  have hmul : ‖Work.Kernels.DeltaFun w‖ * (t⁻¹) ^ 10
      ≤ (2 * Real.exp (-(2 * Real.pi * w.im))) * (1 + 1 / t) ^ 10 :=
    mul_le_mul hΔw hpow (pow_nonneg (inv_nonneg.mpr ht.le) 10) (by positivity)
  have hX : (0 : ℝ) ≤ C * (1 + ‖(w : ℂ)‖) ^ A * Real.exp (-(Real.pi * t⁻¹)) := by
    positivity
  calc ‖Work.Kernels.KMinusClear ℓ 8 w z₀‖
      ≤ C * (1 + ‖(w : ℂ)‖) ^ A * ((1 + t⁻¹) ^ 2 * Real.exp (-(Real.pi * t⁻¹)))
          * ‖Work.Kernels.DeltaFun w‖ * (t⁻¹) ^ 10 := h1
    _ = (C * (1 + ‖(w : ℂ)‖) ^ A * Real.exp (-(Real.pi * t⁻¹)))
          * ((1 + t⁻¹) ^ 2 * (‖Work.Kernels.DeltaFun w‖ * (t⁻¹) ^ 10)) := by ring
    _ ≤ (C * (1 + ‖(w : ℂ)‖) ^ A * Real.exp (-(Real.pi * t⁻¹)))
          * ((1 + t⁻¹) ^ 2
              * ((2 * Real.exp (-(2 * Real.pi * w.im))) * (1 + 1 / t) ^ 10)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmul (by positivity)) hX
    _ = (2 * C * (1 + ‖(w : ℂ)‖) ^ A * Real.exp (-(Real.pi * t⁻¹))
          * Real.exp (-(2 * Real.pi * w.im))) * ((1 + t⁻¹) ^ 2 * (1 + 1 / t) ^ 10) := by ring
    _ ≤ (2 * C * (1 + ‖(w : ℂ)‖) ^ A * Real.exp (-(Real.pi * t⁻¹))
          * Real.exp (-(2 * Real.pi * w.im))) * ((1 + 1 / t) ^ 12) :=
        mul_le_mul_of_nonneg_left hcombo (by positivity)
    _ = 2 * C * (1 + ‖(w : ℂ)‖) ^ A * (1 + 1 / t) ^ 12
          * Real.exp (-(Real.pi * t⁻¹)) * Real.exp (-(2 * Real.pi * w.im)) := by ring

/-! ## The `K_-` half, `d = 24` -/

private lemma KMinusClearSharp_twentyfour (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C A N : ℝ, 0 < C ∧ 0 ≤ A ∧ 0 ≤ N ∧
      ∀ (w : ℍ) (t : ℝ) (ht : 0 < t), Funnel w → t ≤ 1 →
        Work.Kernels.jInvariantFun w ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) →
        ‖Work.Kernels.KMinusClear ℓ 24 w (Work.Kernels.imagAxis t ht)‖
          ≤ C * (1 + ‖(w : ℂ)‖) ^ A * (1 + 1 / t) ^ N
              * Real.exp (-(3 * Real.pi * t⁻¹)) * Real.exp (-(2 * Real.pi * w.im)) := by
  obtain ⟨C, A, hC, hA, hbound⟩ := KMinusFunnelSlash ℓ 24 (Or.inr rfl)
  refine ⟨4 * C, A, 16, by positivity, hA, by norm_num, ?_⟩
  intro w t ht hF ht1 hne
  rw [show (1 + 1 / t) ^ (16 : ℝ) = (1 + 1 / t) ^ 16 from Real.rpow_natCast _ _]
  set z₀ : ℍ := Work.Kernels.imagAxis t ht with hz₀def
  set w₂ : ℍ := ModularGroup.S • z₀ with hw₂def
  have hw₂im : w₂.im = t⁻¹ := by
    rw [hw₂def, hz₀def, ia_S t ht]; exact ia_im t⁻¹ (inv_pos.mpr ht)
  have hw₂1 : (1 : ℝ) ≤ w₂.im := by rw [hw₂im]; exact one_le_inv ht ht1
  have hSw₂ : ModularGroup.S • w₂ = z₀ := by rw [hw₂def]; exact S_invol z₀
  have hjw₂ : Work.Kernels.jInvariantFun w₂ = Work.Kernels.jInvariantFun z₀ := by
    rw [hw₂def]; exact Work.Kernels.KernelFacts.jInvariantFun_S_smul z₀
  have hz₀coe : (z₀ : ℂ) = (t : ℂ) * Complex.I := by rw [hz₀def]; exact ia_coe t ht
  have hw₂norm : ‖(w₂ : ℂ)‖ = t⁻¹ := by
    rw [hw₂def, hz₀def, ia_S t ht]
    exact Work.Asymptotics.ft_norm_coe (ia_coe t⁻¹ (inv_pos.mpr ht)) (inv_pos.mpr ht).le
  have hΔ : Work.Kernels.DeltaFun w₂ = (z₀ : ℂ) ^ 12 * Work.Kernels.DeltaFun z₀ := by
    rw [hw₂def]; exact Work.Asymptotics.EtailE.DeltaFun_Ssmul z₀
  have ht_ne : t ≠ 0 := ht.ne'
  have hz₀D : ‖Work.Kernels.DeltaFun z₀‖ ≠ 0 := by
    rw [norm_ne_zero_iff]; exact Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z₀
  have h248 : ¬ ((24 : ℕ) = 8) := by norm_num
  have hgp : ‖Work.Kernels.growthPrefactor 24 w z₀‖
      = ‖Work.Kernels.DeltaFun w‖ * ‖Work.Kernels.DeltaFun z₀‖ ^ 2
        * ‖Work.Kernels.jInvariantFun w - Work.Kernels.jInvariantFun z₀‖ := by
    simp only [Work.Kernels.growthPrefactor, norm_mul, norm_pow, if_neg h248]
  have hsl : ‖(w₂ : ℂ) ^ (10 : ℤ) * Work.Kernels.KMinus ℓ 24 w z₀‖
      ≤ C * (1 + ‖(w : ℂ)‖) ^ A * ((1 + t⁻¹) ^ 2 * Real.exp (-(Real.pi * t⁻¹)))
          / ‖Work.Kernels.DeltaFun w₂
              * (Work.Kernels.jInvariantFun w - Work.Kernels.jInvariantFun w₂)‖ := by
    have h := hbound w w₂ hF.1 hF.2 (le_trans (by norm_num) hw₂1)
      (by rw [hjw₂]; exact hne)
    rw [show (((24 : ℕ) : ℤ) / 2 - 2) = (10 : ℤ) by norm_num, _root_.zpow_ofNat, hSw₂,
      hw₂norm, hw₂im] at h
    refine le_trans h (le_of_eq ?_)
    ring
  have h1 := kclear_slash_le 24 w z₀ w₂ t (10 : ℤ) 2 C A
    ((1 + t⁻¹) ^ 2 * Real.exp (-(Real.pi * t⁻¹)))
    (fun τ z => Work.Kernels.KMinus ℓ 24 τ z) (fun τ z => Work.Kernels.KMinusClear ℓ 24 τ z)
    ht hz₀coe hw₂norm hΔ hjw₂ hne
    (Work.Kernels.ClearLink.KMinusClear_eq_smul ℓ 24 (Or.inr rfl) w z₀ hne) hgp hsl
  have hconv : C * (1 + ‖(w : ℂ)‖) ^ A * ((1 + t⁻¹) ^ 2 * Real.exp (-(Real.pi * t⁻¹)))
        * ‖Work.Kernels.DeltaFun w‖ * ‖Work.Kernels.DeltaFun z₀‖ ^ 2 * t ^ (10 : ℤ)
        / (t ^ 12 * ‖Work.Kernels.DeltaFun z₀‖)
      = C * (1 + ‖(w : ℂ)‖) ^ A * ((1 + t⁻¹) ^ 2 * Real.exp (-(Real.pi * t⁻¹)))
        * ‖Work.Kernels.DeltaFun w‖ * ‖Work.Kernels.DeltaFun z₀‖ * (t⁻¹) ^ 2 := by
    rw [arith_conv_twentyfour
      (C * (1 + ‖(w : ℂ)‖) ^ A * ((1 + t⁻¹) ^ 2 * Real.exp (-(Real.pi * t⁻¹))))
      (‖Work.Kernels.DeltaFun w‖) (‖Work.Kernels.DeltaFun z₀‖) t ht_ne hz₀D]
  rw [hconv] at h1
  have hΔw : ‖Work.Kernels.DeltaFun w‖ ≤ 2 * Real.exp (-(2 * Real.pi * w.im)) := by
    have h := Work.Asymptotics.DeltaFun_funnel_le w hF
    rwa [Work.Asymptotics.norm_qParamFun w] at h
  have hΔz₀ : ‖Work.Kernels.DeltaFun z₀‖ ≤ 2 * (t⁻¹) ^ 12 * Real.exp (-(2 * Real.pi * t⁻¹)) := by
    have hb : ‖Work.Kernels.DeltaFun w₂‖ ≤ 2 * Real.exp (-(2 * Real.pi * w₂.im)) :=
      Work.Asymptotics.DeltaFun_le_two_exp w₂ hw₂1
    rw [hw₂im] at hb
    have h2 : ‖Work.Kernels.DeltaFun w₂‖ = t ^ 12 * ‖Work.Kernels.DeltaFun z₀‖ := by
      rw [hΔ, norm_mul, norm_pow]
      have hz : ‖(z₀ : ℂ)‖ = t := Work.Asymptotics.ft_norm_coe hz₀coe ht.le
      rw [hz]
    have h3 : ‖Work.Kernels.DeltaFun z₀‖ = ‖Work.Kernels.DeltaFun w₂‖ * (t⁻¹) ^ 12 := by
      rw [h2]
      field_simp
      try ring
    rw [h3]
    calc ‖Work.Kernels.DeltaFun w₂‖ * (t⁻¹) ^ 12
        = (t⁻¹) ^ 12 * ‖Work.Kernels.DeltaFun w₂‖ := by ring
      _ ≤ (t⁻¹) ^ 12 * (2 * Real.exp (-(2 * Real.pi * t⁻¹))) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = 2 * (t⁻¹) ^ 12 * Real.exp (-(2 * Real.pi * t⁻¹)) := by ring
  have hmul : ‖Work.Kernels.DeltaFun w‖ * ‖Work.Kernels.DeltaFun z₀‖
      ≤ (2 * Real.exp (-(2 * Real.pi * w.im)))
        * (2 * (t⁻¹) ^ 12 * Real.exp (-(2 * Real.pi * t⁻¹))) :=
    mul_le_mul hΔw hΔz₀ (norm_nonneg _) (by positivity)
  have hcombo : (1 + t⁻¹) ^ 2 * (t⁻¹) ^ 14 ≤ (1 + 1 / t) ^ 16 := by
    have hp : (t⁻¹) ^ 14 ≤ (1 + 1 / t) ^ 14 := by
      rw [one_div]
      exact pow_le_pow_left₀ (by positivity) (by linarith [inv_pos.mpr ht]) 14
    have h1t : (1 : ℝ) + t⁻¹ = 1 + 1 / t := by rw [one_div]
    rw [h1t]
    calc (1 + 1 / t) ^ 2 * (t⁻¹) ^ 14 ≤ (1 + 1 / t) ^ 2 * (1 + 1 / t) ^ 14 :=
          mul_le_mul_of_nonneg_left hp (by positivity)
      _ = (1 + 1 / t) ^ 16 := by rw [← pow_add]
  have hexp3 : Real.exp (-(Real.pi * t⁻¹)) * Real.exp (-(2 * Real.pi * t⁻¹))
      = Real.exp (-(3 * Real.pi * t⁻¹)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hX : (0 : ℝ) ≤ C * (1 + ‖(w : ℂ)‖) ^ A * ((1 + t⁻¹) ^ 2 * (t⁻¹) ^ 2) := by
    positivity
  calc ‖Work.Kernels.KMinusClear ℓ 24 w z₀‖
      ≤ C * (1 + ‖(w : ℂ)‖) ^ A * ((1 + t⁻¹) ^ 2 * Real.exp (-(Real.pi * t⁻¹)))
          * ‖Work.Kernels.DeltaFun w‖ * ‖Work.Kernels.DeltaFun z₀‖ * (t⁻¹) ^ 2 := h1
    _ = (C * (1 + ‖(w : ℂ)‖) ^ A * ((1 + t⁻¹) ^ 2 * (t⁻¹) ^ 2))
          * (‖Work.Kernels.DeltaFun w‖ * ‖Work.Kernels.DeltaFun z₀‖ * Real.exp (-(Real.pi * t⁻¹))) := by ring
    _ ≤ (C * (1 + ‖(w : ℂ)‖) ^ A * ((1 + t⁻¹) ^ 2 * (t⁻¹) ^ 2))
          * ((2 * Real.exp (-(2 * Real.pi * w.im)))
              * (2 * (t⁻¹) ^ 12 * Real.exp (-(2 * Real.pi * t⁻¹)))
              * Real.exp (-(Real.pi * t⁻¹))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hmul (by positivity)) hX
    _ = 4 * C * (1 + ‖(w : ℂ)‖) ^ A * ((1 + t⁻¹) ^ 2 * (t⁻¹) ^ 14)
          * (Real.exp (-(Real.pi * t⁻¹)) * Real.exp (-(2 * Real.pi * t⁻¹)))
          * Real.exp (-(2 * Real.pi * w.im)) := by ring
    _ = 4 * C * (1 + ‖(w : ℂ)‖) ^ A * ((1 + t⁻¹) ^ 2 * (t⁻¹) ^ 14)
          * Real.exp (-(3 * Real.pi * t⁻¹)) * Real.exp (-(2 * Real.pi * w.im)) := by rw [hexp3]
    _ ≤ 4 * C * (1 + ‖(w : ℂ)‖) ^ A * (1 + 1 / t) ^ 16
          * Real.exp (-(3 * Real.pi * t⁻¹)) * Real.exp (-(2 * Real.pi * w.im)) := by
        have hinner : 4 * C * (1 + ‖(w : ℂ)‖) ^ A * ((1 + t⁻¹) ^ 2 * (t⁻¹) ^ 14)
            ≤ 4 * C * (1 + ‖(w : ℂ)‖) ^ A * (1 + 1 / t) ^ 16 :=
          mul_le_mul_of_nonneg_left hcombo (by positivity)
        have h2 : (0 : ℝ) ≤ Real.exp (-(3 * Real.pi * t⁻¹))
            * Real.exp (-(2 * Real.pi * w.im)) := by positivity
        calc 4 * C * (1 + ‖(w : ℂ)‖) ^ A * ((1 + t⁻¹) ^ 2 * (t⁻¹) ^ 14)
              * Real.exp (-(3 * Real.pi * t⁻¹)) * Real.exp (-(2 * Real.pi * w.im))
            = (4 * C * (1 + ‖(w : ℂ)‖) ^ A * ((1 + t⁻¹) ^ 2 * (t⁻¹) ^ 14))
              * (Real.exp (-(3 * Real.pi * t⁻¹)) * Real.exp (-(2 * Real.pi * w.im))) := by ring
          _ ≤ (4 * C * (1 + ‖(w : ℂ)‖) ^ A * (1 + 1 / t) ^ 16)
              * (Real.exp (-(3 * Real.pi * t⁻¹)) * Real.exp (-(2 * Real.pi * w.im))) :=
              mul_le_mul_of_nonneg_right hinner h2
          _ = 4 * C * (1 + ‖(w : ℂ)‖) ^ A * (1 + 1 / t) ^ 16
              * Real.exp (-(3 * Real.pi * t⁻¹)) * Real.exp (-(2 * Real.pi * w.im)) := by ring

/-! ## The two halves, assembled -/

private theorem KPlusClearSharp (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C A N : ℝ, 0 < C ∧ 0 ≤ A ∧ 0 ≤ N ∧
      ∀ (w : ℍ) (t : ℝ) (ht : 0 < t), Funnel w → t ≤ 1 →
        Work.Kernels.jInvariantFun w ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) →
        ‖Work.Kernels.KPlusClear d w (Work.Kernels.imagAxis t ht)‖
          ≤ C * (1 + ‖(w : ℂ)‖) ^ A * (1 + 1 / t) ^ N
              * Real.exp (-((if d = 8 then 2 * Real.pi else 4 * Real.pi) * t⁻¹))
              * Real.exp (-(2 * Real.pi * w.im)) := by
  rcases hd with rfl | rfl
  · simpa using KPlusClearSharp_eight
  · simpa using KPlusClearSharp_twentyfour

private theorem KMinusClearSharp (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C A N : ℝ, 0 < C ∧ 0 ≤ A ∧ 0 ≤ N ∧
      ∀ (w : ℍ) (t : ℝ) (ht : 0 < t), Funnel w → t ≤ 1 →
        Work.Kernels.jInvariantFun w ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) →
        ‖Work.Kernels.KMinusClear ℓ d w (Work.Kernels.imagAxis t ht)‖
          ≤ C * (1 + ‖(w : ℂ)‖) ^ A * (1 + 1 / t) ^ N
              * Real.exp (-((if d = 8 then Real.pi else 3 * Real.pi) * t⁻¹))
              * Real.exp (-(2 * Real.pi * w.im)) := by
  rcases hd with rfl | rfl
  · simpa using KMinusClearSharp_eight ℓ
  · simpa using KMinusClearSharp_twentyfour ℓ

/-! ## The main theorem -/

theorem KfunClearSharp (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C A N : ℝ, 0 < C ∧ 0 ≤ A ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane) (t : ℝ) (ht : 0 < t), Work.Asymptotics.Funnel w → t ≤ 1 →
        Work.Kernels.jInvariantFun w ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) →
        ‖Work.Kernels.KfunClear ℓ d w (Work.Kernels.imagAxis t ht)‖
          ≤ C * (1 + ‖(w : ℂ)‖) ^ A * (1 + 1 / t) ^ N
              * Real.exp (-((if d = 8 then Real.pi else 3 * Real.pi) * t⁻¹))
              * Real.exp (-(2 * Real.pi * w.im)) := by
  obtain ⟨CP, AP, NP, hCP, hAP, hNP, hP⟩ := KPlusClearSharp d hd
  obtain ⟨CM, AM, NM, hCM, hAM, hNM, hM⟩ := KMinusClearSharp ℓ d hd
  refine ⟨CP + CM, max AP AM, max NP NM, by linarith,
    le_trans hAP (le_max_left _ _), le_trans hNP (le_max_left _ _), ?_⟩
  intro w t ht hF ht1 hne
  have hPw := hP w t ht hF ht1 hne
  have hMw := hM w t ht hF ht1 hne
  have hw1 : (1 : ℝ) ≤ 1 + ‖(w : ℂ)‖ := by have h := norm_nonneg (w : ℂ); linarith
  have ht1' : (1 : ℝ) ≤ 1 + 1 / t := by rw [one_div]; have h := inv_pos.mpr ht; linarith
  have hA1 : (1 + ‖(w : ℂ)‖) ^ AP ≤ (1 + ‖(w : ℂ)‖) ^ max AP AM :=
    Real.rpow_le_rpow_of_exponent_le hw1 (le_max_left _ _)
  have hA2 : (1 + ‖(w : ℂ)‖) ^ AM ≤ (1 + ‖(w : ℂ)‖) ^ max AP AM :=
    Real.rpow_le_rpow_of_exponent_le hw1 (le_max_right _ _)
  have hN1 : (1 + 1 / t) ^ NP ≤ (1 + 1 / t) ^ max NP NM :=
    Real.rpow_le_rpow_of_exponent_le ht1' (le_max_left _ _)
  have hN2 : (1 + 1 / t) ^ NM ≤ (1 + 1 / t) ^ max NP NM :=
    Real.rpow_le_rpow_of_exponent_le ht1' (le_max_right _ _)
  have hc1 : (if d = 8 then Real.pi else 3 * Real.pi)
      ≤ (if d = 8 then 2 * Real.pi else 4 * Real.pi) := by
    split_ifs <;> nlinarith [Real.pi_pos]
  have hE1 : Real.exp (-((if d = 8 then 2 * Real.pi else 4 * Real.pi) * t⁻¹))
      ≤ Real.exp (-((if d = 8 then Real.pi else 3 * Real.pi) * t⁻¹)) := by
    refine Real.exp_le_exp.mpr ?_
    have h := mul_le_mul_of_nonneg_right hc1 (inv_pos.mpr ht).le
    linarith
  have htri : ‖Work.Kernels.KfunClear ℓ d w (Work.Kernels.imagAxis t ht)‖
      ≤ (‖Work.Kernels.KPlusClear d w (Work.Kernels.imagAxis t ht)‖
          + ‖Work.Kernels.KMinusClear ℓ d w (Work.Kernels.imagAxis t ht)‖) / 2 := by
    have h := norm_add_le (Work.Kernels.KPlusClear d w (Work.Kernels.imagAxis t ht))
      (Work.Kernels.KMinusClear ℓ d w (Work.Kernels.imagAxis t ht))
    simp only [Work.Kernels.KfunClear]
    rw [norm_div]
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2]
    linarith
  have hP' : ‖Work.Kernels.KPlusClear d w (Work.Kernels.imagAxis t ht)‖
      ≤ CP * (1 + ‖(w : ℂ)‖) ^ max AP AM * (1 + 1 / t) ^ max NP NM
          * Real.exp (-((if d = 8 then Real.pi else 3 * Real.pi) * t⁻¹))
          * Real.exp (-(2 * Real.pi * w.im)) := by
    refine le_trans hPw ?_
    calc CP * (1 + ‖(w : ℂ)‖) ^ AP * (1 + 1 / t) ^ NP
          * Real.exp (-((if d = 8 then 2 * Real.pi else 4 * Real.pi) * t⁻¹))
          * Real.exp (-(2 * Real.pi * w.im))
        = CP * ((1 + ‖(w : ℂ)‖) ^ AP * ((1 + 1 / t) ^ NP
            * (Real.exp (-((if d = 8 then 2 * Real.pi else 4 * Real.pi) * t⁻¹))
              * Real.exp (-(2 * Real.pi * w.im))))) := by ring
      _ ≤ CP * ((1 + ‖(w : ℂ)‖) ^ max AP AM * ((1 + 1 / t) ^ max NP NM
            * (Real.exp (-((if d = 8 then Real.pi else 3 * Real.pi) * t⁻¹))
              * Real.exp (-(2 * Real.pi * w.im))))) := by
          refine mul_le_mul_of_nonneg_left ?_ hCP.le
          exact mul_le_mul hA1
            (mul_le_mul hN1 (mul_le_mul hE1 le_rfl (by positivity) (by positivity))
              (by positivity) (by positivity)) (by positivity) (by positivity)
      _ = CP * (1 + ‖(w : ℂ)‖) ^ max AP AM * (1 + 1 / t) ^ max NP NM
          * Real.exp (-((if d = 8 then Real.pi else 3 * Real.pi) * t⁻¹))
          * Real.exp (-(2 * Real.pi * w.im)) := by ring
  have hM' : ‖Work.Kernels.KMinusClear ℓ d w (Work.Kernels.imagAxis t ht)‖
      ≤ CM * (1 + ‖(w : ℂ)‖) ^ max AP AM * (1 + 1 / t) ^ max NP NM
          * Real.exp (-((if d = 8 then Real.pi else 3 * Real.pi) * t⁻¹))
          * Real.exp (-(2 * Real.pi * w.im)) := by
    refine le_trans hMw ?_
    calc CM * (1 + ‖(w : ℂ)‖) ^ AM * (1 + 1 / t) ^ NM
          * Real.exp (-((if d = 8 then Real.pi else 3 * Real.pi) * t⁻¹))
          * Real.exp (-(2 * Real.pi * w.im))
        = CM * ((1 + ‖(w : ℂ)‖) ^ AM * ((1 + 1 / t) ^ NM
            * (Real.exp (-((if d = 8 then Real.pi else 3 * Real.pi) * t⁻¹))
              * Real.exp (-(2 * Real.pi * w.im))))) := by ring
      _ ≤ CM * ((1 + ‖(w : ℂ)‖) ^ max AP AM * ((1 + 1 / t) ^ max NP NM
            * (Real.exp (-((if d = 8 then Real.pi else 3 * Real.pi) * t⁻¹))
              * Real.exp (-(2 * Real.pi * w.im))))) := by
          refine mul_le_mul_of_nonneg_left ?_ hCM.le
          exact mul_le_mul hA2
            (mul_le_mul hN2 (mul_le_mul le_rfl le_rfl (by positivity) (by positivity))
              (by positivity) (by positivity)) (by positivity) (by positivity)
      _ = CM * (1 + ‖(w : ℂ)‖) ^ max AP AM * (1 + 1 / t) ^ max NP NM
          * Real.exp (-((if d = 8 then Real.pi else 3 * Real.pi) * t⁻¹))
          * Real.exp (-(2 * Real.pi * w.im)) := by ring
  have hsum : (CP * (1 + ‖(w : ℂ)‖) ^ max AP AM * (1 + 1 / t) ^ max NP NM
        * Real.exp (-((if d = 8 then Real.pi else 3 * Real.pi) * t⁻¹))
        * Real.exp (-(2 * Real.pi * w.im))
      + CM * (1 + ‖(w : ℂ)‖) ^ max AP AM * (1 + 1 / t) ^ max NP NM
        * Real.exp (-((if d = 8 then Real.pi else 3 * Real.pi) * t⁻¹))
        * Real.exp (-(2 * Real.pi * w.im))) / 2
      ≤ (CP + CM) * (1 + ‖(w : ℂ)‖) ^ max AP AM * (1 + 1 / t) ^ max NP NM
        * Real.exp (-((if d = 8 then Real.pi else 3 * Real.pi) * t⁻¹))
        * Real.exp (-(2 * Real.pi * w.im)) := by
    have h0 : (0 : ℝ) ≤ (CP + CM) * (1 + ‖(w : ℂ)‖) ^ max AP AM * (1 + 1 / t) ^ max NP NM
        * Real.exp (-((if d = 8 then Real.pi else 3 * Real.pi) * t⁻¹))
        * Real.exp (-(2 * Real.pi * w.im)) := by positivity
    nlinarith [h0]
  calc ‖Work.Kernels.KfunClear ℓ d w (Work.Kernels.imagAxis t ht)‖
      ≤ (‖Work.Kernels.KPlusClear d w (Work.Kernels.imagAxis t ht)‖
          + ‖Work.Kernels.KMinusClear ℓ d w (Work.Kernels.imagAxis t ht)‖) / 2 := htri
    _ ≤ (CP * (1 + ‖(w : ℂ)‖) ^ max AP AM * (1 + 1 / t) ^ max NP NM
          * Real.exp (-((if d = 8 then Real.pi else 3 * Real.pi) * t⁻¹))
          * Real.exp (-(2 * Real.pi * w.im))
        + CM * (1 + ‖(w : ℂ)‖) ^ max AP AM * (1 + 1 / t) ^ max NP NM
          * Real.exp (-((if d = 8 then Real.pi else 3 * Real.pi) * t⁻¹))
          * Real.exp (-(2 * Real.pi * w.im))) / 2 := by linarith
    _ ≤ (CP + CM) * (1 + ‖(w : ℂ)‖) ^ max AP AM * (1 + 1 / t) ^ max NP NM
          * Real.exp (-((if d = 8 then Real.pi else 3 * Real.pi) * t⁻¹))
          * Real.exp (-(2 * Real.pi * w.im)) := hsum

end

end Work.Asymptotics
