import Mathlib
import Submission.Work.CKFinal.LineDecay.Defs
import Submission.Work.CKFinal.LineDecay.PhiAxis
import Submission.Work.CKFinal.LineDecay.slash_qtau_twentyfour
import Submission.Work.CKFinal.LineDecay.denom_growth_segment
import Submission.Work.CKFinal.LineDecay.P2_norm_segment

namespace Work.CKFinal.LineDecay

open UpperHalfPlane

/-!
# CKMRV (5.12) on the lines `Re τ = ±1/2`: the horizontal pieces `P₂` in dimension 24

The `d = 24` analogue of `P2_line_bound_eight`.
-/

/-- A point of the vertical lines `Re τ = ±1/2` with `Im τ ≥ 2` lies in the fundamental
domain `𝒟` of `Γ(2)`. -/
private lemma line_mem_DomainD (τ : UpperHalfPlane)
    (hline : τ.re = 1 / 2 ∨ τ.re = -1 / 2) (h2 : 2 ≤ τ.im) :
    τ ∈ Work.Asymptotics.DomainD := by
  rw [Work.Asymptotics.mem_DomainD]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rcases hline with h | h <;> rw [h] <;> norm_num
  · rcases hline with h | h <;> rw [h] <;> norm_num
  · have him : ((τ : ℂ) - (1 / 2 : ℂ)).im = τ.im := by
      simp [Complex.sub_im, UpperHalfPlane.coe_im]
    have h := Complex.abs_im_le_norm ((τ : ℂ) - (1 / 2 : ℂ))
    rw [him, abs_of_pos τ.im_pos] at h
    linarith
  · have him : ((τ : ℂ) + (1 / 2 : ℂ)).im = τ.im := by
      simp [Complex.add_im, UpperHalfPlane.coe_im]
    have h := Complex.abs_im_le_norm ((τ : ℂ) + (1 / 2 : ℂ))
    rw [him, abs_of_pos τ.im_pos] at h
    linarith

/-- The modular `S`-action is an involution on `ℍ`. -/
private lemma smul_S_S (w : UpperHalfPlane) : ModularGroup.S • (ModularGroup.S • w) = w := by
  rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.modular_S_smul]
  ext
  simp only [UpperHalfPlane.coe_mk, inv_neg, neg_neg, inv_inv]

/-- For `w` with `Im w = 1` and `|Re w| ≤ 1`, the point `S • w = -1/w` has norm `≥ 1/2`. -/
private lemma norm_S_smul_ge (w : UpperHalfPlane) (hw : w.im = 1) (hwr : |w.re| ≤ 1) :
    (1 / 2 : ℝ) ≤ ‖((ModularGroup.S • w : UpperHalfPlane) : ℂ)‖ := by
  have hwne : (w : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    rw [UpperHalfPlane.coe_im, hw] at this
    simp at this
  have hwpos : 0 < ‖(w : ℂ)‖ := norm_pos_iff.mpr hwne
  have hw2 : ‖(w : ℂ)‖ ≤ 2 := by
    have h := Complex.norm_le_abs_re_add_abs_im (w : ℂ)
    rw [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, hw, abs_one] at h
    linarith [abs_nonneg w.re]
  have hz : ((ModularGroup.S • w : UpperHalfPlane) : ℂ) = (-(w : ℂ))⁻¹ :=
    congrArg UpperHalfPlane.coe (UpperHalfPlane.modular_S_smul w)
  rw [hz, norm_inv, norm_neg]
  simpa only [one_div] using one_div_le_one_div_of_le hwpos hw2

/-- `Kax` is additive in the kernel. -/
private lemma Kax_add {K₁ K₂ : UpperHalfPlane → UpperHalfPlane → ℂ} (τ : UpperHalfPlane) (x t : ℝ) :
    Kax (fun a b => K₁ a b + K₂ a b) τ x t = Kax K₁ τ x t + Kax K₂ τ x t := by
  unfold Kax
  by_cases h : 0 < t <;> simp [h]

/-- `Kax` is additive in the kernel. -/
private lemma Kax_sub {K₁ K₂ : UpperHalfPlane → UpperHalfPlane → ℂ} (τ : UpperHalfPlane) (x t : ℝ) :
    Kax (fun a b => K₁ a b - K₂ a b) τ x t = Kax K₁ τ x t - Kax K₂ τ x t := by
  unfold Kax
  by_cases h : 0 < t <;> simp [h]

/-- `Kax (K / 2) = (Kax K) / 2`. -/
private lemma Kax_div_two (K : UpperHalfPlane → UpperHalfPlane → ℂ) (τ : UpperHalfPlane) (x t : ℝ) :
    Kax (fun a b => K a b / 2) τ x t = Kax K τ x t / 2 := by
  unfold Kax
  by_cases h : 0 < t <;> simp [h]

/-- The pointwise segment bound for a single kernel on `{Im = 1, |Re| ≤ 1}`, transferred from the
CKMRV quotient bound by the divisor lower bound. -/
private theorem seg_single (K : UpperHalfPlane → UpperHalfPlane → ℂ) (Cs As c Yd : ℝ)
    (hCs : 0 ≤ Cs) (hAs : 0 ≤ As) (hc : 0 < c)
    (hslash : ∀ τ z : UpperHalfPlane, τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im →
        (1 : ℝ) / 3 ≤ z.im → Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z →
        ‖(z : ℂ) ^ ((24 : ℤ) / 2 - 2) * K τ (ModularGroup.S • z)‖
          ≤ Cs * (1 + ‖(τ : ℂ)‖) ^ As * ‖Work.Kernels.qParamFun τ‖
              * Real.exp (-(Real.pi * z.im))
            / ‖Work.Kernels.DeltaFun z
                * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖)
    (hD : ∀ τ w : UpperHalfPlane, (τ.re = 1 / 2 ∨ τ.re = -1 / 2) → Yd ≤ τ.im →
        w.im = 1 → |w.re| ≤ 1 →
        c * Real.exp (2 * Real.pi * τ.im)
          ≤ ‖Work.Kernels.DeltaFun (ModularGroup.S • w)
              * (Work.Kernels.jInvariantFun τ
                  - Work.Kernels.jInvariantFun (ModularGroup.S • w))‖) :
    ∀ (τ : UpperHalfPlane) (x : ℝ), (τ.re = 1 / 2 ∨ τ.re = -1 / 2) → max Yd 2 ≤ τ.im →
      |x| ≤ 1 →
      ‖Kax K τ x 1‖
        ≤ (1024 * Cs / c * (5 / 2 : ℝ) ^ As) * τ.im ^ As
            * Real.exp (-(3 * Real.pi * τ.im)) := by
  intro τ x hline hY hx
  have h1 : (0 : ℝ) < 1 := by norm_num
  set w : UpperHalfPlane := (x : ℝ) +ᵥ Work.Kernels.imagAxis 1 h1 with hwdef
  have hwre : w.re = x := by
    rw [hwdef, UpperHalfPlane.vadd_re]; simp [Work.Kernels.imagAxis]
  have hwim : w.im = 1 := by
    rw [hwdef, UpperHalfPlane.vadd_im]; simp [Work.Kernels.imagAxis]
  set z : UpperHalfPlane := ModularGroup.S • w with hzdef
  have hSzz : ModularGroup.S • z = w := by rw [hzdef, smul_S_S]
  have hkax : Kax K τ x 1 = K τ (ModularGroup.S • z) := by
    rw [Kax, dif_pos h1, ← hwdef, ← hSzz]
  rw [hkax]
  have hτ2 : 2 ≤ τ.im := le_trans (le_max_right Yd 2) hY
  have hYd' : Yd ≤ τ.im := le_trans (le_max_left Yd 2) hY
  have hτD : τ ∈ Work.Asymptotics.DomainD := line_mem_DomainD τ hline hτ2
  have hwr : |w.re| ≤ 1 := by rw [hwre]; exact hx
  have hzim : (1 : ℝ) / 3 ≤ z.im := by
    have := (S_smul_im_bounds w hwim hwr).1
    rw [hzdef]; linarith
  have hDbound := hD τ w hline hYd' hwim hwr
  have hcepos : 0 < c * Real.exp (2 * Real.pi * τ.im) := mul_pos hc (Real.exp_pos _)
  have hne : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z := by
    intro heq
    have hsub : Work.Kernels.jInvariantFun τ
        - Work.Kernels.jInvariantFun (ModularGroup.S • w) = 0 := by
      rw [hzdef] at heq; rw [heq, sub_self]
    rw [hsub, mul_zero, norm_zero] at hDbound
    linarith
  have hsl := hslash τ z hτD hτ2 hzim hne
  set D : ℝ := ‖Work.Kernels.DeltaFun z
      * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ with hDdef
  have hDlow : c * Real.exp (2 * Real.pi * τ.im) ≤ D := by
    rw [hDdef, hzdef]; exact hDbound
  have hDpos : 0 < D := lt_of_lt_of_le hcepos hDlow
  have hzpn : (1 / 1024 : ℝ) ≤ ‖(z : ℂ) ^ ((24 : ℤ) / 2 - 2)‖ := by
    have he : ((24 : ℤ) / 2 - 2) = (10 : ℤ) := by norm_num
    rw [he, zpow_ofNat, norm_pow]
    have hzge : (1 / 2 : ℝ) ≤ ‖(z : ℂ)‖ := by rw [hzdef]; exact norm_S_smul_ge w hwim hwr
    calc (1 / 1024 : ℝ) = (1 / 2 : ℝ) ^ 10 := by norm_num
      _ ≤ ‖(z : ℂ)‖ ^ 10 := pow_le_pow_left₀ (by norm_num) hzge 10
  have hsl' : ‖(z : ℂ) ^ ((24 : ℤ) / 2 - 2)‖ * ‖K τ (ModularGroup.S • z)‖
      ≤ Cs * (1 + ‖(τ : ℂ)‖) ^ As * ‖Work.Kernels.qParamFun τ‖
          * Real.exp (-(Real.pi * z.im)) / D := by
    rw [hDdef, ← norm_mul]; exact hsl
  have hq : ‖Work.Kernels.qParamFun τ‖ = Real.exp (-(2 * Real.pi * τ.im)) :=
    Work.Asymptotics.norm_qParamFun τ
  have hDinv : (1 : ℝ) / D ≤ 1 / (c * Real.exp (2 * Real.pi * τ.im)) :=
    one_div_le_one_div_of_le hcepos hDlow
  have hE1 : Real.exp (-(Real.pi * z.im)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos, hzim]
  have hE2 : Real.exp (-(4 * Real.pi * τ.im)) ≤ Real.exp (-(3 * Real.pi * τ.im)) := by
    rw [Real.exp_le_exp]; nlinarith [Real.pi_pos, τ.im_pos]
  have hEsplit : Real.exp (-(2 * Real.pi * τ.im)) * Real.exp (-(2 * Real.pi * τ.im))
      = Real.exp (-(4 * Real.pi * τ.im)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hA : (1 + ‖(τ : ℂ)‖) ^ As ≤ (5 / 2 : ℝ) ^ As * τ.im ^ As := by
    have hre : |τ.re| = 1 / 2 := by rcases hline with h | h <;> rw [h] <;> norm_num
    have hnorm : ‖(τ : ℂ)‖ ≤ 1 / 2 + τ.im := by
      have h := Complex.norm_le_abs_re_add_abs_im (τ : ℂ)
      rw [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, hre, abs_of_pos τ.im_pos] at h
      linarith
    have h1' : 1 + ‖(τ : ℂ)‖ ≤ (5 / 2) * τ.im := by nlinarith [hτ2]
    have h2 : ((5 / 2 : ℝ) * τ.im) ^ As = (5 / 2 : ℝ) ^ As * τ.im ^ As :=
      Real.mul_rpow (by norm_num) τ.im_pos.le
    calc (1 + ‖(τ : ℂ)‖) ^ As ≤ ((5 / 2 : ℝ) * τ.im) ^ As :=
          Real.rpow_le_rpow (by positivity) h1' hAs
      _ = (5 / 2 : ℝ) ^ As * τ.im ^ As := h2
  -- step 1: undo the slash prefactor `z^{10}`
  have hstep1 : ‖K τ (ModularGroup.S • z)‖
      ≤ (Cs * (1 + ‖(τ : ℂ)‖) ^ As * ‖Work.Kernels.qParamFun τ‖
          * Real.exp (-(Real.pi * z.im)) / D) * 1024 := by
    have ha : 0 < ‖(z : ℂ) ^ ((24 : ℤ) / 2 - 2)‖ := lt_of_lt_of_le (by norm_num) hzpn
    have h1' : ‖K τ (ModularGroup.S • z)‖
        ≤ (Cs * (1 + ‖(τ : ℂ)‖) ^ As * ‖Work.Kernels.qParamFun τ‖
            * Real.exp (-(Real.pi * z.im)) / D) / ‖(z : ℂ) ^ ((24 : ℤ) / 2 - 2)‖ := by
      rw [le_div_iff₀ ha, mul_comm]; exact hsl'
    refine le_trans h1' ?_
    rw [div_le_iff₀ ha]
    have hnn : 0 ≤ (Cs * (1 + ‖(τ : ℂ)‖) ^ As * ‖Work.Kernels.qParamFun τ‖
        * Real.exp (-(Real.pi * z.im)) / D) * 1024 := by
      apply mul_nonneg _ (by norm_num)
      apply div_nonneg _ hDpos.le
      exact mul_nonneg (mul_nonneg (mul_nonneg hCs (Real.rpow_nonneg (by positivity) _))
        (norm_nonneg _)) (Real.exp_pos _).le
    calc Cs * (1 + ‖(τ : ℂ)‖) ^ As * ‖Work.Kernels.qParamFun τ‖
            * Real.exp (-(Real.pi * z.im)) / D
        = (Cs * (1 + ‖(τ : ℂ)‖) ^ As * ‖Work.Kernels.qParamFun τ‖
            * Real.exp (-(Real.pi * z.im)) / D) * 1024 * (1 / 1024) := by ring
      _ ≤ (Cs * (1 + ‖(τ : ℂ)‖) ^ As * ‖Work.Kernels.qParamFun τ‖
            * Real.exp (-(Real.pi * z.im)) / D) * 1024
            * ‖(z : ℂ) ^ ((24 : ℤ) / 2 - 2)‖ := mul_le_mul_of_nonneg_left hzpn hnn
  -- step 2: bound the numerator and the denominator
  have hstepA : Cs * (1 + ‖(τ : ℂ)‖) ^ As * ‖Work.Kernels.qParamFun τ‖
        * Real.exp (-(Real.pi * z.im)) / D * 1024
      ≤ 1024 * Cs * ((5 / 2 : ℝ) ^ As * τ.im ^ As)
          * Real.exp (-(2 * Real.pi * τ.im)) / (c * Real.exp (2 * Real.pi * τ.im)) := by
    rw [hq]
    have hnum : Cs * (1 + ‖(τ : ℂ)‖) ^ As * Real.exp (-(2 * Real.pi * τ.im))
        * Real.exp (-(Real.pi * z.im))
        ≤ Cs * ((5 / 2 : ℝ) ^ As * τ.im ^ As) * Real.exp (-(2 * Real.pi * τ.im)) := by
      have hb : Cs * (1 + ‖(τ : ℂ)‖) ^ As * Real.exp (-(2 * Real.pi * τ.im))
          * Real.exp (-(Real.pi * z.im))
          ≤ Cs * (1 + ‖(τ : ℂ)‖) ^ As * Real.exp (-(2 * Real.pi * τ.im)) := by
        have hcomm : 0 ≤ Cs * (1 + ‖(τ : ℂ)‖) ^ As * Real.exp (-(2 * Real.pi * τ.im)) :=
          mul_nonneg (mul_nonneg hCs (Real.rpow_nonneg (by positivity) _))
            (Real.exp_pos _).le
        have := mul_le_mul_of_nonneg_left hE1 hcomm
        rwa [mul_one] at this
      have hc2 : Cs * (1 + ‖(τ : ℂ)‖) ^ As * Real.exp (-(2 * Real.pi * τ.im))
          ≤ Cs * ((5 / 2 : ℝ) ^ As * τ.im ^ As) * Real.exp (-(2 * Real.pi * τ.im)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA hCs) (Real.exp_pos _).le
      exact le_trans hb hc2
    calc Cs * (1 + ‖(τ : ℂ)‖) ^ As * Real.exp (-(2 * Real.pi * τ.im))
            * Real.exp (-(Real.pi * z.im)) / D * 1024
        = (Cs * (1 + ‖(τ : ℂ)‖) ^ As * Real.exp (-(2 * Real.pi * τ.im))
            * Real.exp (-(Real.pi * z.im))) * (1 / D) * 1024 := by ring
      _ ≤ (Cs * ((5 / 2 : ℝ) ^ As * τ.im ^ As) * Real.exp (-(2 * Real.pi * τ.im)))
            * (1 / (c * Real.exp (2 * Real.pi * τ.im))) * 1024 := by
          apply mul_le_mul_of_nonneg_right _ (by norm_num)
          apply mul_le_mul hnum hDinv _ _
          · exact le_of_lt (one_div_pos.mpr hDpos)
          · exact mul_nonneg (mul_nonneg hCs (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
              (Real.rpow_nonneg τ.im_pos.le _))) (Real.exp_pos _).le
      _ = 1024 * Cs * ((5 / 2 : ℝ) ^ As * τ.im ^ As)
            * Real.exp (-(2 * Real.pi * τ.im)) / (c * Real.exp (2 * Real.pi * τ.im)) := by ring
  have hbound : 1024 * Cs * ((5 / 2 : ℝ) ^ As * τ.im ^ As)
        * Real.exp (-(2 * Real.pi * τ.im)) / (c * Real.exp (2 * Real.pi * τ.im))
      ≤ (1024 * Cs / c * (5 / 2 : ℝ) ^ As) * τ.im ^ As
          * Real.exp (-(3 * Real.pi * τ.im)) := by
    have heq : 1024 * Cs * ((5 / 2 : ℝ) ^ As * τ.im ^ As)
          * Real.exp (-(2 * Real.pi * τ.im)) / (c * Real.exp (2 * Real.pi * τ.im))
        = 1024 * Cs / c * ((5 / 2 : ℝ) ^ As * τ.im ^ As)
            * (Real.exp (-(2 * Real.pi * τ.im)) * Real.exp (-(2 * Real.pi * τ.im))) := by
      rw [div_eq_mul_inv, mul_inv, ← Real.exp_neg]; ring
    rw [heq, hEsplit]
    have hC0 : 0 ≤ 1024 * Cs / c * ((5 / 2 : ℝ) ^ As * τ.im ^ As) :=
      mul_nonneg (div_nonneg (mul_nonneg (by norm_num) hCs) hc.le)
        (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg τ.im_pos.le _))
    refine le_trans (mul_le_mul_of_nonneg_left hE2 hC0) (le_of_eq ?_)
    ring
  exact le_trans hstep1 (le_trans hstepA hbound)

theorem P2_line_bound_twentyfour (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N Y₀ : ℝ, 0 ≤ C ∧ 0 ≤ N ∧ 1 ≤ Y₀ ∧
      ∀ (τ : UpperHalfPlane) (r : ℝ), (τ.re = 1 / 2 ∨ τ.re = -1 / 2) → Y₀ ≤ τ.im →
        (‖Work.CKFinal.P2 (Work.Kernels.Kfun ℓ 24) r τ‖
            ≤ C * τ.im ^ N * Real.exp (-(3 * Real.pi * τ.im))
          ∧ ‖Work.CKFinal.P2 (Work.Kernels.Khat ℓ 24) r τ‖
            ≤ C * τ.im ^ N * Real.exp (-(3 * Real.pi * τ.im))) := by
  obtain ⟨Cs, As, hCs, hAs, hslash⟩ := slash_qtau_twentyfour ℓ
  obtain ⟨c, Yd, hc, _hYd, hD⟩ := denom_growth_segment
  have hCnn : 0 ≤ 2 * (1024 * Cs / c * (5 / 2 : ℝ) ^ As) := by
    apply mul_nonneg (by norm_num)
    apply mul_nonneg (div_nonneg (mul_nonneg (by norm_num) hCs.le) hc.le)
    exact Real.rpow_nonneg (by norm_num) _
  refine ⟨2 * (1024 * Cs / c * (5 / 2 : ℝ) ^ As), As, max (max Yd 2) 1,
    hCnn, hAs, le_max_right _ 1, ?_⟩
  intro τ r hline hY
  have hYd2 : max Yd 2 ≤ τ.im := le_trans (le_max_left _ _) hY
  have hline' : τ.re = 1 / 2 ∨ τ.re = -1 / 2 := hline
  have hKP : ∀ x : ℝ, |x| ≤ 1 →
      ‖Kax (Work.Kernels.KPlus 24) τ x 1‖
        ≤ (1024 * Cs / c * (5 / 2 : ℝ) ^ As) * τ.im ^ As
            * Real.exp (-(3 * Real.pi * τ.im)) := fun x hx =>
    seg_single (Work.Kernels.KPlus 24) Cs As c Yd hCs.le hAs hc
      (fun τ z h1 h2 h3 h4 => (hslash τ z h1 h2 h3 h4).1) hD τ x hline' hYd2 hx
  have hKM : ∀ x : ℝ, |x| ≤ 1 →
      ‖Kax (Work.Kernels.KMinus ℓ 24) τ x 1‖
        ≤ (1024 * Cs / c * (5 / 2 : ℝ) ^ As) * τ.im ^ As
            * Real.exp (-(3 * Real.pi * τ.im)) := fun x hx =>
    seg_single (Work.Kernels.KMinus ℓ 24) Cs As c Yd hCs.le hAs hc
      (fun τ z h1 h2 h3 h4 => (hslash τ z h1 h2 h3 h4).2) hD τ x hline' hYd2 hx
  set Kc : ℝ := 1024 * Cs / c * (5 / 2 : ℝ) ^ As with hKc
  have hb : ∀ x : ℝ, |x| ≤ 1 → max ‖Kax (Work.Kernels.KPlus 24) τ x 1‖
      ‖Kax (Work.Kernels.KMinus ℓ 24) τ x 1‖ ≤ Kc * τ.im ^ As * Real.exp (-(3 * Real.pi * τ.im)) := by
    intro x hx
    refine max_le ?_ ?_
    · rw [hKc]; exact hKP x hx
    · rw [hKc]; exact hKM x hx
  set M : ℝ := Kc * τ.im ^ As * Real.exp (-(3 * Real.pi * τ.im)) with hM
  have hfun : ∀ x : ℝ, |x| ≤ 1 → ‖Kax (Work.Kernels.Kfun ℓ 24) τ x 1‖ ≤ M := by
    intro x hx
    have hp : ‖Kax (Work.Kernels.KPlus 24) τ x 1‖ ≤ M := le_trans (le_max_left _ _) (hb x hx)
    have hm : ‖Kax (Work.Kernels.KMinus ℓ 24) τ x 1‖ ≤ M := le_trans (le_max_right _ _) (hb x hx)
    rw [show Kax (Work.Kernels.Kfun ℓ 24) τ x 1
        = (Kax (Work.Kernels.KPlus 24) τ x 1
            + Kax (Work.Kernels.KMinus ℓ 24) τ x 1) / 2 from by
      rw [show Work.Kernels.Kfun ℓ 24
          = (fun a b => (Work.Kernels.KPlus 24 a b + Work.Kernels.KMinus ℓ 24 a b) / 2)
            from rfl]
      rw [Kax_div_two, Kax_add]]
    have h1' : ‖Kax (Work.Kernels.KPlus 24) τ x 1
        + Kax (Work.Kernels.KMinus ℓ 24) τ x 1‖ ≤ M + M := by
      calc _ ≤ ‖Kax (Work.Kernels.KPlus 24) τ x 1‖
              + ‖Kax (Work.Kernels.KMinus ℓ 24) τ x 1‖ := norm_add_le _ _
        _ ≤ M + M := add_le_add hp hm
    rw [norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
    linarith
  have hhat : ∀ x : ℝ, |x| ≤ 1 → ‖Kax (Work.Kernels.Khat ℓ 24) τ x 1‖ ≤ M := by
    intro x hx
    have hp : ‖Kax (Work.Kernels.KPlus 24) τ x 1‖ ≤ M := le_trans (le_max_left _ _) (hb x hx)
    have hm : ‖Kax (Work.Kernels.KMinus ℓ 24) τ x 1‖ ≤ M := le_trans (le_max_right _ _) (hb x hx)
    rw [show Kax (Work.Kernels.Khat ℓ 24) τ x 1
        = (Kax (Work.Kernels.KPlus 24) τ x 1
            - Kax (Work.Kernels.KMinus ℓ 24) τ x 1) / 2 from by
      rw [show Work.Kernels.Khat ℓ 24
          = (fun a b => (Work.Kernels.KPlus 24 a b - Work.Kernels.KMinus ℓ 24 a b) / 2)
            from rfl]
      rw [Kax_div_two, Kax_sub]]
    have h1' : ‖Kax (Work.Kernels.KPlus 24) τ x 1
        - Kax (Work.Kernels.KMinus ℓ 24) τ x 1‖ ≤ M + M := by
      calc _ ≤ ‖Kax (Work.Kernels.KPlus 24) τ x 1‖
              + ‖Kax (Work.Kernels.KMinus ℓ 24) τ x 1‖ := norm_sub_le _ _
        _ ≤ M + M := add_le_add hp hm
    rw [norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
    linarith
  refine ⟨?_, ?_⟩
  · refine le_trans (P2_norm_segment (Work.Kernels.Kfun ℓ 24) τ r M hfun) ?_
    exact le_of_eq (by rw [hM, hKc]; ring)
  · refine le_trans (P2_norm_segment (Work.Kernels.Khat ℓ 24) τ r M hhat) ?_
    exact le_of_eq (by rw [hM, hKc]; ring)

end Work.CKFinal.LineDecay
