/-
# Moderate growth of the normalised logarithm `Lfun` of `λ`

`Lfun` is the holomorphic logarithm of `λ = θ₁₀⁴/θ₀₀⁴` on `U = {im > 0}` which is normalised by
`Lfun = LU` on `W = {im > 1/2}` (`Work.Kernels.LogLambda.Lfun_eq_LU_on_W`).

Writing `Ψ = Lfun - πi·z`, we show that `Lfun` grows at most like the square of the scale
`S τ = 1 + (im τ)⁻¹ + ‖τ‖`.  Two inputs are isolated as hypotheses:

* `hRe` : `|Re Lfun| ≤ C (1 + (im z)⁻¹ + ‖z‖)` on `U` — equivalently
  `log ‖λ‖ = 4 log ‖θ₁₀‖ - 4 log ‖θ₀₀‖` is bounded by the scale;
* `hPsi` : `Ψ` is bounded on `W ∩ {im ≥ 1}` — equivalently `Lfun z = πiz + O(1)` in the cusp.

Given those: for `im τ ≥ 1` we are in `W` and `‖Lfun τ‖ ≤ C₀ + π‖τ‖`; for `im τ < 1` the real
part of `Ψ` is bounded on the disc `‖w - (re τ + i)‖ ≤ 1 - (im τ)/2` (which lies in
`{im ≥ (im τ)/2}`) by the scale, so Borel--Caratheodory on that disc bounds `‖Ψ τ‖` in terms of
`(im τ)⁻¹` and the scale.
-/
import Mathlib
import Submission.Work.Kernels.LogLambda.LogNormalisation
import Submission.Work.Kernels.LogLambda.LogLaws
import Submission.Work.Kernels.Slash

set_option maxHeartbeats 1000000

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Complex Set Filter Topology
open scoped Modular

namespace Work.Kernels.LogLambda

lemma rpow_two_eq (x : ℝ) : x ^ (2 : ℝ) = x ^ 2 := Real.rpow_natCast x 2

/-- The linear function `z ↦ πiz`. -/
def linC (z : ℂ) : ℂ := (Real.pi : ℂ) * Complex.I * z

/-- `Ψ = Lfun - πiz`. -/
def PsiC (z : ℂ) : ℂ := Lfun z - linC z

lemma re_linC (z : ℂ) : (linC z).re = -(Real.pi * z.im) := by
  simp [linC, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]

lemma norm_linC (z : ℂ) : ‖linC z‖ = Real.pi * ‖z‖ := by
  rw [linC, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos]

lemma re_PsiC (z : ℂ) : (PsiC z).re = (Lfun z).re + Real.pi * z.im := by
  rw [PsiC, Complex.sub_re, re_linC]; ring

lemma differentiableOn_PsiC : DifferentiableOn ℂ PsiC U :=
  Lfun_spec.1.sub (by
    have h : DifferentiableOn ℂ (fun w : ℂ => ((Real.pi : ℂ) * Complex.I) * w) U :=
      (differentiableOn_const ((Real.pi : ℂ) * Complex.I)).mul differentiableOn_id
    exact h)

/-- `Lfun` has moderate growth, given the two bounds isolated as hypotheses. -/
theorem Lfun_growth_of_bounds
    (hRe : ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, z ∈ U → |(Lfun z).re| ≤ C * (1 + (z.im)⁻¹ + ‖z‖))
    (hPsi : ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, z ∈ W → 1 ≤ z.im → ‖PsiC z‖ ≤ C) :
    Work.Kernels.ModerateGrowthOn Set.univ (fun τ : ℍ => Lfun (τ : ℂ)) := by
  obtain ⟨C1, hC1, hRe⟩ := hRe
  obtain ⟨C0, hC0, hPsi⟩ := hPsi
  rw [Work.Kernels.moderateGrowthOn_iff_scale]
  refine ⟨4 * C0 + 24 * C1 + 25 * Real.pi + 1, 2, by positivity, by norm_num, fun τ _ => ?_⟩
  set A0 : ℝ := 4 * C0 + 24 * C1 + 25 * Real.pi + 1 with hA0def
  set y : ℝ := τ.im with hydef
  set z : ℂ := (τ : ℂ) with hzdef
  set s : ℝ := Work.Kernels.scale τ with hsdef
  have hy0 : 0 < y := τ.im_pos
  have hs1 : 1 ≤ s := Work.Kernels.one_le_scale τ
  have hspos : 0 < s := Work.Kernels.scale_pos τ
  have hzs : ‖z‖ ≤ s := Work.Kernels.coe_norm_le_scale τ
  have hys : y⁻¹ ≤ s := Work.Kernels.inv_im_le_scale τ
  have hs2 : s ^ (2 : ℝ) = s ^ 2 := rpow_two_eq s
  have hzim : z.im = y := by simp [hzdef, hydef]
  have hA0pos : 0 < A0 := by rw [hA0def]; positivity
  have hA0big : C0 + Real.pi ≤ A0 := by rw [hA0def]; nlinarith [hC1.le, Real.pi_pos]
  rcases le_or_gt 1 y with hy1 | hy1
  · -- Case `im τ ≥ 1`: we are in `W`, where `Ψ` is bounded.
    have hzW : z ∈ W := by
      simp only [W, Set.mem_ofPred_eq, hzim]
      linarith
    have hb : ‖PsiC z‖ ≤ C0 := hPsi z hzW (by rw [hzim]; exact hy1)
    have hdec : Lfun z = PsiC z + linC z := by rw [PsiC]; ring
    have hs2' : (1 : ℝ) ≤ s ^ 2 := one_le_pow₀ hs1
    have hnorm : ‖Lfun z‖ ≤ C0 + Real.pi * s := by
      rw [hdec]
      calc ‖PsiC z + linC z‖ ≤ ‖PsiC z‖ + ‖linC z‖ := norm_add_le _ _
        _ = ‖PsiC z‖ + Real.pi * ‖z‖ := by rw [norm_linC]
        _ ≤ C0 + Real.pi * s := by
            have h := mul_le_mul_of_nonneg_left hzs Real.pi_pos.le
            linarith
    have hkey : ‖Lfun z‖ ≤ A0 * s ^ (2 : ℝ) := by
      rw [hs2]
      have h1 : C0 ≤ C0 * s ^ 2 := by nlinarith [hC0.le, hs2']
      have h2 : Real.pi * s ≤ Real.pi * s ^ 2 := by
        have hle : s ≤ s ^ 2 := le_self_pow₀ hs1 (by norm_num)
        nlinarith [Real.pi_pos, hle]
      have h3 : (C0 + Real.pi) * s ^ 2 ≤ A0 * s ^ 2 :=
        mul_le_mul_of_nonneg_right hA0big (by positivity)
      nlinarith [hnorm, h1, h2, h3]
    simpa using hkey
  · -- Case `im τ < 1`.
    set c : ℂ := (τ.re : ℂ) + Complex.I with hcdef
    have hcim : c.im = 1 := by simp [hcdef]
    have hcW : c ∈ W := by simp only [W, Set.mem_ofPred_eq, hcim]; norm_num
    set R : ℝ := 1 - y / 2 with hRdef
    have hRpos : 0 < R := by rw [hRdef]; linarith
    have hRlt : R < 1 := by rw [hRdef]; linarith
    set M : ℝ := C1 * (1 + 2 * y⁻¹ + (‖z‖ + 2)) + Real.pi * (‖z‖ + 2) with hMdef
    have hMpos : 0 < M := by
      rw [hMdef]
      have h : (0 : ℝ) < 1 + 2 * y⁻¹ + (‖z‖ + 2) := by positivity
      nlinarith [hC1, Real.pi_pos, norm_nonneg z]
    -- The disc is contained in `U` and in `{im ≥ y/2}`.
    have hdisk_im : ∀ v : ℂ, v ∈ Metric.ball 0 R → y / 2 ≤ (c + v).im := by
      intro v hv
      have hvR : ‖v‖ < R := by
        have h := Metric.mem_ball.mp hv
        simpa [dist_eq_norm] using h
      have hvim : -(R) < v.im := by
        have h := neg_abs_le v.im
        have h' := Complex.abs_im_le_norm v
        linarith
      rw [Complex.add_im, hcim]
      linarith
    have hdisk_U : ∀ v : ℂ, v ∈ Metric.ball 0 R → c + v ∈ U := by
      intro v hv
      simp only [U, Set.mem_ofPred_eq]
      have := hdisk_im v hv
      linarith [hy0]
    -- Bound on `Re Ψ` on the disc.
    have hReBall : ∀ v : ℂ, v ∈ Metric.ball 0 R → (PsiC (c + v)).re ≤ M := by
      intro v hv
      have hvR : ‖v‖ < R := by
        have h := Metric.mem_ball.mp hv
        simpa [dist_eq_norm] using h
      have hnorm : ‖c + v‖ ≤ ‖z‖ + 2 := by
        have hcnorm : ‖c‖ ≤ ‖z‖ + 1 := by
          calc ‖c‖ = ‖(τ.re : ℂ) + Complex.I‖ := rfl
            _ ≤ ‖(τ.re : ℂ)‖ + ‖Complex.I‖ := norm_add_le _ _
            _ = |τ.re| + 1 := by rw [Complex.norm_real, Real.norm_eq_abs, Complex.norm_I]
            _ ≤ ‖z‖ + 1 := by
                have h1 := Complex.abs_re_le_norm z
                have h2 : z.re = τ.re := by simp [hzdef]
                rw [h2] at h1
                linarith
        calc ‖c + v‖ ≤ ‖c‖ + ‖v‖ := norm_add_le _ _
          _ ≤ (‖z‖ + 1) + R := add_le_add hcnorm (le_of_lt hvR)
          _ ≤ ‖z‖ + 2 := by linarith [hRlt]
      have h1 := hRe (c + v) (hdisk_U v hv)
      have h2 : (PsiC (c + v)).re ≤ |(Lfun (c + v)).re| + Real.pi * ‖c + v‖ := by
        rw [re_PsiC]
        have h3 : Real.pi * (c + v).im ≤ Real.pi * ‖c + v‖ := by
          have h4 := Complex.im_le_norm (c + v)
          nlinarith [Real.pi_pos]
        have h5 : (Lfun (c + v)).re ≤ |(Lfun (c + v)).re| := le_abs_self _
        linarith
      have hinv : ((c + v).im)⁻¹ ≤ 2 * y⁻¹ := by
        have hge : y / 2 ≤ (c + v).im := hdisk_im v hv
        have hpos : 0 < y / 2 := by linarith
        have hpos' : 0 < (c + v).im := by linarith
        have h := (inv_le_inv₀ hpos' hpos).mpr hge
        rwa [show (y / 2)⁻¹ = 2 * y⁻¹ by field_simp] at h
      have h6 : C1 * (1 + ((c + v).im)⁻¹ + ‖c + v‖) ≤ C1 * (1 + 2 * y⁻¹ + (‖z‖ + 2)) :=
        mul_le_mul_of_nonneg_left (by linarith [hinv, hnorm]) hC1.le
      have h7 : Real.pi * ‖c + v‖ ≤ Real.pi * (‖z‖ + 2) :=
        mul_le_mul_of_nonneg_left hnorm Real.pi_pos.le
      calc (PsiC (c + v)).re ≤ |(Lfun (c + v)).re| + Real.pi * ‖c + v‖ := h2
        _ ≤ C1 * (1 + ((c + v).im)⁻¹ + ‖c + v‖) + Real.pi * ‖c + v‖ := by linarith [h1]
        _ ≤ C1 * (1 + 2 * y⁻¹ + (‖z‖ + 2)) + Real.pi * (‖z‖ + 2) := by linarith [h6, h7]
        _ = M := by rw [hMdef]
    -- Differentiability of the Borel--Caratheodory function.
    have hdiff : DifferentiableOn ℂ (fun w : ℂ => PsiC (c + w)) (Metric.ball 0 R) :=
      differentiableOn_PsiC.comp (by fun_prop) (fun v hv => hdisk_U v hv)
    have hzc : z - c = ((y - 1 : ℝ) : ℂ) * Complex.I := by
      rw [hzdef, show c = (τ.re : ℂ) + Complex.I from rfl, hydef]
      push_cast
      rw [← Complex.re_add_im (τ : ℂ), UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
      ring
    have hzcnorm : ‖z - c‖ = 1 - y := by
      rw [hzc, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_neg (by linarith : y - 1 < 0)]
      ring
    have hmem : z - c ∈ Metric.ball 0 R := by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero, hzcnorm]
      linarith [hRpos]
    have hBC := Complex.borelCaratheodory hMpos hdiff (fun v hv => hReBall v hv) hRpos hmem
    have hc0 : c + (z - c) = z := by ring
    have hden : R - ‖z - c‖ = y / 2 := by rw [hzcnorm, hRdef]; ring
    have hPsiC0 : ‖PsiC c‖ ≤ C0 := hPsi c hcW (by rw [hcim])
    have hy2 : 0 < y / 2 := by linarith
    have hb1 : 2 * M * ‖z - c‖ / (y / 2) ≤ 4 * M / y := by
      have he : 2 * M * ‖z - c‖ / (y / 2) = 4 * M * (1 - y) / y := by
        rw [hzcnorm]; field_simp; ring
      have h2 : 4 * M * (1 - y) / y ≤ 4 * M / y := by
        apply div_le_div_of_nonneg_right _ hy0.le
        nlinarith [hMpos.le, hy0, le_of_lt hy1]
      linarith [he, h2]
    have hb2 : ‖PsiC c‖ * (R + ‖z - c‖) / (y / 2) ≤ 4 * C0 / y := by
      have hRr : R + ‖z - c‖ ≤ 2 := by rw [hzcnorm]; linarith [hRlt]
      have hnum : ‖PsiC c‖ * (R + ‖z - c‖) ≤ C0 * 2 := by
        have h1 : ‖PsiC c‖ * (R + ‖z - c‖) ≤ C0 * (R + ‖z - c‖) :=
          mul_le_mul_of_nonneg_right hPsiC0 (by positivity)
        have h2 : C0 * (R + ‖z - c‖) ≤ C0 * 2 := mul_le_mul_of_nonneg_left hRr hC0.le
        linarith
      have hA : ‖PsiC c‖ * (R + ‖z - c‖) / (y / 2) ≤ (C0 * 2) / (y / 2) :=
        div_le_div_of_nonneg_right hnum (le_of_lt hy2)
      have hB : (C0 * 2) / (y / 2) = 4 * C0 / y := by field_simp; ring
      linarith [hA, hB.symm.le, hB.le]
    have hPsibound : ‖PsiC z‖ ≤ 4 * M / y + 4 * C0 / y := by
      have h := hBC
      rw [hc0, hden, add_zero] at h
      linarith [h, hb1, hb2]
    have hdec : Lfun z = PsiC z + linC z := by rw [PsiC]; ring
    have hfin : ‖Lfun z‖ ≤ 4 * M / y + 4 * C0 / y + Real.pi * s := by
      rw [hdec]
      have h1 : ‖PsiC z + linC z‖ ≤ ‖PsiC z‖ + Real.pi * s := by
        calc ‖PsiC z + linC z‖ ≤ ‖PsiC z‖ + ‖linC z‖ := norm_add_le _ _
          _ = ‖PsiC z‖ + Real.pi * ‖z‖ := by rw [norm_linC]
          _ ≤ ‖PsiC z‖ + Real.pi * s := by
              have h := mul_le_mul_of_nonneg_left hzs Real.pi_pos.le
              linarith
      linarith
    have hMbound : M ≤ 6 * (C1 + Real.pi) * s := by
      rw [hMdef]
      have h1 : 1 + 2 * y⁻¹ + (‖z‖ + 2) ≤ 6 * s := by linarith [hys, hzs, hs1]
      have h2 : ‖z‖ + 2 ≤ 3 * s := by linarith [hzs, hs1]
      have ha : C1 * (1 + 2 * y⁻¹ + (‖z‖ + 2)) ≤ C1 * (6 * s) :=
        mul_le_mul_of_nonneg_left h1 hC1.le
      have hb : Real.pi * (‖z‖ + 2) ≤ Real.pi * (3 * s) :=
        mul_le_mul_of_nonneg_left h2 Real.pi_pos.le
      have h3 : C1 * (6 * s) + Real.pi * (3 * s) ≤ 6 * (C1 + Real.pi) * s := by
        nlinarith [Real.pi_pos, hC1.le]
      linarith [ha, hb]
    have hkey : ‖Lfun z‖ ≤ A0 * s ^ (2 : ℝ) := by
      rw [hs2]
      have hs2' : (1 : ℝ) ≤ s ^ 2 := one_le_pow₀ hs1
      have hsy : s / y ≤ s ^ 2 := by
        rw [div_le_iff₀ hy0]
        have hys' : 1 / y ≤ s := by simpa using hys
        have h1 : (1 : ℝ) ≤ s * y := (div_le_iff₀ hy0).mp hys'
        nlinarith [h1, hspos]
      have hMy : M / y ≤ 6 * (C1 + Real.pi) * (s / y) := by
        have h := (div_le_div_iff_of_pos_right hy0).mpr hMbound
        calc M / y ≤ 6 * (C1 + Real.pi) * s / y := h
          _ = 6 * (C1 + Real.pi) * (s / y) := by ring
      have hC0y : C0 / y ≤ C0 * (s / y) := by
        have h : C0 ≤ C0 * s := by nlinarith [hC0.le, hs1]
        calc C0 / y ≤ C0 * s / y := (div_le_div_iff_of_pos_right hy0).mpr h
          _ = C0 * (s / y) := by ring
      have ha : 4 * M / y ≤ 24 * (C1 + Real.pi) * (s / y) := by
        have he : 4 * M / y = 4 * (M / y) := by ring
        rw [he]
        nlinarith [hMy]
      have hb : 4 * C0 / y ≤ 4 * C0 * (s / y) := by
        have he : 4 * C0 / y = 4 * (C0 / y) := by ring
        rw [he]
        nlinarith [hC0y]
      have hc : 24 * (C1 + Real.pi) * (s / y) ≤ 24 * (C1 + Real.pi) * s ^ 2 :=
        mul_le_mul_of_nonneg_left hsy (by positivity)
      have hd : 4 * C0 * (s / y) ≤ 4 * C0 * s ^ 2 :=
        mul_le_mul_of_nonneg_left hsy (by positivity)
      have he : Real.pi * s ≤ Real.pi * s ^ 2 := by
        have hle : s ≤ s ^ 2 := le_self_pow₀ hs1 (by norm_num)
        nlinarith [Real.pi_pos, hle]
      have hexp : A0 * s ^ 2 = 4 * (C0 * s ^ 2) + 24 * (C1 * s ^ 2)
          + 25 * (Real.pi * s ^ 2) + s ^ 2 := by rw [hA0def]; ring
      rw [hexp]
      have hC0s : C0 ≤ C0 * s ^ 2 := by nlinarith [hC0.le, hs2']
      nlinarith [hfin, ha, hb, hc, hd, he, hC0s, hC1.le, Real.pi_pos, hspos]
    simpa using hkey

end Work.Kernels.LogLambda
