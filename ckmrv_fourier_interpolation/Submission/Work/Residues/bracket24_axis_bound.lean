import Mathlib
import Submission.Work.Residues.KMinusCuspDefs
import Submission.Work.Residues.ThetaDecay
import Submission.Work.Asymptotics.KPlusXiDefs
import Submission.Work.Kernels.ModerateGrowth
import Submission.Work.Asymptotics.DeltaFun_imagAxis_lower_sharp
import Submission.Work.Residues.bracket24_uniform
import Submission.Work.Residues.imagAxis_factor_bounds

namespace Work.Residues

open UpperHalfPlane

theorem bracket24_axis_bound (ℓ : Work.Kernels.LogLambdaData) :
    ∃ H C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧ 0 ≤ H ∧
      ∀ (τ : UpperHalfPlane) (t : ℝ) (ht : 0 < t), H ≤ τ.im → 1 ≤ t → t ≤ τ.im - 1 →
        ‖Work.Residues.bracket24 ℓ (Work.Kernels.imagAxis t ht) τ‖
          ≤ C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M * Real.exp (2 * Real.pi * τ.im) := by
  obtain ⟨Hu, K0, K1, K2, K3, hK0, hK1, hK2, hK3, hu⟩ := bracket24_uniform ℓ
  obtain ⟨CW, Cj, CE, CUV, CLL, M, hCW, hCj, hCE, hCUV, hCLL, hM, hf⟩ := imagAxis_factor_bounds ℓ
  have hAnn : 0 ≤ K0 * CW + K1 * CW * Cj + K2 * CE * CUV + K3 * CE * CLL := by
    have h1 : 0 ≤ K0 * CW := mul_nonneg hK0 hCW
    have h2 : 0 ≤ K1 * CW * Cj := mul_nonneg (mul_nonneg hK1 hCW) hCj.le
    have h3 : 0 ≤ K2 * CE * CUV := mul_nonneg (mul_nonneg hK2 hCE.le) hCUV
    have h4 : 0 ≤ K3 * CE * CLL := mul_nonneg (mul_nonneg hK3 hCE.le) hCLL
    linarith
  refine ⟨max Hu 1, K0 * CW + K1 * CW * Cj + K2 * CE * CUV + K3 * CE * CLL + 1, 1, M,
    by linarith, zero_le_one, hM, le_trans zero_le_one (le_max_right _ _), ?_⟩
  intro τ t ht hH ht1 htle
  have hHu : Hu ≤ τ.im := le_trans (le_max_left _ _) hH
  obtain ⟨hW, hj, hE10, hE14, hUV, hL⟩ := hf t ht ht1
  have hbound := hu (Work.Kernels.imagAxis t ht) τ hHu
  set E : ℝ := Real.exp (2 * Real.pi * t) with hEdef
  set Tp : ℝ := (1 + t) ^ M with hTpdef
  have hE1 : (1 : ℝ) ≤ E := by
    rw [hEdef, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, ht1])
  have hTp1 : (1 : ℝ) ≤ Tp := by
    rw [hTpdef]
    calc (1 : ℝ) = (1 : ℝ) ^ M := (Real.one_rpow M).symm
      _ ≤ (1 + t) ^ M := Real.rpow_le_rpow (by norm_num) (by linarith) hM
  have hEnn : 0 ≤ E := le_trans zero_le_one hE1
  have hTpnn : 0 ≤ Tp := le_trans zero_le_one hTp1
  have hann : 0 ≤ 1 + ‖(τ : ℂ)‖ := by positivity
  have hScnn : 0 ≤ Work.Kernels.scale τ := (Work.Kernels.scale_pos τ).le
  have hscale : (1 + ‖(τ : ℂ)‖) ≤ Work.Kernels.scale τ := by
    simp only [Work.Kernels.scale]
    have := inv_nonneg.mpr τ.im_pos.le
    linarith
  have hEB : E ≤ Real.exp (2 * Real.pi * τ.im) := by
    rw [hEdef]
    exact Real.exp_le_exp.mpr (by nlinarith [htle, Real.pi_pos])
  have hEEτnn : 0 ≤ Real.exp (2 * Real.pi * τ.im) := (Real.exp_pos _).le
  have h1 : K0 * ‖Work.Kernels.WFun (Work.Kernels.imagAxis t ht)‖ ≤ K0 * CW * Tp * E := by
    have hle : K0 * ‖Work.Kernels.WFun (Work.Kernels.imagAxis t ht)‖ ≤ K0 * CW :=
      mul_le_mul_of_nonneg_left hW hK0
    have hcoef : 0 ≤ K0 * CW := mul_nonneg hK0 hCW
    have hTE : (1 : ℝ) ≤ Tp * E := by nlinarith [hTp1, hE1]
    have h2 : K0 * CW ≤ K0 * CW * Tp * E := by
      have := mul_le_mul_of_nonneg_left hTE hcoef
      simpa [mul_assoc] using this
    linarith
  have h2 : K1 * ‖Work.Kernels.WFun (Work.Kernels.imagAxis t ht)‖
      * ‖Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖ ≤ K1 * CW * Cj * Tp * E := by
    have hjE : ‖Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖ ≤ Cj * E := by
      rw [hEdef]; exact hj
    have hprod : ‖Work.Kernels.WFun (Work.Kernels.imagAxis t ht)‖
        * ‖Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖ ≤ CW * (Cj * E) :=
      mul_le_mul hW hjE (norm_nonneg _) hCW
    have hstep : K1 * ‖Work.Kernels.WFun (Work.Kernels.imagAxis t ht)‖
        * ‖Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖ ≤ K1 * (CW * (Cj * E)) := by
      have := mul_le_mul_of_nonneg_left hprod hK1
      simpa [mul_assoc] using this
    have hstep2 : K1 * (CW * (Cj * E)) ≤ K1 * CW * Cj * Tp * E := by
      have hc : 0 ≤ K1 * CW * Cj := mul_nonneg (mul_nonneg hK1 hCW) hCj.le
      have hh : K1 * CW * Cj ≤ K1 * CW * Cj * Tp := le_mul_of_one_le_right hc hTp1
      rw [show K1 * (CW * (Cj * E)) = (K1 * CW * Cj) * E by ring,
          show K1 * CW * Cj * Tp * E = ((K1 * CW * Cj) * Tp) * E by ring]
      exact mul_le_mul_of_nonneg_right hh hEnn
    linarith
  have h3 : K2 * ‖Work.Kernels.E10Fun (Work.Kernels.imagAxis t ht)
        / Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖
      * ‖Work.Kernels.UFun (Work.Kernels.imagAxis t ht) ^ 2
          - Work.Kernels.VFun (Work.Kernels.imagAxis t ht) ^ 2‖ ≤ K2 * CE * CUV * Tp * E := by
    have h10E : ‖Work.Kernels.E10Fun (Work.Kernels.imagAxis t ht)
        / Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ ≤ CE * E := by
      rw [hEdef]; exact hE10
    have hprod : ‖Work.Kernels.E10Fun (Work.Kernels.imagAxis t ht)
        / Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖
        * ‖Work.Kernels.UFun (Work.Kernels.imagAxis t ht) ^ 2
            - Work.Kernels.VFun (Work.Kernels.imagAxis t ht) ^ 2‖ ≤ (CE * E) * CUV :=
      mul_le_mul h10E hUV (norm_nonneg _) (mul_nonneg hCE.le hEnn)
    have hstep : K2 * ‖Work.Kernels.E10Fun (Work.Kernels.imagAxis t ht)
        / Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖
        * ‖Work.Kernels.UFun (Work.Kernels.imagAxis t ht) ^ 2
            - Work.Kernels.VFun (Work.Kernels.imagAxis t ht) ^ 2‖ ≤ K2 * ((CE * E) * CUV) := by
      have := mul_le_mul_of_nonneg_left hprod hK2
      simpa [mul_assoc] using this
    have hstep2 : K2 * ((CE * E) * CUV) ≤ K2 * CE * CUV * Tp * E := by
      have hc : 0 ≤ K2 * CE * CUV := mul_nonneg (mul_nonneg hK2 hCE.le) hCUV
      have hh : K2 * CE * CUV ≤ K2 * CE * CUV * Tp := le_mul_of_one_le_right hc hTp1
      rw [show K2 * ((CE * E) * CUV) = (K2 * CE * CUV) * E by ring,
          show K2 * CE * CUV * Tp * E = ((K2 * CE * CUV) * Tp) * E by ring]
      exact mul_le_mul_of_nonneg_right hh hEnn
    linarith
  have h4 : K3 * ‖Work.Kernels.E14Fun (Work.Kernels.imagAxis t ht)
        / Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖
      * ‖ℓ.L (Work.Kernels.imagAxis t ht)‖ ≤ K3 * CE * CLL * Tp * E := by
    have h14E : ‖Work.Kernels.E14Fun (Work.Kernels.imagAxis t ht)
        / Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ ≤ CE * E := by
      rw [hEdef]; exact hE14
    have hLE : ‖ℓ.L (Work.Kernels.imagAxis t ht)‖ ≤ CLL * Tp := by
      rw [hTpdef]; exact hL
    have hprod : ‖Work.Kernels.E14Fun (Work.Kernels.imagAxis t ht)
        / Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖
        * ‖ℓ.L (Work.Kernels.imagAxis t ht)‖ ≤ (CE * E) * (CLL * Tp) :=
      mul_le_mul h14E hLE (norm_nonneg _) (mul_nonneg hCE.le hEnn)
    have hstep : K3 * ‖Work.Kernels.E14Fun (Work.Kernels.imagAxis t ht)
        / Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖
        * ‖ℓ.L (Work.Kernels.imagAxis t ht)‖ ≤ K3 * ((CE * E) * (CLL * Tp)) := by
      have := mul_le_mul_of_nonneg_left hprod hK3
      simpa [mul_assoc] using this
    have hstep2 : K3 * ((CE * E) * (CLL * Tp)) ≤ K3 * CE * CLL * Tp * E :=
      le_of_eq (by ring)
    linarith
  have hP : K0 * ‖Work.Kernels.WFun (Work.Kernels.imagAxis t ht)‖
      + K1 * ‖Work.Kernels.WFun (Work.Kernels.imagAxis t ht)‖
          * ‖Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖
      + K2 * ‖Work.Kernels.E10Fun (Work.Kernels.imagAxis t ht)
          / Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖
          * ‖Work.Kernels.UFun (Work.Kernels.imagAxis t ht) ^ 2
              - Work.Kernels.VFun (Work.Kernels.imagAxis t ht) ^ 2‖
      + K3 * ‖Work.Kernels.E14Fun (Work.Kernels.imagAxis t ht)
          / Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖
          * ‖ℓ.L (Work.Kernels.imagAxis t ht)‖
      ≤ (K0 * CW + K1 * CW * Cj + K2 * CE * CUV + K3 * CE * CLL) * Tp * E := by
    refine le_trans (add_le_add (add_le_add (add_le_add h1 h2) h3) h4) (le_of_eq ?_)
    ring
  have hmain : ‖Work.Residues.bracket24 ℓ (Work.Kernels.imagAxis t ht) τ‖
      ≤ (K0 * CW + K1 * CW * Cj + K2 * CE * CUV + K3 * CE * CLL) * Tp * E * (1 + ‖(τ : ℂ)‖) := by
    refine le_trans hbound ?_
    exact mul_le_mul_of_nonneg_right hP hann
  have hA1nn : 0 ≤ K0 * CW + K1 * CW * Cj + K2 * CE * CUV + K3 * CE * CLL + 1 := by linarith
  calc ‖Work.Residues.bracket24 ℓ (Work.Kernels.imagAxis t ht) τ‖
      ≤ (K0 * CW + K1 * CW * Cj + K2 * CE * CUV + K3 * CE * CLL) * Tp * E * (1 + ‖(τ : ℂ)‖) :=
        hmain
    _ ≤ (K0 * CW + K1 * CW * Cj + K2 * CE * CUV + K3 * CE * CLL + 1)
          * (Work.Kernels.scale τ) ^ (1 : ℝ) * Tp * Real.exp (2 * Real.pi * τ.im) := by
        rw [Real.rpow_one]
        have hs1 : (K0 * CW + K1 * CW * Cj + K2 * CE * CUV + K3 * CE * CLL) * Tp * E
              * (1 + ‖(τ : ℂ)‖)
            ≤ (K0 * CW + K1 * CW * Cj + K2 * CE * CUV + K3 * CE * CLL + 1) * Tp * E
              * (1 + ‖(τ : ℂ)‖) := by
          have := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (by linarith : K0 * CW + K1 * CW * Cj + K2 * CE * CUV
                  + K3 * CE * CLL ≤ K0 * CW + K1 * CW * Cj + K2 * CE * CUV + K3 * CE * CLL + 1)
                hTpnn) hEnn) hann
          simpa [mul_assoc] using this
        have hs2 : (K0 * CW + K1 * CW * Cj + K2 * CE * CUV + K3 * CE * CLL + 1) * Tp * E
              * (1 + ‖(τ : ℂ)‖)
            ≤ (K0 * CW + K1 * CW * Cj + K2 * CE * CUV + K3 * CE * CLL + 1) * Tp
              * Real.exp (2 * Real.pi * τ.im) * (1 + ‖(τ : ℂ)‖) := by
          have hX : 0 ≤ (K0 * CW + K1 * CW * Cj + K2 * CE * CUV + K3 * CE * CLL + 1) * Tp :=
            mul_nonneg hA1nn hTpnn
          have hinner : (K0 * CW + K1 * CW * Cj + K2 * CE * CUV + K3 * CE * CLL + 1) * Tp * E
              ≤ (K0 * CW + K1 * CW * Cj + K2 * CE * CUV + K3 * CE * CLL + 1) * Tp
                * Real.exp (2 * Real.pi * τ.im) := mul_le_mul_of_nonneg_left hEB hX
          exact mul_le_mul_of_nonneg_right hinner hann
        have hs3 : (K0 * CW + K1 * CW * Cj + K2 * CE * CUV + K3 * CE * CLL + 1) * Tp
              * Real.exp (2 * Real.pi * τ.im) * (1 + ‖(τ : ℂ)‖)
            ≤ (K0 * CW + K1 * CW * Cj + K2 * CE * CUV + K3 * CE * CLL + 1) * Tp
              * Real.exp (2 * Real.pi * τ.im) * Work.Kernels.scale τ :=
          mul_le_mul_of_nonneg_left hscale (mul_nonneg (mul_nonneg hA1nn hTpnn) hEEτnn)
        calc (K0 * CW + K1 * CW * Cj + K2 * CE * CUV + K3 * CE * CLL) * Tp * E
              * (1 + ‖(τ : ℂ)‖)
            ≤ (K0 * CW + K1 * CW * Cj + K2 * CE * CUV + K3 * CE * CLL + 1) * Tp * E
              * (1 + ‖(τ : ℂ)‖) := hs1
          _ ≤ (K0 * CW + K1 * CW * Cj + K2 * CE * CUV + K3 * CE * CLL + 1) * Tp
              * Real.exp (2 * Real.pi * τ.im) * (1 + ‖(τ : ℂ)‖) := hs2
          _ ≤ (K0 * CW + K1 * CW * Cj + K2 * CE * CUV + K3 * CE * CLL + 1) * Tp
              * Real.exp (2 * Real.pi * τ.im) * Work.Kernels.scale τ := hs3
          _ = (K0 * CW + K1 * CW * Cj + K2 * CE * CUV + K3 * CE * CLL + 1) * Work.Kernels.scale τ
              * Tp * Real.exp (2 * Real.pi * τ.im) := by ring

end Work.Residues
