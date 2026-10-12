import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PB3Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PB3V2.mf_L2_le` — removing the box mean does not increase the `L²` norm

`mf ℓ f = f − (ℓ³)⁻¹∫_{boxL ℓ} f` is `f` minus its mean over the corpus box `Λ(ℓ) = ℓ • cell`
(`Work.BoseK15.corpusBox`), i.e. `1 − P` with `P` the rank-one projection onto the constants
(`P f = ℓ⁻³⟨1_{Λ}, f⟩ 1_{Λ}`, and `vol Λ(ℓ) = ℓ³`).  Hence on the box

    `∫_{Λ} ‖mf ℓ f‖² = ∫_{Λ} ‖f‖² − (ℓ³)⁻¹‖∫_{Λ} f‖² ≤ ∫_{Λ} ‖f‖²`.

The proof is the *exact* computation, valid for every continuous `f` (integrability over the
compact box is `ContinuousOn.integrableOn_compact`):

* pointwise, `‖z − w‖² = ‖z‖² − 2 Re(z·conj w) + ‖w‖²` (`Complex.normSq_sub`), so with
  `c := (ℓ³)⁻¹ I`, `I := ∫_{Λ} f`,

    `∫_{Λ}(‖f‖² − ‖f − c‖²) = 2 Re(I·conj c) − (vol Λ)·‖c‖²`,

  the `Re` being pulled out of the integral through the continuous linear functional
  `Complex.reCLM` (`ContinuousLinearMap.integral_comp_comm`) and `I` through
  `integral_mul_const`;
* `I·conj c = (ℓ³)⁻¹‖I‖²` and `‖c‖²·ℓ³ = (ℓ³)⁻¹‖I‖²` (`Complex.mul_conj`,
  `Complex.normSq_eq_norm_sq`, `volume Λ(ℓ) = ℓ³`), so the difference is `(ℓ³)⁻¹‖I‖² ≥ 0`.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock.PB3V2

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- Expanding `‖z - w‖²` over `ℂ`: `‖z - w‖² = ‖z‖² - 2 Re(z·conj w) + ‖w‖²`. -/
private lemma norm_sub_sq_complex (z w : ℂ) :
    ‖z - w‖ ^ 2 = ‖z‖ ^ 2 - 2 * (z * (starRingEnd ℂ) w).re + ‖w‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_sub]
  ring

theorem mf_L2_le {ℓ : ℝ} (hℓ : 0 < ℓ) {h : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hh : Continuous h) :
    (∫ w in Work.BoseK15.corpusBox.boxL ℓ, ‖Work.BoseBoxFock.mf ℓ h w‖ ^ 2)
      ≤ ∫ w in Work.BoseK15.corpusBox.boxL ℓ, ‖h w‖ ^ 2 := by
  classical
  set s : Set E3 := Work.BoseK15.corpusBox.boxL ℓ with hboxdef
  set I : ℂ := ∫ w in s, h w with hI
  set c : ℂ := ((ℓ ^ 3)⁻¹ : ℝ) * I with hc
  have hs_meas : MeasurableSet s := by
    rw [hboxdef]; exact Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ
  have hs_compact : IsCompact s := by
    rw [hboxdef]; exact Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ
  -- `mf ℓ h` is `h` minus the constant `c = (ℓ³)⁻¹∫_{Λ} h`
  have hmf : ∀ w : E3, Work.BoseBoxFock.mf ℓ h w = h w - c := by
    intro w
    have hint : (∫ y in Work.BoseK15.corpusBox.boxL ℓ, h y) = I := by rw [← hI]
    simp only [Work.BoseBoxFock.mf, hint, hc]
  have hcont_mf : Continuous fun w : E3 => ‖Work.BoseBoxFock.mf ℓ h w‖ ^ 2 := by
    have hc' : Continuous fun w : E3 => ‖h w - c‖ ^ 2 := (hh.sub continuous_const).norm.pow 2
    exact hc'.congr (fun w => by rw [hmf w])
  -- integrability on the compact box
  have hA : IntegrableOn (fun w : E3 => ‖h w‖ ^ 2) s :=
    ContinuousOn.integrableOn_compact hs_compact (by fun_prop)
  have hD : IntegrableOn (fun w : E3 => ‖Work.BoseBoxFock.mf ℓ h w‖ ^ 2) s :=
    ContinuousOn.integrableOn_compact hs_compact hcont_mf.continuousOn
  -- the pointwise expansion of the difference
  have hpt : ∀ w : E3,
      ‖h w‖ ^ 2 - ‖Work.BoseBoxFock.mf ℓ h w‖ ^ 2
        = 2 * (h w * (starRingEnd ℂ) c).re - ‖c‖ ^ 2 := by
    intro w
    rw [hmf w, norm_sub_sq_complex]
    ring
  have hcross : IntegrableOn (fun w : E3 => (h w * (starRingEnd ℂ) c).re) s :=
    ContinuousOn.integrableOn_compact hs_compact (by fun_prop)
  have hconst : IntegrableOn (fun _ : E3 => ‖c‖ ^ 2) s :=
    ContinuousOn.integrableOn_compact hs_compact continuousOn_const
  -- the `Re` of the cross term comes out of the integral
  have hInt_cross : (∫ w in s, (h w * (starRingEnd ℂ) c).re)
      = (I * (starRingEnd ℂ) c).re := by
    have hInt' : IntegrableOn (fun w : E3 => h w * (starRingEnd ℂ) c) s :=
      ContinuousOn.integrableOn_compact hs_compact (by fun_prop)
    have hcomm := ContinuousLinearMap.integral_comp_comm (L := Complex.reCLM) hInt'
    simp only [Complex.reCLM_apply] at hcomm
    rw [hcomm, integral_mul_const, ← hI]
  have hsplit : (∫ w in s, (‖h w‖ ^ 2 - ‖Work.BoseBoxFock.mf ℓ h w‖ ^ 2))
      = (∫ w in s, ‖h w‖ ^ 2) - (∫ w in s, ‖Work.BoseBoxFock.mf ℓ h w‖ ^ 2) :=
    integral_sub hA hD
  have heq : (∫ w in s, (‖h w‖ ^ 2 - ‖Work.BoseBoxFock.mf ℓ h w‖ ^ 2))
      = 2 * (I * (starRingEnd ℂ) c).re - (volume.real s) * ‖c‖ ^ 2 := by
    rw [setIntegral_congr_fun hs_meas (fun w _ => hpt w)]
    rw [integral_sub (hcross.const_mul 2) hconst, integral_const_mul, hInt_cross,
      setIntegral_const]
    simp [smul_eq_mul]
  have hvol : (volume : Measure E3).real s = ℓ ^ 3 := by
    rw [MeasureTheory.measureReal_def, hboxdef,
      Work.BoseB4.BoxData.volume_boxL Work.BoseK15.corpusBox hℓ,
      ENNReal.toReal_ofReal (by positivity)]
  -- the exact value of the deficit
  have hfinal : 2 * (I * (starRingEnd ℂ) c).re - (volume.real s) * ‖c‖ ^ 2
      = (ℓ ^ 3)⁻¹ * ‖I‖ ^ 2 := by
    rw [hvol]
    have hconjc : (starRingEnd ℂ) c = (↑((ℓ ^ 3)⁻¹) : ℂ) * (starRingEnd ℂ) I := by
      rw [hc, map_mul, Complex.conj_ofReal]
    have h1 : (I * (starRingEnd ℂ) c).re = (ℓ ^ 3)⁻¹ * ‖I‖ ^ 2 := by
      rw [hconjc]
      have hres : I * ((↑((ℓ ^ 3)⁻¹) : ℂ) * (starRingEnd ℂ) I)
          = ((↑((ℓ ^ 3)⁻¹) : ℂ) * (↑(Complex.normSq I) : ℂ)) := by
        rw [show I * ((↑((ℓ ^ 3)⁻¹) : ℂ) * (starRingEnd ℂ) I)
            = (↑((ℓ ^ 3)⁻¹) : ℂ) * (I * (starRingEnd ℂ) I) by ring, Complex.mul_conj]
      rw [hres, ← Complex.ofReal_mul, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    have h2 : ‖c‖ ^ 2 = ((ℓ ^ 3)⁻¹) ^ 2 * ‖I‖ ^ 2 := by
      rw [hc, norm_mul, mul_pow, Complex.sq_norm, Complex.normSq_ofReal]
      ring
    rw [h1, h2]
    have h3 : (ℓ : ℝ) ^ 3 ≠ 0 := by positivity
    field_simp
    ring
  have hmain : (∫ w in s, ‖h w‖ ^ 2) - (∫ w in s, ‖Work.BoseBoxFock.mf ℓ h w‖ ^ 2)
      = (ℓ ^ 3)⁻¹ * ‖I‖ ^ 2 := by
    rw [← hsplit, heq, hfinal]
  have hnn : (0 : ℝ) ≤ (ℓ ^ 3)⁻¹ * ‖I‖ ^ 2 := by positivity
  linarith [hmain]

end Work.BoseBoxFock.PB3V2
