import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.BoxD1Defs
import Submission.Work.BoseFixB1.boxQInd_update_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.tBamp_boxQInd_normSq` — the slot amplitude dictionary

The windowed `p`-mode amplitude `Work.SmallBoxTBWord.tBamp` of FS's box projection
`Work.UBBInputs8.boxQInd` is the complex integral of the mean-free windowed mode
`boxWinModeC = boxWinModeReGen + i·boxWinModeImGen` against the slot fibre
`z ↦ Ψ(x[i ↦ z])`, hence its squared modulus splits into the two real slot amplitudes:

`‖tBamp χ q (Q_{Ac,i}Ψ) i x‖² = (∫_{Ac} boxWinModeReGen·Ψ(x[i↦·]))² + (∫_{Ac} boxWinModeImGen·Ψ(x[i↦·]))²`.

This is the identity that turns the frame content `boxWinModePGen` (a sum of squares of the two
*real* mode contents) into the corpus's `p`-diagonal form `tBdiagFormInd`, which is written with
`‖tBamp‖²`.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixB1

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- The `ℂ`-valued form of `Work.BoseFixB1.boxQInd_update_eq`. -/
private lemma boxQInd_update_eq_cast {n : ℕ} (volA : ℝ) {Ac : Set E3} (i : Fin n)
    (Ψ : Submission.BoseGases.X n → ℝ) (x : Submission.BoseGases.X n) (z : E3) :
    ((Work.UBBInputs8.boxQInd volA Ac i Ψ (Function.update x i z) : ℝ) : ℂ)
      = (Ac.indicator (fun _ => (1 : ℂ)) z)
        * ((Ψ (Function.update x i z) : ℂ)
            - (((1 / volA) * ∫ w in Ac, Ψ (Function.update x i w) : ℝ) : ℂ)) := by
  rw [Work.BoseFixB1.boxQInd_update_eq volA Ac i Ψ x z]
  by_cases hz : z ∈ Ac
  · rw [Set.indicator_of_mem hz (fun _ => (1 : ℝ)), Set.indicator_of_mem hz (fun _ => (1 : ℂ)),
      one_mul, one_mul]
    push_cast
    ring
  · rw [Set.indicator_of_notMem hz (fun _ => (1 : ℝ)),
      Set.indicator_of_notMem hz (fun _ => (1 : ℂ))]
    push_cast
    ring

/-- The complex windowed mode `boxWinModeC` at a point of the box `Ac` is the indicator-free
mean-free mode `χ z e^{−i⟪q,z⟫} − volA⁻¹∫_{Ac} χ e^{−i⟪q,·⟫}`. -/
private lemma boxWinModeC_of_mem (volA : ℝ) (Ac : Set E3) (χ : E3 → ℝ) (q z : E3)
    (hz : z ∈ Ac) :
    boxWinModeC volA Ac χ q z
      = (χ z : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ q z : ℝ) : ℂ)))
        - ((volA⁻¹ : ℝ) : ℂ) * ∫ w in Ac,
            (χ w : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ q w : ℝ) : ℂ))) := by
  rw [boxWinModeC, Set.indicator_of_mem hz (fun _ => (1 : ℂ)), one_mul]

/-- **The amplitude dictionary (complex form).**  The windowed amplitude of FS's box projection
`Q_{Ac,i}Ψ` is the complex integral of the mean-free windowed mode against the slot fibre. -/
theorem tBamp_boxQInd_ampC {n : ℕ} {a volA : ℝ} (ha : 0 < a) (hvolpos : 0 < volA)
    {Ac : Set (EuclideanSpace ℝ (Fin 3))} (hAcm : MeasurableSet Ac)
    (hAcsub : Ac ⊆ Submission.BoseGases.acube a)
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχc : Continuous χ) (hχs : HasCompactSupport χ)
    {Ψ : Submission.BoseGases.X n → ℝ} (hΨ : Continuous Ψ) (i : Fin n)
    (q : EuclideanSpace ℝ (Fin 3)) (x : Submission.BoseGases.X n) :
    Work.SmallBoxTBWord.tBamp χ q (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x
      = ((∫ z in Ac, Work.BoseFixB1.boxWinModeReGen volA Ac χ q z
            * Ψ (Function.update x i z) : ℝ) : ℂ)
        + Complex.I * ((∫ z in Ac, Work.BoseFixB1.boxWinModeImGen volA Ac χ q z
            * Ψ (Function.update x i z) : ℝ) : ℂ) := by
  classical
  let M : E3 → ℂ := fun z => (χ z : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ q z : ℝ) : ℂ)))
  let U : E3 → ℝ := fun z => Ψ (Function.update x i z)
  let m : ℝ := (1 / volA) * ∫ w in Ac, U w
  let Ic : ℂ := ∫ w in Ac, M w
  let Cbar : ℂ := ((volA⁻¹ : ℝ) : ℂ) * Ic
  have hMcont : Continuous M :=
    (Complex.continuous_ofReal.comp hχc).mul (Complex.continuous_exp.comp (by fun_prop))
  have hMcs : HasCompactSupport M :=
    (hχs.comp_left (g := fun z : ℝ => (z : ℂ)) (by simp)).mul_right
      (f' := fun w : E3 => Complex.exp (-(Complex.I * ((inner ℝ q w : ℝ) : ℂ))))
  have hMglob : Integrable M := hMcont.integrable_of_hasCompactSupport hMcs
  have hMOn : IntegrableOn M Ac := hMglob.integrableOn
  have hUcont : Continuous U := by
    show Continuous (fun z : E3 => Ψ (Function.update x i z))
    exact hΨ.comp (continuous_const.update i continuous_id)
  have hUint : IntegrableOn U Ac :=
    (ContinuousOn.integrableOn_compact (Submission.BoseGases.acube_compact ha)
      hUcont.continuousOn).mono_set hAcsub
  have hUc : IntegrableOn (fun z : E3 => (U z : ℂ)) Ac := hUint.ofReal
  have hMU : IntegrableOn (fun z : E3 => M z * (U z : ℂ)) Ac := by
    obtain ⟨B, hB⟩ := hχs.exists_bound_of_continuous hχc
    refine Integrable.bdd_mul (f := M) (g := fun z => (U z : ℂ)) hUc
      hMcont.aestronglyMeasurable (c := B) ?_
    filter_upwards with z
    have hexp : ‖Complex.exp (-(Complex.I * ((inner ℝ q z : ℝ) : ℂ)))‖ = 1 := by
      have h : -(Complex.I * (((inner ℝ q z : ℝ)) : ℂ))
          = ((-(inner ℝ q z) : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [h, Complex.norm_exp_ofReal_mul_I]
    show ‖(χ z : ℂ) * Complex.exp (-(Complex.I * ((inner ℝ q z : ℝ) : ℂ)))‖ ≤ B
    rw [norm_mul, hexp, mul_one]
    simpa using hB z
  have hMm : IntegrableOn (fun z : E3 => M z * (m : ℂ)) Ac := hMOn.mul_const (m : ℂ)
  have hCU : IntegrableOn (fun z : E3 => Cbar * (U z : ℂ)) Ac := hUc.const_mul Cbar
  -- Step A: unfold the amplitude of the box projection
  have hA : Work.SmallBoxTBWord.tBamp χ q (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x
      = ∫ z, M z * (Ac.indicator (fun _ => (1 : ℂ)) z * ((U z : ℂ) - (m : ℂ))) := by
    rw [Work.SmallBoxTBWord.tBamp]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with z
    rw [boxQInd_update_eq_cast volA i Ψ x z]
  -- Step B: remove the box indicator
  have hB : (∫ z, M z * (Ac.indicator (fun _ => (1 : ℂ)) z * ((U z : ℂ) - (m : ℂ))))
      = ∫ z in Ac, M z * ((U z : ℂ) - (m : ℂ)) := by
    trans ∫ z, Ac.indicator (fun z => M z * ((U z : ℂ) - (m : ℂ))) z
    · apply MeasureTheory.integral_congr_ae
      filter_upwards with z
      by_cases hz : z ∈ Ac
      · rw [Set.indicator_of_mem hz (fun _ => (1 : ℂ)), Set.indicator_of_mem hz, one_mul]
      · rw [Set.indicator_of_notMem hz (fun _ => (1 : ℂ)), Set.indicator_of_notMem hz]
        ring
    · exact MeasureTheory.integral_indicator hAcm
        (f := fun z => M z * ((U z : ℂ) - (m : ℂ)))
  -- Step C: cancel the box mean of the fibre against the box mean of the mode
  have hC : (∫ z in Ac, M z * ((U z : ℂ) - (m : ℂ)))
      = ∫ z in Ac, (M z - Cbar) * (U z : ℂ) := by
    have h1 : (∫ z in Ac, M z * ((U z : ℂ) - (m : ℂ)))
        = ∫ z in Ac, (M z * (U z : ℂ) - M z * (m : ℂ)) := by
      apply MeasureTheory.setIntegral_congr_fun hAcm
      intro z _
      ring
    have h2 : (∫ z in Ac, (M z * (U z : ℂ) - M z * (m : ℂ)))
        = (∫ z in Ac, M z * (U z : ℂ)) - ∫ z in Ac, M z * (m : ℂ) :=
      MeasureTheory.integral_sub hMU hMm
    have h3 : (∫ z in Ac, M z * (m : ℂ)) = Ic * (m : ℂ) :=
      MeasureTheory.integral_mul_const (m : ℂ) M
    have h4 : Ic * (m : ℂ) = Cbar * ((∫ w in Ac, U w : ℝ) : ℂ) := by
      have hm : (m : ℂ) = ((volA⁻¹ : ℝ) : ℂ) * ((∫ w in Ac, U w : ℝ) : ℂ) := by
        dsimp only [m]
        rw [one_div, Complex.ofReal_mul]
      calc Ic * (m : ℂ)
          = Ic * (((volA⁻¹ : ℝ) : ℂ) * ((∫ w in Ac, U w : ℝ) : ℂ)) := by rw [hm]
        _ = (((volA⁻¹ : ℝ) : ℂ) * Ic) * ((∫ w in Ac, U w : ℝ) : ℂ) := by ring
        _ = Cbar * ((∫ w in Ac, U w : ℝ) : ℂ) := rfl
    have h5 : Cbar * ((∫ w in Ac, U w : ℝ) : ℂ) = ∫ z in Ac, Cbar * (U z : ℂ) := by
      rw [MeasureTheory.integral_const_mul]
      congr 1
      exact (Complex.ofRealCLM.integral_comp_comm (φ := U) (φ_int := hUint)).symm
    have h6 : (∫ z in Ac, M z * (U z : ℂ)) - ∫ z in Ac, Cbar * (U z : ℂ)
        = ∫ z in Ac, (M z * (U z : ℂ) - Cbar * (U z : ℂ)) :=
      (MeasureTheory.integral_sub hMU hCU).symm
    have h7 : (∫ z in Ac, (M z * (U z : ℂ) - Cbar * (U z : ℂ)))
        = ∫ z in Ac, (M z - Cbar) * (U z : ℂ) := by
      apply MeasureTheory.setIntegral_congr_fun hAcm
      intro z _
      ring
    calc (∫ z in Ac, M z * ((U z : ℂ) - (m : ℂ)))
        = ∫ z in Ac, (M z * (U z : ℂ) - M z * (m : ℂ)) := h1
      _ = (∫ z in Ac, M z * (U z : ℂ)) - ∫ z in Ac, M z * (m : ℂ) := h2
      _ = (∫ z in Ac, M z * (U z : ℂ)) - Ic * (m : ℂ) := by rw [h3]
      _ = (∫ z in Ac, M z * (U z : ℂ)) - Cbar * ((∫ w in Ac, U w : ℝ) : ℂ) := by rw [h4]
      _ = (∫ z in Ac, M z * (U z : ℂ)) - ∫ z in Ac, Cbar * (U z : ℂ) := by rw [h5]
      _ = ∫ z in Ac, (M z * (U z : ℂ) - Cbar * (U z : ℂ)) := h6
      _ = ∫ z in Ac, (M z - Cbar) * (U z : ℂ) := h7
  -- Step D: identify the integrand with the genuine windowed mode `boxWinModeC`
  have hD : (∫ z in Ac, (M z - Cbar) * (U z : ℂ))
      = ∫ z in Ac, boxWinModeC volA Ac χ q z * (U z : ℂ) := by
    apply MeasureTheory.setIntegral_congr_fun hAcm
    intro z hz
    show (M z - Cbar) * (U z : ℂ) = boxWinModeC volA Ac χ q z * (U z : ℂ)
    rw [boxWinModeC_of_mem volA Ac χ q z hz]
  have hf : IntegrableOn (fun z : E3 => boxWinModeC volA Ac χ q z * (U z : ℂ)) Ac := by
    refine (hMU.sub hCU).congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hAcm] with z hz
    simp only [Pi.sub_apply]
    rw [boxWinModeC_of_mem volA Ac χ q z hz]
    rw [sub_mul]
  -- Step E: split the complex mode into its two real parts
  have hre0 : (∫ z in Ac, boxWinModeC volA Ac χ q z * (U z : ℂ)).re
      = ∫ z in Ac, (boxWinModeC volA Ac χ q z * (U z : ℂ)).re :=
    (integral_re hf).symm
  have him0 : (∫ z in Ac, boxWinModeC volA Ac χ q z * (U z : ℂ)).im
      = ∫ z in Ac, (boxWinModeC volA Ac χ q z * (U z : ℂ)).im :=
    (integral_im hf).symm
  have hre : (∫ z in Ac, boxWinModeC volA Ac χ q z * (U z : ℂ)).re
      = ∫ z in Ac, boxWinModeReGen volA Ac χ q z * U z := by
    rw [hre0]
    apply MeasureTheory.setIntegral_congr_fun hAcm
    intro z _
    show (boxWinModeC volA Ac χ q z * (U z : ℂ)).re = boxWinModeReGen volA Ac χ q z * U z
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
      boxWinModeC_re volA Ac hχc hχs q z]
  have him : (∫ z in Ac, boxWinModeC volA Ac χ q z * (U z : ℂ)).im
      = ∫ z in Ac, boxWinModeImGen volA Ac χ q z * U z := by
    rw [him0]
    apply MeasureTheory.setIntegral_congr_fun hAcm
    intro z _
    show (boxWinModeC volA Ac χ q z * (U z : ℂ)).im = boxWinModeImGen volA Ac χ q z * U z
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add,
      boxWinModeC_im volA Ac hχc hχs q z]
  have hE : (∫ z in Ac, boxWinModeC volA Ac χ q z * (U z : ℂ))
      = ((∫ z in Ac, boxWinModeReGen volA Ac χ q z * U z : ℝ) : ℂ)
        + Complex.I * ((∫ z in Ac, boxWinModeImGen volA Ac χ q z * U z : ℝ) : ℂ) := by
    refine Complex.ext ?_ ?_
    · rw [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, hre]
      ring
    · rw [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, him]
      ring
  exact hA.trans (hB.trans (hC.trans (hD.trans hE)))

/-- `‖A + iB‖² = A² + B²` for real `A`, `B` (the Pythagoras identity used to split the
complex amplitude into its two real slot amplitudes). -/
private lemma normSq_ofReal_add_mul_I (A B : ℝ) :
    ‖((A : ℂ) + Complex.I * (B : ℂ))‖ ^ 2 = A ^ 2 + B ^ 2 := by
  have h : ((A : ℂ) + Complex.I * (B : ℂ)) = ((A : ℂ) + (B : ℂ) * Complex.I) := by ring
  rw [h, Complex.sq_norm, Complex.normSq_add_mul_I]

/-- **The amplitude dictionary (norm-squared form).** -/
theorem tBamp_boxQInd_normSq {n : ℕ} {a volA : ℝ} (ha : 0 < a) (hvolpos : 0 < volA)
    {Ac : Set (EuclideanSpace ℝ (Fin 3))} (hAcm : MeasurableSet Ac)
    (hAc : Ac ⊆ Submission.BoseGases.acube a)
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχc : Continuous χ) (hχs : HasCompactSupport χ)
    {Ψ : Submission.BoseGases.X n → ℝ} (hΨ : Continuous Ψ) (i : Fin n)
    {x : Submission.BoseGases.X n} (hx : x ∈ Submission.BoseGases.abox n a)
    (q : EuclideanSpace ℝ (Fin 3)) :
    ‖Work.SmallBoxTBWord.tBamp χ q (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2
      = (∫ z in Ac, Work.BoseFixB1.boxWinModeReGen volA Ac χ q z
            * Ψ (Function.update x i z)) ^ 2
        + (∫ z in Ac, Work.BoseFixB1.boxWinModeImGen volA Ac χ q z
            * Ψ (Function.update x i z)) ^ 2 := by
  rw [tBamp_boxQInd_ampC ha hvolpos hAcm hAc hχc hχs hΨ i q x]
  exact normSq_ofReal_add_mul_I _ _

end Work.BoseFixB1
