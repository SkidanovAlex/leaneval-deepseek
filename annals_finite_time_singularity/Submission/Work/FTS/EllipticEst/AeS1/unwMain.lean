import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.ProductTools
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.AeS1.unwAux
import Submission.Work.FTS.EllipticEst.AeS1.l2Dictionary
import Submission.Work.FTS.EllipticEst.AngAWeak.AeEnergyMain
import Submission.Work.FTS.EllipticEst.H2W.AeProof.AeGapSlices
import Submission.Work.FTS.EllipticEst.Dispatch.aeLeftLimitD
import Submission.Work.FTS.EllipticEst.H2W.AeProof.AeSliceRightTendsto
import Submission.Work.FTS.EllipticEst.Dispatch.hkMemUD

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AeS1

set_option autoImplicit false

theorem restrict_Iz_eq_Ioi :
    MeasureTheory.volume.restrict Work.Spaces.Iz
      = MeasureTheory.volume.restrict (Set.Ioi 0) := by
  rw [Work.Spaces.Iz]
  exact MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm

/-- **The a.e. slicewise constrained gap in `∫⁻` form**: `9 M ≤ B` with
`M = ∫⁻_z ofReal(w²)∫⁻_θ ofReal(u²)` and `B = ∫⁻_z ofReal(w²)∫⁻_θ ofReal((∂_θu)²)`. -/
theorem gap9_lintegral {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hC : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      ContinuousOn (fun θ => u z θ) (Set.Icc 0 (Real.pi / 2))) :
    ENNReal.ofReal 9 * (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2)))
      ≤ (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2))) := by
  have hgap := Work.FTS.EllipticEst.H2W.AeProof.AeGapSlices α u G h hC
    (ae_integrableOn_pth_sq h)
  have hu := ae_integrableOn_u_sq h
  have hp := ae_integrableOn_pth_sq h
  have hpt : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
          * (ENNReal.ofReal 9
            * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2)))
        ≤ ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
          * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2)) := by
    rw [restrict_Iz_eq_Ioi]
    filter_upwards [hgap, hu, hp] with z hz hzu hzp
    have h1 : ENNReal.ofReal (9 * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2))
        ≤ ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth u z θ) ^ 2) :=
      ENNReal.ofReal_le_ofReal hz
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 9),
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal hzu
        (Filter.Eventually.of_forall fun θ => sq_nonneg _),
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal hzp
        (Filter.Eventually.of_forall fun θ => sq_nonneg _)] at h1
    exact mul_le_mul_of_nonneg_left h1 zero_le
  calc ENNReal.ofReal 9 * (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2)))
      = ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal 9
          * (ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
            * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2))) := by
        rw [MeasureTheory.lintegral_const_mul' (ENNReal.ofReal 9)
          (fun z => ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
            * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2)))
          ENNReal.ofReal_ne_top]
    _ = ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
          * (ENNReal.ofReal 9
            * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2))) := by
        refine lintegral_congr fun z => ?_
        ring
    _ ≤ _ := MeasureTheory.lintegral_mono_ae hpt

/-- **The main reduction**: the unweighted first-order energy inequality follows from the
`∫⁻`-form energy inequality `hineq` (with the constant `13/2 + 3α² + (3/2)α(5+α) < 9`). -/
theorem unwEnergyD_of
    (hineq : ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      ENNReal.ofReal (α ^ 2) * (∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
            * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((z * Work.Spaces.pz u z θ) ^ 2)))
        + (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
          * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2)))
      ≤ ENNReal.ofReal (13 / 2 + (3 * α ^ 2 + (3 / 2) * α * (5 + α)))
          * (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
            * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2)))
        + ENNReal.ofReal (1 / 2) * ENNReal.ofReal (Work.Spaces.HkSq α 0 G)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
        Work.Spaces.L2Mem (fun z θ => z * Work.Spaces.pz u z θ * Work.Spaces.w z) ∧
        Work.Spaces.L2Mem (fun z θ => Work.Spaces.pth u z θ * Work.Spaces.w z) ∧
        α ^ 2 * Work.Spaces.L2Sq (fun z θ => z * Work.Spaces.pz u z θ * Work.Spaces.w z)
          + Work.Spaces.L2Sq (fun z θ => Work.Spaces.pth u z θ * Work.Spaces.w z)
        ≤ C * Work.Spaces.HkSq α 0 G := by
  refine ⟨16, by norm_num, ?_⟩
  intro α u G h
  -- ## the a.e. continuity of the fibres (needed for the gap)
  have hL0 := Work.FTS.EllipticEst.Dispatch.aeLeftLimitD α u G h
  have hC := Work.FTS.EllipticEst.H2W.AeProof.ae_continuousOn_slice h hL0
  -- ## abbreviations
  set A : ℝ≥0∞ := ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
      * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((z * Work.Spaces.pz u z θ) ^ 2)) with hAdef
  set B : ℝ≥0∞ := ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
      * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2)) with hBdef
  set M : ℝ≥0∞ := ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
      * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2)) with hMdef
  set K : ℝ := 13 / 2 + (3 * α ^ 2 + (3 / 2) * α * (5 + α)) with hKdef
  set H : ℝ := Work.Spaces.HkSq α 0 G with hHdef
  have hH0 : 0 ≤ H := by rw [hHdef]; exact Work.Spaces.HkSq_nonneg α 0 G
  have hK0 : 0 ≤ K := by
    rw [hKdef]
    have hα0 := h.hα.le
    nlinarith [sq_nonneg α]
  have hKle : K ≤ 8.657 := by
    rw [hKdef]
    have hα0 := h.hα.le
    have hα4 := h.hα4
    nlinarith [sq_nonneg α]
  -- ## the gap and the finiteness
  have hgap : ENNReal.ofReal 9 * M ≤ B := gap9_lintegral h hC
  have hM : M ≠ ⊤ := lintegral_ne_top_of_HkMem (Work.FTS.EllipticEst.Dispatch.hkMem_uM α u G h)
  have hKW : ENNReal.ofReal K * M ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hM
  have hHH : ENNReal.ofReal (1 / 2) * ENNReal.ofReal H ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hRne : ENNReal.ofReal K * M + ENNReal.ofReal (1 / 2) * ENNReal.ofReal H ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hKW, hHH⟩
  have hineq' : ENNReal.ofReal (α ^ 2) * A + B
      ≤ ENNReal.ofReal K * M + ENNReal.ofReal (1 / 2) * ENNReal.ofReal H := hineq α u G h
  have hLne : ENNReal.ofReal (α ^ 2) * A + B ≠ ⊤ := ne_top_of_le_ne_top hRne hineq'
  have hA : A ≠ ⊤ := by
    intro hAtop
    refine hLne ?_
    have h1 : ENNReal.ofReal (α ^ 2) * A = ⊤ := by
      rw [hAtop, ENNReal.mul_top]
      exact ENNReal.ofReal_ne_zero_iff.mpr (pow_pos h.hα 2)
    rw [h1, top_add]
  have hB : B ≠ ⊤ := by
    intro hBtop
    exact hLne (by rw [hBtop, add_top])
  -- ## passing to `toReal`
  have hA2 : ENNReal.ofReal (α ^ 2) * A ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hA
  have hreal : α ^ 2 * A.toReal + B.toReal ≤ K * M.toReal + (1 / 2) * H := by
    have h1 := ENNReal.toReal_mono hRne hineq'
    rw [ENNReal.toReal_add hA2 hB, ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg α),
      ENNReal.toReal_add hKW hHH, ENNReal.toReal_mul, ENNReal.toReal_ofReal hK0,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ENNReal.toReal_ofReal hH0] at h1
    exact h1
  have hgapR : 9 * M.toReal ≤ B.toReal := by
    have h1 := ENNReal.toReal_mono hB hgap
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 9)] at h1
  have hX0 : 0 ≤ A.toReal := ENNReal.toReal_nonneg
  have hY0 : 0 ≤ B.toReal := ENNReal.toReal_nonneg
  have hW0 : 0 ≤ M.toReal := ENNReal.toReal_nonneg
  -- ## the arithmetic
  have hWle : M.toReal ≤ B.toReal / 9 := by linarith
  have hKWle : K * M.toReal ≤ (K / 9) * B.toReal := by
    have h1 := mul_le_mul_of_nonneg_left hWle hK0
    calc K * M.toReal ≤ K * (B.toReal / 9) := h1
      _ = (K / 9) * B.toReal := by ring
  have hK9 : (1 : ℝ) / 30 ≤ 1 - K / 9 := by linarith
  have hYb : B.toReal ≤ 15 * H := by nlinarith [hreal, hgapR, hK0, hKle, hH0, hX0, hY0]
  have hXb : α ^ 2 * A.toReal ≤ (1 / 2) * H := by
    have hYnn : 0 ≤ (1 - K / 9) * B.toReal := mul_nonneg (by linarith) hY0
    nlinarith [hreal, hKWle, hYnn]
  have hfinal : α ^ 2 * A.toReal + B.toReal ≤ 16 * H := by nlinarith [hXb, hYb]
  -- ## the dictionary: `L2Mem` and the identification of the `∫⁻`-norms
  obtain ⟨hmA, hsqA⟩ := l2Dictionary (f := fun z θ => z * Work.Spaces.pz u z θ)
    (aesm_prod_gradW_sq h.smooth) (integrableOn_gradW_sq h) hA
  obtain ⟨hmB, hsqB⟩ := l2Dictionary (f := Work.Spaces.pth u)
    (aesm_prod_pthW_sq h.smooth) (integrableOn_pthW_sq h) hB
  have hsqA' : Work.Spaces.L2Sq (fun z θ => z * Work.Spaces.pz u z θ * Work.Spaces.w z)
      = A.toReal := hsqA
  have hsqB' : Work.Spaces.L2Sq (fun z θ => Work.Spaces.pth u z θ * Work.Spaces.w z)
      = B.toReal := hsqB
  refine ⟨?_, ?_, ?_⟩
  · exact hmA
  · exact hmB
  · rw [hsqA', hsqB']
    exact hfinal

end Work.FTS.EllipticEst.AeS1
