import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.H2W.AeProof.AeSigmaUpgradeU
import Submission.Work.FTS.EllipticEst.HkSq_eq_lintegral
import Submission.Work.FTS.EllipticEst.Honest.Basic
import Submission.Work.FTS.EllipticEst.Honest.HonSliceRightTendsto
import Submission.Work.FTS.EllipticEst.H2W.Ae.SecDerivBasic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AeS1

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

/-!
**The σ-Poincaré upgrade of the `u`-norm** in the almost-everywhere class `H2W.Ae.AeData`:
`HkSq α 0 u ≤ C · L2Sq (∂_θu · w)`, i.e. `‖u‖_ρ ≤ C‖∂_θu‖_{w²}`.

The *same* statement is already proved in this workspace as `Dispatch.aeSigmaUpD`
(`Dispatch/cores_level_zero.lean`, from the axiom-clean `H2W.AeProof.AeSigmaUpgradeU_all` via
`MeasureTheory.integral_eq_lintegral_of_nonneg_ae`), but that module's import cone currently
contains `Honest/firstOrderHonest`, which is mid-refactor and fails to build; the proof body
there is ported into this file (set the slice integrands
`z ↦ ∫θ u²σ`, `z ↦ ∫θ (∂_θu)²`, compare them with the `∫⁻`-inequality of
`AeSigmaUpgradeU_all` via `ofReal_integral_eq_lintegral_ofReal` /
`lintegral_ofReal_ne_top_iff_integrable`, and finish with `integral_mono_ae`), so that this
version is self-contained.  It does not import `Dispatch.cores_level_zero` nor
`H2W.Ae.hkMem_u`.
-/
theorem sigmaUpD : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      Work.Spaces.L2Mem (fun z θ => Work.Spaces.pth u z θ * Work.Spaces.w z) →
      Work.Spaces.HkSq α 0 u
        ≤ C * Work.Spaces.L2Sq (fun z θ => Work.Spaces.pth u z θ * Work.Spaces.w z) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Work.FTS.EllipticEst.H2W.AeProof.AeSigmaUpgradeU_all
  refine ⟨C₀, hC₀pos, ?_⟩
  intro α u G hA hL2
  -- ## abbreviations
  set Asl : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
    with hAsl
  set Bsl : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth u z θ) ^ 2 with hBsl
  set Apr : ℝ → ℝ≥0∞ := fun z => ∫⁻ θ in Work.Spaces.Iθ,
    ENNReal.ofReal ((u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) with hApr
  set Bpr : ℝ → ℝ≥0∞ := fun z => ∫⁻ θ in Work.Spaces.Iθ,
    ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2) with hBpr
  -- ## elementary facts
  have hsEta_nn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Work.FTS.EllipticEst.sEta θ := by
    intro θ hθ
    show 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
    exact Real.rpow_nonneg (Work.FTS.EllipticEst.Honest.sin_two_nonneg_of_mem_Iθ hθ) _
  have hAsl_nn : ∀ z, 0 ≤ Asl z := by
    intro z
    rw [hAsl]
    exact setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (hsEta_nn θ hθ))
  have hBsl_nn : ∀ z, 0 ≤ Bsl z := by
    intro z
    rw [hBsl]
    exact setIntegral_nonneg measurableSet_Icc (fun θ _ => sq_nonneg _)
  -- ## the level-`0` integrand is `w²·(u²σ)`
  have hptid : ∀ z θ, θ ∈ Work.Spaces.Iθ →
      Work.Spaces.HkIntegrand α 0 u z θ
        = (Work.Spaces.w z) ^ 2 * ((u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
    intro z θ hθ
    rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq, mul_pow,
      Work.FTS.EllipticEst.Honest.sq_weight_eq (Work.FTS.EllipticEst.Honest.sin_two_nonneg_of_mem_Iθ hθ)]
    simp only [Work.FTS.EllipticEst.sEta]
    ring
  have hslice : ∀ z, (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ)
      = (Work.Spaces.w z) ^ 2 * Asl z := by
    intro z
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
    exact hptid z θ hθ
  -- ## `HkSq` as a `toReal` of a `lintegral`
  have hHk : Work.Spaces.HkSq α 0 u
      = (∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * Asl z)).toReal := by
    rw [Work.FTS.EllipticEst.HkSq_eq_lintegral α 0 u hA.smooth]
    congr 1
    exact MeasureTheory.lintegral_congr fun z => by rw [hslice z]
  -- ## `L2Sq` as a `toReal` of a `lintegral`
  have hL2pt : (fun z => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.pth u z θ * Work.Spaces.w z) ^ 2)
      = fun z => (Work.Spaces.w z) ^ 2 * Bsl z := by
    funext z
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
    ring
  have hL2mem : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * Bsl z) Work.Spaces.Iz :=
    hL2.2.congr_fun (fun z _ => congr_fun hL2pt z) measurableSet_Ici
  have hL2l : Work.Spaces.L2Sq (fun z θ => Work.Spaces.pth u z θ * Work.Spaces.w z)
      = (∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * Bsl z)).toReal := by
    rw [Work.Spaces.L2Sq, hL2pt]
    exact MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (hBsl_nn z))
      hL2mem.aestronglyMeasurable
  -- ## the slicewise measurability of `u²σ`
  have hslice_smooth : ∀ z, 0 < z →
      ContDiffOn ℝ 1 (fun θ => u z θ) (Set.Ioo 0 (Real.pi / 2)) := by
    intro z hz
    have hmap : MapsTo (fun θ : ℝ => (z, θ)) (Set.Ioo 0 (Real.pi / 2))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := fun θ hθ => ⟨hz, hθ⟩
    exact (hA.smooth 1).comp (by fun_prop) hmap
  have haesm_slice : ∀ z, 0 < z → AEStronglyMeasurable
      (fun θ => (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    intro z hz
    exact ((Work.FTS.EllipticEst.Honest.aesm_of_contDiffOn_Ioo (hslice_smooth z hz)).pow 2).mul
      (Work.FTS.EllipticEst.H2W.Ae.measurable_sEta.aestronglyMeasurable)
  -- ## the slicewise identity `Asl z = (∫⁻ ...).toReal`
  have hAsl_eq : ∀ z, 0 < z → Asl z = (Apr z).toReal := by
    intro z hz
    rw [hAsl, hApr]
    refine MeasureTheory.integral_eq_lintegral_of_nonneg_ae ?_ (haesm_slice z hz)
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (hsEta_nn θ hθ))
  -- ## pointwise domination, a.e. in `z`
  have hdom_ae : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * Asl z)
        ≤ ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * Apr z := by
    rw [Work.Spaces.Iz, MeasureTheory.ae_restrict_iff' measurableSet_Ici]
    have hne : ∀ᵐ z ∂(MeasureTheory.volume : Measure ℝ), z ≠ 0 := by
      rw [MeasureTheory.ae_iff]
      simp
    filter_upwards [hne] with z hz hzI
    have hzpos : 0 < z := lt_of_le_of_ne hzI (Ne.symm hz)
    rw [ENNReal.ofReal_mul (sq_nonneg (Work.Spaces.w z))]
    refine mul_le_mul_of_nonneg_left ?_ bot_le
    rw [hAsl_eq z hzpos]
    exact ENNReal.ofReal_toReal_le
  have hstepA : (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * Asl z))
      ≤ ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * Apr z :=
    MeasureTheory.lintegral_mono_ae hdom_ae
  -- ## the proved slicewise upgrade
  have hup : (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * Apr z)
      ≤ ENNReal.ofReal C₀ * (∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * Bpr z) :=
    hC₀ α u G hA
  -- ## the two `∫⁻`-expressions agree with the Bochner ones
  have hint2 : ∀ z, 0 < z → MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pth u z θ) ^ 2) Work.Spaces.Iθ := by
    intro z hz
    have hwz : Work.Spaces.w z ≠ 0 := by
      rw [Work.Spaces.w]; positivity
    have hint : MeasureTheory.Integrable
        (fun θ => (Work.Spaces.pth u z θ * Work.Spaces.w z) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hL2.1 z (le_of_lt hz)
    have hdiv : MeasureTheory.Integrable
        (fun θ => (Work.Spaces.pth u z θ * Work.Spaces.w z) ^ 2 / (Work.Spaces.w z) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hint.div_const _
    have haeeq : (fun θ => (Work.Spaces.pth u z θ * Work.Spaces.w z) ^ 2
          / (Work.Spaces.w z) ^ 2) =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun θ => (Work.Spaces.pth u z θ) ^ 2) := by
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ _ => ?_)
      field_simp
    exact hdiv.congr haeeq
  have hBsl_eq : ∀ z, 0 < z → Bsl z = (Bpr z).toReal := by
    intro z hz
    rw [hBsl, hBpr]
    refine MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun θ => sq_nonneg _) (hint2 z hz).aestronglyMeasurable
  have hBpr_ne : ∀ z, 0 < z → Bpr z ≠ ⊤ := by
    intro z hz
    rw [hBpr]
    exact (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable (hint2 z hz).aestronglyMeasurable
      (Filter.Eventually.of_forall fun θ => sq_nonneg _)).mpr (hint2 z hz)
  have hCeq_ae : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * Bpr z
        = ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * Bsl z) := by
    rw [Work.Spaces.Iz, MeasureTheory.ae_restrict_iff' measurableSet_Ici]
    have hne : ∀ᵐ z ∂(MeasureTheory.volume : Measure ℝ), z ≠ 0 := by
      rw [MeasureTheory.ae_iff]
      simp
    filter_upwards [hne] with z hz hzI
    have hzpos : 0 < z := lt_of_le_of_ne hzI (Ne.symm hz)
    rw [hBsl_eq z hzpos, ENNReal.ofReal_mul (sq_nonneg (Work.Spaces.w z)),
      ENNReal.ofReal_toReal (hBpr_ne z hzpos)]
  have hstepC : (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * Bpr z)
      = ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * Bsl z) :=
    MeasureTheory.lintegral_congr_ae hCeq_ae
  -- ## finiteness of the right-hand side
  have hYne : (∫⁻ z in Work.Spaces.Iz,
      ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * Bsl z)) ≠ ⊤ := by
    refine (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
      hL2mem.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (hBsl_nn z))).mpr hL2mem
  have hBne : (∫⁻ z in Work.Spaces.Iz,
      ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * Bpr z) ≠ ⊤ := by
    rw [hstepC]; exact hYne
  have hBne' : ENNReal.ofReal C₀ * (∫⁻ z in Work.Spaces.Iz,
      ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * Bpr z) ≠ ⊤ := by
    rw [hstepC]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hYne
  have hAne : (∫⁻ z in Work.Spaces.Iz,
      ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * Apr z) ≠ ⊤ :=
    ne_top_of_le_ne_top hBne' hup
  -- ## assembly
  calc Work.Spaces.HkSq α 0 u
      = (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * Asl z)).toReal := hHk
    _ ≤ (∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * Apr z).toReal :=
        ENNReal.toReal_mono hAne hstepA
    _ ≤ (ENNReal.ofReal C₀ * ∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * Bpr z).toReal :=
        ENNReal.toReal_mono hBne' hup
    _ = C₀ * (∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * Bpr z).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC₀pos.le]
    _ = C₀ * Work.Spaces.L2Sq (fun z θ => Work.Spaces.pth u z θ * Work.Spaces.w z) := by
        rw [hstepC, ← hL2l]

end Work.FTS.EllipticEst.AeS1
