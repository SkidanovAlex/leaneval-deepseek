import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.H2W.Ae.SecDerivBasic
import Submission.Work.FTS.EllipticEst.H2W.AeProof.AeSigmaUpgradeU
import Submission.Work.FTS.EllipticEst.HkSq_eq_lintegral
import Submission.Work.FTS.EllipticEst.Honest.Basic
import Submission.Work.FTS.EllipticEst.Honest.HonSliceRightTendsto
import Submission.Work.FTS.EllipticEst.H2W.Ae.Assembly
import Submission.Work.FTS.EllipticEst.H2W.Ae.hkMem_u
import Submission.Work.FTS.EllipticEst.AeS1.DzAgmonClean
import Submission.Work.FTS.EllipticEst.AeS1.Assembly
import Submission.Work.FTS.EllipticEst.AeS1.unwEnergyD
import Submission.Work.FTS.EllipticEst.Dispatch.aeSigmaEnergyD
import Submission.Work.FTS.EllipticEst.Dispatch.step2AeD
import Submission.Work.FTS.EllipticEst.Dispatch.step3AeD

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Dispatch

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

/-- `EllWeakPos` is `AeData` (the pointwise moments imply the a.e. ones; the classes are
otherwise identical). -/
theorem aeData_of_ellWeakPos' {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ) :
    Work.FTS.EllipticEst.H2W.Ae.AeData α Ψ F :=
  ⟨hα, hα4, h.eq, h.zero, h.pi_half, h.smooth, h.memF, h.memA, h.memB,
    (by filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
        exact h.orthPsi z hz),
    (by filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
        exact h.orthF z hz)⟩

/-- **The `σ`-upgrade of the `u`-norm in the a.e. class** (Step 1, the `u`-half): for a datum
`u` of the almost-everywhere class, `HkSq α 0 u ≤ C · L2Sq (∂_θu · w)`.

This is the statement `aeSigmaUp` of `H2W/Ae/aeSigmaUp.lean`.  It is proved here from the
*already proved* slicewise σ-Poincaré upgrade `AeProof.AeSigmaUpgradeU_all` (an inequality of
`∫⁻`-integrals, `AeSigmaUpgradeU_all`), by translating the `∫⁻`-statement into the Bochner
statement `HkSq`/`L2Sq` with `MeasureTheory.integral_eq_lintegral_of_nonneg_ae`. -/
theorem aeSigmaUpD : ∃ C : ℝ, 0 < C ∧
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

/-- **Honesty of `z ∂_z u` in the a.e. class** (the `k = 0` case of the Agmon–Nirenberg
certificate of `Work.Blocks.DzVamgm.HkNorm_Dz_amgm`, here imported through the
self-contained copy `AeS1.DzAgmonClean`). -/
theorem hkMem_gradU' (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) := by
  obtain ⟨C, _hC, hmain⟩ := Work.Blocks.DzVamgm.HkNorm_Dz_amgm 0
  have hα1 : α ≤ 1 := by linarith [h.hα4]
  have hu : Work.Spaces.HkMem α 0 u := Work.FTS.EllipticEst.H2W.Ae.hkMem_u α u G h
  exact (hmain α u h.hα hα1 h.smooth hu h.memRad2).1

/-- **Step 1 of `prop:H2` in the a.e. class**, assembled from the three analytic pieces
`aeFirstEnergy`, `aeSigmaUp` and `aeSigmaEnergy` (together with the Agmon honesty
`hkMem_gradU'`).  This is `Ae.step1Ae` with its three inputs exhibited as hypotheses. -/
theorem step1AeD_of
    (hE : ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
        Work.Spaces.L2Mem (fun z θ => z * Work.Spaces.pz u z θ * Work.Spaces.w z) ∧
        Work.Spaces.L2Mem (fun z θ => Work.Spaces.pth u z θ * Work.Spaces.w z) ∧
        α ^ 2 * Work.Spaces.L2Sq (fun z θ => z * Work.Spaces.pz u z θ * Work.Spaces.w z)
          + Work.Spaces.L2Sq (fun z θ => Work.Spaces.pth u z θ * Work.Spaces.w z)
        ≤ C * Work.Spaces.HkSq α 0 G)
    (hU : ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
        Work.Spaces.L2Mem (fun z θ => Work.Spaces.pth u z θ * Work.Spaces.w z) →
        Work.Spaces.HkSq α 0 u
          ≤ C * Work.Spaces.L2Sq (fun z θ => Work.Spaces.pth u z θ * Work.Spaces.w z))
    (hD : ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
        Work.Spaces.L2Mem (fun z θ => z * Work.Spaces.pz u z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ∧
        α ^ 2 * Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u)
          ≤ C * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u)) :
    Work.FTS.EllipticEst.H2W.Ae.Step1 := by
  obtain ⟨C₁, hC₁, hE'⟩ := hE
  obtain ⟨Cσ, hCσ, hU'⟩ := hU
  obtain ⟨C₂, hC₂, hD'⟩ := hD
  have hK1 : 0 ≤ Cσ * C₁ := le_of_lt (mul_pos hCσ hC₁)
  have hK2 : 0 ≤ C₂ * (1 + Cσ * C₁) := le_of_lt (mul_pos hC₂ (by linarith))
  refine ⟨Real.sqrt (Cσ * C₁) + Real.sqrt (C₂ * (1 + Cσ * C₁)),
    lt_of_lt_of_le (Real.sqrt_pos.mpr (mul_pos hCσ hC₁))
      (le_add_of_nonneg_right (Real.sqrt_nonneg _)), ?_⟩
  intro α u G hA
  obtain ⟨hL2D, hL2θ, hineq⟩ := hE' α u G hA
  have hup := hU' α u G hA hL2θ
  obtain ⟨hL2Dρ, hineqD⟩ := hD' α u G hA
  have hG0 : 0 ≤ Work.Spaces.HkSq α 0 G := Work.Spaces.HkSq_nonneg α 0 G
  have hSle : Work.Spaces.L2Sq (fun z θ => Work.Spaces.pth u z θ * Work.Spaces.w z)
      ≤ C₁ * Work.Spaces.HkSq α 0 G := by
    have hA2 : (0 : ℝ) ≤ α ^ 2 * Work.Spaces.L2Sq
        (fun z θ => z * Work.Spaces.pz u z θ * Work.Spaces.w z) :=
      mul_nonneg (sq_nonneg α)
        (integral_nonneg fun z => integral_nonneg fun θ => sq_nonneg _)
    linarith
  have hUu : Work.Spaces.HkSq α 0 u ≤ (Cσ * C₁) * Work.Spaces.HkSq α 0 G := by
    calc Work.Spaces.HkSq α 0 u
        ≤ Cσ * Work.Spaces.L2Sq (fun z θ => Work.Spaces.pth u z θ * Work.Spaces.w z) := hup
      _ ≤ Cσ * (C₁ * Work.Spaces.HkSq α 0 G) := mul_le_mul_of_nonneg_left hSle (le_of_lt hCσ)
      _ = (Cσ * C₁) * Work.Spaces.HkSq α 0 G := by ring
  have hnrmG0 : 0 ≤ Work.FTS.EllipticEst.H2W.Ae.nrm α G := Real.sqrt_nonneg _
  have hG2 : (Work.FTS.EllipticEst.H2W.Ae.nrm α G) ^ 2 = Work.Spaces.HkSq α 0 G :=
    Real.sq_sqrt hG0
  have hu1 : Work.FTS.EllipticEst.H2W.Ae.nrm α u ≤ Real.sqrt (Cσ * C₁)
      * Work.FTS.EllipticEst.H2W.Ae.nrm α G :=
    calc Work.FTS.EllipticEst.H2W.Ae.nrm α u
        = Real.sqrt (Work.Spaces.HkSq α 0 u) := rfl
      _ ≤ Real.sqrt ((Cσ * C₁) * Work.Spaces.HkSq α 0 G) := Real.sqrt_le_sqrt hUu
      _ = Real.sqrt (Cσ * C₁) * Real.sqrt (Work.Spaces.HkSq α 0 G) := Real.sqrt_mul hK1 _
  have hgrad1 : α ^ 2 * Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u)
      ≤ (C₂ * (1 + Cσ * C₁)) * Work.Spaces.HkSq α 0 G := by
    have h2 : Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u
        ≤ Work.Spaces.HkSq α 0 G + (Cσ * C₁) * Work.Spaces.HkSq α 0 G := by linarith
    calc α ^ 2 * Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u)
        ≤ C₂ * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u) := hineqD
      _ ≤ C₂ * (Work.Spaces.HkSq α 0 G + (Cσ * C₁) * Work.Spaces.HkSq α 0 G) :=
          mul_le_mul_of_nonneg_left h2 (le_of_lt hC₂)
      _ = (C₂ * (1 + Cσ * C₁)) * Work.Spaces.HkSq α 0 G := by ring
  have hgrad3 : α * Work.FTS.EllipticEst.H2W.Ae.nrm α (Work.FTS.EllipticEst.H2W.Ae.grad u)
      ≤ Real.sqrt (C₂ * (1 + Cσ * C₁)) * Work.FTS.EllipticEst.H2W.Ae.nrm α G := by
    have hgrad2 : (α * Work.FTS.EllipticEst.H2W.Ae.nrm α
          (Work.FTS.EllipticEst.H2W.Ae.grad u)) ^ 2
        ≤ (Real.sqrt (C₂ * (1 + Cσ * C₁))
            * Work.FTS.EllipticEst.H2W.Ae.nrm α G) ^ 2 := by
      have h3 : (Work.FTS.EllipticEst.H2W.Ae.nrm α
          (Work.FTS.EllipticEst.H2W.Ae.grad u)) ^ 2
          = Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) :=
        Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 0 _)
      rw [mul_pow, mul_pow, h3, Real.sq_sqrt hK2, hG2]
      exact hgrad1
    have hnn : 0 ≤ Real.sqrt (C₂ * (1 + Cσ * C₁)) * Work.FTS.EllipticEst.H2W.Ae.nrm α G :=
      mul_nonneg (Real.sqrt_nonneg _) hnrmG0
    have hα0 : 0 ≤ α := le_of_lt hA.hα
    have hD0 : 0 ≤ Work.FTS.EllipticEst.H2W.Ae.nrm α
        (Work.FTS.EllipticEst.H2W.Ae.grad u) := Real.sqrt_nonneg _
    have h := Real.sqrt_le_sqrt hgrad2
    rw [Real.sqrt_sq (mul_nonneg hα0 hD0), Real.sqrt_sq hnn] at h
    exact h
  refine ⟨Work.FTS.EllipticEst.H2W.Ae.hkMem_u α u G hA, hkMem_gradU' α u G hA, ?_, ?_⟩
  · calc Work.FTS.EllipticEst.H2W.Ae.nrm α u
        ≤ Real.sqrt (Cσ * C₁) * Work.FTS.EllipticEst.H2W.Ae.nrm α G := hu1
      _ ≤ (Real.sqrt (Cσ * C₁) + Real.sqrt (C₂ * (1 + Cσ * C₁)))
            * Work.FTS.EllipticEst.H2W.Ae.nrm α G :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (Real.sqrt_nonneg _)) hnrmG0
  · calc α * Work.FTS.EllipticEst.H2W.Ae.nrm α (Work.FTS.EllipticEst.H2W.Ae.grad u)
        ≤ Real.sqrt (C₂ * (1 + Cσ * C₁)) * Work.FTS.EllipticEst.H2W.Ae.nrm α G := hgrad3
      _ ≤ (Real.sqrt (Cσ * C₁) + Real.sqrt (C₂ * (1 + Cσ * C₁)))
            * Work.FTS.EllipticEst.H2W.Ae.nrm α G :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (Real.sqrt_nonneg _)) hnrmG0

/-- **The level-`0` estimate in the weak class from the three steps** of `prop:H2`. -/
theorem ellWeak0_of_steps (h1 : Work.FTS.EllipticEst.H2W.Ae.Step1)
    (h2 : Work.FTS.EllipticEst.H2W.Ae.Step2) (h3 : Work.FTS.EllipticEst.H2W.Ae.Step3) :
    ∃ C : ℝ, 0 < C ∧ Work.FTS.EllipticEst.TT.EllWeak0 C := by
  obtain ⟨C, hC, hmain⟩ := Work.FTS.EllipticEst.H2W.Ae.level0Ae_of h1 h2 h3
  refine ⟨C, hC, ?_⟩
  intro α F Ψ hα hα4 hW
  exact hmain α Ψ F (aeData_of_ellWeakPos' hα hα4 hW)

/-- **The level-`0` (`η`-weighted) estimate `TT.EllWeak0`** — the paper's `prop:L2` together with
Steps 1--2 of `prop:H2`, assembled from the already proved analytic inputs of the Dispatch route:

* Step 1 (`H2W.Ae.Step1`) from `AeS1.step1_of` with the *proved* unweighted energy inequality
  `AeS1.unwEnergyD`, the `σ`-Poincaré upgrade `aeSigmaUpD` of this file, and the `σ`-weighted
  radial inequality `Dispatch.aeSigmaEnergyD`;
* Step 2 from `Dispatch.step2AeD`;
* Step 3 from `Dispatch.step3AeD`.

The assembly `H2W.Ae.level0Ae_of` (proved, `sorry`-free) turns the three into the estimate for
the a.e. class `AeData`, and `ellWeak0_of_steps` converts that into `TT.EllWeak0` through
`aeData_of_ellWeakPos'`. -/
theorem cores_level_zero : ∃ C : ℝ, 0 < C ∧ Work.FTS.EllipticEst.TT.EllWeak0 C :=
  ellWeak0_of_steps
    (Work.FTS.EllipticEst.AeS1.step1_of Work.FTS.EllipticEst.AeS1.unwEnergyD aeSigmaUpD
      aeSigmaEnergyD)
    step2AeD step3AeD

end Work.FTS.EllipticEst.Dispatch
