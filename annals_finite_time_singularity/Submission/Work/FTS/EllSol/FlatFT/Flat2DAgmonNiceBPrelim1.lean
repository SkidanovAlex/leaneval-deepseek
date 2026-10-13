/-
Copyright: work module for the Elgindi finite-time singularity project.

# Preliminaries for `flat2DAgmonNiceB`, part 1

The general Tonelli/Plancherel identification of the "`ξ`-outer" iterated integral with the
product-measure integral, together with the elementary measure-theory and slice-measurability
tools used by the main file.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.EllSol.FlatFT.Defs
import Submission.Work.FTS.EllSol.FlatFT.slice_hasDerivAt
import Submission.Work.FTS.EllSol.FlatFT.plancherelSlice1
import Submission.Work.FTS.EllSol.FlatFT.plancherelSlice1Deriv
import Submission.Work.FTS.EllSol.FlatFT.plancherelDeriv2
import Submission.Work.FTS.EllSol.FlatFT.dthBound
import Submission.Work.FTS.EllSol.FlatFT.flatNiceSlices
import Submission.Work.FTS.EllSol.FlatFT.niceFlatSliceL2
import Submission.Work.EllipticEst.Core.i0Aux.thetaInterpCore
import Submission.Work.FTS.EllSol.FlatFT.integrable_normSq_slice1
import Submission.Work.FTS.EllSol.FlatFT.aemeasurable_of_continuousOn_strip
import Submission.Work.FTS.EllSol.FlatFT.integrableOn_energy_mul
import Submission.Work.FTS.EllSol.FlatFT.continuousOn_slice_joint

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.FlatFT

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option maxHeartbeats 1000000

/-! ## Elementary facts about the measure on `ℝ × ℝ` and the interval `Iθ` -/

theorem measurableSet_Iθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc

/-- The product measure on `ℝ × ℝ` restricted to `univ ×ˢ Iθ` is the product of Lebesgue
measure with the restriction of Lebesgue measure to `Iθ`. -/
theorem volume_restrict_univ_prod_Iθ :
    ((MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ))).restrict
        (Set.univ ×ˢ Work.Spaces.Iθ)
      = (MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
          ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ) := by
  rw [show (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ))
      = (MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) from rfl,
    ← MeasureTheory.Measure.prod_restrict, MeasureTheory.Measure.restrict_univ]

theorem ae_mem_Iθ :
    ∀ᵐ θ ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ),
      θ ∈ Work.Spaces.Iθ :=
  MeasureTheory.ae_restrict_mem measurableSet_Iθ

/-! ## The general Tonelli/Plancherel identification

Given a "profile" `φ` and the `t`-profile `ψ` that produces the matching `t`-slot, a weight
`W` in `ξ` and a weight `w` in `θ`, the iterated (`ξ`-outer) integral of `W(ξ) · J(ξ)`,
with `J(ξ) = ∫_θ ‖Φ_ξ(θ)‖² w(θ)`, equals the product-measure integral of `ψ(t,θ)² w(θ)`. -/
theorem lintegral_slice_plancherel (φ ψ : ℝ → ℝ → ℝ) (W w : ℝ → ℝ)
    (hWnn : ∀ ξ, 0 ≤ W ξ) (hwnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ w θ)
    (hJint : ∀ ξ, MeasureTheory.IntegrableOn (fun θ : ℝ => ‖slice φ ξ θ‖ ^ 2 * w θ)
      Work.Spaces.Iθ)
    (hφint : ∀ᵐ θ ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ),
      MeasureTheory.Integrable (fun t : ℝ => (ψ t θ) ^ 2))
    (hplanch : ∀ᵐ θ ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ),
      MeasureTheory.Integrable (fun ξ : ℝ => W ξ * ‖slice φ ξ θ‖ ^ 2) ∧
      (∫ ξ : ℝ, W ξ * ‖slice φ ξ θ‖ ^ 2) = ∫ t : ℝ, (ψ t θ) ^ 2)
    (hm1 : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (W p.1) *
        ENNReal.ofReal (‖slice φ p.1 p.2‖ ^ 2 * w p.2))
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
          ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ)))
    (hm2 : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal ((ψ p.1 p.2) ^ 2 * w p.2))
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
          ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ))) :
    (∫⁻ ξ, ENNReal.ofReal (W ξ * ∫ θ in Work.Spaces.Iθ, ‖slice φ ξ θ‖ ^ 2 * w θ))
      = ∫⁻ p in Set.univ ×ˢ Work.Spaces.Iθ,
          ENNReal.ofReal ((ψ p.1 p.2) ^ 2 * w p.2) := by
  have hnn1 : ∀ ξ, 0 ≤ᵐ[((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict
      Work.Spaces.Iθ)] (fun θ : ℝ => ‖slice φ ξ θ‖ ^ 2 * w θ) := fun ξ =>
    ae_mem_Iθ.mono fun θ hθ => mul_nonneg (sq_nonneg _) (hwnn θ hθ)
  have step1 : ∀ ξ, ENNReal.ofReal (W ξ * ∫ θ in Work.Spaces.Iθ, ‖slice φ ξ θ‖ ^ 2 * w θ)
      = ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (W ξ) * ENNReal.ofReal (‖slice φ ξ θ‖ ^ 2 * w θ) := by
    intro ξ
    rw [ENNReal.ofReal_mul (hWnn ξ),
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hJint ξ) (hnn1 ξ),
      ← lintegral_const_mul' (ENNReal.ofReal (W ξ)) _ ENNReal.ofReal_ne_top]
  have step2 : ∀ θ : ℝ, (∫⁻ ξ, ENNReal.ofReal (W ξ) *
        ENNReal.ofReal (‖slice φ ξ θ‖ ^ 2 * w θ))
      = ENNReal.ofReal (w θ) * ∫⁻ ξ, ENNReal.ofReal (W ξ * ‖slice φ ξ θ‖ ^ 2) := by
    intro θ
    have hpt : ∀ ξ : ℝ, ENNReal.ofReal (W ξ) * ENNReal.ofReal (‖slice φ ξ θ‖ ^ 2 * w θ)
        = ENNReal.ofReal (w θ) * ENNReal.ofReal (W ξ * ‖slice φ ξ θ‖ ^ 2) := by
      intro ξ
      rw [ENNReal.ofReal_mul (sq_nonneg (‖slice φ ξ θ‖)), ← mul_assoc,
        ← ENNReal.ofReal_mul (hWnn ξ)]
      exact mul_comm _ _
    rw [lintegral_congr hpt,
      lintegral_const_mul' (ENNReal.ofReal (w θ)) _ ENNReal.ofReal_ne_top]
  have step3 : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (w θ) *
        ∫⁻ ξ, ENNReal.ofReal (W ξ * ‖slice φ ξ θ‖ ^ 2))
      = ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (w θ) * ENNReal.ofReal (∫ t : ℝ, (ψ t θ) ^ 2) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hplanch] with θ hθ
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hθ.1
      (Eventually.of_forall fun ξ => mul_nonneg (hWnn ξ) (sq_nonneg _)), hθ.2]
  have step4 : (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (w θ) * ENNReal.ofReal (∫ t : ℝ, (ψ t θ) ^ 2))
      = ∫⁻ θ in Work.Spaces.Iθ,
          ∫⁻ t, ENNReal.ofReal (w θ) * ENNReal.ofReal ((ψ t θ) ^ 2) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hφint] with θ hθ
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hθ
      (Eventually.of_forall fun t => sq_nonneg _),
      ← lintegral_const_mul' (ENNReal.ofReal (w θ)) _ ENNReal.ofReal_ne_top]
  have step5 : (∫⁻ θ in Work.Spaces.Iθ,
        ∫⁻ t, ENNReal.ofReal (w θ) * ENNReal.ofReal ((ψ t θ) ^ 2))
      = ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ t, ENNReal.ofReal ((ψ t θ) ^ 2 * w θ) := by
    refine lintegral_congr fun θ => lintegral_congr fun t => ?_
    rw [ENNReal.ofReal_mul (sq_nonneg ((ψ t θ) : ℝ)), mul_comm]
  have step6 : (∫⁻ θ in Work.Spaces.Iθ, ∫⁻ t, ENNReal.ofReal ((ψ t θ) ^ 2 * w θ))
      = ∫⁻ p in Set.univ ×ˢ Work.Spaces.Iθ,
          ENNReal.ofReal ((ψ p.1 p.2) ^ 2 * w p.2) := by
    rw [volume_restrict_univ_prod_Iθ]
    exact (MeasureTheory.lintegral_prod_symm
      (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
      (ν := (MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ)
      (fun p : ℝ × ℝ => ENNReal.ofReal ((ψ p.1 p.2) ^ 2 * w p.2)) hm2).symm
  calc (∫⁻ ξ, ENNReal.ofReal (W ξ * ∫ θ in Work.Spaces.Iθ, ‖slice φ ξ θ‖ ^ 2 * w θ))
      = ∫⁻ ξ, ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (W ξ) *
          ENNReal.ofReal (‖slice φ ξ θ‖ ^ 2 * w θ) := lintegral_congr step1
    _ = ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ ξ, ENNReal.ofReal (W ξ) *
          ENNReal.ofReal (‖slice φ ξ θ‖ ^ 2 * w θ) :=
        MeasureTheory.lintegral_lintegral_swap
          (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
          (ν := (MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ) hm1
    _ = ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (w θ) *
          ∫⁻ ξ, ENNReal.ofReal (W ξ * ‖slice φ ξ θ‖ ^ 2) := lintegral_congr step2
    _ = ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (w θ) * ENNReal.ofReal (∫ t : ℝ, (ψ t θ) ^ 2) := step3
    _ = ∫⁻ θ in Work.Spaces.Iθ,
          ∫⁻ t, ENNReal.ofReal (w θ) * ENNReal.ofReal ((ψ t θ) ^ 2) := step4
    _ = ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ t, ENNReal.ofReal ((ψ t θ) ^ 2 * w θ) := step5
    _ = ∫⁻ p in Set.univ ×ˢ Work.Spaces.Iθ,
          ENNReal.ofReal ((ψ p.1 p.2) ^ 2 * w p.2) := step6

/-! ## Angular weights, measurability and slices of `NiceFlat` data -/

/-- The open strip `ℝ × (0,π/2)` on which `NiceFlat` data are smooth. -/
abbrev flStrip : Set (ℝ × ℝ) := Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)

theorem flStrip_isOpen : IsOpen flStrip := isOpen_univ.prod isOpen_Ioo

theorem mem_flStrip {t θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : (t, θ) ∈ flStrip :=
  ⟨trivial, hθ⟩

/-- `∀ᵐ θ ∂(volume.restrict Iθ)`, `θ` lies in the *open* interval. -/
theorem ae_mem_Ioo_Iθ :
    ∀ᵐ θ ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo 0 (Real.pi / 2) := by
  have hcongr : Set.Ioo (0 : ℝ) (Real.pi / 2)
      =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ)] Work.Spaces.Iθ :=
    MeasureTheory.Ioo_ae_eq_Icc
  rw [← MeasureTheory.Measure.restrict_congr_set hcongr]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-- A function vanishing outside the `M`-ball has zero derivative on `{M < |x|}`. -/
theorem deriv_eq_zero_of_lt_abs {f : ℝ → ℝ} {M x : ℝ} (hx : M < |x|)
    (hf : ∀ y : ℝ, M < |y| → f y = 0) : deriv f x = 0 := by
  have hopen : IsOpen {y : ℝ | M < |y|} := isOpen_lt continuous_const continuous_abs
  have hev : f =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [hopen.mem_nhds hx] with y hy
    exact hf y hy
  rw [hev.deriv_eq]
  simp

theorem pz_eq_zero_of_lt_abs {ψ : ℝ → ℝ → ℝ} {θ M t : ℝ} (ht : M < |t|)
    (hψ : ∀ y : ℝ, M < |y| → ψ y θ = 0) : Work.Spaces.pz ψ t θ = 0 :=
  deriv_eq_zero_of_lt_abs ht fun y hy => hψ y hy

theorem measurable_wE : Measurable wE := by
  unfold wE
  exact (Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow measurable_const

theorem measurable_wA (α : ℝ) : Measurable (wA α) := by
  unfold wA
  exact (Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow measurable_const

theorem aemeasurable_wE_snd :
    AEMeasurable (fun p : ℝ × ℝ => wE p.2)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ)) :=
  (measurable_wE.comp measurable_snd).aemeasurable

theorem aemeasurable_wA_snd (α : ℝ) :
    AEMeasurable (fun p : ℝ × ℝ => wA α p.2)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ)) :=
  ((measurable_wA α).comp measurable_snd).aemeasurable

/-- `AEMeasurable` for a function continuous on the open interval, with respect to the measure
`volume` restricted to the closed `Iθ`. -/
theorem aemeasurable_Iθ_of_continuousOn_Ioo {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ioo 0 (Real.pi / 2))) :
    AEMeasurable f ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ) := by
  have h : AEMeasurable f
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Ioo 0 (Real.pi / 2))) :=
    hf.aemeasurable measurableSet_Ioo
  have hcongr : Set.Ioo (0 : ℝ) (Real.pi / 2)
      =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ)] Work.Spaces.Iθ :=
    MeasureTheory.Ioo_ae_eq_Icc
  rwa [MeasureTheory.Measure.restrict_congr_set hcongr] at h

/-- The `t`-slice of a function continuous on the strip is continuous. -/
theorem continuous_slice_of_continuousOn_strip {ψ : ℝ → ℝ → ℝ}
    (hψ : ContinuousOn (Function.uncurry ψ) flStrip) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Continuous fun t : ℝ => ψ t θ := by
  simpa [Function.comp_def, Function.uncurry] using
    hψ.comp_continuous (continuous_id.prodMk continuous_const) fun t => mem_flStrip hθ

/-- The `t`-slice of a function with uniformly compact `t`-support has compact support. -/
theorem slice_hasCompactSupport {ψ : ℝ → ℝ → ℝ} {M : ℝ} (_hM : 0 ≤ M)
    (hsupp : ∀ t θ : ℝ, M < |t| → ψ t θ = 0) (θ : ℝ) :
    HasCompactSupport fun t : ℝ => ψ t θ :=
  HasCompactSupport.intro (K := Set.Icc (-M) M) isCompact_Icc fun t ht => by
    have ht' : M < |t| := not_le.mp fun hle => ht (abs_le.mp hle)
    rw [hsupp t θ ht']

/-- The complex version, for the `t`-Fourier slice kernels. -/
theorem slice_hasCompactSupport_ofReal {ψ : ℝ → ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hsupp : ∀ t θ : ℝ, M < |t| → ψ t θ = 0) (θ : ℝ) :
    HasCompactSupport fun t : ℝ => (ψ t θ : ℂ) :=
  (slice_hasCompactSupport hM hsupp θ).comp_left Complex.ofReal_zero

/-- `t ↦ f(t)²` is integrable for `f` continuous with compact support. -/
theorem integrable_sq_of_continuous_hasCompactSupport {f : ℝ → ℝ} (hf : Continuous f)
    (hs : HasCompactSupport f) : MeasureTheory.Integrable fun t : ℝ => f t ^ 2 := by
  have hsupp : HasCompactSupport (fun t : ℝ => f t ^ 2) :=
    hs.comp_left (g := fun x : ℝ => x ^ 2) (by norm_num)
  exact (hf.pow 2).integrable_of_hasCompactSupport hsupp

/-- For `ψ` continuous on the strip with uniformly compact `t`-support, the `t`-slice of `ψ²`
is integrable. -/
theorem integrable_sq_slice {ψ : ℝ → ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hcont : ContinuousOn (Function.uncurry ψ) flStrip)
    (hsupp : ∀ t θ : ℝ, M < |t| → ψ t θ = 0) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    MeasureTheory.Integrable fun t : ℝ => (ψ t θ) ^ 2 :=
  integrable_sq_of_continuous_hasCompactSupport
    (continuous_slice_of_continuousOn_strip hcont hθ) (slice_hasCompactSupport hM hsupp θ)

/-- Joint measurability of `(t,θ) ↦ ψ(t,θ)² w(θ)`, as an `ℝ≥0∞`-valued function. -/
theorem aemeasurable_ofReal_sq_mul_snd {ψ : ℝ → ℝ → ℝ} {w : ℝ → ℝ}
    (hψ : ContinuousOn (Function.uncurry ψ) flStrip) (hw : Measurable w) :
    AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal ((ψ p.1 p.2) ^ 2 * w p.2))
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ)) := by
  have h1 : AEMeasurable (fun p : ℝ × ℝ => ψ p.1 p.2)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ)) :=
    aemeasurable_of_continuousOn_strip hψ
  have h2 : AEMeasurable (fun p : ℝ × ℝ => (ψ p.1 p.2) ^ 2)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ)) :=
    h1.pow_const 2
  have h3 : AEMeasurable (fun p : ℝ × ℝ => w p.2)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ)) :=
    (hw.comp measurable_snd).aemeasurable
  exact ENNReal.measurable_ofReal.comp_aemeasurable (h2.mul h3)

/-- Joint measurability of `(ξ,θ) ↦ ofReal(W(ξ)) · ofReal(‖Φ_ξ(θ)‖² w(θ))`. -/
theorem aemeasurable_ofReal_weight_mul {ψ : ℝ → ℝ → ℝ} {W w : ℝ → ℝ}
    (hsl : ContinuousOn (fun p : ℝ × ℝ => slice ψ p.1 p.2) flStrip)
    (hW : Measurable W) (hw : Measurable w) :
    AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (W p.1) *
        ENNReal.ofReal (‖slice ψ p.1 p.2‖ ^ 2 * w p.2))
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ)) := by
  have hslice : AEMeasurable (fun p : ℝ × ℝ => ‖slice ψ p.1 p.2‖ ^ 2)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ)) :=
    ((aemeasurable_of_continuousOn_strip
      (F := fun p : ℝ × ℝ => ‖slice ψ p.1 p.2‖) hsl.norm)).pow_const 2
  have hWs : AEMeasurable (fun p : ℝ × ℝ => W p.1)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ)) :=
    (hW.comp measurable_fst).aemeasurable
  have hws : AEMeasurable (fun p : ℝ × ℝ => w p.2)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ)) :=
    (hw.comp measurable_snd).aemeasurable
  exact (ENNReal.measurable_ofReal.comp_aemeasurable hWs).mul
    (ENNReal.measurable_ofReal.comp_aemeasurable (hslice.mul hws))

end

end Work.FTS.EllSol.FlatFT
