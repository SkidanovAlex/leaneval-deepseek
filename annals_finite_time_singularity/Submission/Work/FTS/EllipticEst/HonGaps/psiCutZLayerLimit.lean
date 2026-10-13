/-
Work module for the Elgindi finite-time singularity project.

# The `z`-integral of the two angular layers of the cut-off vanishes

This file proves `Work.FTS.EllipticEst.HonGaps.psiCutZLayerLimit`: for a jointly measurable
`g(z,θ) = σ(θ)·F(z,θ)²` (with `σ = sigS θ = sin(2θ)^{-η} ≥ 0` on `Iθ`), whose `z`-slices are
integrable on `Iθ` for a.e. `z` and whose weighted `z`-integral

  `z ↦ χ(z)² w(z)² ∫_θ σ(θ) F(z,θ)²`

is integrable on `(0,∞)`, the `z`-integral of `χ²w²` times the *mass of `σF²` on the two angular
layers* `(0, 2ε)` and `(π/2 - 2ε, π/2)` tends to `0` as `ε → 0⁺`.

This is the `z`-level counterpart of `psiCutThetaLayerLimit` and is used in the proof of
`mixedInterp` (`HonGaps/truncChain`), where the angular cut-off `ψ_ε` of the `(D_z∂_θΨ)²` term is
removed: the layer pieces are exactly the parts of `Iθ` outside the support of `ψ_ε`.

The proof is dominated convergence in `z` with respect to `μ = volume.restrict (Ioi 0)`:
* domination: on the a.e. set where the `θ`-slice is integrable, both layer masses are `≥ 0` and
  `≤ ∫_θ σF²` (monotonicity of the set integral for a nonnegative integrand), so
  `‖χ²w²·(L_lo + L_hi)‖ ≤ 2‖χ²w² ∫_θ σF²‖`, and the latter is integrable by hypothesis;
* pointwise convergence for a.e. `z`: each layer mass is a set integral of the fixed integrable
  function `θ ↦ σ(θ)F(z,θ)²` over a set whose `Iθ`-measure tends to `0`
  (`Integrable.tendsto_setIntegral_nhds_zero`);
* a.e. strong measurability: `z ↦ ∫_θ (layer).indicator (g z)` is obtained from the joint
  measurability hypothesis via `AEStronglyMeasurable.integral_prod_right'` (Fubini), after
  identifying the product of the two restricted measures with `volume.restrict (Ioi 0 ×ˢ Iθ)`.
-/

import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.HonGaps.mixedInterpDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.EllipticEst.HonGaps

set_option linter.unusedSimpArgs false

/-! ## Elementary facts about the weight `σ = sigS` and the interval `Iθ` -/

/-- `σ θ = sin(2θ)^{-η}` is nonnegative on `Iθ = [0, π/2]`. -/
theorem sigS_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ sigS θ := by
  rw [sigS]
  exact Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2]⟩) _

/-- The radial weight `w(z) = (1+z)²/z²` is measurable. -/
theorem measurable_w : Measurable Work.Spaces.w := by
  have h : Work.Spaces.w = fun z : ℝ => (1 + z) ^ 2 / z ^ 2 := rfl
  rw [h]
  exact ((measurable_const.add measurable_id).pow_const 2).div (measurable_id.pow_const 2)

/-- `Iθ = [0, π/2]` is measurable. -/
theorem measurableSet_Iθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc

/-! ## The two angular layers and their measures -/

/-- The lower angular layer `(0, min (2ε) (π/2))`. -/
def layLo (ε : ℝ) : Set ℝ := Set.Ioo 0 (min (2 * ε) (Real.pi / 2))

/-- The upper angular layer `(max (π/2 - 2ε) 0, π/2)`. -/
def layHi (ε : ℝ) : Set ℝ := Set.Ioo (max (Real.pi / 2 - 2 * ε) 0) (Real.pi / 2)

theorem measurableSet_layLo (ε : ℝ) : MeasurableSet (layLo ε) := measurableSet_Ioo

theorem measurableSet_layHi (ε : ℝ) : MeasurableSet (layHi ε) := measurableSet_Ioo

theorem layLo_subset_Iθ (ε : ℝ) : layLo ε ⊆ Work.Spaces.Iθ := by
  intro θ hθ
  exact ⟨le_of_lt hθ.1, le_trans (le_of_lt hθ.2) (min_le_right _ _)⟩

theorem layHi_subset_Iθ (ε : ℝ) : layHi ε ⊆ Work.Spaces.Iθ := by
  intro θ hθ
  exact ⟨le_trans (le_max_right _ _) (le_of_lt hθ.1), le_of_lt hθ.2⟩

/-- The `Iθ`-measure of the lower layer tends to `0` as `ε → 0⁺`. -/
theorem tendsto_measure_layLo :
    Tendsto (fun ε : ℝ => (volume.restrict Work.Spaces.Iθ) (layLo ε))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hl : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds (0 : ℝ) := nhdsWithin_le_nhds
  have hlt : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), ε < Real.pi / 4 :=
    hl (Iio_mem_nhds (by linarith [Real.pi_pos]))
  have hev : (fun ε : ℝ => ENNReal.ofReal (2 * ε))
      =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
      (fun ε : ℝ => (volume.restrict Work.Spaces.Iθ) (layLo ε)) := by
    filter_upwards [hlt] with ε hε
    rw [layLo, Measure.restrict_apply measurableSet_Ioo, min_eq_left (by linarith)]
    rw [Set.inter_eq_self_of_subset_left (show Set.Ioo 0 (2 * ε) ⊆ Work.Spaces.Iθ from
      fun θ hθ => ⟨le_of_lt hθ.1, le_trans (le_of_lt hθ.2) (by linarith [hε, Real.pi_pos])⟩)]
    rw [Real.volume_Ioo, sub_zero]
  have h2 : Tendsto (fun ε : ℝ => ENNReal.ofReal (2 * ε))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have h : Tendsto (fun ε : ℝ => 2 * ε) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      simpa using tendsto_const_nhds.mul (tendsto_id.mono_left hl)
    have h' : Tendsto (fun ε : ℝ => ENNReal.ofReal (2 * ε))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (ENNReal.ofReal 0)) :=
      (ENNReal.continuous_ofReal.tendsto 0).comp h
    simpa using h'
  exact Tendsto.congr' hev h2

/-- The `Iθ`-measure of the upper layer tends to `0` as `ε → 0⁺`. -/
theorem tendsto_measure_layHi :
    Tendsto (fun ε : ℝ => (volume.restrict Work.Spaces.Iθ) (layHi ε))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hl : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds (0 : ℝ) := nhdsWithin_le_nhds
  have hlt : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), ε < Real.pi / 4 :=
    hl (Iio_mem_nhds (by linarith [Real.pi_pos]))
  have hev : (fun ε : ℝ => ENNReal.ofReal (2 * ε))
      =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
      (fun ε : ℝ => (volume.restrict Work.Spaces.Iθ) (layHi ε)) := by
    filter_upwards [hlt] with ε hε
    have hmax : max (Real.pi / 2 - 2 * ε) 0 = Real.pi / 2 - 2 * ε := max_eq_left (by linarith)
    rw [layHi, Measure.restrict_apply measurableSet_Ioo, hmax]
    rw [Set.inter_eq_self_of_subset_left (show Set.Ioo (Real.pi / 2 - 2 * ε) (Real.pi / 2) ⊆
        Work.Spaces.Iθ from fun θ hθ => ⟨by linarith [hθ.1, hε], le_of_lt hθ.2⟩)]
    rw [Real.volume_Ioo, show Real.pi / 2 - (Real.pi / 2 - 2 * ε) = 2 * ε from by ring]
  have h2 : Tendsto (fun ε : ℝ => ENNReal.ofReal (2 * ε))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have h : Tendsto (fun ε : ℝ => 2 * ε) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      simpa using tendsto_const_nhds.mul (tendsto_id.mono_left hl)
    have h' : Tendsto (fun ε : ℝ => ENNReal.ofReal (2 * ε))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (ENNReal.ofReal 0)) :=
      (ENNReal.continuous_ofReal.tendsto 0).comp h
    simpa using h'
  exact Tendsto.congr' hev h2

/-! ## The general layer limit

The statement below is the general form of the target: `g` is an angular integrand on `Iθ`,
nonnegative on `Iθ`, with jointly measurable uncurried form, a.e. integrable `θ`-slices and
square-weighted `z`-integral (the `χ²w²`-weighted mass of `g` on `Iθ`) integrable on `(0,∞)`. -/
theorem zLayerLimit_of_joint {g : ℝ → ℝ → ℝ} {χ : ℝ → ℝ} (hχ : Measurable χ)
    (hjoint : AEStronglyMeasurable (fun p : ℝ × ℝ => g p.1 p.2)
      (volume.restrict (Set.Ioi 0 ×ˢ Work.Spaces.Iθ)))
    (hgz : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)), IntegrableOn (g z) Work.Spaces.Iθ)
    (hint : IntegrableOn (fun z : ℝ => (χ z) ^ 2 * (Work.Spaces.w z) ^ 2 *
      ∫ θ in Work.Spaces.Iθ, g z θ) (Set.Ioi 0))
    (hnn : ∀ z θ, θ ∈ Work.Spaces.Iθ → 0 ≤ g z θ) :
    Tendsto (fun ε : ℝ => ∫ z in Set.Ioi 0, (χ z) ^ 2 * (Work.Spaces.w z) ^ 2 *
        ((∫ θ in layLo ε, g z θ) + (∫ θ in layHi ε, g z θ)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  set l : Filter ℝ := nhdsWithin (0 : ℝ) (Set.Ioi 0) with hl
  set μ : Measure ℝ := volume.restrict (Set.Ioi 0) with hμ
  set ν : Measure ℝ := volume.restrict Work.Spaces.Iθ with hν
  have hνrestr : ν.restrict Work.Spaces.Iθ = ν := by
    rw [hν, Measure.restrict_restrict_of_subset (le_refl Work.Spaces.Iθ)]
  set P : ℝ → ℝ → ℝ := fun ε z => (χ z) ^ 2 * (Work.Spaces.w z) ^ 2 *
    ((∫ θ, (layLo ε).indicator (g z) θ ∂ν) + (∫ θ, (layHi ε).indicator (g z) θ ∂ν)) with hP
  set Bd : ℝ → ℝ := fun z => 2 * ‖(χ z) ^ 2 * (Work.Spaces.w z) ^ 2 *
    (∫ θ, g z θ ∂ν)‖ with hBd
  -- joint measurability with respect to the product of the two restricted measures
  have hjoint' : AEStronglyMeasurable (fun p : ℝ × ℝ => g p.1 p.2) (μ.prod ν) := by
    rw [hμ, hν, Measure.prod_restrict]
    exact hjoint
  -- (1) a.e. strong measurability of the integrands
  have hmeas : ∀ᶠ ε in l, AEStronglyMeasurable (P ε) μ := by
    refine Filter.Eventually.of_forall fun ε => ?_
    have key : ∀ A : Set ℝ, MeasurableSet A →
        AEStronglyMeasurable (fun z : ℝ => ∫ θ, A.indicator (g z) θ ∂ν) μ := by
      intro A hA
      have hset : MeasurableSet {p : ℝ × ℝ | p.2 ∈ A} := hA.preimage measurable_snd
      have h1 : AEStronglyMeasurable ({p : ℝ × ℝ | p.2 ∈ A}.indicator
          (fun p : ℝ × ℝ => g p.1 p.2)) (μ.prod ν) := hjoint'.indicator hset
      refine (h1.integral_prod_right').congr ?_
      filter_upwards with z
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Iθ
      intro y _
      beta_reduce
      by_cases hy : y ∈ A
      · rw [Set.indicator_of_mem (show (z, y) ∈ {p : ℝ × ℝ | p.2 ∈ A} from hy)
            (fun p => g p.1 p.2), Set.indicator_of_mem hy (g z)]
      · rw [Set.indicator_of_notMem (show (z, y) ∉ {p : ℝ × ℝ | p.2 ∈ A} from hy)
            (fun p => g p.1 p.2), Set.indicator_of_notMem hy (g z)]
    have hχ2 : AEStronglyMeasurable (fun z : ℝ => (χ z) ^ 2) μ :=
      (hχ.pow_const 2).aestronglyMeasurable
    have hw2 : AEStronglyMeasurable (fun z : ℝ => (Work.Spaces.w z) ^ 2) μ :=
      (measurable_w.pow_const 2).aestronglyMeasurable
    have hsum : AEStronglyMeasurable (fun z : ℝ =>
        (∫ θ, (layLo ε).indicator (g z) θ ∂ν) + (∫ θ, (layHi ε).indicator (g z) θ ∂ν)) μ :=
      (key (layLo ε) (measurableSet_layLo ε)).add (key (layHi ε) (measurableSet_layHi ε))
    have hfin := (hχ2.mul hw2).mul hsum
    simp only [hP]
    exact hfin
  -- (2) domination by the weighted full `θ`-integral
  have hbound : ∀ᶠ ε in l, ∀ᵐ z ∂μ, ‖P ε z‖ ≤ Bd z := by
    refine Filter.Eventually.of_forall fun ε => ?_
    filter_upwards [hgz] with z hz
    have hzν : Integrable (g z) ν := hz
    have hgnn : 0 ≤ᵐ[ν] (g z) := by
      filter_upwards [MeasureTheory.ae_restrict_mem (s := Work.Spaces.Iθ) measurableSet_Iθ]
        with θ hθ
      exact hnn z θ hθ
    have hI_nn : 0 ≤ ∫ θ, g z θ ∂ν := MeasureTheory.integral_nonneg_of_ae hgnn
    have hL1_nn : 0 ≤ ∫ θ, (layLo ε).indicator (g z) θ ∂ν :=
      MeasureTheory.integral_nonneg fun θ => by
        by_cases h : θ ∈ layLo ε
        · rw [Set.indicator_of_mem h]; exact hnn z θ (layLo_subset_Iθ ε h)
        · rw [Set.indicator_of_notMem h]; simp
    have hL2_nn : 0 ≤ ∫ θ, (layHi ε).indicator (g z) θ ∂ν :=
      MeasureTheory.integral_nonneg fun θ => by
        by_cases h : θ ∈ layHi ε
        · rw [Set.indicator_of_mem h]; exact hnn z θ (layHi_subset_Iθ ε h)
        · rw [Set.indicator_of_notMem h]; simp
    have hz' : IntegrableOn (g z) Work.Spaces.Iθ ν := by
      show Integrable (g z) (ν.restrict Work.Spaces.Iθ)
      rw [hνrestr]
      exact hzν
    have hL1_le : (∫ θ, (layLo ε).indicator (g z) θ ∂ν) ≤ ∫ θ, g z θ ∂ν := by
      rw [MeasureTheory.integral_indicator (measurableSet_layLo ε)]
      have h := MeasureTheory.setIntegral_mono_set (μ := ν) (f := g z) (s := layLo ε)
        (t := Work.Spaces.Iθ) hz' (by rw [hνrestr]; exact hgnn)
        (Filter.Eventually.of_forall fun θ hθ => layLo_subset_Iθ ε hθ)
      rwa [hνrestr] at h
    have hL2_le : (∫ θ, (layHi ε).indicator (g z) θ ∂ν) ≤ ∫ θ, g z θ ∂ν := by
      rw [MeasureTheory.integral_indicator (measurableSet_layHi ε)]
      have h := MeasureTheory.setIntegral_mono_set (μ := ν) (f := g z) (s := layHi ε)
        (t := Work.Spaces.Iθ) hz' (by rw [hνrestr]; exact hgnn)
        (Filter.Eventually.of_forall fun θ hθ => layHi_subset_Iθ ε hθ)
      rwa [hνrestr] at h
    have hsum_le : (∫ θ, (layLo ε).indicator (g z) θ ∂ν) + (∫ θ, (layHi ε).indicator (g z) θ ∂ν)
        ≤ 2 * (∫ θ, g z θ ∂ν) := by linarith
    have hc : 0 ≤ (χ z) ^ 2 * (Work.Spaces.w z) ^ 2 := by positivity
    simp only [hBd, hP]
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hc (add_nonneg hL1_nn hL2_nn)),
      abs_of_nonneg (mul_nonneg hc hI_nn)]
    calc (χ z) ^ 2 * (Work.Spaces.w z) ^ 2 * ((∫ θ, (layLo ε).indicator (g z) θ ∂ν) +
          (∫ θ, (layHi ε).indicator (g z) θ ∂ν))
        ≤ (χ z) ^ 2 * (Work.Spaces.w z) ^ 2 * (2 * (∫ θ, g z θ ∂ν)) :=
          mul_le_mul_of_nonneg_left hsum_le hc
      _ = 2 * ((χ z) ^ 2 * (Work.Spaces.w z) ^ 2 * (∫ θ, g z θ ∂ν)) := by ring
  -- (3) pointwise convergence for a.e. `z`
  have hlim : ∀ᵐ z ∂μ, Tendsto (fun ε : ℝ => P ε z) l (nhds 0) := by
    filter_upwards [hgz] with z hz
    have hzν : Integrable (g z) ν := hz
    have h1 : Tendsto (fun ε : ℝ => ∫ θ, (layLo ε).indicator (g z) θ ∂ν) l (nhds 0) :=
      Tendsto.congr' (Filter.Eventually.of_forall fun ε =>
          (MeasureTheory.integral_indicator (measurableSet_layLo ε) (f := g z) (μ := ν)).symm)
        (hzν.tendsto_setIntegral_nhds_zero (l := l) (s := layLo) tendsto_measure_layLo)
    have h2 : Tendsto (fun ε : ℝ => ∫ θ, (layHi ε).indicator (g z) θ ∂ν) l (nhds 0) :=
      Tendsto.congr' (Filter.Eventually.of_forall fun ε =>
          (MeasureTheory.integral_indicator (measurableSet_layHi ε) (f := g z) (μ := ν)).symm)
        (hzν.tendsto_setIntegral_nhds_zero (l := l) (s := layHi) tendsto_measure_layHi)
    have h3 : Tendsto (fun ε : ℝ => (∫ θ, (layLo ε).indicator (g z) θ ∂ν) +
        (∫ θ, (layHi ε).indicator (g z) θ ∂ν)) l (nhds 0) := by
      simpa using h1.add h2
    have hc : Tendsto (fun _ : ℝ => (χ z) ^ 2 * (Work.Spaces.w z) ^ 2) l
        (nhds ((χ z) ^ 2 * (Work.Spaces.w z) ^ 2)) := tendsto_const_nhds
    have h4 := hc.mul h3
    simp only [hP]
    simpa using h4
  -- (4) the dominating function is integrable
  have hboundint : Integrable Bd μ := by
    rw [hBd]
    exact hint.norm.const_mul 2
  have hmain := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := μ) (l := l) (F := P) (f := fun _ : ℝ => (0 : ℝ)) Bd hmeas hbound hboundint hlim
  have hmain' : Tendsto (fun ε : ℝ => ∫ z, P ε z ∂μ) l (nhds 0) := by
    simpa using hmain
  refine Tendsto.congr' ?_ hmain'
  refine Filter.Eventually.of_forall fun ε => ?_
  rw [hμ]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with z
  have hconv : ∀ (A : Set ℝ), MeasurableSet A → A ⊆ Work.Spaces.Iθ →
      (∫ θ, A.indicator (g z) θ ∂ν) = ∫ θ in A, g z θ := by
    intro A hAmeas hA
    rw [MeasureTheory.integral_indicator hAmeas]
    rw [hν, Measure.restrict_restrict_of_subset hA]
  simp only [hP]
  rw [hconv (layLo ε) (measurableSet_layLo ε) (layLo_subset_Iθ ε),
    hconv (layHi ε) (measurableSet_layHi ε) (layHi_subset_Iθ ε)]

/-! ## The requested lemma -/

theorem psiCutZLayerLimit {F : ℝ → ℝ → ℝ} {χ : ℝ → ℝ} (hχ : Measurable χ)
    (hjoint : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.FTS.EllipticEst.HonGaps.sigS p.2 * (F p.1 p.2) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi 0 ×ˢ Work.Spaces.Iθ)))
    (hFz : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn (fun θ : ℝ => Work.FTS.EllipticEst.HonGaps.sigS θ * (F z θ) ^ 2) Work.Spaces.Iθ)
    (hint : MeasureTheory.IntegrableOn (fun z : ℝ => (χ z) ^ 2 * (Work.Spaces.w z) ^ 2 *
      ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.HonGaps.sigS θ * (F z θ) ^ 2) (Set.Ioi 0)) :
    Filter.Tendsto
      (fun ε : ℝ => ∫ z in Set.Ioi 0, (χ z) ^ 2 * (Work.Spaces.w z) ^ 2 *
        ((∫ θ in Set.Ioo (0 : ℝ) (min (2 * ε) (Real.pi / 2)), Work.FTS.EllipticEst.HonGaps.sigS θ * (F z θ) ^ 2)
          + (∫ θ in Set.Ioo (max (Real.pi / 2 - 2 * ε) 0) (Real.pi / 2),
              Work.FTS.EllipticEst.HonGaps.sigS θ * (F z θ) ^ 2)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  exact zLayerLimit_of_joint (g := fun z θ => sigS θ * (F z θ) ^ 2) hχ hjoint hFz hint
    (fun z θ hθ => mul_nonneg (sigS_nonneg_of_mem_Iθ hθ) (sq_nonneg _))

end Work.FTS.EllipticEst.HonGaps
