import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.DzAmgm.SliceTaylorIdentity
import Submission.Work.FTS.EllipticEst.DzAmgm.OfRealIntervalIntegralSqLe
import Submission.Work.FTS.EllipticEst.Blocks.PzIterTwoContinuousOn
import Submission.Work.FTS.EllipticEst.Blocks.SliceSwapLintegral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Blocks

set_option maxHeartbeats 800000

/-! ## Measurability of the second `z`-partial and of the `θ`-slice of `V`

The ingredients of the proof that have nothing to do with the Taylor identity itself: a.e. strong
measurability of the `t`-slice of `∂_z²V` (from joint continuity of `∂_z²V` on the open
quadrant, `Work.FTS.EllipticEst.Blocks.PzIterTwoContinuousOn`) and a.e. measurability of the
`θ`-slice of `V`.
-/

/-- The `t`-slice `t ↦ ∂_z²V (z₀+t) θ` (for an interior angle `θ`) is a.e. strongly measurable
on `(0,δ]`: it is continuous there, being the composition of the jointly continuous
`(z,θ) ↦ ∂_z²V z θ` on the quadrant with the continuous map `t ↦ (z₀+t, θ)`, whose image of
`(0,δ]` lies in the quadrant because `z₀ > 0` and `θ ∈ (0,π/2)`. -/
private lemma aesm_timeSlice_pzIter2 (V : ℝ → ℝ → ℝ)
    (hV : ContDiffOn ℝ 2 (Function.uncurry V) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {z₀ δ θ : ℝ} (hz₀ : 0 < z₀) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    MeasureTheory.AEStronglyMeasurable (fun t => Work.Spaces.pzIter 2 V (z₀ + t) θ)
      (MeasureTheory.volume.restrict (Set.Ioc 0 δ)) := by
  have hmap : ContinuousOn (fun t : ℝ => (z₀ + t, θ)) (Set.Ioc 0 δ) :=
    (by fun_prop : Continuous fun t : ℝ => (z₀ + t, θ)).continuousOn
  have hc : ContinuousOn (fun t : ℝ => Work.Spaces.pzIter 2 V (z₀ + t) θ) (Set.Ioc 0 δ) := by
    have hcomp := (PzIterTwoContinuousOn (isOpen_Ioi.prod isOpen_Ioo) hV).comp hmap
      (fun t ht => by
        simp only [Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
        exact ⟨by linarith [ht.1, hz₀], hθ⟩)
    have hfun : (Function.uncurry (Work.Spaces.pzIter 2 V) ∘ fun t : ℝ => (z₀ + t, θ))
        = fun t : ℝ => Work.Spaces.pzIter 2 V (z₀ + t) θ := by
      funext t; rfl
    rwa [hfun] at hcomp
  exact hc.aestronglyMeasurable measurableSet_Ioc

/-- The `θ`-slice `θ ↦ ofReal ((V z θ · wth θ)²)` is a.e. measurable on `(0,π/2)`: the slice
`θ ↦ V z θ` is continuous there (as `z > 0`), `wth` is measurable, and `ofReal` and squaring
are measurable. -/
private lemma aemeasurable_slice_V_sq (V : ℝ → ℝ → ℝ) (wth : ℝ → ℝ) (hwthmeas : Measurable wth)
    (hV : ContDiffOn ℝ 2 (Function.uncurry V) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {z : ℝ} (hz : 0 < z) :
    AEMeasurable (fun θ => ENNReal.ofReal ((V z θ * wth θ) ^ 2))
      (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) := by
  have hcomp := hV.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
    (fun θ hθ => ⟨hz, hθ⟩)
  have hcont : ContinuousOn (fun θ : ℝ => V z θ) (Set.Ioo 0 (Real.pi / 2)) := hcomp
  have h1 : AEMeasurable (fun θ : ℝ => V z θ)
      (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
    (hcont.aestronglyMeasurable measurableSet_Ioo).aemeasurable
  have h2 : AEMeasurable wth (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
    hwthmeas.aemeasurable
  have h3 : AEMeasurable (fun θ : ℝ => V z θ * wth θ)
      (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) := h1.mul h2
  have h4 : AEMeasurable (fun θ : ℝ => (V z θ * wth θ) * (V z θ * wth θ))
      (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) := h3.mul h3
  exact ENNReal.measurable_ofReal.comp_aemeasurable (by simpa only [pow_two] using h4)

/-- **Finiteness of the `∂_z`-slice from finiteness of the slice and its second derivative.**

Let `V : ℝ → ℝ → ℝ` be `C²` on the open quadrant `(0,∞) × (0,π/2)` and let `wth : ℝ → ℝ` be
measurable, nonnegative.  Assume

* for every `z > 0`, `∫⁻_{θ ∈ (0,π/2)} ofReal ((V z θ · wth θ)²) < ∞`;
* for every `z > 0` there is `δ > 0` with
  `∫⁻_{z' ∈ (z, z+δ)} ( ∫⁻_{θ ∈ (0,π/2)} ofReal ((∂_z²V (z',θ) · wth θ)²) ) < ∞`.

Then for every `z₀ > 0`, `∫⁻_{θ ∈ (0,π/2)} ofReal ((∂_zV (z₀,θ) · wth θ)²) < ∞`.

(This is the statement of `Submission.Work.FTS.EllipticEst.DzAmgm.SliceDerivLtTop`, currently
`sorry` there; a copy is needed here since that file cannot be edited.)

ROUTE.  Fix `z₀ > 0` and `δ > 0` as in the second hypothesis.  For every `θ ∈ (0,π/2)` the
one-variable Taylor formula with integral remainder applied to the `C²` slice `z ↦ V z θ`
between `z₀` and `z₀+δ` gives

  `V (z₀+δ) θ - V z₀ θ = δ · ∂_zV z₀ θ + ∫_0^δ (δ-t) ∂_z²V (z₀+t) θ dt`,

hence `∂_zV z₀ θ = (1/δ)(V (z₀+δ) θ - V z₀ θ - F θ)` with
`F θ = ∫_0^δ (δ-t) ∂_z²V (z₀+t) θ dt`, and `(a+b+c)² ≤ 3(a²+b²+c²)` reduces the claim to the
finiteness of `∫⁻_θ ofReal ((F θ · wth θ)²)`.  The weighted Cauchy–Schwarz inequality
`F θ² ≤ (δ²/2) ∫_0^δ (δ-t) (∂_z²V (z₀+t) θ)² dt` followed by Tonelli (pull the `t`-integral out
of the `θ`-`lintegral`) bounds this by
`ofReal (δ³/2) ∫⁻_{z' ∈ (z₀, z₀+δ)} ( ∫⁻_θ ofReal ((∂_z²V (z',θ) · wth θ)²) )`,
which is finite by the second hypothesis at `z = z₀`.  Measurability: `V` is continuous on the
open quadrant, so its uncurried form is a.e. strongly measurable for the product measure
(`Work.Spaces.aesm_of_continuousOn_Qd`); `wth` is measurable; slices of a.e. strongly
measurable functions are a.e. strongly measurable.  The `θ`-endpoints `0, π/2` are null and
irrelevant.  No integrability of `∂_zV` and no smoothness beyond `C²` of the uncurried `V` are
assumed. -/
theorem SliceZDeriv_finite (V : ℝ → ℝ → ℝ) (wth : ℝ → ℝ) (hwth : ∀ θ, 0 ≤ wth θ)
    (hwthmeas : Measurable wth)
    (hsm : ContDiffOn ℝ 2 (Function.uncurry V) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hG : ∀ z ∈ Set.Ioi (0 : ℝ),
      MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)))
        (fun θ => ENNReal.ofReal ((V z θ * wth θ) ^ 2)) < ⊤)
    (hB : ∀ z ∈ Set.Ioi (0 : ℝ), ∃ δ : ℝ, 0 < δ ∧
      MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioo z (z + δ)))
        (fun z' => MeasureTheory.lintegral
          (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)))
          (fun θ => ENNReal.ofReal ((Work.Spaces.pzIter 2 V z' θ * wth θ) ^ 2))) < ⊤)
    {z₀ : ℝ} (hz₀ : 0 < z₀) :
    MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)))
      (fun θ => ENNReal.ofReal ((Work.Spaces.pz V z₀ θ * wth θ) ^ 2)) < ⊤ := by
  obtain ⟨δ, hδpos, hBfin⟩ := hB z₀ hz₀
  have hδnn : (0 : ℝ) ≤ δ := le_of_lt hδpos
  set c3 : ℝ≥0∞ := ENNReal.ofReal (3 * δ⁻¹ ^ 2) with hc3
  set c6 : ℝ≥0∞ := ENNReal.ofReal (δ ^ 3 / 3) with hc6
  have hc3top : c3 ≠ ⊤ := by rw [hc3]; exact ENNReal.ofReal_ne_top
  have hc6top : c6 ≠ ⊤ := by rw [hc6]; exact ENNReal.ofReal_ne_top

  -- ### The pointwise bound
  have hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ENNReal.ofReal ((Work.Spaces.pz V z₀ θ * wth θ) ^ 2) ≤
        c3 * (ENNReal.ofReal ((V (z₀ + δ) θ * wth θ) ^ 2)
              + (ENNReal.ofReal ((V z₀ θ * wth θ) ^ 2)
                 + c6 * ∫⁻ t in Set.Ioc (0 : ℝ) δ,
                     ENNReal.ofReal ((Work.Spaces.pzIter 2 V (z₀ + t) θ * wth θ) ^ 2))) := by
    intro θ hθ
    -- (1) the Cauchy–Schwarz bound for the integral remainder
    have hZA : ENNReal.ofReal
        (((∫ t in (0 : ℝ)..δ, (δ - t) * Work.Spaces.pzIter 2 V (z₀ + t) θ) * wth θ) ^ 2)
        ≤ c6 * ∫⁻ t in Set.Ioc (0 : ℝ) δ,
            ENNReal.ofReal ((Work.Spaces.pzIter 2 V (z₀ + t) θ * wth θ) ^ 2) := by
      have hcs := Work.FTS.EllipticEst.DzAmgm.OfRealIntervalIntegralSqLe (a := (0 : ℝ))
        (b := δ) hδnn (fun t => Work.Spaces.pzIter 2 V (z₀ + t) θ)
        (aesm_timeSlice_pzIter2 V hsm hz₀ hθ)
      have hsq : 0 ≤ (wth θ) ^ 2 := sq_nonneg _
      calc ENNReal.ofReal
              (((∫ t in (0 : ℝ)..δ, (δ - t) * Work.Spaces.pzIter 2 V (z₀ + t) θ) * wth θ) ^ 2)
          = ENNReal.ofReal
              (((∫ t in (0 : ℝ)..δ, (δ - t) * Work.Spaces.pzIter 2 V (z₀ + t) θ)) ^ 2)
              * ENNReal.ofReal ((wth θ) ^ 2) := by
            rw [show ((∫ t in (0 : ℝ)..δ, (δ - t) * Work.Spaces.pzIter 2 V (z₀ + t) θ)
                  * wth θ) ^ 2
                  = (∫ t in (0 : ℝ)..δ, (δ - t) * Work.Spaces.pzIter 2 V (z₀ + t) θ) ^ 2
                    * (wth θ) ^ 2 from by ring,
                ENNReal.ofReal_mul (sq_nonneg _)]
        _ ≤ (ENNReal.ofReal ((δ - 0) ^ 3 / 3) * ∫⁻ t in Set.Ioc (0 : ℝ) δ,
              ENNReal.ofReal ((Work.Spaces.pzIter 2 V (z₀ + t) θ) ^ 2))
              * ENNReal.ofReal ((wth θ) ^ 2) :=
            mul_le_mul_of_nonneg_right hcs bot_le
        _ = c6 * (ENNReal.ofReal ((wth θ) ^ 2) * ∫⁻ t in Set.Ioc (0 : ℝ) δ,
              ENNReal.ofReal ((Work.Spaces.pzIter 2 V (z₀ + t) θ) ^ 2)) := by
            rw [hc6, sub_zero]
            ring
        _ = c6 * ∫⁻ t in Set.Ioc (0 : ℝ) δ,
              ENNReal.ofReal ((wth θ) ^ 2)
                * ENNReal.ofReal ((Work.Spaces.pzIter 2 V (z₀ + t) θ) ^ 2) := by
            rw [← MeasureTheory.lintegral_const_mul' (ENNReal.ofReal ((wth θ) ^ 2)) _
              ENNReal.ofReal_ne_top]
        _ = c6 * ∫⁻ t in Set.Ioc (0 : ℝ) δ,
              ENNReal.ofReal ((Work.Spaces.pzIter 2 V (z₀ + t) θ * wth θ) ^ 2) := by
            congr 1
            refine lintegral_congr (fun t => ?_)
            rw [← ENNReal.ofReal_mul (sq_nonneg (wth θ)),
              show (wth θ) ^ 2 * (Work.Spaces.pzIter 2 V (z₀ + t) θ) ^ 2
                = (Work.Spaces.pzIter 2 V (z₀ + t) θ * wth θ) ^ 2 from by ring]
    -- (2) Taylor + the three term inequality
    have hmain : ENNReal.ofReal ((Work.Spaces.pz V z₀ θ * wth θ) ^ 2) ≤
        c3 * (ENNReal.ofReal ((V (z₀ + δ) θ * wth θ) ^ 2)
              + (ENNReal.ofReal ((V z₀ θ * wth θ) ^ 2)
                 + ENNReal.ofReal
                     (((∫ t in (0 : ℝ)..δ, (δ - t) * Work.Spaces.pzIter 2 V (z₀ + t) θ)
                        * wth θ) ^ 2))) := by
      have htay := Work.FTS.EllipticEst.DzAmgm.SliceTaylorIdentity V hsm hz₀ hδpos hθ
      set A : ℝ := V (z₀ + δ) θ * wth θ with hA
      set B : ℝ := V z₀ θ * wth θ with hBreal
      set C : ℝ := (∫ t in (0 : ℝ)..δ, (δ - t) * Work.Spaces.pzIter 2 V (z₀ + t) θ) * wth θ
        with hC
      have hreal : (δ⁻¹ * (A - B - C)) ^ 2 ≤ (3 * δ⁻¹ ^ 2) * (A ^ 2 + (B ^ 2 + C ^ 2)) := by
        have h3 : (A - B - C) ^ 2 ≤ 3 * (A ^ 2 + (B ^ 2 + C ^ 2)) := by
          nlinarith [sq_nonneg (A + B), sq_nonneg (C - B), sq_nonneg (A + C)]
        have h4 := mul_le_mul_of_nonneg_left h3 (sq_nonneg (δ⁻¹))
        nlinarith [h4]
      have hconv : (Work.Spaces.pz V z₀ θ * wth θ) ^ 2 = (δ⁻¹ * (A - B - C)) ^ 2 := by
        rw [htay]
        simp only [hA, hBreal, hC]
        ring
      calc ENNReal.ofReal ((Work.Spaces.pz V z₀ θ * wth θ) ^ 2)
          = ENNReal.ofReal ((δ⁻¹ * (A - B - C)) ^ 2) := by rw [hconv]
        _ ≤ ENNReal.ofReal ((3 * δ⁻¹ ^ 2) * (A ^ 2 + (B ^ 2 + C ^ 2))) :=
            ENNReal.ofReal_le_ofReal hreal
        _ = c3 * (ENNReal.ofReal (A ^ 2) + (ENNReal.ofReal (B ^ 2) + ENNReal.ofReal (C ^ 2))) := by
            rw [hc3, ENNReal.ofReal_mul (by positivity),
              ENNReal.ofReal_add (sq_nonneg A) (by positivity),
              ENNReal.ofReal_add (sq_nonneg B) (sq_nonneg C)]
        _ = c3 * (ENNReal.ofReal ((V (z₀ + δ) θ * wth θ) ^ 2)
              + (ENNReal.ofReal ((V z₀ θ * wth θ) ^ 2)
                 + ENNReal.ofReal
                     (((∫ t in (0 : ℝ)..δ, (δ - t) * Work.Spaces.pzIter 2 V (z₀ + t) θ)
                        * wth θ) ^ 2))) := by
            rw [hA, hBreal, hC]
    calc ENNReal.ofReal ((Work.Spaces.pz V z₀ θ * wth θ) ^ 2)
        ≤ c3 * (ENNReal.ofReal ((V (z₀ + δ) θ * wth θ) ^ 2)
              + (ENNReal.ofReal ((V z₀ θ * wth θ) ^ 2)
                 + ENNReal.ofReal
                     (((∫ t in (0 : ℝ)..δ, (δ - t) * Work.Spaces.pzIter 2 V (z₀ + t) θ)
                        * wth θ) ^ 2))) := hmain
      _ ≤ c3 * (ENNReal.ofReal ((V (z₀ + δ) θ * wth θ) ^ 2)
              + (ENNReal.ofReal ((V z₀ θ * wth θ) ^ 2)
                 + c6 * ∫⁻ t in Set.Ioc (0 : ℝ) δ,
                     ENNReal.ofReal ((Work.Spaces.pzIter 2 V (z₀ + t) θ * wth θ) ^ 2))) := by
            have hstep : ENNReal.ofReal ((V z₀ θ * wth θ) ^ 2)
                  + ENNReal.ofReal
                      (((∫ t in (0 : ℝ)..δ, (δ - t) * Work.Spaces.pzIter 2 V (z₀ + t) θ)
                        * wth θ) ^ 2)
                ≤ ENNReal.ofReal ((V z₀ θ * wth θ) ^ 2)
                  + c6 * ∫⁻ t in Set.Ioc (0 : ℝ) δ,
                      ENNReal.ofReal ((Work.Spaces.pzIter 2 V (z₀ + t) θ * wth θ) ^ 2) :=
              add_le_add (le_refl _) hZA
            refine mul_le_mul_of_nonneg_left ?_ bot_le
            exact add_le_add (le_refl _) hstep

  -- ### Integration
  have h1 : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
        ENNReal.ofReal ((Work.Spaces.pz V z₀ θ * wth θ) ^ 2))
      ≤ ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          c3 * (ENNReal.ofReal ((V (z₀ + δ) θ * wth θ) ^ 2)
              + (ENNReal.ofReal ((V z₀ θ * wth θ) ^ 2)
                 + c6 * ∫⁻ t in Set.Ioc (0 : ℝ) δ,
                     ENNReal.ofReal ((Work.Spaces.pzIter 2 V (z₀ + t) θ * wth θ) ^ 2))) := by
    refine lintegral_mono_ae ?_
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
    exact Filter.Eventually.of_forall (fun θ hθ => hpt θ hθ)

  have h2 : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          c3 * (ENNReal.ofReal ((V (z₀ + δ) θ * wth θ) ^ 2)
              + (ENNReal.ofReal ((V z₀ θ * wth θ) ^ 2)
                 + c6 * ∫⁻ t in Set.Ioc (0 : ℝ) δ,
                     ENNReal.ofReal ((Work.Spaces.pzIter 2 V (z₀ + t) θ * wth θ) ^ 2))))
      = c3 * ((∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
            ENNReal.ofReal ((V (z₀ + δ) θ * wth θ) ^ 2))
          + ((∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
                ENNReal.ofReal ((V z₀ θ * wth θ) ^ 2))
             + c6 * ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
                 ∫⁻ t in Set.Ioc (0 : ℝ) δ,
                   ENNReal.ofReal ((Work.Spaces.pzIter 2 V (z₀ + t) θ * wth θ) ^ 2))) := by
    rw [MeasureTheory.lintegral_const_mul' c3 _ hc3top]
    congr 1
    rw [MeasureTheory.lintegral_add_left'
      (aemeasurable_slice_V_sq V wth hwthmeas hsm (by linarith : 0 < z₀ + δ))]
    congr 1
    rw [MeasureTheory.lintegral_add_left'
      (aemeasurable_slice_V_sq V wth hwthmeas hsm hz₀)]
    rw [MeasureTheory.lintegral_const_mul' c6 _ hc6top]

  have hXAfin : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
        ENNReal.ofReal ((V (z₀ + δ) θ * wth θ) ^ 2)) < ⊤ :=
    hG (z₀ + δ) (by simp only [Set.mem_Ioi]; linarith)
  have hYAfin : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
        ENNReal.ofReal ((V z₀ θ * wth θ) ^ 2)) < ⊤ := hG z₀ hz₀
  have hHfin : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
        ∫⁻ t in Set.Ioc (0 : ℝ) δ,
          ENNReal.ofReal ((Work.Spaces.pzIter 2 V (z₀ + t) θ * wth θ) ^ 2)) < ⊤ := by
    rw [SliceSwapLintegral V wth hwthmeas hsm hz₀ hδpos]
    exact hBfin

  have hfin : c3 * ((∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          ENNReal.ofReal ((V (z₀ + δ) θ * wth θ) ^ 2))
        + ((∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
              ENNReal.ofReal ((V z₀ θ * wth θ) ^ 2))
           + c6 * ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
               ∫⁻ t in Set.Ioc (0 : ℝ) δ,
                 ENNReal.ofReal ((Work.Spaces.pzIter 2 V (z₀ + t) θ * wth θ) ^ 2))) < ⊤ :=
    ENNReal.mul_lt_top (by rw [hc3]; exact ENNReal.ofReal_lt_top)
      ((ENNReal.add_lt_top).mpr ⟨hXAfin,
        (ENNReal.add_lt_top).mpr ⟨hYAfin,
          ENNReal.mul_lt_top (by rw [hc6]; exact ENNReal.ofReal_lt_top) hHfin⟩⟩)

  exact lt_of_le_of_lt (h1.trans (le_of_eq h2)) hfin

end Work.FTS.EllipticEst.Blocks
