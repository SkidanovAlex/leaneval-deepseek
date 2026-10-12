import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB3.HighMass.OneBody
import Submission.Work.BoseFixB3.Split.lowSlotBound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.Conv.highMult_box_transfer`

The **box self-adjointness of the complementary low-momentum multiplier** `1 − f_L`
(`Work.BoseFixB3.highMult`, FS §7): for `κ > 0`, `ℓ > 0`, a function `u` measurable and
bounded on the box `Λ = acube ℓ`, and a function `W` measurable and bounded on all of `ℝ³`,

`∫_Λ (1 − f_L)(u)·W = ∫_Λ u·(1 − f_L)(W)`.

Since `highMult = id − lowMult`, this is equivalent to the self-adjointness of the
box-restricted multiplier `lowMult` (`∫_Λ f_L(u)·W = ∫_Λ u·f_L(W)`), together with the
integrability of the pieces on the finite-measure box.

## The argument

`Work.BoseFixB3.HighMassAux.lowMult_pairing` computes the weak pairing of `lowMult` with a
compactly supported `φ`: with `θ` the extension by zero off `Λ`,

`∫_x φ x · f_L(Ψ) x = (2π)⁻³ ∫_p Re( conj(kinFT(θφ)(p)) · f(‖p‖/κ) · kinFT(θΨ)(p) )`.

Applying this twice, with `(φ, Ψ) = (θW, u)` and `(φ, Ψ) = (θu, W)`, the two right-hand sides
agree **pointwise in `p`** because `f(‖p‖/κ)` is real (`re_conj_mul_real_mul_comm`); hence
`∫_x θW·f_L(u) = ∫_x θu·f_L(W)`, which, by `integral_indicator`, is the box identity
`∫_Λ f_L(u)·W = ∫_Λ u·f_L(W)`.

The remaining step is bookkeeping: all four pieces (`u·W`, `f_L(u)·W`, `u·f_L(W)`) are
integrable on the box, being products of measurable functions bounded on the finite-measure
cube `Λ` (`lowMult` is bounded on the box by `Split.lowMult_abs_le` +
`Split.integral_indicator_norm_le`, and strongly measurable by
`HighMass.aestronglyMeasurable_lowMult`).
-/

noncomputable section

open MeasureTheory Filter Metric
open scoped Real Topology BigOperators

namespace Work.BoseFixB3.Conv

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## 1. Two elementary helpers -/

/-- A box-restricted integral is the integral of the indicator of the box times the other
factor: `∫_s f·g = ∫_x 1_s(x)·f x·g x`. -/
private lemma setIntegral_indicator_mul {s : Set E3} (hs : MeasurableSet s) (f g : E3 → ℝ) :
    (∫ x in s, f x * g x) = ∫ x, s.indicator f x * g x := by
  rw [← MeasureTheory.integral_indicator hs]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]

/-- The `p`-space integrand `Re(conj(a)·r·b)`, `r` real, is symmetric in its two Fourier
factors: `Re(conj a·r·b) = Re(conj b·r·a)`. -/
private lemma re_conj_mul_real_mul_comm (a b : ℂ) (r : ℝ) :
    (starRingEnd ℂ a * (r : ℂ) * b).re = (starRingEnd ℂ b * (r : ℂ) * a).re := by
  have h : starRingEnd ℂ (starRingEnd ℂ a * (r : ℂ) * b) = starRingEnd ℂ b * (r : ℂ) * a := by
    simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal]
    ring
  rw [← h]
  exact (Complex.conj_re _).symm

/-! ## 2. Integrability on the box

Everything rests on the two standing bounds: `|u| ≤ C` on `Λ` and `|W| ≤ C'` everywhere. -/

/-- A product of two functions bounded on the finite-measure box `acube ℓ` is `L¹` on the
box. -/
private lemma integrableOn_mul_of_box_bounds {ℓ : ℝ} (hℓ : 0 < ℓ) {f g : E3 → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (Submission.BoseGases.acube ℓ)))
    (hg : AEStronglyMeasurable g (volume.restrict (Submission.BoseGases.acube ℓ)))
    {A B : ℝ} (hfb : ∀ x ∈ Submission.BoseGases.acube ℓ, |f x| ≤ A)
    (hgb : ∀ x ∈ Submission.BoseGases.acube ℓ, |g x| ≤ B) :
    IntegrableOn (fun x => f x * g x) (Submission.BoseGases.acube ℓ) := by
  refine IntegrableOn.of_bound (Submission.BoseGases.acube_lt_top ℓ hℓ.le) (hf.mul hg)
    (|A| * |B|) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem (Submission.BoseGases.acube_measurable ℓ)]
    with x hx
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (le_trans (hfb x hx) (le_abs_self A))
    (le_trans (hgb x hx) (le_abs_self B)) (abs_nonneg _) (abs_nonneg _)

/-- `u` is integrable on the box when it is measurable and bounded there. -/
private lemma integrableOn_of_box_bounded {ℓ : ℝ} (hℓ : 0 < ℓ) {u : E3 → ℝ}
    (hum : Measurable u) (hub : ∃ C : ℝ, ∀ x ∈ Submission.BoseGases.acube ℓ, |u x| ≤ C) :
    IntegrableOn u (Submission.BoseGases.acube ℓ) := by
  obtain ⟨C, hC⟩ := hub
  refine IntegrableOn.of_bound (Submission.BoseGases.acube_lt_top ℓ hℓ.le)
    (hum.aestronglyMeasurable.mono_measure Measure.restrict_le_self) (max C 0) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem (Submission.BoseGases.acube_measurable ℓ)]
    with x hx
  rw [Real.norm_eq_abs]
  exact le_trans (hC x hx) (le_max_left _ _)

/-- **The uniform bound on `lowMult` on the box**: if `|ψ| ≤ M` on `Λ`, then `lowMult fc κ ℓ ψ`
is bounded everywhere by `(2π)⁻³ M ℓ³ vol(B(0,2κ))`. -/
private lemma lowMult_bound_exists {fc : Work.BoseBoxFix.LowCut} {κ ℓ M : ℝ} (hκ : 0 < κ)
    (hℓ : 0 < ℓ) (hM : 0 ≤ M) {ψ : E3 → ℝ}
    (hψ : ∀ z ∈ Submission.BoseGases.acube ℓ, |ψ z| ≤ M) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : E3, |Work.BoseBoxFix.lowMult fc κ ℓ ψ y| ≤ K := by
  refine ⟨((2 * π) ^ 3)⁻¹ * (M * ℓ ^ 3)
      * (volume (Metric.closedBall (0 : E3) (2 * κ))).toReal, ?_, ?_⟩
  · have h1 : 0 ≤ (M * ℓ ^ 3) := mul_nonneg hM (by positivity)
    exact mul_nonneg (mul_nonneg (by positivity) h1) ENNReal.toReal_nonneg
  · intro y
    exact Work.BoseFixB3.Split.lowMult_abs_le (fc := fc) (κ := κ) (ℓ := ℓ) (D := M * ℓ ^ 3)
      hκ (mul_nonneg hM (by positivity))
      (Work.BoseFixB3.Split.integral_indicator_norm_le hℓ hM hψ) y

/-- `lowMult fc κ ℓ u · W` is integrable on the box. -/
private lemma integrableOn_lowMult_mul {fc : Work.BoseBoxFix.LowCut} {κ ℓ : ℝ} (hκ : 0 < κ)
    (hℓ : 0 < ℓ) {u W : E3 → ℝ} (hum : Measurable u)
    (hub : ∃ C : ℝ, ∀ x ∈ Submission.BoseGases.acube ℓ, |u x| ≤ C) (hWm : Measurable W)
    (hWb : ∃ C : ℝ, ∀ x, |W x| ≤ C) :
    IntegrableOn (fun x => Work.BoseBoxFix.lowMult fc κ ℓ u x * W x)
      (Submission.BoseGases.acube ℓ) := by
  obtain ⟨C, hC⟩ := hub
  obtain ⟨C', hC'⟩ := hWb
  obtain ⟨K, _hK0, hK⟩ := lowMult_bound_exists (fc := fc) (κ := κ) (ℓ := ℓ) (M := max C 0)
    hκ hℓ (le_max_right _ _) (fun z hz => le_trans (hC z hz) (le_max_left _ _))
  refine integrableOn_mul_of_box_bounds (A := K) (B := max C' 0) hℓ ?_ ?_
    (fun x _ => hK x) (fun x _ => ?_)
  · exact (Work.BoseFixB3.HighMass.aestronglyMeasurable_lowMult hum).mono_measure
      Measure.restrict_le_self
  · exact hWm.aestronglyMeasurable.mono_measure Measure.restrict_le_self
  · exact le_trans (hC' x) (le_max_left _ _)

/-- `u · lowMult fc κ ℓ W` is integrable on the box. -/
private lemma integrableOn_mul_lowMult {fc : Work.BoseBoxFix.LowCut} {κ ℓ : ℝ} (hκ : 0 < κ)
    (hℓ : 0 < ℓ) {u W : E3 → ℝ} (hum : Measurable u)
    (hub : ∃ C : ℝ, ∀ x ∈ Submission.BoseGases.acube ℓ, |u x| ≤ C) (hWm : Measurable W)
    (hWb : ∃ C : ℝ, ∀ x, |W x| ≤ C) :
    IntegrableOn (fun x => u x * Work.BoseBoxFix.lowMult fc κ ℓ W x)
      (Submission.BoseGases.acube ℓ) := by
  obtain ⟨C, hC⟩ := hub
  obtain ⟨C', hC'⟩ := hWb
  obtain ⟨K, _hK0, hK⟩ := lowMult_bound_exists (fc := fc) (κ := κ) (ℓ := ℓ) (M := max C' 0)
    hκ hℓ (le_max_right _ _) (fun z hz => le_trans (hC' z) (le_max_left _ _))
  refine integrableOn_mul_of_box_bounds (A := max C 0) (B := K) hℓ ?_ ?_
    (fun x hx => ?_) (fun x _ => hK x)
  · exact hum.aestronglyMeasurable.mono_measure Measure.restrict_le_self
  · exact (Work.BoseFixB3.HighMass.aestronglyMeasurable_lowMult hWm).mono_measure
      Measure.restrict_le_self
  · exact le_trans (hC x hx) (le_max_left _ _)

/-! ## 3. The transfer identity -/

theorem highMult_box_transfer {fc : Work.BoseBoxFix.LowCut} {κ ℓ : ℝ} (hκ : 0 < κ) (hℓ : 0 < ℓ)
    {u W : EuclideanSpace ℝ (Fin 3) → ℝ} (hum : Measurable u)
    (hub : ∃ C : ℝ, ∀ x ∈ Submission.BoseGases.acube ℓ, |u x| ≤ C)
    (hWm : Measurable W) (hWb : ∃ C : ℝ, ∀ x, |W x| ≤ C) :
    (∫ x in Submission.BoseGases.acube ℓ, Work.BoseFixB3.highMult fc κ ℓ u x * W x)
      = ∫ x in Submission.BoseGases.acube ℓ, u x * Work.BoseFixB3.highMult fc κ ℓ W x := by
  have hs : MeasurableSet (Submission.BoseGases.acube ℓ) :=
    Submission.BoseGases.acube_measurable ℓ
  have hcs : HasCompactSupport (fun p : E3 => fc.f (‖p‖ / κ)) :=
    Work.BoseFixB3.HighMass.lowcut_symbol_hasCompactSupport (fc := fc) (κ := κ) hκ
  -- ### integrability of the inputs of the pairing formula
  have hIntOn_u : IntegrableOn u (Submission.BoseGases.acube ℓ) :=
    integrableOn_of_box_bounded hℓ hum hub
  have hIntOn_W : IntegrableOn W (Submission.BoseGases.acube ℓ) := by
    obtain ⟨C, hC⟩ := hWb
    exact integrableOn_of_box_bounded hℓ hWm ⟨C, fun x _ => hC x⟩
  have hind_u : Integrable ((Submission.BoseGases.acube ℓ).indicator u) :=
    MeasureTheory.IntegrableOn.integrable_indicator hIntOn_u hs
  have hind_W : Integrable ((Submission.BoseGases.acube ℓ).indicator W) :=
    MeasureTheory.IntegrableOn.integrable_indicator hIntOn_W hs
  have hcsind_u : HasCompactSupport ((Submission.BoseGases.acube ℓ).indicator u) :=
    HasCompactSupport.intro' (Submission.BoseGases.acube_compact hℓ)
      (Submission.BoseGases.acube_isClosed ℓ) (fun x hx => Set.indicator_of_notMem hx u)
  have hcsind_W : HasCompactSupport ((Submission.BoseGases.acube ℓ).indicator W) :=
    HasCompactSupport.intro' (Submission.BoseGases.acube_compact hℓ)
      (Submission.BoseGases.acube_isClosed ℓ) (fun x hx => Set.indicator_of_notMem hx W)
  -- ### the two weak pairing identities
  have hpairW := Work.BoseFixB3.HighMassAux.lowMult_pairing (fc := fc) (κ := κ) (ℓ := ℓ) hℓ
    (φ := (Submission.BoseGases.acube ℓ).indicator W) hind_W hcsind_W (Ψ := u) hIntOn_u hcs
  have hpairU := Work.BoseFixB3.HighMassAux.lowMult_pairing (fc := fc) (κ := κ) (ℓ := ℓ) hℓ
    (φ := (Submission.BoseGases.acube ℓ).indicator u) hind_u hcsind_u (Ψ := W) hIntOn_W hcs
  -- ### the two `p`-space forms coincide
  have hglobal :
      (∫ x : E3, (Submission.BoseGases.acube ℓ).indicator W x
          * Work.BoseBoxFix.lowMult fc κ ℓ u x)
        = ∫ x : E3, (Submission.BoseGases.acube ℓ).indicator u x
            * Work.BoseBoxFix.lowMult fc κ ℓ W x := by
    rw [hpairW, hpairU]
    congr 1
    apply MeasureTheory.integral_congr_ae
    filter_upwards with p
    exact re_conj_mul_real_mul_comm _ _ _
  -- ### the box form of the self-adjointness
  have hAB :
      (∫ x in Submission.BoseGases.acube ℓ, Work.BoseBoxFix.lowMult fc κ ℓ u x * W x)
        = ∫ x in Submission.BoseGases.acube ℓ,
            u x * Work.BoseBoxFix.lowMult fc κ ℓ W x := by
    have hcomm : (∫ x in Submission.BoseGases.acube ℓ,
          Work.BoseBoxFix.lowMult fc κ ℓ u x * W x)
        = ∫ x in Submission.BoseGases.acube ℓ, W x * Work.BoseBoxFix.lowMult fc κ ℓ u x :=
      MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall (fun x => mul_comm _ _))
    rw [hcomm,
      setIntegral_indicator_mul hs W (Work.BoseBoxFix.lowMult fc κ ℓ u),
      setIntegral_indicator_mul hs u (Work.BoseBoxFix.lowMult fc κ ℓ W),
      hglobal]
  -- ### the four integrability facts on the box
  have hi1 : IntegrableOn (fun x => u x * W x) (Submission.BoseGases.acube ℓ) := by
    obtain ⟨C, hC⟩ := hub
    obtain ⟨C', hC'⟩ := hWb
    refine integrableOn_mul_of_box_bounds (A := max C 0) (B := max C' 0) hℓ ?_ ?_
      (fun x hx => ?_) (fun x hx => ?_)
    · exact hum.aestronglyMeasurable.mono_measure Measure.restrict_le_self
    · exact hWm.aestronglyMeasurable.mono_measure Measure.restrict_le_self
    · exact le_trans (hC x hx) (le_max_left _ _)
    · exact le_trans (hC' x) (le_max_left _ _)
  have hi2 : IntegrableOn (fun x => Work.BoseBoxFix.lowMult fc κ ℓ u x * W x)
      (Submission.BoseGases.acube ℓ) :=
    integrableOn_lowMult_mul hκ hℓ hum hub hWm hWb
  have hi3 : IntegrableOn (fun x => u x * Work.BoseBoxFix.lowMult fc κ ℓ W x)
      (Submission.BoseGases.acube ℓ) :=
    integrableOn_mul_lowMult hκ hℓ hum hub hWm hWb
  -- ### assemble
  have h1 : (∫ x in Submission.BoseGases.acube ℓ, Work.BoseFixB3.highMult fc κ ℓ u x * W x)
      = (∫ x in Submission.BoseGases.acube ℓ, u x * W x)
        - ∫ x in Submission.BoseGases.acube ℓ, Work.BoseBoxFix.lowMult fc κ ℓ u x * W x := by
    rw [show (∫ x in Submission.BoseGases.acube ℓ,
            Work.BoseFixB3.highMult fc κ ℓ u x * W x)
        = ∫ x in Submission.BoseGases.acube ℓ,
            (u x * W x - Work.BoseBoxFix.lowMult fc κ ℓ u x * W x) from
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => by
        simp only [Work.BoseFixB3.highMult]; ring))]
    exact MeasureTheory.integral_sub hi1 hi2
  have h2 : (∫ x in Submission.BoseGases.acube ℓ, u x * Work.BoseFixB3.highMult fc κ ℓ W x)
      = (∫ x in Submission.BoseGases.acube ℓ, u x * W x)
        - ∫ x in Submission.BoseGases.acube ℓ,
            u x * Work.BoseBoxFix.lowMult fc κ ℓ W x := by
    rw [show (∫ x in Submission.BoseGases.acube ℓ,
            u x * Work.BoseFixB3.highMult fc κ ℓ W x)
        = ∫ x in Submission.BoseGases.acube ℓ,
            (u x * W x - u x * Work.BoseBoxFix.lowMult fc κ ℓ W x) from
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => by
        simp only [Work.BoseFixB3.highMult]; ring))]
    exact MeasureTheory.integral_sub hi1 hi3
  rw [h1, h2, hAB]

end Work.BoseFixB3.Conv
