import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PCFU.dictBricks
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.PCFU.fibre_mean_removal_le`

Removing the mean of a function over the centred cube `acube ℓ` can only *decrease* its `L²`-mass:
for `ℓ > 0` and any `ψ : ℝ³ → ℝ`,

    ∫⁻ ‖1_{Λ(ℓ)}·(ψ − c)‖²  ≤  ∫⁻ ‖1_{Λ(ℓ)}·ψ‖² ,   c := (1/ℓ³)∫_{Λ(ℓ)} ψ ,

i.e. the deviations from the average have smaller `L²`-mass than the function itself (the mean is
the best approximation of `ψ` by a constant in `L²`).

## Proof

Both sides are rewritten over the restricted measure `μ := volume.restrict (acube ℓ)`
(`lintegral_indicator_sq_eq`), whose total mass is `ℓ³` (`CentreBox.acube_volume`), and the
following general statement (`lintegral_sub_mean_sq_le`, on an abstract finite measure space) is
applied:

* if `f ∉ L¹(μ)` then the Bochner integral `∫ f` is `0`, so `c = 0` and the two sides are the same
  function;
* otherwise split on whether `∫⁻ ofReal(f²)` is finite.  If it is infinite the inequality is
  trivial.  If it is finite then `f² ∈ L¹(μ)` (`lintegral_ofReal_ne_top_iff_integrable`), hence
  `(f − c)² ∈ L¹(μ)` and both `∫⁻`'s are `ofReal`-images of Bochner integrals; the algebraic
  identity

      ∫ (f − c)² = ∫ f² − V·c²       (`V = (μ univ).toReal`)

  (with `∫ f = c·V`) gives `∫ (f − c)² ≤ ∫ f²`.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Work.PCFU

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Elimination of a set indicator inside a squared `∫⁻`.**  For measurable `A`,
`∫⁻ ‖A.indicator f‖² = ∫⁻_{A} ‖f‖²`. -/
private lemma lintegral_indicator_sq_eq {α : Type*} [MeasureSpace α] (A : Set α)
    (hA : MeasurableSet A) (f : α → ℝ) :
    (∫⁻ u, ENNReal.ofReal ((A.indicator f u) ^ 2)) = ∫⁻ u in A, ENNReal.ofReal ((f u) ^ 2) := by
  have hpt : ∀ u, ENNReal.ofReal ((A.indicator f u) ^ 2)
      = A.indicator (fun u => ENNReal.ofReal ((f u) ^ 2)) u := by
    intro u
    by_cases h : u ∈ A
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]
      simp
  rw [show (fun u => ENNReal.ofReal ((A.indicator f u) ^ 2))
      = A.indicator (fun u => ENNReal.ofReal ((f u) ^ 2)) from funext hpt]
  exact MeasureTheory.lintegral_indicator hA _

/-- **Mean removal does not increase the `L²`-mass.**  On a finite measure space `(α, μ)` with
`(μ univ).toReal = V ≠ 0`, the deviations of `f` from its mean `c = V⁻¹∫ f` have smaller
`∫⁻`-mass (of the square) than `f` itself. -/
private theorem lintegral_sub_mean_sq_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {f : α → ℝ} {V : ℝ} (hVμ : (μ Set.univ).toReal = V) (hV : V ≠ 0) :
    (∫⁻ x, ENNReal.ofReal ((f x - (1 / V) * ∫ y, f y ∂μ) ^ 2) ∂μ)
      ≤ ∫⁻ x, ENNReal.ofReal ((f x) ^ 2) ∂μ := by
  by_cases hint : Integrable f μ
  · -- the mean is an honest Bochner integral
    set I : ℝ := ∫ y, f y ∂μ with hIdef
    set c : ℝ := (1 / V) * I with hcdef
    by_cases hR : (∫⁻ x, ENNReal.ofReal ((f x) ^ 2) ∂μ) = ∞
    · rw [hR]
      exact le_top
    · have hsm : AEStronglyMeasurable (fun x => (f x) ^ 2) μ :=
        hint.aestronglyMeasurable.pow 2
      have hf2 : Integrable (fun x => (f x) ^ 2) μ :=
        (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hsm
          (Filter.Eventually.of_forall fun x => sq_nonneg _)).mp hR
      have hVnn : 0 ≤ V := by rw [← hVμ]; exact ENNReal.toReal_nonneg
      have hcv : c * V = I := by
        rw [hcdef]
        calc ((1 / V) * I) * V = I * ((1 / V) * V) := by ring
          _ = I * 1 := by rw [one_div, inv_mul_cancel₀ hV]
          _ = I := by ring
      have h3' : Integrable (fun x => (f x) ^ 2 - 2 * c * f x + c ^ 2) μ :=
        (hf2.sub (hint.const_mul (2 * c))).add (MeasureTheory.integrable_const (c ^ 2))
      have h3 : Integrable (fun x => (f x - c) ^ 2) μ :=
        h3'.congr (Filter.Eventually.of_forall fun x => by ring)
      have hle : (∫ x, (f x - c) ^ 2 ∂μ) ≤ ∫ x, (f x) ^ 2 ∂μ := by
        have e1 : (∫ x, (f x - c) ^ 2 ∂μ)
            = ∫ x, ((f x) ^ 2 - 2 * c * f x + c ^ 2) ∂μ :=
          MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
        have e2 : (∫ x, ((f x) ^ 2 - 2 * c * f x + c ^ 2) ∂μ)
            = (∫ x, ((f x) ^ 2 - 2 * c * f x) ∂μ) + ∫ x, (c ^ 2 : ℝ) ∂μ :=
          MeasureTheory.integral_add (hf2.sub (hint.const_mul (2 * c)))
            (MeasureTheory.integrable_const _)
        have e3 : (∫ x, ((f x) ^ 2 - 2 * c * f x) ∂μ)
            = (∫ x, (f x) ^ 2 ∂μ) - 2 * c * ∫ x, f x ∂μ := by
          rw [MeasureTheory.integral_sub hf2 (hint.const_mul (2 * c)),
            MeasureTheory.integral_const_mul]
        have e4 : (∫ x, (c ^ 2 : ℝ) ∂μ) = V * c ^ 2 := by
          rw [MeasureTheory.integral_const, MeasureTheory.Measure.real_def, smul_eq_mul, hVμ]
        have hkey : (∫ x, (f x - c) ^ 2 ∂μ) = (∫ x, (f x) ^ 2 ∂μ) - V * c ^ 2 := by
          rw [e1, e2, e3, e4, ← hIdef, ← hcv]
          ring
        rw [hkey]
        linarith [mul_nonneg hVnn (sq_nonneg c)]
      calc (∫⁻ x, ENNReal.ofReal ((f x - c) ^ 2) ∂μ)
          = ENNReal.ofReal (∫ x, (f x - c) ^ 2 ∂μ) :=
            (MeasureTheory.ofReal_integral_eq_lintegral_ofReal h3
              (Filter.Eventually.of_forall fun x => sq_nonneg _)).symm
        _ ≤ ENNReal.ofReal (∫ x, (f x) ^ 2 ∂μ) := ENNReal.ofReal_le_ofReal hle
        _ = (∫⁻ x, ENNReal.ofReal ((f x) ^ 2) ∂μ) :=
            MeasureTheory.ofReal_integral_eq_lintegral_ofReal hf2
              (Filter.Eventually.of_forall fun x => sq_nonneg _)
  · -- the Bochner integral is `0`, so the mean vanishes and the two sides coincide
    have hI0 : (∫ y, f y ∂μ) = 0 := MeasureTheory.integral_undef hint
    have hgoal : (∫⁻ x, ENNReal.ofReal ((f x - (1 / V) * ∫ y, f y ∂μ) ^ 2) ∂μ)
        = ∫⁻ x, ENNReal.ofReal ((f x) ^ 2) ∂μ := by
      apply MeasureTheory.lintegral_congr
      intro x
      rw [hI0, mul_zero, sub_zero]
    exact le_of_eq hgoal

theorem fibre_mean_removal_le {ℓ : ℝ} (hℓ : 0 < ℓ) {ψ : EuclideanSpace ℝ (Fin 3) → ℝ} :
    (∫⁻ u : EuclideanSpace ℝ (Fin 3),
        ENNReal.ofReal (((Submission.BoseGases.acube ℓ).indicator
          (fun u => ψ u - (1 / ℓ ^ 3) * ∫ v in Submission.BoseGases.acube ℓ, ψ v) u) ^ 2))
      ≤ ∫⁻ u : EuclideanSpace ℝ (Fin 3),
          ENNReal.ofReal (((Submission.BoseGases.acube ℓ).indicator ψ u) ^ 2) := by
  have hA : MeasurableSet (Submission.BoseGases.acube ℓ) :=
    Submission.BoseGases.acube_measurable ℓ
  have hvol : ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) Set.univ
      = ENNReal.ofReal (ℓ ^ 3) := by
    rw [Measure.restrict_apply_univ, Submission.BoseGases.acube_volume ℓ hℓ.le]
  have hVt : (((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) Set.univ).toReal
      = ℓ ^ 3 := by
    rw [hvol, ENNReal.toReal_ofReal (by positivity)]
  have hfin : IsFiniteMeasure ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) :=
    ⟨by rw [hvol]; exact ENNReal.ofReal_lt_top⟩
  rw [lintegral_indicator_sq_eq (Submission.BoseGases.acube ℓ) hA ψ,
    lintegral_indicator_sq_eq (Submission.BoseGases.acube ℓ) hA
      (fun u => ψ u - (1 / ℓ ^ 3) * ∫ v in Submission.BoseGases.acube ℓ, ψ v)]
  exact lintegral_sub_mean_sq_le
    (μ := (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))
    (f := ψ) (V := ℓ ^ 3) hVt (by positivity)

end Work.PCFU
