import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.SmallBoxSliding.boxMass_integral_u
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Measurability and uniform boundedness of the sliding box mean of a continuous `w`

For `ℓ, d > 0` and `w : EuclideanSpace ℝ (Fin 3) → ℝ` continuous, the normalised
sliding box mean

    u ↦ (boxMass ℓ d u)⁻¹ * ∫ z in dlBox ℓ d u, w z

(`dlBox ℓ d u = acube ℓ ∩ ((ℓd)•u + acube (ℓd))` the sliding small box,
`boxMass ℓ d u` its true Lebesgue volume) is measurable in `u` and uniformly bounded
in `u`.

* **Measurability.** The box indicator `(u,x) ↦ 1_{B(u)}(x)` is *jointly* measurable
  (its support `{(u,x) | x ∈ dlBox ℓ d u} = {x ∈ acube ℓ} ∩ {x - (ℓd)•u ∈ acube (ℓd)}`
  is an intersection of two closed sets, `measurableSet_boxIndSet`).  Hence
  `(u,x) ↦ 1_{B(u)}(x)·w x` is jointly measurable and its parametric Bochner integral
  is strongly measurable in `u` (`StronglyMeasurable.integral_prod_right'`, which needs
  *no* integrability hypothesis); `integral_indicator` converts the integral against the
  indicator into the set integral over `B(u)`.  The same argument with `w = 1` gives the
  measurability of `boxMass`.

* **Boundedness.** Continuity of `w` makes `|w|` bounded on the compact cube `acube ℓ`
  (`IsCompact.exists_bound_of_continuousOn`); since `dlBox ℓ d u ⊆ acube ℓ`, the box mean
  of a bounded function has the same bound:
  `|B(u)|⁻¹·|∫_{B(u)} w| ≤ |B(u)|⁻¹·(M·|B(u)|) = M`, and the degenerate case
  `|B(u)| = 0` gives `0⁻¹ = 0`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1S.corrMarg

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false

/-- The box indicator `(u,x) ↦ 1_{B(u)}(x)` is jointly measurable. -/
private lemma measurable_uncurry_boxInd (ℓ d : ℝ) :
    Measurable (Function.uncurry (Work.SmallBoxSliding.boxInd ℓ d)) := by
  have hEq : Function.uncurry (Work.SmallBoxSliding.boxInd ℓ d)
      = {p : ℝ³ × ℝ³ | p.2 ∈ Submission.BoseGases.dlBox ℓ d p.1}.indicator
          (fun _ => (1 : ℝ)) := by
    funext p
    obtain ⟨u, x⟩ := p
    simp only [Function.uncurry_apply_pair]
    by_cases hx : x ∈ Submission.BoseGases.dlBox ℓ d u
    · rw [Work.SmallBoxSliding.boxInd, Set.indicator_of_mem hx,
        Set.indicator_of_mem (show (u, x) ∈
          {p : ℝ³ × ℝ³ | p.2 ∈ Submission.BoseGases.dlBox ℓ d p.1} from hx)]
    · rw [Work.SmallBoxSliding.boxInd, Set.indicator_of_notMem hx,
        Set.indicator_of_notMem (show (u, x) ∉
          {p : ℝ³ × ℝ³ | p.2 ∈ Submission.BoseGases.dlBox ℓ d p.1} from hx)]
  rw [hEq]
  exact measurable_const.indicator (Work.SmallBoxSliding.measurableSet_boxIndSet ℓ d)

/-- The true box volume `boxMass ℓ d` is a measurable function of the sliding centre. -/
private lemma measurable_boxMass' (ℓ d : ℝ) :
    Measurable (fun u : ℝ³ => Work.SmallBoxSliding.boxMass ℓ d u) := by
  have h := (measurable_uncurry_boxInd ℓ d).stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure ℝ³))
  have h2 : (fun u : ℝ³ => ∫ y : ℝ³,
        Function.uncurry (Work.SmallBoxSliding.boxInd ℓ d) (u, y))
      = fun u : ℝ³ => Work.SmallBoxSliding.boxMass ℓ d u := by
    funext u
    simp [Work.SmallBoxSliding.boxMass, Function.uncurry]
  rw [h2] at h
  exact h.measurable

theorem measurable_and_bound_boxMean {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {w : EuclideanSpace ℝ (Fin 3) → ℝ} (hw : Continuous w) :
    Measurable (fun u : EuclideanSpace ℝ (Fin 3) =>
      (Work.SmallBoxSliding.boxMass ℓ d u)⁻¹ *
        ∫ z in Submission.BoseGases.dlBox ℓ d u, w z)
    ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ u : EuclideanSpace ℝ (Fin 3),
        |(Work.SmallBoxSliding.boxMass ℓ d u)⁻¹ *
          ∫ z in Submission.BoseGases.dlBox ℓ d u, w z| ≤ C := by
  constructor
  · -- measurability of the normalised box mean
    have hjoint : Measurable (fun p : ℝ³ × ℝ³ =>
        Work.SmallBoxSliding.boxInd ℓ d p.1 p.2 * w p.2) :=
      (measurable_uncurry_boxInd ℓ d).mul (hw.measurable.comp measurable_snd)
    have hint : StronglyMeasurable (fun u : ℝ³ =>
        ∫ z : ℝ³, Work.SmallBoxSliding.boxInd ℓ d u z * w z) :=
      MeasureTheory.StronglyMeasurable.integral_prod_right' hjoint.stronglyMeasurable
    have hconv : (fun u : ℝ³ => ∫ z : ℝ³,
          Work.SmallBoxSliding.boxInd ℓ d u z * w z)
        = fun u : ℝ³ => ∫ z in Submission.BoseGases.dlBox ℓ d u, w z := by
      funext u
      have hpt : (fun z : ℝ³ => Work.SmallBoxSliding.boxInd ℓ d u z * w z)
          = (Submission.BoseGases.dlBox ℓ d u).indicator w := by
        funext z
        by_cases hz : z ∈ Submission.BoseGases.dlBox ℓ d u
        · rw [Work.SmallBoxSliding.boxInd, Set.indicator_of_mem hz,
            Set.indicator_of_mem hz, one_mul]
        · rw [Work.SmallBoxSliding.boxInd, Set.indicator_of_notMem hz,
            Set.indicator_of_notMem hz, zero_mul]
      rw [hpt]
      exact MeasureTheory.integral_indicator
        (Work.SmallBoxSliding.measurableSet_dlBox ℓ d u)
    rw [hconv] at hint
    exact (measurable_boxMass' ℓ d).inv.mul hint.measurable
  · -- uniform bound
    obtain ⟨C₀, hC₀⟩ := (Submission.BoseGases.acube_compact hℓ).exists_bound_of_continuousOn
      hw.norm.continuousOn
    -- `hC₀ : ∀ z ∈ acube ℓ, ‖w z‖ ≤ C₀`
    refine ⟨max C₀ 0, le_max_right _ _, fun u => ?_⟩
    have hMw : ∀ z ∈ Submission.BoseGases.acube ℓ, |w z| ≤ max C₀ 0 := by
      intro z hz
      refine le_trans ?_ (le_max_left _ _)
      simpa [Real.norm_eq_abs] using hC₀ z hz
    have hsub : Submission.BoseGases.dlBox ℓ d u ⊆ Submission.BoseGases.acube ℓ :=
      Work.SmallBoxSliding.dlBox_subset_acube ℓ d u
    have hfin : (volume : Measure ℝ³) (Submission.BoseGases.dlBox ℓ d u) < ⊤ :=
      Work.SmallBoxSliding.volume_dlBox_lt_top hℓ d u
    have hJ : |∫ z in Submission.BoseGases.dlBox ℓ d u, w z|
        ≤ (max C₀ 0) * Work.SmallBoxSliding.boxMass ℓ d u := by
      have h := MeasureTheory.norm_setIntegral_le_of_norm_le_const
        (μ := (volume : Measure ℝ³)) (f := w)
        (s := Submission.BoseGases.dlBox ℓ d u) (C := max C₀ 0) hfin
        (fun z hz => by rw [Real.norm_eq_abs]; exact hMw z (hsub hz))
      rwa [Real.norm_eq_abs, ← Work.SmallBoxSliding.boxMass_eq_measureReal] at h
    have hVnn : 0 ≤ Work.SmallBoxSliding.boxMass ℓ d u := by
      rw [Work.SmallBoxSliding.boxMass_eq_measureReal]
      exact ENNReal.toReal_nonneg
    rcases eq_or_lt_of_le hVnn with hV0 | hVpos
    · -- degenerate box: the normalisation factor `0⁻¹ = 0`
      rw [← hV0, inv_zero, zero_mul, abs_zero]
      exact le_max_right _ _
    · rw [abs_mul, abs_inv, abs_of_pos hVpos]
      refine le_trans (mul_le_mul_of_nonneg_left hJ (inv_nonneg.mpr hVnn)) ?_
      have key : (Work.SmallBoxSliding.boxMass ℓ d u)⁻¹ * max C₀ 0 *
          Work.SmallBoxSliding.boxMass ℓ d u = max C₀ 0 := by
        rw [mul_assoc, mul_comm (max C₀ 0) (Work.SmallBoxSliding.boxMass ℓ d u),
          ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hVpos), one_mul]
      rw [← mul_assoc, key]

end Work.BoseFixB1S.corrMarg
