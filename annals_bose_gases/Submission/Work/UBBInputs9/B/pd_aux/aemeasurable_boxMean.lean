import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.UBBInputs9.B.pd_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `u`-measurability of the sliding box mean `boxMean`

`boxMean ℓ d u Φ = (boxMass ℓ d u)⁻¹ * ∫_{B(u)} Φ(z,·)` is the coefficient of the
box projection `P_{B(u)}Φ` (see `pd_defs.boxMean`).  Here we show that, for
continuous `Φ`, it is an a.e.-measurable function of the sliding centre `u`.

Both factors are parametric integrals over the `u`-dependent domain `B(u)`, so the
proof is a single joint-measurability argument:

* `boxInd ℓ d u x = 1_{B(u)}(x)` is jointly measurable in `(u,x)`, because
  `{(u,x) | x ∈ B(u)} = {x ∈ acube ℓ} ∩ {x - (ℓd)•u ∈ acube (ℓd)}` is the
  intersection of two closed sets (`pd_aux` re-uses
  `SmallBoxSliding.measurableSet_boxIndSet`);
* `(u,x) ↦ boxInd ℓ d u x * Φ(fun _ => x)` is jointly measurable, hence its
  partial integral in `x` is `StronglyMeasurable` in `u`
  (`MeasureTheory.StronglyMeasurable.integral_prod_right'`), which yields
  measurability of `u ↦ ∫_{B(u)} Φ` via `integral_indicator`, and of `boxMass`
  by taking `Φ = 1`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.UBBInputs9.B.pd_aux

set_option linter.unusedVariables false

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
local notation "X1" => Submission.BoseGases.X 1

/-- The `B(u)`-indicator times the evaluation of `Φ` at the constant configuration equals the
indicator of `Φ ∘ (fun _ => ·)` on `dlBox ℓ d u`. -/
private lemma boxInd_mul_eq_indicator (ℓ d : ℝ) (u : ℝ³) (Φ : X1 → ℝ) :
    (fun z : ℝ³ => Work.SmallBoxSliding.boxInd ℓ d u z * Φ (fun _ => z))
      = (Submission.BoseGases.dlBox ℓ d u).indicator (fun z => Φ (fun _ => z)) := by
  funext z
  by_cases hz : z ∈ Submission.BoseGases.dlBox ℓ d u
  · rw [Work.SmallBoxSliding.boxInd, Set.indicator_of_mem hz, Set.indicator_of_mem hz]
    simp
  · rw [Work.SmallBoxSliding.boxInd, Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]
    simp

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

lemma aemeasurable_boxMean {ℓ d : ℝ} (hℓ : 0 < ℓ) {Φ : Submission.BoseGases.X 1 → ℝ} (hΦ : Continuous Φ) : AEMeasurable (fun u : EuclideanSpace ℝ (Fin 3) => Work.UBBInputs9.B.boxMean ℓ d u Φ) (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) := by
  -- joint measurability of the box indicator
  have hboxInd_meas : Measurable (Function.uncurry (Work.SmallBoxSliding.boxInd ℓ d)) :=
    measurable_uncurry_boxInd ℓ d
  -- measurability of the constant-configuration evaluation of `Φ`
  have hΦf : Measurable (fun z : ℝ³ => Φ (fun _ => z)) :=
    hΦ.measurable.comp (by fun_prop)
  -- joint measurability of the `(u,x)`-integrand
  have hjoint : Measurable (fun p : ℝ³ × ℝ³ =>
      Work.SmallBoxSliding.boxInd ℓ d p.1 p.2 * Φ (fun _ => p.2)) :=
    hboxInd_meas.mul (hΦf.comp measurable_snd)
  -- hence its parametric integral is strongly measurable in `u`
  have hint : StronglyMeasurable (fun u : ℝ³ =>
      ∫ z : ℝ³, Work.SmallBoxSliding.boxInd ℓ d u z * Φ (fun _ => z)) :=
    MeasureTheory.StronglyMeasurable.integral_prod_right' hjoint.stronglyMeasurable
  -- rewrite the whole-space integral as an integral over the moving box `B(u)`
  have hconv : (fun u : ℝ³ => ∫ z : ℝ³,
        Work.SmallBoxSliding.boxInd ℓ d u z * Φ (fun _ => z))
      = fun u : ℝ³ => ∫ z in Submission.BoseGases.dlBox ℓ d u, Φ (fun _ => z) := by
    funext u
    rw [boxInd_mul_eq_indicator ℓ d u Φ]
    exact MeasureTheory.integral_indicator (Work.SmallBoxSliding.measurableSet_dlBox ℓ d u)
  have hF : AEMeasurable (fun u : ℝ³ =>
      ∫ z in Submission.BoseGases.dlBox ℓ d u, Φ (fun _ => z)) (volume : Measure ℝ³) :=
    hconv ▸ hint.aemeasurable
  -- the box volume `boxMass` is measurable, by the same argument with `Φ = 1`
  have hboxMass : AEMeasurable (Work.SmallBoxSliding.boxMass ℓ d) (volume : Measure ℝ³) := by
    have : StronglyMeasurable (fun u : ℝ³ =>
        ∫ z : ℝ³, Work.SmallBoxSliding.boxInd ℓ d u z) :=
      MeasureTheory.StronglyMeasurable.integral_prod_right'
        (f := fun p : ℝ³ × ℝ³ => Work.SmallBoxSliding.boxInd ℓ d p.1 p.2)
        hboxInd_meas.stronglyMeasurable
    exact this.aemeasurable
  -- unfold `boxMean` and combine
  have hfinal : (fun u : ℝ³ => Work.UBBInputs9.B.boxMean ℓ d u Φ)
      = fun u : ℝ³ => (Work.SmallBoxSliding.boxMass ℓ d u)⁻¹ *
          (∫ z in Submission.BoseGases.dlBox ℓ d u, Φ (fun _ => z)) := by
    funext u; rw [Work.UBBInputs9.B.boxMean]
  rw [hfinal]
  exact (hboxMass.inv).mul hF

end Work.UBBInputs9.B.pd_aux
