import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1.BoxTauGen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.BoxPairIntGenC2.AuxIntegrable` — real-analysis support for the C² window

Three self-contained real-analysis facts used by the box `τ`-commutation lemmas of
`Work.BoseFixB1.BoxPairIntGenC2`.  Nothing here mentions the `τ`-operators; the whole module is
about a measurable `A ⊆ acube ℓ` (hence of finite measure) and a continuous kernel.

* `integrable_uncurry_prod_restrict` — a continuous `f : ℝ³ → ℝ³ → ℝ` is `(volume.restrict A).prod
  (volume.restrict A)`-integrable (via `A ×ˢ A ⊆ acube ℓ ×ˢ acube ℓ` and compactness);
* `integrable_parametricIntegral` — consequently the parametric integral
  `w ↦ ∫_{z∈A} f z w` is `Integrable` on `volume.restrict A` (`Integrable.integral_prod_right`);
* `setIntegral_setIntegral_swap` — the iterated `A`-integrals may be exchanged
  (`MeasureTheory.integral_integral_swap`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1.BoxPairIntGenC2

open _root_.BoseGases Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- A continuous kernel `f` is integrable for the product of the restricted measures on `A`,
whenever `A ⊆ acube ℓ` (so that `A ×ˢ A` sits in a compact set). -/
theorem integrable_uncurry_prod_restrict {ℓ : ℝ} {A : Set E3}
    (hℓ : 0 < ℓ) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {f : E3 → E3 → ℝ} (hf : Continuous (Function.uncurry f)) :
    Integrable (Function.uncurry f) ((volume.restrict A).prod (volume.restrict A)) := by
  have hK : IsCompact (Submission.BoseGases.acube ℓ) := Submission.BoseGases.acube_compact hℓ
  have h1 : IntegrableOn (Function.uncurry f)
      (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ) volume :=
    ContinuousOn.integrableOn_compact (hK.prod hK) hf.continuousOn
  have h2 : IntegrableOn (Function.uncurry f) (A ×ˢ A) volume :=
    h1.mono_set (Set.prod_mono hAc hAc)
  have hvol : (volume : Measure (E3 × E3)) = (volume : Measure E3).prod (volume : Measure E3) :=
    Measure.volume_eq_prod _ _
  rw [Measure.prod_restrict, ← hvol]
  exact h2.integrable

/-- The parametric integral `w ↦ ∫_{z ∈ A} f z w` of a continuous kernel is integrable on `A`. -/
theorem integrable_parametricIntegral {ℓ : ℝ} {A : Set E3}
    (hℓ : 0 < ℓ) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {f : E3 → E3 → ℝ} (hf : Continuous (Function.uncurry f)) :
    Integrable (fun w => ∫ z in A, f z w) (volume.restrict A) :=
  (integrable_uncurry_prod_restrict hℓ hAc hf).integral_prod_right

/-- The two `A`-integrals of an integrable kernel commute. -/
theorem setIntegral_setIntegral_swap {A : Set E3} {f : E3 → E3 → ℝ}
    (hf : Integrable (Function.uncurry f) ((volume.restrict A).prod (volume.restrict A))) :
    (∫ w in A, ∫ z in A, f w z) = ∫ w in A, ∫ z in A, f z w := by
  rw [integral_integral_swap hf]

end Work.BoseFixB1.BoxPairIntGenC2
