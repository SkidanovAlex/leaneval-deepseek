import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.boxConstCalibB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.integrableOn_chiSmallB_pow_dlBox`

Box-restricted integrability of a power of the localised cutoff
`χ_{B(u)} = chiSmallB M ℓ d u`: for every `k : ℕ`,

    IntegrableOn (fun x => (χ_{B(u)}(x))^k) (B(u)) ,   B(u) = dlBox ℓ d u .

No support hypothesis is used (in particular the statement is valid for `k = 0`, where the
integrand is the constant `1`): `dlBox ℓ d u ⊆ acube ℓ` is a set of finite measure
(`acube_lt_top`), while `χ_{B(u)}` is continuous (`chiScale_continuous`, `chiSmall_continuous`)
and **globally bounded**:

    |χ_{B(u)}(x)| = |χ(x/ℓ)| · |χ_M(x/(ℓd) − u)| ≤ chiSupAbs · chiSmallDecay M ,

both factors being bounded uniformly — the corpus bump by its absolute sup `chiSupAbs`
(`chiScale_abs_le_sup`), the cosine bump `χ_M` by its decay constant `chiSmallDecay M`
(`chiSmall_decay_coord_le_decay`).  Bounded measurable on a finite-measure set is integrable
(`IntegrableOn.of_bound`).
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixB1S

set_option autoImplicit false

theorem integrableOn_chiSmallB_pow_dlBox {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) (k : ℕ) :
    MeasureTheory.IntegrableOn (fun x : EuclideanSpace ℝ (Fin 3) =>
      (Submission.BoseGases.chiSmallB M ℓ d u x) ^ k) (Submission.BoseGases.dlBox ℓ d u) := by
  -- the integrand is continuous
  have hcont : Continuous (fun x : EuclideanSpace ℝ (Fin 3) =>
      (Submission.BoseGases.chiSmallB M ℓ d u x) ^ k) := by
    refine Continuous.pow ?_ k
    show Continuous (fun x : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.chiScale ℓ x * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u))
    exact (Submission.BoseGases.chiScale_continuous ℓ).mul
      ((Submission.BoseGases.chiSmall_continuous hM).comp (by fun_prop))
  have hmeas : MeasureTheory.AEStronglyMeasurable (fun x : EuclideanSpace ℝ (Fin 3) =>
      (Submission.BoseGases.chiSmallB M ℓ d u x) ^ k)
      ((volume : Measure ℝ³).restrict (Submission.BoseGases.dlBox ℓ d u)) :=
    hcont.aestronglyMeasurable
  refine MeasureTheory.IntegrableOn.of_bound (μ := (volume : Measure ℝ³)) ?_ hmeas
    ((Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) ^ k) ?_
  · -- `dlBox ℓ d u ⊆ acube ℓ` has finite measure
    exact lt_of_le_of_lt (measure_mono (fun x hx => hx.1))
      (Submission.BoseGases.acube_lt_top ℓ hℓ.le)
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_pow]
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ k
    change |Submission.BoseGases.chiScale ℓ x
      * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)| ≤
      Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M
    rw [abs_mul]
    exact mul_le_mul (Submission.BoseGases.chiScale_abs_le_sup ℓ x)
      (Submission.BoseGases.chiSmall_decay_coord_le_decay hM _) (abs_nonneg _)
      Submission.BoseGases.chiSupAbs_nonneg

end Work.BoseFixB1S
