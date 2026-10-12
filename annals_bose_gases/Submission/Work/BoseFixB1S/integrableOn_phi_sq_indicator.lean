import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.BoxQIndCore
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.integrableOn_phi_sq_indicator`

`x ↦ Φ(x)² · c·1_A(x i)` is integrable over the centred box `abox N ℓ`.

Both factors are bounded on the compact box: `Φ` is continuous hence bounded by
`B` (`IsCompact.exists_bound_of_continuousOn`), and the indicator factor by `|c|`.
Since `abox N ℓ` has finite volume (`abox_lt_top`), the product is dominated by
the constant `B²·|c|` and `Integrable.mono'` applies.  (The hypothesis
`A ⊆ acube ℓ` is not needed for this: the bound on `1_A` is `1` regardless.)
-/

namespace Work.BoseFixB1S

open MeasureTheory

set_option linter.unusedVariables false in
theorem integrableOn_phi_sq_indicator {N : ℕ} {ℓ c : ℝ}
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hℓ : 0 < ℓ) (hA : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (i : Fin N)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        (Φ x) ^ 2 * (c * A.indicator (fun _ => (1 : ℝ)) (x i)))
      (Submission.BoseGases.abox N ℓ)
      (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)) := by
  -- `Φ` is bounded on the compact box.
  obtain ⟨B, hB⟩ := (Submission.BoseGases.abox_compact N hℓ).exists_bound_of_continuousOn
    (s := Submission.BoseGases.abox N ℓ) (f := Φ) hΦc.continuousOn
  -- the box has finite volume
  have hfin : (volume : Measure (Submission.BoseGases.X N))
      (Submission.BoseGases.abox N ℓ) < ⊤ :=
    Submission.BoseGases.abox_lt_top N ℓ hℓ.le
  have _instFinite : IsFiniteMeasure
      ((volume : Measure (Submission.BoseGases.X N)).restrict (Submission.BoseGases.abox N ℓ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  refine Integrable.mono' (integrable_const (B ^ 2 * |c|)) ?_ ?_
  · -- measurability: `Φ²` times the indicator composed with the `i`-th coordinate
    exact (hΦc.measurable.pow_const 2).aestronglyMeasurable.mul
      ((measurable_const.mul ((measurable_const.indicator hA).comp
        (measurable_pi_apply i)))).aestronglyMeasurable
  · -- a.e. domination by the constant `B²·|c|`
    filter_upwards [self_mem_ae_restrict (Submission.BoseGases.abox_measurable N ℓ)] with x hx
    have hΦx : ‖Φ x‖ ≤ B := hB x hx
    have hid : ‖A.indicator (fun _ => (1 : ℝ)) (x i)‖ ≤ 1 := by
      by_cases h : x i ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
    have hbnd : ‖c * A.indicator (fun _ => (1 : ℝ)) (x i)‖ ≤ |c| := by
      calc ‖c * A.indicator (fun _ => (1 : ℝ)) (x i)‖
          = |c| * ‖A.indicator (fun _ => (1 : ℝ)) (x i)‖ := by
            rw [norm_mul, Real.norm_eq_abs]
        _ ≤ |c| * 1 := mul_le_mul_of_nonneg_left hid (abs_nonneg c)
        _ = |c| := mul_one _
    rw [norm_mul, norm_pow]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hΦx 2) hbnd (norm_nonneg _) (sq_nonneg B)

end Work.BoseFixB1S
