import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Fatou's lemma on an interval, with explicit sup bound

If `gs n → g` almost everywhere on `(a, b]` and both are bounded by `C ≥ 0` there,
then the (Bochner) integral of `‖g‖ ^ 2` is at most `⨆ n, ∫ ‖gs n‖ ^ 2`.

This is the dominated-convergence specialisation of Fatou's lemma that the
MRTTZ/MRT argument uses to compare a limiting mean square with the supremum of
the approximating ones.
-/

open MeasureTheory Filter
open scoped Topology

set_option linter.unusedVariables false

namespace Work.BMF

theorem fatou_interval {a b : ℝ} (hab : a ≤ b) (C : ℝ) (hC : 0 ≤ C)
    (g : ℝ → ℂ) (gs : ℕ → ℝ → ℂ)
    (hgC : ∀ x ∈ Set.Ioc a b, ‖g x‖ ≤ C)
    (hgsC : ∀ n, ∀ x ∈ Set.Ioc a b, ‖gs n x‖ ≤ C)
    (hgs_meas : ∀ n, AEMeasurable (gs n) (MeasureTheory.volume.restrict (Set.Ioc a b)))
    (hg_meas : AEMeasurable g (MeasureTheory.volume.restrict (Set.Ioc a b)))
    (htend : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Set.Ioc a b)), Filter.Tendsto (fun n => gs n x) Filter.atTop (nhds (g x))) :
    ∫ x in a..b, ‖g x‖ ^ 2 ≤ ⨆ n, ∫ x in a..b, ‖gs n x‖ ^ 2 := by
  -- Rewrite the oriented interval integrals as integrals over `Ioc a b`.
  simp_rw [intervalIntegral.integral_of_le hab]
  -- Measurability of the squared norms.
  have hmeas : ∀ n, AEStronglyMeasurable (fun x => ‖gs n x‖ ^ 2)
      (volume.restrict (Set.Ioc a b)) :=
    fun n => ((hgs_meas n).aestronglyMeasurable.norm).pow 2
  -- The restricted measure of the bounded interval is finite.
  have hfin : IsFiniteMeasure (volume.restrict (Set.Ioc a b)) := by
    rw [isFiniteMeasure_iff, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  -- Hence constants are integrable, providing the dominating function `C ^ 2`.
  have hint : Integrable (fun _ : ℝ => C ^ 2) (volume.restrict (Set.Ioc a b)) :=
    integrable_const_iff.mpr (Or.inr hfin)
  have hbound : ∀ n, ∀ᵐ x ∂(volume.restrict (Set.Ioc a b)),
      ‖(fun x => ‖gs n x‖ ^ 2) x‖ ≤ C ^ 2 := by
    intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have h1 : ‖gs n x‖ ≤ C := hgsC n x hx
    have h2 : ‖gs n x‖ ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact h2
  -- Almost everywhere convergence of the squared norms.
  have hconv : ∀ᵐ x ∂(volume.restrict (Set.Ioc a b)),
      Tendsto (fun n => ‖gs n x‖ ^ 2) atTop (nhds (‖g x‖ ^ 2)) :=
    htend.mono (fun x hx => hx.norm.pow 2)
  -- Dominated convergence: the integrals of `‖gs n‖ ^ 2` converge to that of `‖g‖ ^ 2`.
  have hlim := tendsto_integral_of_dominated_convergence (bound := fun _ => C ^ 2)
    hmeas hint hbound hconv
  -- A convergent sequence is bounded above, so the sup dominates every term.
  have hbdd : BddAbove
      (Set.range (fun n => ∫ x, ‖gs n x‖ ^ 2 ∂(volume.restrict (Set.Ioc a b)))) :=
    (Metric.isBounded_range_of_tendsto _ hlim).bddAbove
  exact le_of_tendsto hlim (Eventually.of_forall (fun n => le_ciSup hbdd n))

end Work.BMF
