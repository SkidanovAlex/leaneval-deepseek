import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixGlue.Residuals
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixGlue.Pot

open MeasureTheory
open scoped BigOperators

set_option linter.unusedVariables false

/-!
# `Work.BoseFixGlue.Pot.integrable_abox_pair_domination`

Integrability of the FS-type pair domination

`x ↦ (Φ x)² * (A + B * Σ_{q ∈ pairSet N} |v (x q.1 - x q.2)|)`

for a smooth state `Φ` supported in the centred box `abox N L` and `v ∈ L¹(ℝ³)`.

The substance is: on the (finite-measure) box `abox N L`, each pair term
`(Φ x)² * |v (x q.1 - x q.2)|` is integrable — `|v (· q.1 - · q.2)|` is integrable on the box by
`Submission.BoseGases.integrableOn_abs_sub_abox`, and multiplying by the bounded measurable
factor `(Φ x)²` preserves integrability (`Integrable.bdd_mul`) — and the constant part
`(Φ x)²` is integrable on the compact box.  The finite sum and the constants `A`, `B` are then
handled by hand, and the passage from the box to the whole space uses that `Φ` vanishes off the
box (its topological support is contained in `abox N L`).
-/

/-- **The pair-dominated weight is integrable.**  For `v ∈ L¹(ℝ³)` and a smooth `Φ` supported
in the centred box `abox N L`, the function
`x ↦ (Φ x)² * (A + B * Σ_{q ∈ pairSet N} |v (x q.1 - x q.2)|)` is integrable. -/
theorem integrable_abox_pair_domination {N : ℕ} {v : EuclideanSpace ℝ (Fin 3) → ℝ} {L A B : ℝ}
    (hL : 0 < L) (hv1 : MeasureTheory.MemLp v 1)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hsupp : tsupport Φ ⊆ Submission.BoseGases.abox N L) :
    MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X N =>
        (Φ x) ^ 2 *
          (A + B * ∑ q ∈ Submission.BoseGases.pairSet N, |v (x q.1 - x q.2)|))
      MeasureTheory.volume := by
  have hΦc : Continuous Φ := hΦ.continuous
  have hvInt : Integrable v := MeasureTheory.memLp_one_iff_integrable.mp hv1
  have hbox : MeasurableSet (Submission.BoseGases.abox N L) :=
    Submission.BoseGases.abox_measurable N L
  -- `Φ` vanishes off the box
  have hΦzero : ∀ x : Submission.BoseGases.X N, x ∉ Submission.BoseGases.abox N L → Φ x = 0 := by
    intro x hx
    by_contra hne
    exact hx (hsupp (subset_tsupport Φ hne))
  -- a uniform bound for `Φ²` on the box
  obtain ⟨C, hC⟩ := (Submission.BoseGases.abox_compact N hL).exists_bound_of_continuousOn
    ((hΦc.pow 2).continuousOn)
  -- the constant part is integrable on the (compact) box
  have hconst : Integrable (fun x : Submission.BoseGases.X N => (Φ x) ^ 2)
      (volume.restrict (Submission.BoseGases.abox N L)) :=
    ContinuousOn.integrableOn_compact (Submission.BoseGases.abox_compact N hL)
      ((hΦc.pow 2).continuousOn)
  -- every pair term is integrable on the box
  have hpair : ∀ q ∈ Submission.BoseGases.pairSet N,
      Integrable (fun x : Submission.BoseGases.X N => (Φ x) ^ 2 * |v (x q.1 - x q.2)|)
        (volume.restrict (Submission.BoseGases.abox N L)) := by
    intro q hq
    have hne : q.1 ≠ q.2 := by
      simpa only [Submission.BoseGases.pairSet, Finset.mem_filter, Finset.mem_univ,
        true_and] using hq
    have habs : Integrable (fun x : Submission.BoseGases.X N => |v (x q.1 - x q.2)|)
        (volume.restrict (Submission.BoseGases.abox N L)) :=
      Submission.BoseGases.integrableOn_abs_sub_abox hL hvInt q.1 q.2 hne
    refine habs.bdd_mul (c := C) ((hΦc.pow 2).aestronglyMeasurable) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hbox] with x hx
    have h1 : ‖(Φ x) ^ 2‖ ≤ C := hC x hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Φ x))] using h1
  -- hence their finite sum
  have hsum : Integrable
      (fun x : Submission.BoseGases.X N =>
        ∑ q ∈ Submission.BoseGases.pairSet N, (Φ x) ^ 2 * |v (x q.1 - x q.2)|)
      (volume.restrict (Submission.BoseGases.abox N L)) :=
    integrable_finsetSum _ (fun q hq => hpair q hq)
  -- the whole box integrand, with the constants and the overall `Φ²`-factor pulled out
  have hmain : Integrable
      (fun x : Submission.BoseGases.X N => A * (Φ x) ^ 2 + B *
        (∑ q ∈ Submission.BoseGases.pairSet N, (Φ x) ^ 2 * |v (x q.1 - x q.2)|))
      (volume.restrict (Submission.BoseGases.abox N L)) :=
    (hconst.const_mul A).add (hsum.const_mul B)
  have hae : (fun x : Submission.BoseGases.X N =>
        (Φ x) ^ 2 *
          (A + B * ∑ q ∈ Submission.BoseGases.pairSet N, |v (x q.1 - x q.2)|))
      =ᵐ[volume.restrict (Submission.BoseGases.abox N L)]
      (fun x : Submission.BoseGases.X N => A * (Φ x) ^ 2 + B *
        (∑ q ∈ Submission.BoseGases.pairSet N, (Φ x) ^ 2 * |v (x q.1 - x q.2)|)) := by
    filter_upwards with x
    have hsplit : (∑ q ∈ Submission.BoseGases.pairSet N, (Φ x) ^ 2 * |v (x q.1 - x q.2)|)
        = (Φ x) ^ 2 * (∑ q ∈ Submission.BoseGases.pairSet N, |v (x q.1 - x q.2)|) := by
      rw [Finset.mul_sum]
    rw [hsplit]
    ring
  have hOn : IntegrableOn (fun x : Submission.BoseGases.X N =>
        (Φ x) ^ 2 *
          (A + B * ∑ q ∈ Submission.BoseGases.pairSet N, |v (x q.1 - x q.2)|))
      (Submission.BoseGases.abox N L) volume := hmain.congr hae.symm
  -- pass from the box to the whole space: the integrand vanishes outside the box
  refine ((MeasureTheory.integrable_indicator_iff hbox).mpr hOn).congr ?_
  filter_upwards with x
  by_cases hx : x ∈ Submission.BoseGases.abox N L
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx]
    simp [hΦzero x hx]

end Work.BoseFixGlue.Pot
