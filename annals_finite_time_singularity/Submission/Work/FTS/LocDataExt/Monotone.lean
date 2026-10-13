/-
# `Work.FTS.LocDataExt.Monotone` — monotonicity of `ℋ^k` in the order

The interior class `Work.FTS.Nonlin.RegQ α k` is monotone in `k`, so the order-`5` statement
of the localised datum (`LocG5.lean`, the design's `N9-ext`) subsumes the order-`4` one which
`galerkin_bound` consumes.  This module records that, together with the underlying pointwise
monotonicity of the `ℋ^k`-integrand.

The regularity hypothesis `SmoothQuad f` in `HkMem_mono` is *not* removable: the `ℋ^k`-integrand
involves `deriv` with a parameter, so `HkMem α m f` says nothing about the measurability of the
level-`m` slices of an arbitrary `f` (see the discussion in
`Submission/Work/FTS/LocData/HkMem_of_majorant.lean`); for `SmoothQuad f` the integrand is
continuous on the open quadrant and `HkMem_of_majorant` applies with the order-`k` integrand
itself as majorant.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.LocDataExt.Defs
import Submission.Work.FTS.LocData.Main
import Submission.Work.FTS.Vocab

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocDataExt

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- **The `ℋ^k`-integrand is monotone in the order**: every summand is a square and the index
sets grow with `k`. -/
theorem HkIntegrand_mono {α : ℝ} {m k : ℕ} (hmk : m ≤ k) (f : Fn) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α m f z θ ≤ Work.Spaces.HkIntegrand α k f z θ := by
  rw [Work.Spaces.HkIntegrand, Work.Spaces.HkIntegrand]
  refine add_le_add ?_ ?_
  · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
      (fun i _ _ => sq_nonneg _)
  · have hinner : ∀ i : ℕ,
        (∑ j ∈ Finset.range (m + 1),
          (if 1 ≤ i ∧ i + j ≤ m then
            (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
        ≤ (∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) := by
      intro i
      refine le_trans (Finset.sum_le_sum (fun j _ => ?_))
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
          (fun j _ _ => ?_))
      · by_cases hc : 1 ≤ i ∧ i + j ≤ m
        · rw [if_pos hc, if_pos ⟨hc.1, le_trans hc.2 hmk⟩]
        · rw [if_neg hc]
          by_cases h2 : 1 ≤ i ∧ i + j ≤ k
          · rw [if_pos h2]; exact sq_nonneg _
          · rw [if_neg h2]
      · by_cases h2 : 1 ≤ i ∧ i + j ≤ k
        · rw [if_pos h2]; exact sq_nonneg _
        · rw [if_neg h2]
    calc (∑ i ∈ Finset.range (m + 1),
          (∑ j ∈ Finset.range (m + 1),
            (if 1 ≤ i ∧ i + j ≤ m then
              (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)))
        ≤ ∑ i ∈ Finset.range (m + 1),
            (∑ j ∈ Finset.range (k + 1),
              (if 1 ≤ i ∧ i + j ≤ k then
                (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) :=
          Finset.sum_le_sum (fun i _ => hinner i)
      _ ≤ ∑ i ∈ Finset.range (k + 1),
            (∑ j ∈ Finset.range (k + 1),
              (if 1 ≤ i ∧ i + j ≤ k then
                (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_subset_range.mpr (by omega)) ?_
          intro i _ _
          exact Finset.sum_nonneg (fun j _ => by
            by_cases h2 : 1 ≤ i ∧ i + j ≤ k
            · rw [if_pos h2]; exact sq_nonneg _
            · rw [if_neg h2])

/-- **`ℋ^k`-membership is monotone in the order** for functions of the interior class
`SmoothQuad`. -/
theorem HkMem_mono {α : ℝ} {m k : ℕ} (hmk : m ≤ k) {f : Fn}
    (hf : Work.FTS.LocData.SmoothQuad f) (hk : Work.Spaces.HkMem α k f) :
    Work.Spaces.HkMem α m f :=
  Work.FTS.LocData.HkMem_of_majorant (f := f)
    (M := fun z θ => Work.Spaces.HkIntegrand α k f z θ) α m
    (Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad α m f hf)
    hk.1 hk.2 (fun z _ θ _ => HkIntegrand_mono hmk f z θ)

/-- **The interior class `RegQ` is monotone in the order.** -/
theorem RegQ_mono {α : ℝ} {m k : ℕ} (hmk : m ≤ k) {f : Fn}
    (hf : Work.FTS.Nonlin.RegQ α k f) : Work.FTS.Nonlin.RegQ α m f :=
  ⟨hf.1, HkMem_mono hmk hf.1 hf.2.1, fun a b hab => hf.2.2 a b (le_trans hab hmk)⟩

end Work.FTS.LocDataExt
