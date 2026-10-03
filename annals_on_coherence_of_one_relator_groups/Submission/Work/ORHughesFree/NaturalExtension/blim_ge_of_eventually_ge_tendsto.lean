import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.blim_of_tendsto

namespace Work.ORHughesFree.NaturalExtension

/-- If a bounded sequence `f` eventually dominates a bounded sequence `g` that converges to `y`,
then the ultralimit of `f` along an ultrafilter above `atTop` is at least `y`.

Proof sketch: `blim ω f = sSup S` with `S = {r | {i | r ≤ f i} ∈ ω}`; `S` is bounded above by `M`,
and for every `r < y` the set `{i | g i ≤ f i} ∩ {i | r ≤ g i}` is in `atTop`, hence in `ω` by
`hω`, showing `r ∈ S`; so `y ≤ sSup S`. -/
theorem blim_ge_of_eventually_ge_tendsto (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ Filter.atTop)
    {f g : ℕ → ℝ} {M M' y : ℝ} (hf : ∀ i, |f i| ≤ M) (hg : ∀ i, |g i| ≤ M')
    (hgt : Filter.Tendsto g Filter.atTop (nhds y))
    (h : ∀ᶠ i in Filter.atTop, g i ≤ f i) : y ≤ blim ω f := by
  rw [blim]
  -- `S` is bounded above by `M`, because it is `ω`-large for each of its elements.
  have hbdd : BddAbove {r : ℝ | {i | r ≤ f i} ∈ ω} := by
    refine ⟨M, fun r hr => ?_⟩
    obtain ⟨i, hi⟩ := Filter.nonempty_of_mem (f := (ω : Filter ℕ)) hr
    exact le_trans hi (abs_le.mp (hf i)).2
  -- Every `r < y` belongs to `S`: eventually `r ≤ g i ≤ f i`.
  have hmem : ∀ r : ℝ, r < y → {i : ℕ | r ≤ f i} ∈ (ω : Filter ℕ) := by
    intro r hr
    have hε : 0 < (y - r) / 2 := by linarith
    have hgb : ∀ᶠ i in Filter.atTop, r ≤ g i := by
      filter_upwards [hgt.eventually (Metric.ball_mem_nhds y hε)] with i hi
      rw [Real.dist_eq] at hi
      linarith [(abs_lt.mp hi).1]
    have hfg : ∀ᶠ i in Filter.atTop, r ≤ f i := by
      filter_upwards [hgb, h] with i hig hif
      exact le_trans hig hif
    exact hω hfg
  -- Hence each `z < y` is strictly below `sSup S`, so `y ≤ sSup S`.
  refine le_of_forall_lt fun z hz => ?_
  have hr : (z + y) / 2 < y := by linarith
  have hzr : z < (z + y) / 2 := by linarith
  have hle := le_csSup hbdd (hmem ((z + y) / 2) hr)
  linarith

end Work.ORHughesFree.NaturalExtension
