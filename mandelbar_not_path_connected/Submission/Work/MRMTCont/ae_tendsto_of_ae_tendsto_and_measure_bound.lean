import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMTCont

open MeasureTheory Filter
open scoped ENNReal Topology

/-- **A Borel–Cantelli / `ae_tendsto` transfer lemma.**

If `g · z → w z` for almost every `z`, if `a → 0`, and if the `j`-th "bad set"
`{z | a j < ‖f j z - g j z‖}` has measure at most `c j` with `∑' j, c j` finite,
then also `f · z → w z` for almost every `z`.

Indeed, by Borel–Cantelli almost every `z` lies in only finitely many bad sets,
so `‖f j z - g j z‖ ≤ a j` for all large `j`; since `a j → 0` the squeeze theorem
gives `f j z - g j z → 0`, and `f j z = g j z + (f j z - g j z)`. -/
theorem ae_tendsto_of_ae_tendsto_and_measure_bound {f g : ℕ → ℂ → ℂ} {w : ℂ → ℂ} {a : ℕ → ℝ}
    {c : ℕ → ENNReal}
    (hg : ∀ᶠ z in (MeasureTheory.ae ((MeasureTheory.volume : MeasureTheory.Measure ℂ))),
      Filter.Tendsto (fun j => g j z) Filter.atTop (nhds (w z)))
    (ha : Filter.Tendsto a Filter.atTop (nhds 0))
    (hc : (tsum fun j => c j) ≠ ⊤)
    (hmeas : ∀ j, (MeasureTheory.volume : MeasureTheory.Measure ℂ)
      {z : ℂ | a j < ‖f j z - g j z‖} ≤ c j) :
    ∀ᶠ z in (MeasureTheory.ae ((MeasureTheory.volume : MeasureTheory.Measure ℂ))),
      Filter.Tendsto (fun j => f j z) Filter.atTop (nhds (w z)) := by
  -- The total measure of the bad sets is finite, since each one is bounded by `c j`.
  have hsum : (∑' j, (MeasureTheory.volume : MeasureTheory.Measure ℂ)
        {z : ℂ | a j < ‖f j z - g j z‖}) ≠ ⊤ := by
    intro htop
    have hle : (∑' j, (MeasureTheory.volume : MeasureTheory.Measure ℂ)
        {z : ℂ | a j < ‖f j z - g j z‖}) ≤ ∑' j, c j :=
      ENNReal.tsum_le_tsum fun j => hmeas j
    rw [htop] at hle
    exact hc (top_le_iff.mp hle)
  -- Borel–Cantelli: a.e. `z` lies in only finitely many bad sets.
  have hbc := MeasureTheory.ae_eventually_notMem
    (μ := (MeasureTheory.volume : MeasureTheory.Measure ℂ)) hsum
  filter_upwards [hbc, hg] with z hz hgz
  -- `z` is eventually outside every bad set, i.e. `‖f j z - g j z‖ ≤ a j`.
  have hz' : ∀ᶠ j in atTop, ‖f j z - g j z‖ ≤ a j := by
    filter_upwards [hz] with j hj
    exact le_of_not_gt hj
  -- Squeeze `‖f j z - g j z‖` between `0` and `a j → 0`.
  have hb : Tendsto (fun j => ‖f j z - g j z‖) atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ha
      (Filter.Eventually.of_forall fun j => norm_nonneg _) hz'
  have hb2 : Tendsto (fun j => f j z - g j z) atTop (nhds 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa using hb)
  -- `f j z = g j z + (f j z - g j z)` and both summands converge.
  have h2 : Tendsto (fun j => g j z + (f j z - g j z)) atTop (nhds (w z + 0)) :=
    hgz.add hb2
  simpa using h2

end Work.MRMTCont
