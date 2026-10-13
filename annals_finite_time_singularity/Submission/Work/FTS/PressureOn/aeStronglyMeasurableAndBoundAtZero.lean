import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PressureOn.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Topology

namespace Work.FTS.PressureOn

/-- **The time-zero slices inherit the `(0,S]` bound and measurability** (piece of
`tendsto_timeDeriv_physVel`).

If the slices `ω · s`, `s ∈ (0,S]`, are uniformly bounded by `M ≥ 0` and a.e. strongly
measurable, and every curve `s ↦ ω x s` is continuous on `[0,S]`, then the same bound and
measurability hold at `s = 0`.

Recipe: for the bound, `ContinuousOn (fun s => ω x s) (Icc 0 S)` restricts to
`ContinuousWithinAt … (Ioc 0 S) 0`, so `Tendsto (fun s => ω x s) (𝓝[Ioc 0 S] 0) (𝓝 (ω x 0))`
(`ContinuousWithinAt.mono`) and `le_of_tendsto` against the constant bound (which holds on
`Ioc 0 S`) gives `‖ω x 0‖ ≤ M`; the filter is nontrivial because `hS : 0 < S`.  For the
measurability, use the null sequence `s n = S/(n+2) ∈ (0,S]` and
`aestronglyMeasurable_of_tendsto_ae Filter.atTop` with the pointwise convergence
`ω z (s n) → ω z 0` from `hcontω`. -/
theorem aeStronglyMeasurableAndBoundAtZero {ω : R3 → ℝ → R3} {S M : ℝ}
    (hS : 0 < S) (hM : 0 ≤ M)
    (hbdd : ∀ s ∈ Set.Ioc 0 S, ∀ x, ‖ω x s‖ ≤ M)
    (hmeas : ∀ s ∈ Set.Ioc 0 S,
      MeasureTheory.AEStronglyMeasurable (fun z => ω z s) MeasureTheory.volume)
    (hcontω : ∀ x, ContinuousOn (fun s => ω x s) (Set.Icc 0 S)) :
    (∀ x, ‖ω x 0‖ ≤ M) ∧
      MeasureTheory.AEStronglyMeasurable (fun z => ω z 0) MeasureTheory.volume := by
  have h0mem : (0 : ℝ) ∈ Set.Icc 0 S := ⟨le_refl 0, hS.le⟩
  -- the null sequence `s n = S/(n+2)` sits in `(0,S]`, tends to `0` and stays in `[0,S]`
  have hsn_mem : ∀ n : ℕ, S / ((n : ℝ) + 2) ∈ Set.Ioc 0 S := by
    intro n
    refine ⟨div_pos hS (by positivity), ?_⟩
    refine div_le_self hS.le ?_
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hg : Tendsto (fun n : ℕ => (n : ℝ) + 2) Filter.atTop Filter.atTop := by
    simpa [add_comm] using
      (Tendsto.add_atTop (tendsto_const_nhds (x := (2 : ℝ))) tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => (2 : ℝ) + (n : ℝ)) Filter.atTop Filter.atTop)
  have hsn_tend : Tendsto (fun n : ℕ => S / ((n : ℝ) + 2)) Filter.atTop
      (𝓝[Set.Icc 0 S] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨tendsto_const_nhds.div_atTop hg, ?_⟩
    exact Eventually.of_forall fun n => Set.Ioc_subset_Icc_self (hsn_mem n)
  constructor
  · -- the bound: pass to the limit along `s n → 0` in `‖ω x ·‖ ≤ M`
    intro x
    have hseq : Tendsto (fun n : ℕ => ‖ω x (S / ((n : ℝ) + 2))‖) Filter.atTop
        (𝓝 ‖ω x 0‖) := by
      have h := (((hcontω x) 0 h0mem).tendsto.comp hsn_tend).norm
      simpa only [Function.comp_def] using h
    exact le_of_tendsto_of_tendsto' hseq
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => M) Filter.atTop (𝓝 M))
      (fun n => hbdd _ (hsn_mem n) x)
  · -- the measurability: an a.e. pointwise limit of a.e. strongly measurable maps
    refine aestronglyMeasurable_of_tendsto_ae Filter.atTop
      (fun n => hmeas _ (hsn_mem n)) ?_
    refine Eventually.of_forall fun z => ?_
    have h := ((hcontω z) 0 h0mem).tendsto.comp hsn_tend
    simpa only [Function.comp_def] using h

end Work.FTS.PressureOn
