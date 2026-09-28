import Mathlib
import Submission.Work.Milnor.Clutch

namespace Work.Milnor

open scoped Manifold ContDiff Topology
open Submission.Milnor

/-- The graph of `clutchMap k` over the open set `clutchOpens = {x ≠ 0}` is closed in
`MSpace × MSpace`.

The point is that the only way to leave `clutchOpens` is to approach the origin of the `ℝ⁴`
factor, where the first component `invBase x = x/‖x‖²` of `clutchMap k` blows up: on the graph the
product `‖z.1.1‖ * ‖z.2.1‖` is identically `1`, and the set where it is `≥ 1` is closed and avoids
the origin.  Hence any limit point of the graph lies again on the graph. -/
theorem graph_closed_clutchMap (k : ℤ) :
    IsClosed {z : MSpace × MSpace | z.1 ∈ (clutchOpens : Set MSpace) ∧
      z.2 = clutchMap k z.1} := by
  set S : Set (MSpace × MSpace) :=
    {z : MSpace × MSpace | z.1 ∈ (clutchOpens : Set MSpace) ∧ z.2 = clutchMap k z.1}
    with hS
  rw [← closure_subset_iff_isClosed]
  intro z hz
  -- The closed set `A = {‖z.1.1‖ * ‖z.2.1‖ ≥ 1}` contains the graph and misses `{z.1.1 = 0}`.
  have hcontF : Continuous (fun z : MSpace × MSpace => ‖z.1.1‖ * ‖z.2.1‖) := by fun_prop
  have hAclosed : IsClosed {z : MSpace × MSpace | 1 ≤ ‖z.1.1‖ * ‖z.2.1‖} :=
    isClosed_le continuous_const hcontF
  have hSA : S ⊆ {z : MSpace × MSpace | 1 ≤ ‖z.1.1‖ * ‖z.2.1‖} := by
    intro w hw
    rw [hS] at hw
    obtain ⟨hw1, hw2⟩ := hw
    have hw1' : w.1.1 ≠ 0 := mem_clutchOpens.mp hw1
    have hw21 : w.2.1 = invBase w.1.1 := by rw [hw2]; rfl
    change 1 ≤ ‖w.1.1‖ * ‖w.2.1‖
    rw [hw21, norm_invBase]
    exact le_of_eq (mul_inv_cancel₀ (norm_ne_zero_iff.mpr hw1')).symm
  have hzA : 1 ≤ ‖z.1.1‖ * ‖z.2.1‖ := closure_minimal hSA hAclosed hz
  -- hence `z.1` lies in `clutchOpens`
  have hpos : 0 < ‖z.1.1‖ := by
    rcases eq_or_lt_of_le (norm_nonneg z.1.1) with h | h
    · rw [← h, zero_mul] at hzA
      linarith
    · exact h
  have hz1 : z.1.1 ≠ 0 := norm_pos_iff.mp hpos
  have hz1mem : z.1 ∈ (clutchOpens : Set MSpace) := mem_clutchOpens.mpr hz1
  -- `clutchMap k` is continuous at `z.1`, so `w ↦ (w.1, clutchMap k w.1)` is continuous at `z`
  have hcontOn : ContinuousOn (clutchMap k) (clutchOpens : Set MSpace) :=
    (contMDiffOn_clutchMap k).continuousOn
  have hcat : ContinuousAt (clutchMap k) z.1 :=
    (hcontOn.continuousWithinAt hz1mem).continuousAt (clutchOpens.2.mem_nhds hz1mem)
  have hcont : ContinuousAt (fun w : MSpace × MSpace => (w.1, clutchMap k w.1)) z :=
    continuousAt_fst.prodMk (hcat.comp continuousAt_fst)
  have htend1 : Filter.Tendsto id (𝓝[S] z) (𝓝 z) :=
    continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
  have htend2 : Filter.Tendsto (fun w : MSpace × MSpace => (w.1, clutchMap k w.1)) (𝓝[S] z)
      (𝓝 (z.1, clutchMap k z.1)) := hcont.tendsto.mono_left nhdsWithin_le_nhds
  -- on `S` the map `w ↦ (w.1, clutchMap k w.1)` is the identity
  have hev : (fun w : MSpace × MSpace => (w.1, clutchMap k w.1)) =ᶠ[𝓝[S] z] id := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    rw [hS] at hw
    exact Prod.ext rfl hw.2.symm
  -- uniqueness of limits in a T2 space gives `z = (z.1, clutchMap k z.1)`
  have hz' : z = (z.1, clutchMap k z.1) := by
    have hneBot : (𝓝[S] z).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hz
    exact tendsto_nhds_unique htend1 (Filter.Tendsto.congr' hev htend2)
  have hz2 : z.2 = clutchMap k z.1 := by
    have h := congrArg Prod.snd hz'
    simpa using h
  rw [hS]
  exact ⟨hz1mem, hz2⟩

end Work.Milnor
