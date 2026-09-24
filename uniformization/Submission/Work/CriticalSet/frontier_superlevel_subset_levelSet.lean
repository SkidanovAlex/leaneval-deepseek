import Mathlib
import Submission.Work.CriticalSet.Defs

open scoped Topology Manifold ContDiff
open Filter Set

namespace Work.CriticalSet

/-- **The boundary of a superlevel set of a Green function is contained in the level set.**

For `E` with the weak Green function data at `z₀` and `ε > 0`, any point of `X ∖ {z₀}` lying on the
topological frontier of `{x | ε ≤ E x}` satisfies `E x = ε`.  (Points of the frontier at `z₀` are
excluded because `E` need not be continuous there.)

Proof strategy.  `E` is harmonic, hence continuous, at every point of `punctured z₀`
(`Submission.HarmonicOnXAt.continuousAt`, using `hE.2.1`).  Let `y ∈ punctured z₀` be in the
frontier of `s := {x | ε ≤ E x}`.  If `ε < E y`, continuity gives a neighbourhood of `y` contained in
`s`, so `y ∈ interior s`, contradicting `frontier s = closure s \ interior s`.  If `E y < ε`,
continuity gives a neighbourhood of `y` disjoint from `s`, so `y ∉ closure s`, again a contradiction.
Hence `E y = ε`. -/
theorem frontier_superlevel_subset_levelSet {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {z₀ : X} {E : X → ℝ}
    (hE : Submission.HasGreenFunctionWeak z₀ E) {ε : ℝ} (hε : 0 < ε) :
    frontier {x : X | ε ≤ E x} ∩ punctured z₀ ⊆ {x : X | E x = ε} := by
  have hεpos : 0 < ε := hε
  intro x hx
  obtain ⟨hxfr, hxp⟩ := hx
  rw [mem_punctured] at hxp
  rw [frontier] at hxfr
  obtain ⟨hxcl, hxni⟩ := hxfr
  have hcont : ContinuousAt E x :=
    Submission.HarmonicOnXAt.continuousAt (hE.2.1 x (by simp [hxp]))
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- `E x < ε`: a neighbourhood of `x` misses `{ε ≤ E}`, so `x ∉ closure {ε ≤ E}`.
    have hmem : {y : X | E y < ε} ∈ 𝓝 x := hcont (Iio_mem_nhds hlt)
    obtain ⟨z, hz1, hz2⟩ := mem_closure_iff_nhds.mp hxcl _ hmem
    rw [Set.mem_ofPred_eq] at hz1 hz2
    exact absurd hz2 (not_le.mpr hz1)
  · -- `ε < E x`: a neighbourhood of `x` lies in `{ε ≤ E}`, so `x ∈ interior {ε ≤ E}`.
    have hsub : {y : X | ε ≤ E y} ∈ 𝓝 x := hcont (Ici_mem_nhds hgt)
    exact hxni (mem_interior_iff_mem_nhds.mpr hsub)

end Work.CriticalSet
