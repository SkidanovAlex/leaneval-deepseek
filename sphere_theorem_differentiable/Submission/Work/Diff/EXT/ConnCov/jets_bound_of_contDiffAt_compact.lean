import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Uniform jet bounds on a compact set from pointwise smoothness

If `f : E → F` is `C^∞` at every point of an open-ish set `O` (only `ContDiffAt` at each point of
`O` is required, so `O` need not be open), then on every compact `K ⊆ O` the `k`-th iterated
Fréchet derivative of `f` is uniformly bounded.

This is the elementary compactness step used to turn the *joint* smoothness of the chart matrix of a
family of metrics into uniform bounds on a compact slab of time and space. -/

set_option linter.unusedSectionVars false

open scoped Topology
open Set

namespace Work.Diff.EXT.ConnCov

/-- **Uniform jet bounds on a compact set from pointwise smoothness.**  If `f` is `C^∞` at every
point of a set `O`, then the `k`-th iterated derivative of `f` is bounded on every compact
`K ⊆ O`. -/
theorem jets_bound_of_contDiffAt_compact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {O K : Set E} (hK : IsCompact K) (hKO : K ⊆ O)
    (hf : ∀ y ∈ O, ContDiffAt ℝ (⊤ : ℕ∞) f y) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ‖iteratedFDeriv ℝ k f y‖ ≤ C := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    (f := fun y => iteratedFDeriv ℝ k f y)
    (fun y hy => ((hf y (hKO hy)).continuousAt_iteratedFDeriv (by simp)).continuousWithinAt)
  exact ⟨max C 0, le_max_right _ _, fun y hy => le_trans (hC y hy) (le_max_left _ _)⟩

end Work.Diff.EXT.ConnCov
