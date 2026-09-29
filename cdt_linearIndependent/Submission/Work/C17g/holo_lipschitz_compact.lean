import Mathlib
import Submission.Work.C17g.local_lipschitz_holo
import Submission.Work.C17g.lipschitz_of_local_bound

/-!
# Holomorphic functions are Lipschitz on compact subsets of their domain

Let `S ⊆ ℂ` be open, `f : ℂ → E` complex differentiable on `S` (here `E` is an arbitrary complex
normed space -- in particular no completeness of `E` is assumed), and `T ⊆ S` compact. Then `f`
is Lipschitz on `T`.

The proof combines two ingredients:

* `Work.C17g.local_lipschitz_holo`: near `T` the function `f` is bounded, and the Schwarz lemma /
  Cauchy estimate for a complex differentiable function turns that bound into a bound on `f'`,
  hence (mean value inequality) into a *local* Lipschitz estimate;
* `Work.C17g.lipschitz_of_local_bound`: a function which is locally Lipschitz on a uniform scale
  and globally bounded on `T` is Lipschitz on `T`.
-/

namespace Work.C17g

open Metric Complex

/-- A function complex differentiable on an open set is Lipschitz on every compact subset of its
domain. -/
theorem holo_lipschitz_compact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {S : Set ℂ} (hSo : IsOpen S) {f : ℂ → E} (hf : DifferentiableOn ℂ f S)
    {T : Set ℂ} (hT : IsCompact T) (hTS : T ⊆ S) :
    ∃ K : NNReal, LipschitzOnWith K f T := by
  -- `T` has a closed thickening contained in `S`
  obtain ⟨ρ, hρ, hρS⟩ := hT.exists_cthickening_subset_open hSo hTS
  -- `f` is bounded on that thickening
  obtain ⟨C, hC⟩ := hT.cthickening.exists_bound_of_continuousOn (hf.continuousOn.mono hρS)
  set B : ℝ := max C 0 with hBdef
  have hB0 : 0 ≤ B := le_max_right _ _
  have hBbd : ∀ z ∈ Metric.cthickening ρ T, ‖f z‖ ≤ B :=
    fun z hz => (hC z hz).trans (le_max_left _ _)
  -- local Lipschitz estimate with constant `2 * B / ρ` on scale `ρ / 2`
  have hr : 0 < ρ / 2 := by linarith
  have hloc := local_lipschitz_holo hSo hf hρ hρS hBbd
  have hCc : 0 ≤ 2 * B / ρ := by positivity
  refine ⟨_, lipschitz_of_local_bound (f := f) hr hCc hB0 hloc ?_⟩
  intro x hx
  exact hBbd x (Metric.self_subset_cthickening T hx)

end Work.C17g
