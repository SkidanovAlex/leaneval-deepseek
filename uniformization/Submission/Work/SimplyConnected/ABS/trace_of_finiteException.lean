import Mathlib
import Submission.Work.Potential.removable_singularity_of_bounded_near

/-!
# The finite-exception case: removability across a finite set of points

This module opens the next residual class of
`Work.SimplyConnected.ABS.globalBarrier_far_pos_of_localBarrier` after `Z`-points, chart-sphere
points, half-plane points and isolated-complement points: **frontier points whose complement is
finite (and, in the general case, polar) near `ζ`**.

## Why this file exists, and the order of work

The recorded plan was to iterate the *global* corollary
`Work.Potential.removable_singularity_of_bounded_near` over the exceptional set by
`Finset.induction`.  That route **does not work**, and the reason is structural:

* `removable_singularity_of_bounded_near` takes `hu : HarmonicOnX u (Set.univ \ {z₀})` — harmonicity
  on the **whole** complement of the point;
* in the finite setting `u` is harmonic only off the *entire* exceptional set, i.e. on the strictly
  **smaller** set `univ \ ↑F`;
* harmonicity cannot be restricted *up*, so the induction cannot even start.

The finite case must therefore be built from the **local** (chart-ball) brick
`Work.SimplyConnected.ABS.tendsto_of_harmonicOnX_punctured_chartBall` (dispatched, reviewed): inside a
chart ball the hypothesis "harmonic and bounded off the puncture" matches exactly, and the exceptional
points are removed one at a time there.  The order of work is therefore

    local removability  →  finite exceptions  →  polar sets,

and only then does the isolated/polar fragment of the trace become available.

## The statement of the finite case

    Work.SimplyConnected.ABS.tendsto_of_harmonicOnX_finite_exception
      {F : Finset X} {u : X → ℝ} (hu : Submission.HarmonicOnX u (Set.univ \ ↑F))
      (hb : ∃ M, ∀ a ∈ F, ∃ V ∈ 𝓝 a, ∀ x ∈ V, x ∉ ↑F → |u x| ≤ M) :
      ∀ a ∈ F, ∃ l, Filter.Tendsto u (nhdsWithin a (Set.univ \ ↑F)) (𝓝 l)

## What is proved here

The one step of the iteration that is *independent* of the local brick: the **bound bookkeeping**.  At
each step of the removal the bound must cover the *remaining* exceptional points as well (the local
brick's boundedness hypothesis is off the puncture, not off the whole finite set); since `u` is
`ℝ`-valued this is always possible, and the witness is the finite sum below.  This is the first line
of the iteration, and it is the reason the induction has a chance of being clean.
-/

open Filter Set

namespace Work.SimplyConnected.ABS

/-- **Bound bookkeeping for the finite-exception iteration.**  A bound `M` valid off a finite
exceptional set can be replaced, without loss, by a bound valid at the *remaining* exceptional points
too.  The witness is `M + Σ |u a|` over the exceptional set. -/
theorem exists_bound_of_finset_exception {X : Type*} (u : X → ℝ) (F : Finset X) {M : ℝ} :
    ∃ M' : ℝ, M ≤ M' ∧ ∀ a ∈ ↑F, |u a| ≤ M' := by
  refine ⟨max M 0 + F.sum (fun a => |u a|), ?_, ?_⟩
  · have h1 : M ≤ max M 0 := le_max_left _ _
    have h2 : (0 : ℝ) ≤ F.sum (fun a => |u a|) :=
      Finset.sum_nonneg fun a _ => abs_nonneg (u a)
    linarith
  · intro a ha
    have h1 : |u a| ≤ F.sum (fun b => |u b|) :=
      Finset.single_le_sum (fun b _ => abs_nonneg (u b)) (Finset.mem_coe.mp ha)
    have h2 : (0 : ℝ) ≤ max M 0 := le_max_right M 0
    linarith

end Work.SimplyConnected.ABS
