import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.FTS.PressureOn.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Topology

namespace Work.FTS.PressureOn

/-- **The support of `∂ₜf` is controlled by the support of `f`** (no regularity needed).

Hypothesis: at time `t` the slices `f · s`, `s ∈ (t-1, t+1)`, are all supported in a ball
`B(0,R)`.  Conclusion: the same ball contains the support of `∂ₜf · s` for every `s` in the
*window*.

The point is that the hypothesis is uniform over the whole window: if `‖x‖ > R` then
`f x s' = 0` for **every** `s' ∈ (t-1,t+1)`, hence `s' ↦ f x s'` is identically `0` on the
window, so its derivative at any interior point `s` vanishes. -/
theorem timeDeriv_support {f : R3 → ℝ → R3}
    (hsupp : ∀ t : ℝ, ∃ R, ∀ s ∈ Set.Ioo (t - 1) (t + 1), ∀ x, f x s ≠ 0 → ‖x‖ ≤ R) :
    ∀ t : ℝ, ∃ R, ∀ s ∈ Set.Ioo (t - 1) (t + 1), ∀ x,
      FiniteTimeSingularity.timeDeriv f x s ≠ 0 → ‖x‖ ≤ R := by
  intro t
  obtain ⟨R, hR⟩ := hsupp t
  refine ⟨R, ?_⟩
  intro s hs x hx
  by_contra hle
  rw [not_le] at hle
  -- outside `B(0,R)` the slice `f x ·` vanishes on the whole window around `t`
  have hzero : ∀ s' ∈ Set.Ioo (t - 1) (t + 1), f x s' = 0 := by
    intro s' hs'
    by_contra hne
    exact absurd (hR s' hs' x hne) (not_le.mpr hle)
  -- hence it is eventually equal to `0` at `s`, so its derivative vanishes there
  have hev : (fun s' => f x s') =ᶠ[𝓝 s] (fun _ => (0 : R3)) := by
    filter_upwards [Ioo_mem_nhds hs.1 hs.2] with s' hs'
    exact hzero s' hs'
  exact hx (by
    rw [FiniteTimeSingularity.timeDeriv, Filter.EventuallyEq.deriv_eq hev, deriv_const])

end Work.FTS.PressureOn
