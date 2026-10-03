import Mathlib

namespace Work.FIArea5.HeckeZFR

/-- If `f : ℂ → ℂ` is differentiable (hence entire) and is not identically zero, then at every
point `z` the order of vanishing of `f` at `z` is finite.

Indeed, if the order were infinite at some `z`, then by `analyticOrderAt_eq_top` the function
would vanish on a neighbourhood of `z`; by the identity theorem for analytic functions it would
vanish on all of `ℂ`, contradicting that `f` takes a nonzero value somewhere. -/
theorem analyticOrderAt_ne_top_of_differentiable_ne_zero (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hne : ∃ z : ℂ, f z ≠ 0) (z : ℂ) : analyticOrderAt f z ≠ ⊤ := by
  obtain ⟨w, hw⟩ := hne
  -- At the point `w` where `f w ≠ 0`, the order of vanishing is `0`, hence finite.
  have hw' : analyticOrderAt f w ≠ ⊤ := by
    have h0 : analyticOrderAt f w = 0 := analyticOrderAt_eq_zero.mpr (Or.inr hw)
    rw [h0]
    exact ENat.zero_ne_top
  -- `ℂ` is preconnected, so finiteness of the order propagates from `w` to `z`.
  exact AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected
    (hf.differentiableOn.analyticOnNhd isOpen_univ) isPreconnected_univ
    (Set.mem_univ w) (Set.mem_univ z) hw'

end Work.FIArea5.HeckeZFR
