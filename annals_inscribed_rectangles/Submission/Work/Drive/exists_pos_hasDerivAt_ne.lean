import Mathlib

open scoped Topology
open Filter

namespace Work.Drive

/-- If `f` has a nonzero derivative `c` at `t`, then `f` is locally injective at `t`:
there is a neighbourhood of `t` on which `f s ≠ f t` for every `s ≠ t`. -/
theorem exists_pos_hasDerivAt_ne {f : ℝ → ℝ} {t c : ℝ} (h : HasDerivAt f c t) (hc : c ≠ 0) :
    ∃ δ > 0, ∀ s : ℝ, 0 < |s - t| → |s - t| < δ → f s ≠ f t := by
  -- `HasDerivAt.eventually_ne` already gives the punctured-neighbourhood statement.
  have hev : ∀ᶠ z in 𝓝[{t}ᶜ] t, f z ≠ f t := h.eventually_ne hc
  -- Rewrite the punctured filter as `𝓝 t` restricted to `{t}ᶜ`, then as an explicit ε-δ ball.
  rw [eventually_nhdsWithin_iff] at hev
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδpos, hδ⟩ := hev
  refine ⟨δ, hδpos, fun s hs hsδ => ?_⟩
  have hst : s ≠ t := by
    have hsub : s - t ≠ 0 := abs_pos.mp hs
    exact sub_ne_zero.mp hsub
  exact hδ (by rw [Real.dist_eq]; exact hsδ) (by simpa using hst)

end Work.Drive
