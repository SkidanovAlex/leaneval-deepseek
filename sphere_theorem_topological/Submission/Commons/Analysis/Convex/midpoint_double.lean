import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace Commons.Analysis.Convex

/-- Midpoint convexity with a fixed step `u` on `[0,T]` upgrades to step `2u`.

For `t = s + 2u` the three instances of the hypothesis at pairs
`(s, s+u)`, `(s+u, s+2u)` and `(s+u/2, s+3u/2)` combine to give the claim. -/
theorem midpoint_double {H : ℝ → ℝ} {T u : ℝ} (hu : 0 < u)
    (h : ∀ s t : ℝ, s ∈ Set.Icc 0 T → t ∈ Set.Icc 0 T → t - s = u →
      H s + H t ≤ 2 * H ((s + t) / 2)) :
    ∀ s t : ℝ, s ∈ Set.Icc 0 T → t ∈ Set.Icc 0 T → t - s = 2 * u →
      H s + H t ≤ 2 * H ((s + t) / 2) := by
  intro s t hs ht hst
  have ht' : t = s + 2 * u := by linarith
  obtain ⟨hs0, hsT⟩ := hs
  obtain ⟨ht0, htT⟩ := ht
  rw [ht'] at ht0 htT ⊢
  have h1 : s + u ∈ Set.Icc 0 T := ⟨by linarith, by linarith⟩
  have h2 : s + 2 * u ∈ Set.Icc 0 T := ⟨by linarith, by linarith⟩
  have h3 : s + u / 2 ∈ Set.Icc 0 T := ⟨by linarith, by linarith⟩
  have h4 : s + 3 * u / 2 ∈ Set.Icc 0 T := ⟨by linarith, by linarith⟩
  have hs' : s ∈ Set.Icc 0 T := ⟨hs0, hsT⟩
  have e1 := h s (s + u) hs' h1 (by ring)
  have e2 := h (s + u) (s + 2 * u) h1 h2 (by ring)
  have e3 := h (s + u / 2) (s + 3 * u / 2) h3 h4 (by ring)
  have e1' : H s + H (s + u) ≤ 2 * H (s + u / 2) := by
    rw [show (s + (s + u)) / 2 = s + u / 2 by ring] at e1
    exact e1
  have e2' : H (s + u) + H (s + 2 * u) ≤ 2 * H (s + 3 * u / 2) := by
    rw [show (s + u + (s + 2 * u)) / 2 = s + 3 * u / 2 by ring] at e2
    exact e2
  have e3' : H (s + u / 2) + H (s + 3 * u / 2) ≤ 2 * H (s + u) := by
    rw [show (s + u / 2 + (s + 3 * u / 2)) / 2 = s + u by ring] at e3
    exact e3
  rw [show (s + (s + 2 * u)) / 2 = s + u by ring]
  linarith [e1', e2', e3']

end Commons.Analysis.Convex