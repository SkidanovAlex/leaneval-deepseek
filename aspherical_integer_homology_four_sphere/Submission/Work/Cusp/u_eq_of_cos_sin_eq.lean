import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

/-- If two angles `2πu₁ + c` and `2πu₂ + c` have equal cosine and sine, then the
reduced parameters `u₁, u₂ ∈ [0,1)` coincide. -/
theorem u_eq_of_cos_sin_eq (u₁ u₂ c : ℝ) (h₁ : 0 ≤ u₁) (h₁' : u₁ < 1) (h₂ : 0 ≤ u₂) (h₂' : u₂ < 1)
    (hc : Real.cos (2 * Real.pi * u₁ + c) = Real.cos (2 * Real.pi * u₂ + c))
    (hs : Real.sin (2 * Real.pi * u₁ + c) = Real.sin (2 * Real.pi * u₂ + c)) : u₁ = u₂ := by
  set a := 2 * Real.pi * u₁ + c with ha
  set b := 2 * Real.pi * u₂ + c with hb
  have hcos : Real.cos (a - b) = 1 := by
    rw [Real.cos_sub, ← hc, ← hs]
    nlinarith [Real.cos_sq_add_sin_sq a]
  obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff (a - b)).mp hcos
  have hab : a - b = (u₁ - u₂) * (2 * Real.pi) := by rw [ha, hb]; ring
  have hn' : (n : ℝ) = u₁ - u₂ := by
    rw [hab] at hn
    exact mul_right_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0) hn
  have hlt : (n : ℝ) < 1 := by rw [hn']; linarith
  have hgt : (-1 : ℝ) < n := by rw [hn']; linarith
  have h1 : n < 1 := by exact_mod_cast hlt
  have h2 : -1 < n := by exact_mod_cast hgt
  have hn0 : n = 0 := by omega
  rw [hn0] at hn'
  push_cast at hn'
  linarith

end Work.Cusp
