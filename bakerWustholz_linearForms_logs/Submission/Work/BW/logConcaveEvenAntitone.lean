import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- An even, log-concave function `ℝ → ℝ≥0∞` is non-increasing on `[0, ∞)`.

The proof uses that the super-level sets `{z | f z ≥ t}` are convex (a convex
combination of two points above `t` is again above `t`, by log-concavity and
`t ^ λ * t ^ (1 - λ) = t`), and that a convex set which is symmetric about `0`
contains the whole interval between a point and its mirror image. -/
theorem logConcaveEvenAntitone {f : ℝ → ENNReal} (heven : ∀ x, f (-x) = f x)
    (hlog : ∀ x y (lam : ℝ), 0 ≤ lam → lam ≤ 1 →
      f (lam * x + (1 - lam) * y) ≥ f x ^ lam * f y ^ (1 - lam)) :
    AntitoneOn f (Set.Ici 0) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ici] at hx hy
  rcases eq_or_lt_of_le hy with hy0 | hypos
  · -- case `y = 0`: then also `x = 0`
    have hy' : y = 0 := hy0.symm
    subst hy'
    have hx0 : x = 0 := le_antisymm hxy hx
    subst hx0
    rfl
  · -- case `0 < y`
    set lam : ℝ := (y + x) / (2 * y) with hlamdef
    have hlam0 : 0 ≤ lam := by
      rw [hlamdef]; exact div_nonneg (by linarith) (by linarith)
    have hlam1 : lam ≤ 1 := by
      rw [hlamdef, div_le_one (by linarith)]; linarith
    have hcomb : lam * y + (1 - lam) * (-y) = x := by
      rw [hlamdef]; field_simp; ring
    have h := hlog y (-y) lam hlam0 hlam1
    rw [hcomb, heven y] at h
    have hrpow : f y ^ lam * f y ^ (1 - lam) = f y := by
      rw [← ENNReal.rpow_add_of_nonneg lam (1 - lam) hlam0 (by linarith),
        show lam + (1 - lam) = 1 by ring, ENNReal.rpow_one]
    rw [hrpow] at h
    exact h

end Work.BW
