import Mathlib
import Submission.Work.HP.Defs

namespace Work.HP.Vero

/-- The gcd of the `2 × 2` minors of two `ℤ`-linearly independent vectors is positive (as a real
number).  Proof route: `gcdMinors2 x y` is a normalized `Finset.gcd`, hence `≥ 0`; if it were `0`
then all minors `x i * y j - x j * y i` would vanish, which forces `x` and `y` to be `ℚ`-proportional
(pick `j₀` with `y j₀ ≠ 0`, then `x i = (x j₀ / y j₀) * y i` for all `i`), contradicting
`hxy : LinearIndependent ℤ ![x, y]`. -/
theorem gcdMinors2_posR {n : ℕ} (x y : Fin (n + 1) → ℤ)
    (hxy : LinearIndependent ℤ ![x, y]) :
    (0 : ℝ) < (gcdMinors2 x y : ℝ) := by
  -- `gcdMinors2` is a normalized `Finset.gcd`, hence nonnegative.
  have hnn : (0 : ℤ) ≤ gcdMinors2 x y := by
    have h : |gcdMinors2 x y| = gcdMinors2 x y := by
      rw [Int.abs_eq_normalize, gcdMinors2, Finset.normalize_gcd]
    exact h ▸ abs_nonneg _
  -- If it vanished, every `2 × 2` minor would vanish, forcing `x, y` to be proportional.
  have hne : gcdMinors2 x y ≠ 0 := by
    intro h0
    rw [gcdMinors2] at h0
    have hmin : ∀ i j : Fin (n + 1), x i * y j - x j * y i = 0 := by
      intro i j
      exact Finset.gcd_eq_zero_iff.mp h0 (i, j) (Finset.mem_univ _)
    -- `y` is a nonzero vector, so some coordinate `y j₀` is nonzero.
    have hy : y ≠ 0 := by
      have := hxy.ne_zero 1
      simpa using this
    obtain ⟨j0, hj0⟩ := Function.ne_iff.mp hy
    -- Then `y j₀ • x - x j₀ • y = 0` is a nontrivial `ℤ`-linear relation.
    have hrel : y j0 • x + (-(x j0)) • y = 0 := by
      funext i
      have h := hmin i j0
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      linarith [h]
    obtain ⟨h1, _⟩ := (LinearIndependent.pair_iff.mp hxy) (y j0) (-(x j0)) hrel
    exact hj0 h1
  have hpos : (0 : ℤ) < gcdMinors2 x y := lt_of_le_of_ne hnn (Ne.symm hne)
  exact_mod_cast hpos

end Work.HP.Vero
