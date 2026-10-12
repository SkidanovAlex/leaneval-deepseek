import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseSym.Minimiser

/-- Cauchy–Schwarz inequality for a symmetric positive-semidefinite bilinear form,
stated for a bare function `B : X → X → ℝ` that is additive and `ℝ`-homogeneous in
its first argument, symmetric, and nonnegative on the diagonal. -/
theorem cs_bilinear {X : Type*} [AddCommGroup X] [Module ℝ X]
    (B : X → X → ℝ) (hsymm : ∀ x y, B x y = B y x)
    (hadd : ∀ x y z, B (x + y) z = B x z + B y z)
    (hsmul : ∀ (c : ℝ) x y, B (c • x) y = c * B x y)
    (hpos : ∀ x, 0 ≤ B x x) (x y : X) :
    B x y ^ 2 ≤ B x x * B y y := by
  -- Additivity/homogeneity in the second argument, obtained from symmetry.
  have hadd₂ : ∀ a b c, B a (b + c) = B a b + B a c := by
    intro a b c
    rw [hsymm a (b + c), hadd, hsymm b a, hsymm c a]
  have hsmul₂ : ∀ (c : ℝ) a b, B a (c • b) = c * B a b := by
    intro c a b
    rw [hsymm a (c • b), hsmul c b a, hsymm b a]
  -- Expansion of the diagonal quadratic form.
  have hexp : ∀ t : ℝ, B (x + t • y) (x + t • y) = B x x + 2 * t * B x y + t ^ 2 * B y y := by
    intro t
    rw [hadd, hadd₂, hsmul₂, hsmul, hadd₂, hsmul₂, hsymm y x]
    ring
  -- The quadratic form is nonnegative for every real `t`.
  have hquad : ∀ t : ℝ, 0 ≤ B x x + 2 * t * B x y + t ^ 2 * B y y := fun t => by
    rw [← hexp t]; exact hpos _
  rcases lt_trichotomy (B y y) 0 with hlt | heq | hgt
  · exact absurd (hpos y) (not_le.mpr hlt)
  · -- Case `B y y = 0`: then the linear bound forces `B x y = 0`.
    have hquad0 : ∀ t : ℝ, 0 ≤ B x x + 2 * t * B x y := by
      intro t
      have h := hquad t
      rw [heq, mul_zero, add_zero] at h
      exact h
    have hD : B x y = 0 := by
      by_contra hne
      have h := hquad0 (-(B x x + 1) / (2 * B x y))
      have hkey : B x x + 2 * (-(B x x + 1) / (2 * B x y)) * B x y = -1 := by
        field_simp
        ring
      linarith
    rw [hD, heq]
    norm_num
  · -- Case `0 < B y y`: evaluate the quadratic at its minimiser.
    have hne : B y y ≠ 0 := ne_of_gt hgt
    have h := hquad (-(B x y) / (B y y))
    have hkey : B x x + 2 * (-(B x y) / (B y y)) * B x y + (-(B x y) / (B y y)) ^ 2 * B y y
        = B x x - (B x y)^2 / B y y := by
      field_simp
      ring
    rw [hkey] at h
    have h1 : (B x y)^2 / B y y ≤ B x x := by linarith
    have h2 : (B x y)^2 / B y y * B y y ≤ B x x * B y y :=
      mul_le_mul_of_nonneg_right h1 (le_of_lt hgt)
    rw [div_mul_cancel₀ _ hne] at h2
    exact h2

end Work.BoseSym.Minimiser
