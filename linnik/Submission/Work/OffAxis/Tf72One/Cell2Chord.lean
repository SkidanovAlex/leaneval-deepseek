/-
# OffAxis/Tf72One/Cell2Chord

The elementary one-dimensional input behind both `s`- and `t`-interpolation for `Isub`:
if `f` is `C¹` on `[a,b]` with a lower bound `-M ≤ f''` on `(a,b)` (so that
`t ↦ f t + (M/2) t²` is convex), then `f` at `x ∈ [a,b]` is at most its chord plus the
sharp error `(b-a)²/8 · M`.

This is the "upper half" of `abs_interp_error_le`, stated for an explicit first and second
derivative so that it can be applied to the integrand of `Isub` without computing
`iteratedDeriv`.
-/
import Mathlib

namespace Work.OffAxis.Tf72One

/-- **Sharp two-point interpolation, upper bound.**  If `f` has derivatives `f'`, `f''` on
`(a,b)` and `-M ≤ f''` there, with `M ≥ 0`, then for `x ∈ [a,b]`
`f x ≤ (b-x)/(b-a) f a + (x-a)/(b-a) f b + (b-a)²/8 · M`. -/
theorem chord_upper_of_second_deriv (f f' f'' : ℝ → ℝ) (a b x M : ℝ)
    (hab : a < b) (hx : x ∈ Set.Icc a b) (hM0 : 0 ≤ M)
    (hcont : ContinuousOn f (Set.Icc a b))
    (h1 : ∀ y ∈ Set.Ioo a b, HasDerivAt f (f' y) y)
    (h2 : ∀ y ∈ Set.Ioo a b, HasDerivAt f' (f'' y) y)
    (h3 : ∀ y ∈ Set.Ioo a b, -M ≤ f'' y) :
    f x ≤ (b - x) / (b - a) * f a + (x - a) / (b - a) * f b + (b - a) ^ 2 / 8 * M := by
  have hconv : ConvexOn ℝ (Set.Icc a b) (fun t => f t + M / 2 * t ^ 2) := by
    refine convexOn_of_hasDerivWithinAt2_nonneg (D := Set.Icc a b)
      (f := fun t => f t + M / 2 * t ^ 2) (f' := fun t => f' t + M * t)
      (f'' := fun t => f'' t + M) (convex_Icc a b) ?_ ?_ ?_ ?_
    · exact hcont.add (by fun_prop)
    · intro y hy
      rw [interior_Icc] at hy
      exact ((h1 y hy).add (by
        have h := (hasDerivAt_pow 2 y).const_mul (M / 2)
        simp only [Nat.reduceSub, pow_one] at h
        exact h.congr_deriv (by ring))).hasDerivWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      exact ((h2 y hy).add (by
        simpa using (hasDerivAt_id y).const_mul M)).hasDerivWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      linarith [h3 y hy]
  have hba : 0 < b - a := by linarith
  have hw1 : 0 ≤ (b - x) / (b - a) := div_nonneg (by linarith [hx.2]) hba.le
  have hw2 : 0 ≤ (x - a) / (b - a) := div_nonneg (by linarith [hx.1]) hba.le
  have hsum : (b - x) / (b - a) + (x - a) / (b - a) = 1 := by field_simp; ring
  have hcombo : (b - x) / (b - a) * a + (x - a) / (b - a) * b = x := by field_simp; ring
  have hQ : (b - x) / (b - a) * a ^ 2 + (x - a) / (b - a) * b ^ 2 - x ^ 2
      = (x - a) * (b - x) := by field_simp; ring
  have hbd : (x - a) * (b - x) ≤ (b - a) ^ 2 / 4 := by
    nlinarith [sq_nonneg (2 * x - a - b)]
  have h3c := hconv.2 (show a ∈ Set.Icc a b from ⟨le_refl a, hab.le⟩)
    (show b ∈ Set.Icc a b from ⟨hab.le, le_refl b⟩) hw1 hw2 hsum
  simp only [smul_eq_mul] at h3c
  rw [hcombo] at h3c
  have hrew : (b - x) / (b - a) * (f a + M / 2 * a ^ 2)
        + (x - a) / (b - a) * (f b + M / 2 * b ^ 2)
      = ((b - x) / (b - a) * f a + (x - a) / (b - a) * f b)
        + M / 2 * ((b - x) / (b - a) * a ^ 2 + (x - a) / (b - a) * b ^ 2) := by ring
  rw [hrew] at h3c
  have hfin : f x - ((b - x) / (b - a) * f a + (x - a) / (b - a) * f b)
      ≤ (b - a) ^ 2 / 8 * M := by
    calc f x - ((b - x) / (b - a) * f a + (x - a) / (b - a) * f b)
        ≤ M / 2 * ((b - x) / (b - a) * a ^ 2 + (x - a) / (b - a) * b ^ 2) - M / 2 * x ^ 2 := by
          linarith
      _ = M / 2 * ((x - a) * (b - x)) := by rw [← hQ]; ring
      _ ≤ M / 2 * ((b - a) ^ 2 / 4) := mul_le_mul_of_nonneg_left hbd (by linarith)
      _ = (b - a) ^ 2 / 8 * M := by ring
  linarith

end Work.OffAxis.Tf72One
