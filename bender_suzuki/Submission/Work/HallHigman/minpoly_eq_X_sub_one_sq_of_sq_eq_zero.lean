import Mathlib
import Submission.Work.HallHigman.minpoly_eq_X_sub_one_pow_iff

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.HallHigman

open Polynomial

/-- If an endomorphism `f` satisfies `(f - 1)^2 = 0` but `f ≠ 1`, then its minimal polynomial
over the base field is exactly `(X - 1)^2`: it divides `(X - 1)^2`, and the two proper divisors
`1` and `X - 1` are both excluded (the first because it would force `1 = 0`, the second because
it would force `f = 1`). -/
theorem minpoly_eq_X_sub_one_sq_of_sq_eq_zero {K M : Type*} [Field K] [AddCommGroup M]
    [Module K M] {f : Module.End K M} (hsq : (f - 1) ^ 2 = 0) (hne : f ≠ 1) :
    minpoly K f = (Polynomial.X - 1) ^ 2 := by
  have hX1 : (aeval f) (X - 1 : K[X]) = f - 1 := by simp
  have h2 : (aeval f) ((X - 1 : K[X]) ^ 2) = 0 := by
    rw [map_pow, hX1, hsq]
  -- `f` is integral, being a root of the monic polynomial `(X - 1)^2`.
  have hint : IsIntegral K f :=
    ⟨(X - 1 : K[X]) ^ 2, (Polynomial.monic_X_sub_C 1).pow 2,
      by rw [← Polynomial.aeval_def, h2]⟩
  -- hence `minpoly K f` is monic and divides `(X - 1)^2`.
  have hmem : minpoly K f ∣ (X - 1 : K[X]) ^ 2 := minpoly.dvd_iff.mpr h2
  obtain ⟨k, hk_le, hk⟩ :=
    monic_dvd_X_sub_one_pow 2 (minpoly K f) (minpoly.monic hint) hmem
  -- a monic divisor of `(X - 1)^2` is a power `(X - 1)^k` with `k ≤ 2`; rule out `k = 0, 1`.
  have hk2 : k = 2 := by
    interval_cases k
    · exfalso
      -- `minpoly K f = 1` would give `1 = 0` in `Module.End K M`, hence `f = 1`.
      have ha := minpoly.aeval K f
      rw [hk] at ha
      have h1 : (1 : Module.End K M) = 0 := by simpa using ha
      have hf1 : f = 1 := by
        calc f = f * 1 := (mul_one f).symm
          _ = f * 0 := by rw [h1]
          _ = 0 := mul_zero f
          _ = 1 := h1.symm
      exact hne hf1
    · exfalso
      -- `minpoly K f = X - 1` would give `f - 1 = 0`, i.e. `f = 1`.
      have ha := minpoly.aeval K f
      rw [hk] at ha
      simp only [pow_one] at ha
      rw [hX1] at ha
      exact hne (sub_eq_zero.mp ha)
    · rfl
  rw [hk, hk2]

end Work.HallHigman
