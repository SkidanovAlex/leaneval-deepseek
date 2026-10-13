import Mathlib

namespace Work.DSM5b

universe a

/-- **Killing in the kernel of an `Away` localisation, in fraction form.**
Let `W` be a commutative ring, `s c tk w ∈ W` with `s * tk = c * w`, and let `x y ∈ W_s`
be given together with numerators `a b ∈ W` for the *same* denominator `s^N`
(`x * s^N = a`, `y * s^N = b` in `W_s`).  If the numerators already agree after multiplication
by a power of `c` (`c^m * a = c^m * b` in `W`), then `x` and `y` agree in `W_s` after
multiplication by that same power of the image of `tk`.

Proof route: `(s*tk)^m = (c*w)^m = (w*c)^m`, so multiplying `c^m a = c^m b` by `w^m` gives
`(s*tk)^m a = (s*tk)^m b` in `W`; mapping to `W_s` and substituting `s^N x = a`, `s^N y = b`
gives `s^m tk^m x s^N = s^m tk^m y s^N` in `W_s`; the image of `s` is a unit in `W_s`
(`IsLocalization.Away.algebraMap_isUnit`), so cancel `s^m` on the left and `s^N` on the right
(`IsUnit.mul_left_cancel`, `IsUnit.mul_right_cancel`).  No hypothesis on `tk`, `w`, `c` or `s`
beyond `s * tk = c * w` is needed.-/
theorem awayKernel_pow_mul {W : Type a} [CommRing W] (s c tk w : W) (hh : s * tk = c * w)
    {x y : Localization.Away s} {N m : ℕ} {a b : W}
    (ha : x * (algebraMap W (Localization.Away s) s) ^ N = algebraMap W (Localization.Away s) a)
    (hb : y * (algebraMap W (Localization.Away s) s) ^ N = algebraMap W (Localization.Away s) b)
    (hab : c ^ m * a = c ^ m * b) :
    (algebraMap W (Localization.Away s) tk) ^ m * x =
      (algebraMap W (Localization.Away s) tk) ^ m * y := by
  -- Step 1: in `W`, multiply `c ^ m * a = c ^ m * b` by `w ^ m` and use
  -- `s * tk = c * w`, i.e. `(s * tk) ^ m = (c * w) ^ m = w ^ m * c ^ m`.
  have h1 : (s * tk) ^ m * a = (s * tk) ^ m * b := by
    calc (s * tk) ^ m * a = (w ^ m * c ^ m) * a := by
          rw [hh, mul_pow, mul_comm (c ^ m) (w ^ m)]
      _ = w ^ m * (c ^ m * a) := by rw [mul_assoc]
      _ = w ^ m * (c ^ m * b) := by rw [hab]
      _ = (w ^ m * c ^ m) * b := by rw [mul_assoc]
      _ = (s * tk) ^ m * b := by
          rw [hh, mul_pow, mul_comm (c ^ m) (w ^ m)]
  -- Step 2: push the identity to `W_s` and substitute the numerators `s ^ N * x = a`,
  -- `s ^ N * y = b`, obtaining `s ^ m * tk ^ m * x * s ^ N = s ^ m * tk ^ m * y * s ^ N`.
  have h2 := congrArg (algebraMap W (Localization.Away s)) h1
  simp only [map_mul, map_pow, mul_pow] at h2
  rw [← ha, ← hb] at h2
  simp only [mul_assoc] at h2
  -- Step 3: the image of `s` is a unit in `W_s`; cancel `s ^ m` on the left and `s ^ N`
  -- on the right.
  have hu := IsLocalization.Away.algebraMap_isUnit (R := W) (S := Localization.Away s) s
  have hc2 := IsUnit.mul_left_cancel (hu.pow m) h2
  simp only [← mul_assoc] at hc2
  exact IsUnit.mul_right_cancel (hu.pow N) hc2

end Work.DSM5b
