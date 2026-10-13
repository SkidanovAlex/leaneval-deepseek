import Mathlib
import Submission.Work.WilC4.Defs

/-!
  `ValEq x y` says that `x` and `y` lie in the same Archimedean class of the ordered field `M`:
  there is `N > 0` with `N⁻¹ * |y| ≤ |x| ≤ N * |y|`.

  This file shows that this relation is preserved by **integer** powers:

      `ValEq x y → ValEq (x ^ n) (y ^ n)`  for every `n : ℤ`.

  The proof splits the integer exponent into its nonnegative and negative parts.  For a natural
  exponent the bound `N` simply becomes `N ^ k` (using `|x ^ k| = |x| ^ k`); for a negative
  exponent it is an inversion of that statement.  Both ingredients are proved here as private
  auxiliaries, so that the file is self-contained.
-/

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilC4
open WilkiesDesign WilkiesDesign.CG

/-- `ValEq` is reflexive: every element is in its own Archimedean class. -/
private theorem valEq_self' {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    (x : M) : ValEq x x :=
  ⟨1, Nat.one_pos, by simp, by simp⟩

/-- `ValEq` is preserved by natural powers. -/
private theorem valEq_pow {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    {x y : M} (h : ValEq x y) (k : ℕ) : ValEq (x ^ k) (y ^ k) := by
  obtain ⟨N, hN, ha, hb⟩ := h
  refine ⟨N ^ k, pow_pos (Nat.cast_pos.mpr hN) k, ?_, ?_⟩
  · have h1 : ((N : M)⁻¹ * |y|) ^ k ≤ |x| ^ k :=
      pow_le_pow_left₀ (mul_nonneg (inv_nonneg.mpr (le_of_lt (Nat.cast_pos.mpr hN)))
        (abs_nonneg y)) ha k
    have e : ((↑(N ^ k) : M))⁻¹ * |y| ^ k = ((N : M)⁻¹ * |y|) ^ k := by
      rw [Nat.cast_pow, ← inv_pow, mul_pow]
    rw [abs_pow, abs_pow, e]
    exact h1
  · have h1 : |x| ^ k ≤ ((N : M) * |y|) ^ k :=
      pow_le_pow_left₀ (abs_nonneg x) hb k
    have e : (↑(N ^ k) : M) * |y| ^ k = ((N : M) * |y|) ^ k := by
      rw [Nat.cast_pow, mul_pow]
    rw [abs_pow, abs_pow, e]
    exact h1

/-- Inversion preserves `ValEq` (with the convention `0⁻¹ = 0`). -/
private theorem valEq_inv {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    {x y : M} (h : ValEq x y) : ValEq x⁻¹ y⁻¹ := by
  obtain ⟨N, hN, ha, hb⟩ := h
  by_cases hy : y = 0
  · -- then `x = 0` as well and both sides are `0`
    have hx : x = 0 := by
      have h0 : |x| ≤ 0 := by simpa [hy] using hb
      exact abs_eq_zero.mp (le_antisymm h0 (abs_nonneg x))
    subst hx
    subst hy
    simpa using valEq_self' (0 : M)
  · have hypos : 0 < |y| := abs_pos.mpr hy
    have hNpos : (0 : M) < (N : M) := Nat.cast_pos.mpr hN
    have hNinvpos : 0 < (N : M)⁻¹ := inv_pos.mpr hNpos
    have hgpos : 0 < (N : M)⁻¹ * |y| := mul_pos hNinvpos hypos
    have hxpos : 0 < |x| := lt_of_lt_of_le hgpos ha
    refine ⟨N, hN, ?_, ?_⟩
    · have h1 : ((N : M) * |y|)⁻¹ ≤ |x|⁻¹ := by
        rw [inv_le_inv₀ (mul_pos hNpos hypos) hxpos]
        exact hb
      rw [abs_inv, abs_inv]
      rw [mul_inv] at h1
      exact h1
    · have h1 : |x|⁻¹ ≤ ((N : M)⁻¹ * |y|)⁻¹ := by
        rw [inv_le_inv₀ hxpos hgpos]
        exact ha
      rw [abs_inv, abs_inv]
      rw [mul_inv, inv_inv] at h1
      exact h1

/-- **`ValEq` is preserved by integer powers.**  The Archimedean class of `x ^ n` depends only on
the Archimedean class of `x`, for every integer exponent `n`. -/
theorem valEq_zpow {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    {x y : M} (h : ValEq x y) (n : ℤ) : ValEq (x ^ n) (y ^ n) := by
  obtain ⟨k, hk | hk⟩ := Int.eq_nat_or_neg n
  · have hx : x ^ ((k : ℤ)) = x ^ k := zpow_natCast x k
    have hy : y ^ ((k : ℤ)) = y ^ k := zpow_natCast y k
    rw [hk, hx, hy]
    exact valEq_pow h k
  · have hx : x ^ (-(k : ℤ)) = (x ^ k)⁻¹ := by rw [zpow_neg, zpow_natCast]
    have hy : y ^ (-(k : ℤ)) = (y ^ k)⁻¹ := by rw [zpow_neg, zpow_natCast]
    rw [hk, hx, hy]
    exact valEq_inv (valEq_pow h k)

end Work.WilC4
