import Mathlib
import Submission.Work.HP.BridgeDefs

namespace Work.HP.BridgeAux

/-- Two primitive integer vectors that are proportional over `ℚ` differ by a sign.

This is the uniqueness half of the primitive-representative construction: if
`a = c • b` over `ℚ` with `a` and `b` both primitive, then `c = ±1`, hence `a = ±b`.
The proof is elementary: cross-multiplying at a coordinate `m0` with `b m0 ≠ 0`
shows `b m0 * a = a m0 * b` as integer vectors, and comparing the gcds of the two
sides (using primitivity of `a` and `b`) gives `|a m0| = |b m0|`, whence
`c = a m0 / b m0 = ±1`. -/
theorem prim_eq_or_eq_neg {d n : ℕ} {a b : Mon d n → ℤ} (ha : IsPrim a) (hb : IsPrim b)
    (c : ℚ) (h : ∀ m, (a m : ℚ) = c * b m) : a = b ∨ a = -b := by
  classical
  -- `b` is non-zero, so some coordinate `b m0` does not vanish.
  obtain ⟨m0, -, hm0⟩ := Finset.gcd_ne_zero_iff.mp (by rw [hb]; exact one_ne_zero)
  -- Cross-multiplication over `ℚ` at the coordinate `m0`.
  have hmul : ∀ m, (a m : ℚ) * (b m0 : ℚ) = (a m0 : ℚ) * (b m : ℚ) := by
    intro m
    rw [h m, h m0]
    ring
  -- The same identity over `ℤ`.
  have hint : ∀ m, b m0 * a m = a m0 * b m := by
    intro m
    have h' : ((b m0 * a m : ℤ) : ℚ) = ((a m0 * b m : ℤ) : ℚ) := by
      push_cast
      rw [mul_comm ((b m0 : ℤ) : ℚ) ((a m : ℤ) : ℚ)]
      exact hmul m
    exact_mod_cast h'
  -- Compare the gcds of the two sides.
  have hgcd : Finset.univ.gcd (fun m => b m0 * a m) = Finset.univ.gcd (fun m => a m0 * b m) :=
    Finset.gcd_congr rfl (fun m _ => hint m)
  rw [Finset.gcd_mul_left, Finset.gcd_mul_left, ha, hb] at hgcd
  simp only [mul_one] at hgcd
  have habs : |a m0| = |b m0| := by simpa [Int.abs_eq_normalize] using hgcd.symm
  have hq : ((b m0 : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hm0
  rcases (abs_eq_abs.mp habs) with hm0eq | hm0eq
  · -- `a m0 = b m0`, so `c = 1` and `a = b`.
    left
    have hc1 : c = 1 := by
      have h0 := h m0
      rw [hm0eq] at h0
      have hx : c * ((b m0 : ℤ) : ℚ) = 1 * ((b m0 : ℤ) : ℚ) := by
        rw [one_mul]; exact h0.symm
      exact mul_right_cancel₀ hq hx
    funext m
    have hm := h m
    rw [hc1, one_mul] at hm
    exact_mod_cast hm
  · -- `a m0 = -b m0`, so `c = -1` and `a = -b`.
    right
    have hc1 : c = -1 := by
      have h0 := h m0
      rw [hm0eq] at h0
      have h0' : c * ((b m0 : ℤ) : ℚ) = -((b m0 : ℤ) : ℚ) := by
        rw [← h0]
        push_cast
        ring
      have hx : c * ((b m0 : ℤ) : ℚ) = (-1) * ((b m0 : ℤ) : ℚ) := by
        rw [neg_mul, one_mul]; exact h0'
      exact mul_right_cancel₀ hq hx
    funext m
    have hm := h m
    rw [hc1, neg_mul, one_mul] at hm
    exact_mod_cast hm

end Work.HP.BridgeAux
