import Mathlib
import Submission.Work.WilC4.Defs

namespace Work.WilC4

/-- For `x > 0`, the defining relation `IsRpow` for the exponent `p / n` is already *saturated*:
it holds for `t` exactly when `t^n = x^p` and `t` is `0` or a nonzero square.  The content is the
forward direction: any other pair `(p', n')` presenting the same rational `p / n` with
`t ^ n' = x ^ p'` yields the same relation `t ^ n = x ^ p` (the elementary fact that on
nonnegative reals `u ↦ u ^ n'` is injective). -/
theorem isRpow_canon {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M] {x t : M} {p : ℤ} {n : ℕ} (hn : 0 < n) (hx : 0 < x) : Work.WilC4.IsRpow x ((p : ℚ) / (n : ℚ)) t ↔ t ^ n = x ^ p ∧ (t = 0 ∨ ∃ w : M, w ≠ 0 ∧ w ^ 2 = t) := by
  constructor
  · rintro ⟨p', n', hn', hq, hpow, hsq⟩
    refine ⟨?_, hsq⟩
    -- `p / n = p' / n'` forces `p * n' = p' * n`
    have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
    have hn'q : (n' : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hn')
    have hkey : (p : ℚ) * (n' : ℚ) = (p' : ℚ) * (n : ℚ) := (div_eq_div_iff hnq hn'q).mp hq
    have hkeyZ : p * (n' : ℤ) = p' * (n : ℤ) := by exact_mod_cast hkey
    -- `t` is `0` or a nonzero square, hence nonnegative
    have ht0 : 0 ≤ t := by
      rcases hsq with h | ⟨w, hw, hw2⟩
      · rw [h]
      · rw [← hw2]; exact (sq_pos_of_ne_zero hw).le
    -- raise `t ^ n' = x ^ p'` to the `n`-th power
    have hpow' : (t ^ n) ^ n' = (x ^ p) ^ n' := by
      have h1 : (t ^ n) ^ n' = t ^ (n * n') := (pow_mul t n n').symm
      have h2 : (x ^ p) ^ n' = x ^ (p * (n' : ℤ)) := by
        rw [← zpow_natCast (x ^ p) n', ← zpow_mul]
      have h3 : t ^ (n * n') = x ^ (p * (n' : ℤ)) := by
        rw [Nat.mul_comm n n', pow_mul, hpow, ← zpow_natCast (x ^ p') n, ← zpow_mul, hkeyZ]
      rw [h1, h3, ← h2]
    -- injectivity of `u ↦ u ^ n'` on nonnegative elements
    have htn0 : 0 ≤ t ^ n := pow_nonneg ht0 n
    have hxp0 : 0 ≤ x ^ p := (zpow_pos hx p).le
    exact (pow_left_inj₀ htn0 hxp0 (ne_of_gt hn')).mp hpow'
  · rintro ⟨hpow, hsq⟩
    exact ⟨p, n, hn, rfl, hpow, hsq⟩

end Work.WilC4
