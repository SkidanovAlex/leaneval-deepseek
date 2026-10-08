import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BSLit.Wielandt

/-- If an integer `N` is divisible by every power `q ^ k` (`k ≥ 1`) of a prime `q`,
then `N = 0`. -/
theorem intCastZmodEqZero {q : ℕ} [Fact q.Prime] (N : ℤ)
    (h : ∀ k : ℕ, 1 ≤ k → (N : ZMod (q ^ k)) = 0) : N = 0 := by
  -- `q > 1`, hence powers of `q` are unbounded.
  have hq : (1 : ℤ) < (q : ℤ) := by
    have h1 : 1 < q := (Fact.out : q.Prime).one_lt
    exact_mod_cast h1
  -- Choose `n` with `|N| < q ^ n`; then `|N| < q ^ (n + 1)` as well, and `n + 1 ≥ 1`.
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (|N| : ℤ) hq
  have hle : (q : ℤ) ^ n ≤ ((q ^ (n + 1) : ℕ) : ℤ) := by
    rw [Nat.cast_pow]
    exact pow_le_pow_right₀ (le_of_lt hq) (Nat.le_succ n)
  have hkpow : |N| < ((q ^ (n + 1) : ℕ) : ℤ) := lt_of_lt_of_le hn hle
  -- The hypothesis at `k = n + 1` says that `q ^ (n + 1)` divides `N`.
  have hdvd : ((q ^ (n + 1) : ℕ) : ℤ) ∣ N :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd N (q ^ (n + 1))).mp (h (n + 1) (Nat.le_add_left 1 n))
  -- A nonzero multiple cannot be smaller in absolute value than its divisor.
  exact Int.eq_zero_of_abs_lt_dvd hdvd hkpow

end Work.BSLit.Wielandt
