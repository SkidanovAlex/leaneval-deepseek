import Mathlib

namespace NK.NUV2.ArtinBridge

/-- If an element `x` of an additive commutative group is annihilated by, for every prime `q`,
some non-zero integer `n` which is **not** divisible by `q`, then `x = 0`.

Indeed, if `x ≠ 0` then `m = addOrderOf x` satisfies `m ≠ 1`, so some prime `q` divides `m`;
writing `n` for the integer attached to `q` by the hypothesis, `n • x = 0` gives `m ∣ n`, whence
`q ∣ n`, contradicting `¬ q ∣ n`. -/
theorem eq_zero_of_forall_prime_exists_nsmul_eq_zero {Q : Type*} [AddCommGroup Q] (x : Q)
    (h : ∀ q : ℕ, q.Prime → ∃ n : ℕ, n ≠ 0 ∧ ¬ q ∣ n ∧ n • x = 0) : x = 0 := by
  by_contra hx
  -- `x ≠ 0` forces the additive order of `x` to be different from `1`.
  have hne1 : addOrderOf x ≠ 1 := by
    intro h1
    have : (1 : ℕ) • x = 0 := addOrderOf_dvd_iff_nsmul_eq_zero.mp (h1 ▸ dvd_rfl)
    rw [one_nsmul] at this
    exact hx this
  -- hence some prime `q` divides `addOrderOf x`
  obtain ⟨q, hq, hqdiv⟩ := Nat.exists_prime_and_dvd hne1
  -- the hypothesis at `q` produces `n` coprime to `q` with `n • x = 0`
  obtain ⟨n, _hn, hqn, hn0⟩ := h q hq
  -- but then `addOrderOf x ∣ n`, so `q ∣ n`: contradiction
  exact hqn (hqdiv.trans (addOrderOf_dvd_iff_nsmul_eq_zero.mpr hn0))

end NK.NUV2.ArtinBridge
