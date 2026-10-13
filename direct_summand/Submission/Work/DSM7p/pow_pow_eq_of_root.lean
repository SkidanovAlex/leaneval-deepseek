import Mathlib

namespace Work.DSM7p

/-- Compatible `p`-power roots: if `ϖ : ℕ → R` satisfies `(ϖ (k+1))^p = ϖ k` for all `k`, then
`(ϖ K)^(p^K) = ϖ 0`. -/
theorem pow_pow_eq_of_root {R : Type*} [CommRing R] {p : ℕ} (ϖ : ℕ → R)
    (h : ∀ k, (ϖ (k + 1)) ^ p = ϖ k) (K : ℕ) : (ϖ K) ^ (p ^ K) = ϖ 0 := by
  induction K with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', pow_mul, h n, ih]

end Work.DSM7p
