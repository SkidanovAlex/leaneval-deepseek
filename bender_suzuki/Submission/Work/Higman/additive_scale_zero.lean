import Mathlib
import Submission.Work.Higman.QuadAux

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman

theorem additive_scale_zero {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
    {n : ℕ} (hcard : Fintype.card F = 2 ^ n) (nu lam : F) (a : ℕ → F)
    (h : ∀ x : F, ∑ k ∈ Finset.range n, (a k * (nu ^ (2 ^ k) - lam)) * x ^ (2 ^ k) = 0)
    (hne : ∀ k : ℕ, k < n → nu ^ (2 ^ k) ≠ lam) :
    ∀ k : ℕ, k < n → a k = 0 := by
  intro k hk
  -- The functions `x ↦ x ^ (2 ^ m)` (`m < n`) have distinct exponents, all `< |F| = 2 ^ n`,
  -- so by linear independence of monomials every coefficient `a m * (nu ^ (2 ^ m) - lam)`
  -- must vanish.
  have hzero : ∀ m ∈ Finset.range n, a m * (nu ^ (2 ^ m) - lam) = 0 :=
    monomial_indep_finset (Finset.range n) (fun m => 2 ^ m)
      (fun m _ m' _ hm => Nat.pow_right_injective (by norm_num : 1 < (2 : ℕ)) hm)
      (fun m hm => by
        rw [Finset.mem_range] at hm
        rw [hcard]
        exact Nat.pow_lt_pow_right (by norm_num : 1 < 2) hm)
      (fun m => a m * (nu ^ (2 ^ m) - lam)) h
  have hc := hzero k (Finset.mem_range.mpr hk)
  rcases mul_eq_zero.mp hc with h1 | h1
  · exact h1
  · exact absurd h1 (sub_ne_zero.mpr (hne k hk))

end Work.Higman
