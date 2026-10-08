import Mathlib
import Submission.Work.Higman.QuadAux

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman

/-- **Linear independence of the Frobenius power maps.**  Over a field `F` with
`|F| = 2 ^ n`, the coordinate functions `x ↦ x ^ (2 ^ k)`, `k < n`, are linearly
independent over `F`:  if `∑_{k < n} c k * x ^ (2 ^ k) = 0` for every `x : F`, then
every `c k` vanishes.

This is the special case of `monomial_indep_finset` for the exponent map `k ↦ 2 ^ k`,
whose exponents are pairwise distinct and all `< |F| = 2 ^ n` for `k < n`. -/
theorem frobenius_powers_indep {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {n : ℕ} (hcard : Fintype.card F = 2 ^ n) (c : ℕ → F)
    (h : ∀ x : F, ∑ k ∈ Finset.range n, c k * x ^ (2 ^ k) = 0) :
    ∀ k ∈ Finset.range n, c k = 0 := by
  refine monomial_indep_finset (Finset.range n) (fun k => 2 ^ k) ?_ ?_ c h
  · intro a _ b _ hab
    exact Nat.pow_right_injective (by norm_num) hab
  · intro k hk
    rw [Finset.mem_range] at hk
    rw [hcard]
    exact Nat.pow_lt_pow_right (by norm_num) hk

theorem coeff_vanishing_of_scale {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
    {n : ℕ} (hcard : Fintype.card F = 2 ^ n) (nu lam : F) (d : ℕ → ℕ → F)
    (h : ∀ x y : F, ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
      (d k l * (nu ^ (2 ^ k + 2 ^ l) - lam)) * x ^ (2 ^ k) * y ^ (2 ^ l) = 0) :
    ∀ k l : ℕ, k < n → l < n → d k l * (nu ^ (2 ^ k + 2 ^ l) - lam) = 0 := by
  -- Step 1: for each fixed `y`, the coefficients `k ↦ ∑_l (d k l * (ν ^ (2^k+2^l) - λ)) * y ^ (2^l)`
  -- of the `x`-expansion vanish, by linear independence of `x ↦ x ^ (2 ^ k)`.
  have step1 : ∀ y : F, ∀ k ∈ Finset.range n,
      (∑ l ∈ Finset.range n, (d k l * (nu ^ (2 ^ k + 2 ^ l) - lam)) * y ^ (2 ^ l)) = 0 := by
    intro y
    refine frobenius_powers_indep hcard
      (fun k => ∑ l ∈ Finset.range n, (d k l * (nu ^ (2 ^ k + 2 ^ l) - lam)) * y ^ (2 ^ l)) ?_
    intro x
    rw [← h x y]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l hl
    ring
  -- Step 2: for each fixed `k`, the resulting relation in `y` forces `d k l * (ν ^ (2^k+2^l) - λ) = 0`.
  intro k l hk hl
  have hk_mem : k ∈ Finset.range n := Finset.mem_range.mpr hk
  have h2 := frobenius_powers_indep hcard
    (fun l => d k l * (nu ^ (2 ^ k + 2 ^ l) - lam))
    (fun y => step1 y k hk_mem)
  exact h2 l (Finset.mem_range.mpr hl)

end Work.Higman
