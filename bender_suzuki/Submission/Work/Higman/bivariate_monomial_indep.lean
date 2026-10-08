import Mathlib
import Submission.Work.Higman.QuadAux
import Submission.Work.Higman.coeff_vanishing_of_scale

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman

/-- **Linear independence of the bivariate Frobenius monomials.**

Over a field `F` with `|F| = 2 ^ n`, the functions `(x, y) ↦ x ^ (2 ^ k) * y ^ (2 ^ l)`
for `k, l < n` are linearly independent over `F`:  if
`∑_{k < n} ∑_{l < n} c k l * x ^ (2 ^ k) * y ^ (2 ^ l) = 0` for every `x y : F`, then
every `c k l` vanishes.

Fixing `y` and applying `frobenius_powers_indep` in the variable `x` shows that each
coefficient `∑_{l < n} c k l * y ^ (2 ^ l)` vanishes for all `y`; applying the same
lemma in the variable `y` then gives `c k l = 0`. -/
theorem bivariate_monomial_indep {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}
    (hcard : Fintype.card F = 2 ^ n) (c : ℕ → ℕ → F)
    (h : ∀ x y, ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n, c k l * x ^ (2 ^ k) * y ^ (2 ^ l) = 0) :
    ∀ k ∈ Finset.range n, ∀ l ∈ Finset.range n, c k l = 0 := by
  -- Step 1: for each fixed `y`, the `x`-coefficients `k ↦ ∑_l c k l * y ^ (2 ^ l)` vanish.
  have step1 : ∀ y : F, ∀ k ∈ Finset.range n,
      (∑ l ∈ Finset.range n, c k l * y ^ (2 ^ l)) = 0 := by
    intro y
    refine frobenius_powers_indep hcard
      (fun k => ∑ l ∈ Finset.range n, c k l * y ^ (2 ^ l)) ?_
    intro x
    rw [← h x y]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l hl
    ring
  -- Step 2: for each fixed `k`, the resulting relation in `y` forces `c k l = 0`.
  intro k hk l hl
  exact frobenius_powers_indep hcard (fun l => c k l) (fun y => step1 y k hk) l hl

end Work.Higman
