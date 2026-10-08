import Mathlib
import Submission.Work.Higman.QuadAux
import Submission.Work.Higman.sum_range_lt_split
import Submission.Work.Higman.sum_range_lt_swap

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman

/-- Term-by-term expansion in characteristic two: the "polar" of the monomials `x ^ (2^k + 2^l)`.
`(x+y)^(2^k+2^l) + x^(2^k+2^l) + y^(2^k+2^l) = x^(2^k) y^(2^l) + x^(2^l) y^(2^k)`. -/
theorem polar_term_id {F : Type*} [Field F] [CharP F 2] (x y c : F) (k l : ℕ) :
    c * (x + y) ^ (2 ^ k + 2 ^ l) + c * x ^ (2 ^ k + 2 ^ l) + c * y ^ (2 ^ k + 2 ^ l)
      = c * x ^ (2 ^ k) * y ^ (2 ^ l) + c * x ^ (2 ^ l) * y ^ (2 ^ k) := by
  have hcross : (x + y) ^ (2 ^ k + 2 ^ l) + x ^ (2 ^ k + 2 ^ l) + y ^ (2 ^ k + 2 ^ l)
      = x ^ (2 ^ k) * y ^ (2 ^ l) + x ^ (2 ^ l) * y ^ (2 ^ k) := by
    have h3 : (x + y) ^ (2 ^ k + 2 ^ l)
        = x ^ (2 ^ k + 2 ^ l) + x ^ (2 ^ k) * y ^ (2 ^ l) + y ^ (2 ^ k) * x ^ (2 ^ l)
          + y ^ (2 ^ k + 2 ^ l) := by
      rw [pow_add, add_pow_char_pow, add_pow_char_pow]
      ring
    rw [h3]
    have hgrp : x ^ (2 ^ k + 2 ^ l) + x ^ (2 ^ k) * y ^ (2 ^ l) + y ^ (2 ^ k) * x ^ (2 ^ l)
        + y ^ (2 ^ k + 2 ^ l) + x ^ (2 ^ k + 2 ^ l) + y ^ (2 ^ k + 2 ^ l)
        = (x ^ (2 ^ k + 2 ^ l) + x ^ (2 ^ k + 2 ^ l))
          + (y ^ (2 ^ k + 2 ^ l) + y ^ (2 ^ k + 2 ^ l))
          + (x ^ (2 ^ k) * y ^ (2 ^ l) + y ^ (2 ^ k) * x ^ (2 ^ l)) := by ring
    rw [hgrp, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, zero_add, zero_add]
    ring
  calc c * (x + y) ^ (2 ^ k + 2 ^ l) + c * x ^ (2 ^ k + 2 ^ l) + c * y ^ (2 ^ k + 2 ^ l)
      = c * ((x + y) ^ (2 ^ k + 2 ^ l) + x ^ (2 ^ k + 2 ^ l) + y ^ (2 ^ k + 2 ^ l)) := by ring
    _ = c * (x ^ (2 ^ k) * y ^ (2 ^ l) + x ^ (2 ^ l) * y ^ (2 ^ k)) := by rw [hcross]
    _ = c * x ^ (2 ^ k) * y ^ (2 ^ l) + c * x ^ (2 ^ l) * y ^ (2 ^ k) := by ring

theorem polar_Q1_eq_B {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
    {n : ℕ} (d : ℕ → ℕ → F) (hddiag : ∀ k, d k k = 0) (hdsym : ∀ k l, d k l = d l k)
    (B : F → F → F)
    (hB : ∀ x y, B x y = ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
      d k l * x ^ (2 ^ k) * y ^ (2 ^ l)) :
    ∀ x y, (∑ k ∈ Finset.range n, ∑ l ∈ (Finset.range n).filter (fun l => k < l),
        d k l * (x + y) ^ (2 ^ k + 2 ^ l))
      + (∑ k ∈ Finset.range n, ∑ l ∈ (Finset.range n).filter (fun l => k < l),
        d k l * x ^ (2 ^ k + 2 ^ l))
      + (∑ k ∈ Finset.range n, ∑ l ∈ (Finset.range n).filter (fun l => k < l),
        d k l * y ^ (2 ^ k + 2 ^ l)) = B x y := by
  intro x y
  -- Both sides equal the "polar" sum over the pairs `k < l`, i.e.
  -- `∑_{k<l} (d k l x^(2^k) y^(2^l) + d k l x^(2^l) y^(2^k))`.
  trans (∑ k ∈ Finset.range n, ∑ l ∈ (Finset.range n).filter (fun l => k < l),
      (d k l * x ^ (2 ^ k) * y ^ (2 ^ l) + d k l * x ^ (2 ^ l) * y ^ (2 ^ k)))
  · -- Left-hand side: expand the three sums termwise.
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro l hl
    exact polar_term_id x y (d k l) k l
  · -- Right-hand side: `B x y` is the full double sum, whose diagonal vanishes.
    symm
    rw [hB x y]
    have hsplit := sum_range_lt_split n (fun k l => d k l * x ^ (2 ^ k) * y ^ (2 ^ l))
    rw [hsplit]
    have hP3 :
        (∑ k ∈ Finset.range n, (fun k l => d k l * x ^ (2 ^ k) * y ^ (2 ^ l)) k k) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      simp [hddiag k]
    have hP2 := sum_range_lt_swap n (fun k l => d k l * x ^ (2 ^ k) * y ^ (2 ^ l))
    rw [hP3, hP2, add_zero]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro l hl
    rw [(hdsym k l).symm]

end Work.Higman
