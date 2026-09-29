import Mathlib
import Submission.Work.ConvR.basic

/-!
# `negaMul` is additive in each argument (left/right linearity over `ℂ`)

The product in the synthetic ring `ℝ = ℂ[y]/(y^r+1)`,
`negaMul r a b = a * b`, is bilinear: both the left and the right factor can be
pulled out of a difference.  This is the `negaMul`-additivity conjunct of
`Work.ConvR.norms`.

The proof is pointwise in the output index `k`: each summand of the defining
double sum is a product of the two `k`-th coefficient families, and splitting
the `if` on the two wrap-around cases reduces it to `mul_sub`/`sub_mul`; then the
subtraction is pulled out of the `Finset` sums.
-/

set_option autoImplicit false

namespace Work.ConvR

open HvdH

theorem negaLin (r : ℕ) :
    (∀ (a a' b : Fin r → ℂ),
      HvdH.negaMul r (a - a') b = HvdH.negaMul r a b - HvdH.negaMul r a' b) ∧
    (∀ (a b b' : Fin r → ℂ),
      HvdH.negaMul r a (b - b') = HvdH.negaMul r a b - HvdH.negaMul r a b') := by
  constructor
  · intro a a' b
    funext k
    simp only [HvdH.negaMul, Pi.sub_apply]
    have h : ∀ i j : Fin r,
        (if (i : ℕ) + (j : ℕ) = (k : ℕ) then (a i - a' i) * b j
         else if (i : ℕ) + (j : ℕ) = (k : ℕ) + r then -((a i - a' i) * b j) else 0)
        = (if (i : ℕ) + (j : ℕ) = (k : ℕ) then a i * b j
           else if (i : ℕ) + (j : ℕ) = (k : ℕ) + r then -(a i * b j) else 0)
          - (if (i : ℕ) + (j : ℕ) = (k : ℕ) then a' i * b j
             else if (i : ℕ) + (j : ℕ) = (k : ℕ) + r then -(a' i * b j) else 0) := by
      intro i j
      split <;> (try split) <;> ring
    simp_rw [h]
    simp only [Finset.sum_sub_distrib]
  · intro a b b'
    funext k
    simp only [HvdH.negaMul, Pi.sub_apply]
    have h : ∀ i j : Fin r,
        (if (i : ℕ) + (j : ℕ) = (k : ℕ) then a i * (b j - b' j)
         else if (i : ℕ) + (j : ℕ) = (k : ℕ) + r then -(a i * (b j - b' j)) else 0)
        = (if (i : ℕ) + (j : ℕ) = (k : ℕ) then a i * b j
           else if (i : ℕ) + (j : ℕ) = (k : ℕ) + r then -(a i * b j) else 0)
          - (if (i : ℕ) + (j : ℕ) = (k : ℕ) then a i * b' j
             else if (i : ℕ) + (j : ℕ) = (k : ℕ) + r then -(a i * b' j) else 0) := by
      intro i j
      split <;> (try split) <;> ring
    simp_rw [h]
    simp only [Finset.sum_sub_distrib]

end Work.ConvR
