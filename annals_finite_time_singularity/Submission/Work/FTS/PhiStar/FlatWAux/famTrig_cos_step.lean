import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Data.Int.Star
import Submission.Work.FTS.PhiStar.FamLopAux.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.FlatWAux

set_option autoImplicit false

/-- `famC` vanishes on the negative integers (local copy, keeping the import base minimal). -/
private lemma famC_eq_zero_of_neg' {k : ℤ} (hk : k < 0) : Work.FTS.PhiStar.famC k = 0 := by
  rw [Work.FTS.PhiStar.famC]
  rw [if_neg]
  omega

/-- The product-to-sum identity: `2·cos a·(A·cos b) = A·(cos (a+b) + cos (a-b))`. -/
private lemma two_cos_mul_aux' (A a b : ℝ) :
    2 * (Real.cos a * (A * Real.cos b)) = A * (Real.cos (a + b) + Real.cos (a - b)) := by
  rw [Real.cos_add, Real.cos_sub]
  ring

/--
The three-term Gegenbauer recurrence in its product-to-sum form: the angular shift
`cos ψ · famTrig (n+1) ψ` is the symmetric average of the two neighbouring coefficient
families, `famC j · famC (n+1-j)` and `famC (j-1) · famC (n+2-j)`, read against the
common cosine `cos ((2j - n - 2)ψ)`.

The proof reindexes the second family (`famC ((j:ℤ)-1) · famC ((n:ℤ)+2-(j:ℤ))`
is `famC (i:ℤ) · famC ((n:ℤ)+1-(i:ℤ))` at `i = j+1`, the `j = 0` boundary being
`famC (-1) = 0`, and the first family truncates at `j = n+2` for the same reason),
and then uses `cos(A-ψ) + cos(A+ψ) = 2 cos A cos ψ`.
-/
theorem famTrig_cos_step (n : ℕ) (ψ : ℝ) :
    Real.cos ψ * Work.FTS.PhiStar.famTrig (n + 1) ψ
      = ∑ j ∈ Finset.range (n + 3),
          (Work.FTS.PhiStar.famC (j : ℤ) * Work.FTS.PhiStar.famC ((n : ℤ) + 1 - (j : ℤ))
            + Work.FTS.PhiStar.famC ((j : ℤ) - 1) * Work.FTS.PhiStar.famC ((n : ℤ) + 2 - (j : ℤ)))
            * Real.cos ((2 * (j : ℝ) - ((n : ℝ) + 2)) * ψ) / 2 := by
  -- the two coefficient families and the common cosine
  set P : ℕ → ℝ := fun i =>
    Work.FTS.PhiStar.famC (i : ℤ) * Work.FTS.PhiStar.famC ((n : ℤ) + 1 - (i : ℤ)) with hP
  set Q : ℕ → ℝ := fun i =>
    Work.FTS.PhiStar.famC ((i : ℤ) - 1) * Work.FTS.PhiStar.famC ((n : ℤ) + 2 - (i : ℤ)) with hQ
  set K : ℕ → ℝ := fun i => Real.cos ((2 * (i : ℝ) - ((n : ℝ) + 2)) * ψ) with hK
  -- `famTrig (n+1)` against the family `P`
  have hfam : Work.FTS.PhiStar.famTrig (n + 1) ψ
      = ∑ j ∈ Finset.range (n + 2),
          P j * Real.cos ((2 * (j : ℝ) - ((n : ℝ) + 1)) * ψ) := by
    rw [Work.FTS.PhiStar.famTrig]
    refine Finset.sum_congr (by rfl) (fun j _ => ?_)
    simp only [hP]
    rw [show ((((n + 1 : ℕ)) : ℤ)) - (j : ℤ) = (n : ℤ) + 1 - (j : ℤ) from by push_cast; ring,
        show (((2 : ℝ) * (j : ℝ) - ((((n + 1 : ℕ)) : ℝ))) * ψ)
            = ((2 : ℝ) * (j : ℝ) - ((n : ℝ) + 1)) * ψ from by push_cast; ring]
  -- the left-hand side, as a sum over `j ∈ range (n+2)`
  have hLHS : 2 * (Real.cos ψ * Work.FTS.PhiStar.famTrig (n + 1) ψ)
      = ∑ j ∈ Finset.range (n + 2), P j * (K j + K (j + 1)) := by
    rw [hfam, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr (by rfl) (fun j _ => ?_)
    simp only [hP, hK]
    rw [show 2 * (Real.cos ψ * (Work.FTS.PhiStar.famC (j : ℤ)
            * Work.FTS.PhiStar.famC ((n : ℤ) + 1 - (j : ℤ))
            * Real.cos (((2 : ℝ) * (j : ℝ) - ((n : ℝ) + 1)) * ψ)))
          = 2 * (Real.cos (((2 : ℝ) * (j : ℝ) - ((n : ℝ) + 1)) * ψ)
              * (Work.FTS.PhiStar.famC (j : ℤ)
                * Work.FTS.PhiStar.famC ((n : ℤ) + 1 - (j : ℤ))
                * Real.cos ψ)) from by ring]
    rw [two_cos_mul_aux']
    rw [show (((2 : ℝ) * (j : ℝ) - ((n : ℝ) + 1)) * ψ) + ψ
          = (2 * ((((j + 1 : ℕ)) : ℝ)) - ((n : ℝ) + 2)) * ψ from by push_cast; ring,
        show (((2 : ℝ) * (j : ℝ) - ((n : ℝ) + 1)) * ψ) - ψ
          = (2 * (j : ℝ) - ((n : ℝ) + 2)) * ψ from by ring]
    ring
  -- the boundary terms
  have hPtop : P (n + 2) = 0 := by
    simp only [hP]
    rw [show (n : ℤ) + 1 - ((((n + 2 : ℕ)) : ℤ)) = (-1 : ℤ) from by push_cast; ring,
        famC_eq_zero_of_neg' (by norm_num : (-1 : ℤ) < 0), mul_zero]
  have hQ0 : Q 0 = 0 := by
    simp only [hQ]
    rw [show (((0 : ℕ)) : ℤ) - 1 = (-1 : ℤ) from by norm_num,
        famC_eq_zero_of_neg' (by norm_num : (-1 : ℤ) < 0), zero_mul]
  have hQP : ∀ j : ℕ, Q (j + 1) = P j := by
    intro j
    simp only [hQ, hP]
    rw [show ((((j + 1 : ℕ)) : ℤ)) - 1 = (j : ℤ) from by push_cast; ring,
        show (n : ℤ) + 2 - ((((j + 1 : ℕ)) : ℤ)) = (n : ℤ) + 1 - (j : ℤ) from by push_cast; ring]
  -- the `P`-sum truncates at `n+2`
  have hsum1 : (∑ i ∈ Finset.range (n + 3), P i * K i)
      = ∑ i ∈ Finset.range (n + 2), P i * K i := by
    have h := Finset.sum_range_succ (fun i => P i * K i) (n + 2)
    rw [hPtop, zero_mul, add_zero] at h
    exact h
  -- the `Q`-sum is the shifted `P`-sum
  have hsum2 : (∑ i ∈ Finset.range (n + 3), Q i * K i)
      = ∑ j ∈ Finset.range (n + 2), P j * K (j + 1) := by
    have h := Finset.sum_range_succ' (fun i => Q i * K i) (n + 2)
    rw [hQ0, zero_mul, add_zero] at h
    rw [h]
    refine Finset.sum_congr (by rfl) (fun j _ => ?_)
    rw [hQP j]
  -- the right-hand side, in the `P`/`K` normal form
  have hRHS : (∑ i ∈ Finset.range (n + 3), (P i + Q i) * K i)
      = ∑ j ∈ Finset.range (n + 2), P j * (K j + K (j + 1)) := by
    have hsplit : (∑ i ∈ Finset.range (n + 3), (P i + Q i) * K i)
        = (∑ i ∈ Finset.range (n + 3), P i * K i)
          + (∑ i ∈ Finset.range (n + 3), Q i * K i) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [hsplit, hsum1, hsum2, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  -- the doubled identity
  have hmain : 2 * (Real.cos ψ * Work.FTS.PhiStar.famTrig (n + 1) ψ)
      = ∑ i ∈ Finset.range (n + 3), (P i + Q i) * K i := hLHS.trans hRHS.symm
  -- unfold the abbreviations
  have hfinal : (∑ i ∈ Finset.range (n + 3), (P i + Q i) * K i) / 2
      = ∑ j ∈ Finset.range (n + 3),
          (Work.FTS.PhiStar.famC (j : ℤ) * Work.FTS.PhiStar.famC ((n : ℤ) + 1 - (j : ℤ))
            + Work.FTS.PhiStar.famC ((j : ℤ) - 1) * Work.FTS.PhiStar.famC ((n : ℤ) + 2 - (j : ℤ)))
            * Real.cos ((2 * (j : ℝ) - ((n : ℝ) + 2)) * ψ) / 2 := by
    rw [Finset.sum_div]
  rw [← hfinal, ← hmain]
  ring

end Work.FTS.PhiStar.FlatWAux
