import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Submission.Work.UBBInputs3.MatLoc.gamma_neg_eq
import Submission.Work.UBBInputs3.MatLoc.prof_zero_outside
import Submission.Work.UBBInputs3.MatLoc.shift_sum_collapse
import Submission.Work.UBBInputs3.MatLoc.telescope_sq_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.UBBInputs3.MatLoc.gamma_le_shift` — the basic profile estimate `γ_k ≤ ½ k² G`

For the normalised triangle profile `prof p` (support `[-p,p]`, `Σ_s prof(s)² = 1`) one has,
for every shift `k : ℤ`,

    γ_k = ½ Σ_s (prof(s+k) - prof(s))² ≤ (k²/2) · G,   G = Σ_s (prof(s+1) - prof(s))².

The proof is the usual telescoping/Cauchy–Schwarz estimate: writing `D s = prof(s+1) - prof s`
one has `prof(s+k) - prof(s) = Σ_{i<k} D(s+i)`, so by Cauchy–Schwarz
`(prof(s+k) - prof(s))² ≤ k Σ_{i<k} D(s+i)²`; summing over the (symmetric, and hence
large enough) window `[-p-k, p+k]` and translating each inner sum back to `[-p-1, p+1]`
— legitimate because `D` is supported in `[-p-1, p]` — produces a factor `k²`.  The case of
negative `k` reduces to the positive one by the evenness `γ_{-k} = γ_k` (the profile is even
and the window symmetric).

The three ingredients are the delegated lemmas `telescope_sq_le` (the pointwise
Cauchy–Schwarz bound), `shift_sum_collapse` (the translation of each inner sum, using that
`prof` is supported in `[-p,p]`), and `gamma_neg_eq` (evenness in the shift).
-/

noncomputable section

open scoped BigOperators
open Finset

namespace Work.UBBInputs3.MatLoc

/-- The nonnegative-shift estimate: `γ_k ≤ (k²/2)·G` for `k = (m : ℤ)`, `m : ℕ`. -/
theorem gamma_nat_le (p m : ℕ) :
    Work.UBBInputs3.gamma p (m : ℤ) ≤ ((m : ℝ) ^ 2 / 2) * Work.UBBInputs3.profG p := by
  -- Identification of `γ_{(m:ℤ)}` with the window sum over `[-p-m, p+m]`.
  have hgamma : Work.UBBInputs3.gamma p (m : ℤ)
      = (1 / 2) * ∑ s ∈ Finset.Icc (-(p : ℤ) - (m : ℤ)) ((p : ℤ) + (m : ℤ)),
          (Work.UBBInputs3.prof p (s + (m : ℤ)) - Work.UBBInputs3.prof p s) ^ 2 := by
    rw [Work.UBBInputs3.gamma, Int.abs_eq_natAbs,
      Int.natAbs_of_nonneg (Int.natCast_nonneg m)]
  -- The sum-level bound, obtained by summing the pointwise Cauchy–Schwarz bound.
  have hbound : (∑ s ∈ Finset.Icc (-(p : ℤ) - (m : ℤ)) ((p : ℤ) + (m : ℤ)),
          (Work.UBBInputs3.prof p (s + (m : ℤ)) - Work.UBBInputs3.prof p s) ^ 2)
        ≤ (m : ℝ) ^ 2 * Work.UBBInputs3.profG p := by
    calc ∑ s ∈ Finset.Icc (-(p : ℤ) - (m : ℤ)) ((p : ℤ) + (m : ℤ)),
            (Work.UBBInputs3.prof p (s + (m : ℤ)) - Work.UBBInputs3.prof p s) ^ 2
        ≤ ∑ s ∈ Finset.Icc (-(p : ℤ) - (m : ℤ)) ((p : ℤ) + (m : ℤ)),
            (m : ℝ) * ∑ i ∈ Finset.range m,
              (Work.UBBInputs3.prof p (s + (i : ℤ) + 1) - Work.UBBInputs3.prof p (s + (i : ℤ))) ^ 2 :=
          Finset.sum_le_sum (fun s _ => telescope_sq_le (Work.UBBInputs3.prof p) m s)
      _ = (m : ℝ) * ∑ s ∈ Finset.Icc (-(p : ℤ) - (m : ℤ)) ((p : ℤ) + (m : ℤ)),
            ∑ i ∈ Finset.range m,
              (Work.UBBInputs3.prof p (s + (i : ℤ) + 1) - Work.UBBInputs3.prof p (s + (i : ℤ))) ^ 2 := by
          rw [Finset.mul_sum]
      _ = (m : ℝ) * ∑ i ∈ Finset.range m, ∑ s ∈ Finset.Icc (-(p : ℤ) - (m : ℤ)) ((p : ℤ) + (m : ℤ)),
              (Work.UBBInputs3.prof p (s + (i : ℤ) + 1) - Work.UBBInputs3.prof p (s + (i : ℤ))) ^ 2 := by
          rw [Finset.sum_comm]
      _ = (m : ℝ) * ∑ i ∈ Finset.range m, Work.UBBInputs3.profG p := by
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          rw [shift_sum_collapse (Work.UBBInputs3.prof p) p m i (Finset.mem_range.mp hi)
                (fun s hs => prof_zero_outside p s hs)]
          rfl
      _ = (m : ℝ) ^ 2 * Work.UBBInputs3.profG p := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  rw [hgamma]
  calc (1 / 2) * (∑ s ∈ Finset.Icc (-(p : ℤ) - (m : ℤ)) ((p : ℤ) + (m : ℤ)),
          (Work.UBBInputs3.prof p (s + (m : ℤ)) - Work.UBBInputs3.prof p s) ^ 2)
      ≤ (1 / 2) * ((m : ℝ) ^ 2 * Work.UBBInputs3.profG p) :=
        mul_le_mul_of_nonneg_left hbound (by norm_num)
    _ = ((m : ℝ) ^ 2 / 2) * Work.UBBInputs3.profG p := by ring

theorem gamma_le_shift (p : ℕ) (k : ℤ) :
    Work.UBBInputs3.gamma p k ≤ ((k : ℝ) ^ 2 / 2) * Work.UBBInputs3.profG p := by
  rcases Int.eq_nat_or_neg k with ⟨m, hm | hm⟩
  · rw [hm]
    simpa using gamma_nat_le p m
  · rw [hm, gamma_neg_eq p (m : ℤ)]
    rw [show (((-(m : ℤ) : ℤ)) : ℝ) = -(m : ℝ) by push_cast; ring, neg_sq]
    exact gamma_nat_le p m

end Work.UBBInputs3.MatLoc
