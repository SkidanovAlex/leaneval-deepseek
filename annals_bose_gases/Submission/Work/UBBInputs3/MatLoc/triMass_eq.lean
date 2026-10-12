import Mathlib.Algebra.Module.NatInt
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Interval
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Work.UBBInputs3.MatLoc.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.UBBInputs3.MatLoc.triMass_eq` — the squared mass of the triangle profile

For the triangle profile `tri p s = max 0 (p + 1 - |s|)` (supported on `[-p,p]` with values
`p+1, p, …, 1`) the squared mass is

    triMass p = Σ_{s=-p}^{p} tri(s)² = (p+1)(2p² + 4p + 3)/3 .

Proof: `tri(p, ·)²` is even, so (Mathlib's `Finset.sum_Icc_of_even_eq_range`) the symmetric
sum over `[-p,p]` is `2 · Σ_{m=0}^{p} tri(p,m)² - tri(p,0)²`; on `0 ≤ m ≤ p` the absolute
value collapses and `tri(p,m) = p + 1 - m`.  The window sum `Σ_{m=0}^{p} (p+1-m)²` is
`(p+1)(p+2)(2p+3)/6`, which follows by induction from
`Σ_{m=0}^{p+1} (p+2-m)² = (p+2)² + Σ_{m=0}^{p} (p+1-m)²` (i.e. from `Σ_{k=1}^{n} k²`).
-/

noncomputable section

open scoped BigOperators
open Finset

namespace Work.UBBInputs3

/-- The window sum `Σ_{m=0}^{p} (p+1-m)² = (p+1)(p+2)(2p+3)/6`. -/
lemma triMass_window_sum (p : ℕ) :
    (∑ m ∈ Finset.range (p + 1), (((p : ℝ) + 1) - (m : ℝ)) ^ 2)
      = ((p : ℝ) + 1) * ((p : ℝ) + 2) * (2 * (p : ℝ) + 3) / 6 := by
  induction p with
  | zero => norm_num
  | succ p ih =>
    rw [Finset.sum_range_succ']
    rw [show (∑ m ∈ Finset.range (p + 1), (((↑(p + 1) : ℝ) + 1) - (↑(m + 1) : ℝ)) ^ 2)
          = (∑ m ∈ Finset.range (p + 1), (((p : ℝ) + 1) - (m : ℝ)) ^ 2) from by
        refine Finset.sum_congr rfl fun m _ => ?_
        push_cast; ring]
    rw [ih]
    push_cast
    ring

/-- `tri p` is an even function. -/
lemma tri_even (p : ℕ) : Function.Even (fun s : ℤ => (tri p s) ^ 2) := by
  intro s
  simp only [tri]
  have : ((-s : ℤ) : ℝ) = -((s : ℝ)) := by simp
  rw [this, abs_neg]

/-- On the nonnegative half `0 ≤ m ≤ p` the triangle profile is `p + 1 - m`. -/
lemma tri_nat (p m : ℕ) (hm : m ≤ p) : tri p (m : ℤ) = (p : ℝ) + 1 - (m : ℝ) := by
  simp only [tri]
  have h1 : ((m : ℤ) : ℝ) = (m : ℝ) := by simp
  rw [h1, abs_of_nonneg (by positivity)]
  have h2 : (0 : ℝ) ≤ (p : ℝ) + 1 - (m : ℝ) := by
    have : (m : ℝ) ≤ (p : ℝ) := by exact_mod_cast hm
    linarith
  exact max_eq_right h2

/-- `tri p 0 = p + 1`. -/
lemma tri_zero (p : ℕ) : tri p (0 : ℤ) = (p : ℝ) + 1 := by
  simp only [tri, Int.cast_zero, abs_zero, sub_zero]
  exact max_eq_right (by positivity)

end Work.UBBInputs3

namespace Work.UBBInputs3.MatLoc

theorem triMass_eq (p : ℕ) :
    Work.UBBInputs3.triMass p
      = ((p : ℝ) + 1) * (2 * (p : ℝ) ^ 2 + 4 * (p : ℝ) + 3) / 3 := by
  rw [Work.UBBInputs3.triMass,
    Finset.sum_Icc_of_even_eq_range (Work.UBBInputs3.tri_even p) p]
  have h1 : ∀ m ∈ Finset.range (p + 1),
      (Work.UBBInputs3.tri p (↑m : ℤ)) ^ 2 = (((p : ℝ) + 1) - (m : ℝ)) ^ 2 := by
    intro m hm
    rw [Finset.mem_range] at hm
    have hm' : m ≤ p := by omega
    rw [Work.UBBInputs3.tri_nat p m hm']
  rw [Finset.sum_congr rfl h1, Work.UBBInputs3.triMass_window_sum,
    Work.UBBInputs3.tri_zero p, two_smul]
  ring

end Work.UBBInputs3.MatLoc
