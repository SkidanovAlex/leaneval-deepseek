import Mathlib
import Submission.Work.FIArea2.R6.SixDefs
import Submission.Work.FIArea2.Count.summable_Wt_tau4

namespace Work.FIArea2.R6

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The frequency weight of §9 against the `(u₁,u₂)`-sum `sec9Usumming` is summable.

`sec9Usumming Pa h₁ h₂ = Σ_{u₁,u₂ ∈ Icc(-R,R)} (u₁,u₂)·τ₄(u₁h₁² − u₂h₂²)` is a *finite* sum over
the box `Icc(-radN, radN)`, and each of its terms is summable in `h = (h₁,h₂)` by
`Work.FIArea2.Count.summable_Wt_tau4` (the weight comparison `(1+h²H⁻²)⁻¹ ≤ (1+H²)(1+h²)⁻¹`
together with the divisor bound `τ₄(m) ≪ |u₁|^{1/4}|h₁|^{1/2} + |u₂|^{1/4}|h₂|^{1/2}`). -/
lemma summable_sec9Uwt_Usumming (Pa : Work.FITop.Params) :
    Summable (fun h : ℤ × ℤ =>
      Work.FIArea2.sec9Uwt Pa h.1 h.2 * Work.FIArea2.sec9Usumming Pa h.1 h.2) := by
  have hkey : (fun h : ℤ × ℤ =>
        Work.FIArea2.sec9Uwt Pa h.1 h.2 * Work.FIArea2.sec9Usumming Pa h.1 h.2)
      = fun h : ℤ × ℤ => ∑ u1 ∈ Finset.Icc (-(Work.FITop.radN Pa)) (Work.FITop.radN Pa),
          ∑ u2 ∈ Finset.Icc (-(Work.FITop.radN Pa)) (Work.FITop.radN Pa),
            (Nat.gcd u1.natAbs u2.natAbs : ℝ)
              * (Work.FIArea2.sec9Uwt Pa h.1 h.2
                  * (((u1 * h.1 ^ 2 - u2 * h.2 ^ 2).natAbs.divisors.card : ℝ) ^ 4)) := by
    funext h
    unfold Work.FIArea2.sec9Usumming
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u1 _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u2 _ => ?_
    ring
  rw [hkey]
  refine summable_sum (s := Finset.Icc (-(Work.FITop.radN Pa)) (Work.FITop.radN Pa)) ?_
  intro u1 _
  refine summable_sum (s := Finset.Icc (-(Work.FITop.radN Pa)) (Work.FITop.radN Pa)) ?_
  intro u2 _
  exact (Work.FIArea2.Count.summable_Wt_tau4 Pa u1 u2).mul_left _

end

end Work.FIArea2.R6
