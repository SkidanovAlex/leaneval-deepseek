import Mathlib
import Submission.Work.FIArea2.Sec9AggDefs
import Submission.Work.FIArea2.summable_uniform_weight

/-!
# The §9 interchange kernel

The integrand of the `h`-sum/pair-sum interchange of *FI* §9 and the two facts about it used in
`Submission/Work/FIArea2/Sec9Aggregate.lean`: termwise summability (from
`summable_uniform_weight` and `(Λ,Δ) ≤ |Δ|`) and the identification of the double box sum with
the product-finset sum.
-/
set_option autoImplicit false

namespace Work.FIArea2

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section


/-- The §9 weight `τ(Δ)³|Δ|^{−1}` vanishes on the pairs with `Δ = 0`. -/
theorem sec9Core_eq_zero_of_absDelta_eq_zero (Pa : Work.FITop.Params) {z1 z2 : GaussianInt}
    (h : Work.FIPlan.absDelta z1 z2 = 0) : sec9Core Pa z1 z2 = 0 := by
  unfold sec9Core
  rw [h]
  simp

/-- `Hscale M N > 0` for admissible parameters. -/
theorem Hscale_pos (Pa : Work.FITop.Params) : 0 < Work.FIPlan.Hscale Pa.M Pa.N := by
  rw [Work.FIPlan.Hscale]
  exact mul_pos (Real.rpow_pos_of_pos (by linarith [Pa.hM1]) _)
    (Real.rpow_pos_of_pos (by linarith [Pa.hN1]) _)

/-! ## 2. The interchange of the `h`-sum with the pair sum -/

/-- The integrand of the swap: the pair weight times the frequency weight. -/
def sec9Swap (Pa : Work.FITop.Params) (z1 z2 : GaussianInt) (h : ℤ × ℤ) : ℝ :=
  sec9Core Pa z1 z2 *
    (if h = (0, 0) then 0 else (gcdDelta z1 z2 h.1 h.2 : ℝ) * sec9Uwt Pa h.1 h.2)

theorem summable_sec9Swap (Pa : Work.FITop.Params) (z1 z2 : GaussianInt) :
    Summable (fun h : ℤ × ℤ => sec9Swap Pa z1 z2 h) := by
  by_cases hD : Work.FIPlan.Delta z1 z2 = 0
  · have h0 : Work.FIPlan.absDelta z1 z2 = 0 := by
      unfold Work.FIPlan.absDelta; rw [hD]; simp
    have hc0 : sec9Core Pa z1 z2 = 0 := sec9Core_eq_zero_of_absDelta_eq_zero Pa h0
    refine (summable_zero).congr fun h => ?_
    simp [sec9Swap, hc0]
  · have hsum := summable_uniform_weight z1 z2 hD (Work.FIPlan.Hscale Pa.M Pa.N)
      (Hscale_pos Pa)
    refine (hsum.mul_left (sec9Core Pa z1 z2)).congr fun h => ?_
    by_cases hh : h = (0, 0)
    · simp [sec9Swap, hh]
    · simp only [sec9Swap, sec9Uwt, if_neg hh]
      ring

/-- The double sum over the box as a sum over the product finset. -/
theorem sec9Sum_product (Pa : Work.FITop.Params) (h : ℤ × ℤ) :
    (∑ p ∈ (Work.FITop.boxN Pa).product (Work.FITop.boxN Pa), sec9Swap Pa p.1 p.2 h)
      = ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa, sec9Swap Pa z1 z2 h :=
  Finset.sum_product _ _ (fun p : GaussianInt × GaussianInt => sec9Swap Pa p.1 p.2 h)


/-- The interchange of the frequency sum with the pair sum, for the §9 integrand. -/
theorem sec9_tsum_swap (Pa : Work.FITop.Params) :
    (∑' h : ℤ × ℤ, ∑ p ∈ (Work.FITop.boxN Pa).product (Work.FITop.boxN Pa),
        sec9Swap Pa p.1 p.2 h)
      = ∑ p ∈ (Work.FITop.boxN Pa).product (Work.FITop.boxN Pa),
          ∑' h : ℤ × ℤ, sec9Swap Pa p.1 p.2 h := by
  refine Summable.tsum_finsetSum (L := SummationFilter.unconditional (ℤ × ℤ))
    (s := (Work.FITop.boxN Pa).product (Work.FITop.boxN Pa))
    (f := fun p (h : ℤ × ℤ) => sec9Swap Pa p.1 p.2 h) ?_
  intro p _
  exact summable_sec9Swap Pa p.1 p.2

end

end Work.FIArea2
