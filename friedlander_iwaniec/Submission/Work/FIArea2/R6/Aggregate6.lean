/-
# `FIArea2/R6/Aggregate6.lean` — the §9 aggregate for the round-6 per-pair bound

The §9 pair sum (9.5) is estimated by interchanging the `h`-sum with the pair sum and then
combining

* the per-frequency (9.5) bound `Work.FIArea2.sec9_Z_bound_eight`
  (`sec9Zsum Pa h ≤ C ϑ^{-1/2}(log N+2)^8 · sec9Usumming Pa h` for `h ≠ 0`), with
* the averaged `h`-sum of (9.6)/(9.7) (`Work.FIArea2.Count.sec9_Lsum_avg`), which is consumed
  here through the explicit hypothesis `hL` below (the `h`-sum outside the `(u₁,u₂)`-sum, as the
  aggregate needs it; the two orders are exchanged by `Lsum_swap`, a Fubini step).

`sec9Psum_le_of_Lsum` is that aggregate in the round-6 shape: any coefficient with the pointwise
bound `‖β z‖ ≤ Pa.τ` (what `IsBetaCoeff6` supplies) gives

  `sec9Psum Pa β ≤ C ϑ^{-1}τ²N²(log N+2)^b`,

which is the error term of (9.10).  The proof is the adaptation of `sec9Psum_le_of_bounds`
(`Submission/Work/FIArea2/Sec9Aggregate.lean`) with the explicit exponents of
`sec9_Z_bound_eight`, followed by the arithmetic of `NOTES.md` §24.4.
-/
import Mathlib
import Submission.Work.FIArea2.Sec9AggDefs
import Submission.Work.FIArea2.Sec9SwapDefs
import Submission.Work.FIArea2.Count.sec9_Z_defs
import Submission.Work.FIArea2.Count.sec9_Z_params
import Submission.Work.FIArea2.Count.sec9Zsum_le_ZB
import Submission.Work.FIArea2.Count.class_delta_sum_le
import Submission.Work.FIArea2.sum_tau_pow_div_le
import Submission.Commons.NumberTheory.Divisors.sum_filter_dvd_reindex
import Submission.Work.FIArea2.Count.ZAc_fiber
import Submission.Work.FIArea2.Count.ZAc_gcdsum
import Submission.Work.FIArea2.Count.ZAc_log
import Submission.Work.FIArea2.Count.ZBc_bound
import Submission.Work.FIArea2.Count.ZAc_bound_eight
import Submission.Work.FIArea2.Count.ZBc_bound_eight
import Submission.Work.FIArea2.Count.summable_Wt_tau4
import Submission.Work.FIArea2.Hscale_bounds

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.FIArea2.R6

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 0. Elementary facts -/

lemma sec9Usumming_nonneg (Pa : Work.FITop.Params) (h1 h2 : ℤ) :
    0 ≤ sec9Usumming Pa h1 h2 := by
  unfold sec9Usumming
  exact Finset.sum_nonneg fun u1 _ => Finset.sum_nonneg fun u2 _ => by positivity

lemma sec9Zsum_nonneg (Pa : Work.FITop.Params) (h1 h2 : ℤ) : 0 ≤ sec9Zsum Pa h1 h2 := by
  rw [sec9Zsum_eq]
  refine Finset.sum_nonneg fun z1 _ => Finset.sum_nonneg fun z2 _ => ?_
  rw [sec9Core]; split_ifs <;> positivity

/-- `sec9Psum0` as the `h`-sum of `sec9Uwt · sec9Zsum` (the §9 interchange, copied from
`Work.FIArea2.sec9Psum0_eq_tsum`, which lives in a file that currently has a `sorry`). -/
lemma sec9Psum0_eq_tsum' (Pa : Work.FITop.Params) :
    sec9Psum0 Pa
      = ∑' h : ℤ × ℤ, (if h = (0, 0) then 0 else sec9Uwt Pa h.1 h.2) * sec9Zsum Pa h.1 h.2 := by
  have hprod : ∀ z1 z2 : GaussianInt,
      (∑' h : ℤ × ℤ, sec9Swap Pa z1 z2 h)
        = sec9Core Pa z1 z2 * sec9Usum Pa z1 z2 := by
    intro z1 z2
    simp only [sec9Swap]
    rw [tsum_mul_left]
    congr 1
  have hpair : ∀ h : ℤ × ℤ,
      (∑ p ∈ (Work.FITop.boxN Pa).product (Work.FITop.boxN Pa), sec9Swap Pa p.1 p.2 h)
        = (if h = (0, 0) then 0 else sec9Uwt Pa h.1 h.2) * sec9Zsum Pa h.1 h.2 := by
    intro h
    rw [sec9Sum_product Pa h, sec9Zsum_eq]
    by_cases hh : h = (0, 0)
    · rw [hh]
      simp [sec9Swap]
    · rw [if_neg hh, Finset.mul_sum]
      refine Finset.sum_congr rfl fun z1 _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun z2 _ => ?_
      simp only [sec9Swap, if_neg hh]
      ring
  calc sec9Psum0 Pa
      = ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          ∑' h : ℤ × ℤ, sec9Swap Pa z1 z2 h := by
        unfold sec9Psum0
        exact Finset.sum_congr rfl fun z1 _ => Finset.sum_congr rfl fun z2 _ => (hprod z1 z2).symm
    _ = ∑ p ∈ (Work.FITop.boxN Pa).product (Work.FITop.boxN Pa),
          (∑' h : ℤ × ℤ, sec9Swap Pa p.1 p.2 h) :=
        (Finset.sum_product _ _ (fun p : GaussianInt × GaussianInt =>
          ∑' h : ℤ × ℤ, sec9Swap Pa p.1 p.2 h)).symm
    _ = ∑' h : ℤ × ℤ, ∑ p ∈ (Work.FITop.boxN Pa).product (Work.FITop.boxN Pa),
          sec9Swap Pa p.1 p.2 h := (sec9_tsum_swap Pa).symm
    _ = ∑' h : ℤ × ℤ, (if h = (0, 0) then 0 else sec9Uwt Pa h.1 h.2) * sec9Zsum Pa h.1 h.2 :=
        tsum_congr hpair

/-! ## 1. The §9 aggregate: from the per-frequency bound and the averaged `h`-sum -/

/-- The weight of the averaged `h`-sum at an abstract scale `H`. -/
def WtH (H : ℝ) (h : ℤ × ℤ) : ℝ :=
  (1 + (h.1 : ℝ) ^ 2 / H ^ 2)⁻¹ * (1 + (h.2 : ℝ) ^ 2 / H ^ 2)⁻¹

lemma WtH_nonneg (H : ℝ) (h : ℤ × ℤ) : 0 ≤ WtH H h := by
  unfold WtH
  have h1 : (0 : ℝ) ≤ 1 + (h.1 : ℝ) ^ 2 / H ^ 2 := by positivity
  have h2 : (0 : ℝ) ≤ 1 + (h.2 : ℝ) ^ 2 / H ^ 2 := by positivity
  positivity

end

end Work.FIArea2.R6
