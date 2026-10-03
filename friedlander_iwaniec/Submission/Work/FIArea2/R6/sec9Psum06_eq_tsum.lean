/-
# `FIArea2/R6/sec9Psum06_eq_tsum.lean` — the §9 interchange at the sector-scale threshold

The §9 pair sum (9.5) without coefficients equals the `h`-sum of the frequency weight against the
per-frequency sum (9.5).  This is the sector-scale mirror (`sec9Psum06`, `sec9Zsum6`, `sec9Swap6`)
of `Work.FIArea2.sec9Psum0_eq_tsum`; the interchange itself is `R6.sec9_tsum_swap6`, and the two
identifications

* `∑' h, sec9Swap6 z₁ z₂ h = sec9Core6 z₁ z₂ · sec9Usum z₁ z₂`  (definition of `sec9Usum`), and
* `∑_{(z₁,z₂)} sec9Swap6 z₁ z₂ h = [h ≠ 0]·sec9Uwt h · sec9Zsum6 h`

finish the chain.  Only `SixDefs` is used: no new analytic input is needed.
-/
import Mathlib
import Submission.Work.FIArea2.R6.SixDefs

set_option autoImplicit false

namespace Work.FIArea2.R6

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

lemma sec9Psum06_eq_tsum (Pa : Work.FITop.Params) :
    sec9Psum06 Pa
      = ∑' h : ℤ × ℤ,
          (if h = (0, 0) then 0 else Work.FIArea2.sec9Uwt Pa h.1 h.2) * sec9Zsum6 Pa h.1 h.2 := by
  -- The `h`-sum of one pair is the pair weight times the uniform `H(z₁,z₂)`.
  have hprod : ∀ z1 z2 : GaussianInt,
      (∑' h : ℤ × ℤ, sec9Swap6 Pa z1 z2 h)
        = sec9Core6 Pa z1 z2 * Work.FIArea2.sec9Usum Pa z1 z2 := by
    intro z1 z2
    simp only [sec9Swap6]
    rw [tsum_mul_left]
    congr 1
  -- The pair sum at one frequency is the frequency weight times `sec9Zsum6`.
  have hpair : ∀ h : ℤ × ℤ,
      (∑ p ∈ (Work.FITop.boxN Pa).product (Work.FITop.boxN Pa), sec9Swap6 Pa p.1 p.2 h)
        = (if h = (0, 0) then 0 else Work.FIArea2.sec9Uwt Pa h.1 h.2) * sec9Zsum6 Pa h.1 h.2 := by
    intro h
    rw [sec9Sum_product6 Pa h, sec9Zsum6_eq]
    by_cases hh : h = (0, 0)
    · rw [hh]
      simp [sec9Swap6]
    · rw [if_neg hh, Finset.mul_sum]
      refine Finset.sum_congr rfl fun z1 _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun z2 _ => ?_
      simp only [sec9Swap6, if_neg hh]
      ring
  calc sec9Psum06 Pa
      = ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          ∑' h : ℤ × ℤ, sec9Swap6 Pa z1 z2 h := by
        unfold sec9Psum06
        exact Finset.sum_congr rfl fun z1 _ => Finset.sum_congr rfl fun z2 _ => (hprod z1 z2).symm
    _ = ∑ p ∈ (Work.FITop.boxN Pa).product (Work.FITop.boxN Pa),
          (∑' h : ℤ × ℤ, sec9Swap6 Pa p.1 p.2 h) :=
        (Finset.sum_product _ _ (fun p : GaussianInt × GaussianInt =>
          ∑' h : ℤ × ℤ, sec9Swap6 Pa p.1 p.2 h)).symm
    _ = ∑' h : ℤ × ℤ, ∑ p ∈ (Work.FITop.boxN Pa).product (Work.FITop.boxN Pa),
          sec9Swap6 Pa p.1 p.2 h := (sec9_tsum_swap6 Pa).symm
    _ = ∑' h : ℤ × ℤ,
          (if h = (0, 0) then 0 else Work.FIArea2.sec9Uwt Pa h.1 h.2) * sec9Zsum6 Pa h.1 h.2 :=
        tsum_congr hpair

end

end Work.FIArea2.R6
