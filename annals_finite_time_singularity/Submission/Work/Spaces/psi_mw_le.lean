import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.Spaces

/-- Auxiliary: for `s ∈ [0,1]` and `c ≥ 0`, the product `s^c · s^{-c}` is at most `1`.
This is the algebraic heart of `psi_mw_le`: the "weight" `A = (α+s)·s^{α/5}` and the
"reciprocal weight" `Z = s^{-α/5}/(α+s)` multiply to `s^{α/5}·s^{-α/5} ≤ 1`. -/
theorem rpow_mul_rpow_neg_le_one {s c : ℝ} (hs : 0 ≤ s) (hc : 0 ≤ c) :
    s ^ c * s ^ (-c) ≤ 1 := by
  rcases eq_or_lt_of_le hs with h | h
  · rw [← h]
    rcases eq_or_lt_of_le hc with hc0 | hcpos
    · rw [← hc0]; norm_num
    · rw [Real.zero_rpow (ne_of_gt hcpos), Real.zero_rpow (by linarith : (-c : ℝ) ≠ 0)]
      norm_num
  · rw [← Real.rpow_add h, show c + -c = 0 by ring, Real.rpow_zero]

/-- Auxiliary: for `α ∈ (0,1]` and `s ∈ [0,1]`, `(α+s)·s^{α/5} ≤ 2`. -/
theorem add_mul_rpow_le_two {α s : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    (α + s) * s ^ (α / 5) ≤ 2 := by
  have hα5 : (0:ℝ) < α / 5 := by linarith
  have hB1 : s ^ (α / 5) ≤ 1 := Real.rpow_le_one hs hs1 (le_of_lt hα5)
  have hAs : 0 ≤ α + s := by linarith
  calc (α + s) * s ^ (α / 5) ≤ (α + s) * 1 := mul_le_mul_of_nonneg_left hB1 hAs
    _ ≤ 2 := by linarith

/-- Elgindi's weight estimate for the `W^{l,∞}` product rule: the "middle-factor"
combination `A_a · A_{j-a} · Z` is bounded by the constant `2` uniformly in `0 < α ≤ 1`
and `θ ∈ [0,π/2]`, where `A_k = (α+sin 2θ)·sin(2θ)^{α/5}` for `k ≠ 0` and `A_0 = 1`,
and `Z = sin(2θ)^{-α/5}/(α+sin 2θ)`. -/
theorem psi_mw_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ)
    (a j : ℕ) (ha : a ≤ j) (hj : 1 ≤ j) :
    (if a = 0 then (1 : ℝ) else (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
        * (if j - a = 0 then (1 : ℝ) else (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) ≤ 2 := by
  have hθ0 : 0 ≤ θ := hθ.1
  have hθ1 : θ ≤ Real.pi / 2 := hθ.2
  have hs0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  set s : ℝ := Real.sin (2 * θ) with hs
  have hs0' : 0 ≤ s := by rw [hs]; exact hs0
  have hs1' : s ≤ 1 := by rw [hs]; exact hs1
  set A : ℝ := (α + s) * s ^ (α / 5) with hAdef
  set Z : ℝ := s ^ (-(α / 5)) / (α + s) with hZdef
  have hα5 : (0:ℝ) < α / 5 := by linarith
  have hAs : 0 ≤ α + s := by linarith
  have hA0 : 0 ≤ A := by rw [hAdef]; exact mul_nonneg hAs (Real.rpow_nonneg hs0' _)
  have hA2 : A ≤ 2 := by rw [hAdef]; exact add_mul_rpow_le_two hα hα1 hs0' hs1'
  have hBC : s ^ (α / 5) * s ^ (-(α / 5)) ≤ 1 := rpow_mul_rpow_neg_le_one hs0' (le_of_lt hα5)
  have hne : α + s ≠ 0 := by positivity
  have hAZ : A * Z ≤ 1 := by
    have heq : A * Z = s ^ (α / 5) * s ^ (-(α / 5)) := by
      rw [hAdef, hZdef]; field_simp
    rw [heq]; exact hBC
  by_cases ha0 : a = 0
  · rw [ite_eq_left ha0]
    have hja : j - a ≠ 0 := by rw [ha0, Nat.sub_zero]; omega
    rw [ite_eq_right hja]
    nlinarith [hAZ]
  · rw [ite_eq_right ha0]
    by_cases hja : j - a = 0
    · rw [ite_eq_left hja]; nlinarith [hAZ]
    · rw [ite_eq_right hja]; nlinarith [hAZ, hA0, hA2]

end Work.Spaces
