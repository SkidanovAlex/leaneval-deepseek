import Mathlib
import Submission.Subspace.Classical
import Submission.Commons.Analysis.Normed.intVec_norm_ge_one
import Submission.Commons.NumberTheory.Height.Rat.mulHeight_int_le_norm

/-!
# Stage B: heights of integer points versus the sup norm

For an integer point `x : σ → ℤ` (viewed as a tuple over `ℚ`), its multiplicative
tuple height over `ℚ` is at most its sup norm `‖x‖` (the p-adic factors are ≤ 1);
consequently the logarithmic height is at most `log ‖x‖`.  This is the
`H(x) ≤ ‖x‖` direction used when passing between the challenge inequality (stated
with `‖x‖`) and height-based statements.

The reverse direction (`‖x‖` up to the gcd) is `Commons.NumberTheory.Height.Rat.
projective_northcott_int`.
-/

open scoped BigOperators

namespace Submission.Subspace

section HeightLink

variable {σ : Type*} [Fintype σ]

/-- The (multiplicative) tuple height over ℚ of an integer point is at most its
sup norm. -/
theorem mulHeight_int_le_norm (x : σ → ℤ) (hx : x ≠ 0) :
    Height.mulHeight (fun i : σ => (x i : ℚ)) ≤ ‖x‖ :=
  Commons.NumberTheory.Height.Rat.mulHeight_int_le_norm x hx

/-- Consequently the logarithmic height is at most the logarithm of the sup norm. -/
theorem logHeight_int_le_log_norm (x : σ → ℤ) (hx : x ≠ 0) :
    Height.logHeight (fun i : σ => (x i : ℚ)) ≤ Real.log ‖x‖ := by
  rw [Height.logHeight_eq_log_mulHeight]
  exact Real.log_le_log (Height.mulHeight_pos _) (mulHeight_int_le_norm x hx)

/-- A nonzero integer point has norm at least one. -/
theorem one_le_norm_of_ne_zero (x : σ → ℤ) (hx : x ≠ 0) : 1 ≤ ‖x‖ :=
  Commons.Analysis.Normed.intVec_norm_ge_one x hx

/-- Bridge from the strict smallness hypothesis (product of complex norms) to the
logarithmic form used by the pigeonhole/exponent-extraction step: if all form
values are nonzero then `∑ᵢ log‖Lᵢ(x)‖ < -ε log‖x‖`. -/
theorem small_imp_log_sum (L : σ → σ → ℂ) (ε : ℝ) {x : σ → ℤ} (hx : x ≠ 0)
    (hnz : ∀ i : σ, (∑ j : σ, L i j * (x j : ℂ) : ℂ) ≠ 0) (hs : Small L ε x) :
    ∑ i : σ, Real.log ‖(∑ j : σ, L i j * (x j : ℂ) : ℂ)‖ <
      -ε * Real.log ‖x‖ := by
  rw [small_iff_prod] at hs
  have hpos : ∀ i : σ, (0:ℝ) < ‖(∑ j : σ, L i j * (x j : ℂ) : ℂ)‖ :=
    fun i => norm_pos_iff.mpr (hnz i)
  have hprodpos : (0:ℝ) < ∏ i : σ, ‖(∑ j : σ, L i j * (x j : ℂ) : ℂ)‖ :=
    Finset.prod_pos (fun i _ => hpos i)
  have hlog := Real.log_lt_log hprodpos hs
  rw [Real.log_prod (fun i _ => (hpos i).ne')] at hlog
  have hnx : (0:ℝ) < ‖x‖ := lt_of_lt_of_le zero_lt_one (one_le_norm_of_ne_zero x hx)
  rw [Real.log_rpow hnx] at hlog
  exact hlog

/-- Under the strict smallness hypothesis, the product of the norms of the form
values is `< 1`. -/
theorem prod_lt_one_of_small (L : σ → σ → ℂ) (ε : ℝ) (hε : 0 < ε) {x : σ → ℤ}
    (hx : x ≠ 0) (h : Small L ε x) :
    (∏ i : σ, ‖(∑ j : σ, L i j * (x j : ℂ) : ℂ)‖) < 1 := by
  have hprod := (small_iff_prod L ε x).mp h
  have h1 : (1 : ℝ) ≤ ‖x‖ := one_le_norm_of_ne_zero x hx
  have h0 : (0 : ℝ) < ‖x‖ := lt_of_lt_of_le zero_lt_one h1
  rw [Real.rpow_neg h0.le] at hprod
  have hpow1 : (1 : ℝ) ≤ ‖x‖ ^ ε := Real.one_le_rpow h1 hε.le
  have hinv : (‖x‖ ^ ε)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hpow1
  linarith

end HeightLink

end Submission.Subspace
