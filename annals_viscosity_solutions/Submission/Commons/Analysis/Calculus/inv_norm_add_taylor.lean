import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Taylor expansion of `‖v + h‖⁻¹` up to second order

For `v, h` in a real inner product space and `ν > 0` with `ν ≤ ‖v‖` and `2‖h‖ ≤ ν`,
we prove the second order Taylor bound

`| ‖v + h‖⁻¹ - ‖v‖⁻¹ + ⟪v, h⟫ / ‖v‖³ | ≤ 32 ‖h‖² / ν³`.

The proof rests on the exact algebraic identity (valid whenever `a, b ≠ 0` and
`c = (b² - a² - d)/2`)

`1/b - 1/a + c/a³ = (a - b)² (2a + b) / (2 a³ b) - d / (2 a³)`,

applied to `a = ‖v‖`, `b = ‖v + h‖`, `c = ⟪v, h⟫`, `d = ‖h‖²`.  The first term is
`O(‖h‖²)` because `(‖v‖ - ‖v + h‖)² ≤ ‖h‖²`, and the remaining factor `(2a+b)/(2a³b)`
is controlled by `b ∈ [a/2, 3a/2]`.
-/

namespace Commons.Analysis.Calculus

/-- Exact algebraic identity underlying the second order Taylor bound for `1/‖·‖`.
If `c = (b² - a² - d)/2` then `1/b - 1/a + c/a³ = (a-b)²(2a+b)/(2a³b) - d/(2a³)`. -/
lemma inv_norm_add_taylor_alg (a b c d : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcd : c = (b^2 - a^2 - d)/2) :
    1/b - 1/a + c/a^3 = (a-b)^2*(2*a+b)/(2*a^3*b) - d/(2*a^3) := by
  subst hcd
  field_simp
  ring

/-- The inequality `|(a-b)²(2a+b)/(2a³b) - d/(2a³)| ≤ 32 d/ν³` under the hypotheses
`0 < ν ≤ a`, `a/2 ≤ b`, `0 ≤ d` and `(a-b)² ≤ d` used to conclude the Taylor bound. -/
lemma inv_norm_add_taylor_bound (A B d ν : ℝ) (hν : 0 < ν) (hA : ν ≤ A) (hB : A/2 ≤ B)
    (hd : 0 ≤ d) (hAB : (A-B)^2 ≤ d) :
    |(A-B)^2*(2*A+B)/(2*A^3*B) - d/(2*A^3)| ≤ 32*d/ν^3 := by
  have hApos : 0 < A := lt_of_lt_of_le hν hA
  have hBpos : 0 < B := by linarith
  have h2A3Bpos : 0 < 2*A^3*B := by positivity
  have hA3pos : 0 < 2*A^3 := by positivity
  have hABnn : 0 ≤ (A-B)^2 := sq_nonneg _
  have h2ABnn : 0 ≤ 2*A+B := by linarith
  have hP : 0 ≤ (A-B)^2*(2*A+B)/(2*A^3*B) :=
    div_nonneg (mul_nonneg hABnn h2ABnn) h2A3Bpos.le
  have hQ : 0 ≤ d/(2*A^3) := div_nonneg hd hA3pos.le
  have hsplit : |(A-B)^2*(2*A+B)/(2*A^3*B) - d/(2*A^3)|
      ≤ (A-B)^2*(2*A+B)/(2*A^3*B) + d/(2*A^3) := by
    rw [abs_le]; constructor <;> linarith
  have hfac : (2*A+B)/(2*A^3*B) ≤ 5/(2*A^3) := by
    rw [div_le_div_iff₀ h2A3Bpos hA3pos]
    have h25 : 2*A+B ≤ 5*B := by linarith
    nlinarith [mul_le_mul_of_nonneg_right h25 (by positivity : (0:ℝ) ≤ 2*A^3)]
  have hfacnn : 0 ≤ (2*A+B)/(2*A^3*B) := div_nonneg h2ABnn h2A3Bpos.le
  have hPbound : (A-B)^2*(2*A+B)/(2*A^3*B) ≤ d * (5/(2*A^3)) := by
    calc (A-B)^2*(2*A+B)/(2*A^3*B) = (A-B)^2 * ((2*A+B)/(2*A^3*B)) := by ring
      _ ≤ d * ((2*A+B)/(2*A^3*B)) :=
            mul_le_mul_of_nonneg_right hAB hfacnn
      _ ≤ d * (5/(2*A^3)) :=
            mul_le_mul_of_nonneg_left hfac hd
  have hsum : (A-B)^2*(2*A+B)/(2*A^3*B) + d/(2*A^3) ≤ 3*d/A^3 := by
    have : d * (5/(2*A^3)) + d/(2*A^3) = 3*d/A^3 := by field_simp; ring
    linarith [hPbound]
  have h3 : 3*d/A^3 ≤ 32*d/ν^3 := by
    have hA3 : ν^3 ≤ A^3 := pow_le_pow_left₀ hν.le hA 3
    have h1 : 3*d/A^3 ≤ 3*d/ν^3 :=
      div_le_div_of_nonneg_left (by linarith : 0 ≤ 3*d) (by positivity) hA3
    have h2 : 3*d/ν^3 ≤ 32*d/ν^3 :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    linarith
  linarith [hsplit, hsum, h3]

/-- Second order Taylor bound for the inverse of the norm: for `ν > 0`, `ν ≤ ‖v‖` and
`2‖h‖ ≤ ν`,
`| ‖v + h‖⁻¹ - ‖v‖⁻¹ + ⟪v, h⟫ / ‖v‖³ | ≤ 32 ‖h‖² / ν³`. -/
theorem inv_norm_add_taylor {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {v h : E} {ν : ℝ} (hν : 0 < ν) (hv : ν ≤ ‖v‖) (hh : 2 * ‖h‖ ≤ ν) :
    |‖v + h‖⁻¹ - ‖v‖⁻¹ + inner ℝ v h / ‖v‖ ^ 3| ≤ 32 * ‖h‖ ^ 2 / ν ^ 3 := by
  have hApos : 0 < ‖v‖ := lt_of_lt_of_le hν hv
  have hhnorm : ‖h‖ ≤ ν/2 := by linarith
  have hB : ‖v‖/2 ≤ ‖v+h‖ := by
    have h1 : ‖v‖ - ‖h‖ ≤ ‖v + h‖ := by
      have h2 : ‖v‖ ≤ ‖v + h‖ + ‖h‖ := by
        calc ‖v‖ = ‖(v + h) - h‖ := by rw [add_sub_cancel_right]
          _ ≤ ‖v + h‖ + ‖h‖ := norm_sub_le _ _
      linarith
    have h3 : ‖v‖/2 ≤ ‖v‖ - ‖h‖ := by linarith [hhnorm]
    linarith
  have hBpos : 0 < ‖v + h‖ := by linarith [hApos, hB]
  have hAB : (‖v‖ - ‖v+h‖)^2 ≤ ‖h‖^2 := by
    have hdiff := abs_norm_sub_norm_le (v + h) v
    have h2 : ‖(v + h) - v‖ = ‖h‖ := by rw [add_sub_cancel_left]
    rw [h2] at hdiff
    rw [sq_le_sq, abs_of_nonneg (norm_nonneg h)]
    rwa [abs_sub_comm]
  have hcd : inner ℝ v h = (‖v + h‖^2 - ‖v‖^2 - ‖h‖^2)/2 := by
    have := norm_add_sq_real v h
    linarith
  have hkey := inv_norm_add_taylor_alg ‖v‖ ‖v+h‖ (inner ℝ v h) (‖h‖^2)
    (ne_of_gt hApos) (ne_of_gt hBpos) hcd
  have hkey' : ‖v + h‖⁻¹ - ‖v‖⁻¹ + inner ℝ v h / ‖v‖ ^ 3
      = (‖v‖-‖v+h‖)^2*(2*‖v‖+‖v+h‖)/(2*‖v‖^3*‖v+h‖) - ‖h‖^2/(2*‖v‖^3) := by
    simpa [one_div] using hkey
  rw [hkey']
  exact inv_norm_add_taylor_bound ‖v‖ ‖v+h‖ (‖h‖^2) ν hν hv hB (sq_nonneg _) hAB

end Commons.Analysis.Calculus