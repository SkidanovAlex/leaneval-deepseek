import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Order.Star.Real

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.DivQ

/-- The arithmetic core of the weighted Hardy inequality with a boundary term.  From the
integration-by-parts identity `s·A = m - e - 2·J` (`m, e ≥ 0`) and the AM-GM estimate
`2·Ja/|s| ≤ A/2 + 2·c/s²` with `|J| ≤ Ja`, conclude `A ≤ 4·C/s² + 2·(m+e)/|s|` (using `c ≤ C`).
The two sign cases of `s` are where `|J| ≤ Ja` and `m ≥ 0` are needed. -/
lemma hardy_combine (A m e J Ja c C s : ℝ) (hs : s ≠ 0) (hA : 0 ≤ A) (hm : 0 ≤ m)
    (he : 0 ≤ e) (hJ : |J| ≤ Ja) (hJa : 0 ≤ Ja) (hc : 0 ≤ c) (hcC : c ≤ C)
    (hibp : s * A = m - e - 2 * J) (hamgm : 2 * Ja / |s| ≤ A / 2 + 2 * c / s ^ 2) :
    A ≤ 4 * C / s ^ 2 + 2 * (m + e) / |s| := by
  -- The two sign cases of `s` enter through `|s| > 0` and `s² > 0`.
  have hspos : 0 < |s| := abs_pos.mpr hs
  have hs2pos : 0 < s ^ 2 := pow_two_pos_of_ne_zero hs
  -- Take absolute values of the integration-by-parts identity (using `A ≥ 0`).
  have h1 : |s| * A = |m - e - 2 * J| := by
    rw [← hibp, abs_mul, abs_of_nonneg hA]
  -- Triangle inequality: `|m - e - 2J| ≤ m + e + 2|J|`.
  have hab : |m + -e| ≤ m + e := by
    rw [abs_le]; constructor <;> linarith
  have h2 : |m - e - 2 * J| ≤ m + e + 2 * Ja := by
    have h3 : |m - e - 2 * J| ≤ m + e + 2 * |J| := by
      calc |m - e - 2 * J| = |(m + -e) + -(2 * J)| := by ring_nf
        _ ≤ |m + -e| + |-(2 * J)| := abs_add_le _ _
        _ ≤ (m + e) + 2 * |J| := by
            have h4 : |-(2 * J)| = 2 * |J| := by rw [abs_neg, abs_mul]; norm_num
            rw [h4]; linarith [hab]
    linarith [h3, hJ]
  have h5 : |s| * A ≤ m + e + 2 * Ja := by rw [h1]; linarith [h2]
  -- Divide by `|s| > 0`.
  have h6 : A ≤ (m + e) / |s| + 2 * Ja / |s| := by
    have hdiv : (|s| * A) / |s| ≤ (m + e + 2 * Ja) / |s| :=
      div_le_div_of_nonneg_right h5 (le_of_lt hspos)
    rw [mul_div_cancel_left₀ A (ne_of_gt hspos), add_div] at hdiv
    linarith [hdiv]
  -- Combine with the AM-GM estimate and halve.
  have h7 : A / 2 ≤ (m + e) / |s| + 2 * c / s ^ 2 := by linarith [h6, hamgm]
  have h8 : A ≤ 2 * ((m + e) / |s|) + 4 * (c / s ^ 2) := by
    have h7b : 2 * (A / 2) ≤ 2 * ((m + e) / |s| + 2 * c / s ^ 2) :=
      mul_le_mul_of_nonneg_left h7 (by norm_num)
    rw [mul_add] at h7b
    have hAA : 2 * (A / 2) = A := by ring
    have hcc : 2 * (2 * c / s ^ 2) = 4 * (c / s ^ 2) := by rw [mul_div_assoc]; ring
    rw [hAA, hcc] at h7b
    exact h7b
  -- Replace `c` by `C` and reassemble.
  have h9 : 4 * (c / s ^ 2) ≤ 4 * (C / s ^ 2) :=
    mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hcC (le_of_lt hs2pos)) (by norm_num)
  have h10 : A ≤ 2 * ((m + e) / |s|) + 4 * (C / s ^ 2) :=
    calc A ≤ 2 * ((m + e) / |s|) + 4 * (c / s ^ 2) := h8
      _ ≤ 2 * ((m + e) / |s|) + 4 * (C / s ^ 2) := add_le_add (le_refl _) h9
  rw [mul_div_assoc, mul_div_assoc]
  linarith [h10]

end Work.FTS.H2.DivQ
