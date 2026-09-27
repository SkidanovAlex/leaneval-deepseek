import Mathlib
import Submission.Work.Mostow.Hyper

namespace Work.Mostow

open Submission.Mostow

/-- The second difference of `t ↦ √(a + 2ct + t²)` at `0` is strictly positive when `c² < a`.

This is the purely algebraic core of the strict convexity of `tpart` along a line: it says that
`√(a + 2cε + ε²) + √(a - 2cε + ε²) > 2√a` for `ε ≠ 0`, and `a - c²` is exactly `g''·g³` for
`g(t) = √(a + 2ct + t²)`. -/
private lemma sqrt_secondDiff_pos {a c ε : ℝ} (hc : c ^ 2 < a) (hε : ε ≠ 0) :
    0 < Real.sqrt (a + 2 * c * ε + ε ^ 2) + Real.sqrt (a - 2 * c * ε + ε ^ 2)
        - 2 * Real.sqrt a := by
  have ha : 0 < a := by nlinarith [sq_nonneg c]
  have hε2 : 0 < ε ^ 2 := sq_pos_of_ne_zero hε
  set A := a + 2 * c * ε + ε ^ 2 with hAdef
  set B := a - 2 * c * ε + ε ^ 2 with hBdef
  have hA : 0 ≤ A := by rw [hAdef]; nlinarith [sq_nonneg (c + ε)]
  have hB : 0 ≤ B := by rw [hBdef]; nlinarith [sq_nonneg (c - ε)]
  have hAB : (a - ε ^ 2) ^ 2 < A * B := by
    rw [hAdef, hBdef]; nlinarith [sq_pos_of_ne_zero hε]
  have hprod : Real.sqrt (A * B) = Real.sqrt A * Real.sqrt B := Real.sqrt_mul hA B
  have hlt : a - ε ^ 2 < Real.sqrt A * Real.sqrt B := by
    have h1 : |a - ε ^ 2| < Real.sqrt A * Real.sqrt B := by
      rw [← Real.sqrt_sq_eq_abs, ← hprod]
      exact Real.sqrt_lt_sqrt (sq_nonneg _) hAB
    linarith [le_abs_self (a - ε ^ 2)]
  have hsq : (2 * Real.sqrt a) ^ 2 < (Real.sqrt A + Real.sqrt B) ^ 2 := by
    have h1 : Real.sqrt A ^ 2 = A := Real.sq_sqrt hA
    have h2 : Real.sqrt B ^ 2 = B := Real.sq_sqrt hB
    have h3 : Real.sqrt a ^ 2 = a := Real.sq_sqrt (le_of_lt ha)
    nlinarith [h1, h2, h3, hlt]
  have hfin : 2 * Real.sqrt a < Real.sqrt A + Real.sqrt B := by
    by_contra h
    have h' : Real.sqrt A + Real.sqrt B ≤ 2 * Real.sqrt a := not_lt.mp h
    have hle := mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ Real.sqrt A + Real.sqrt B) h'
    nlinarith [hsq, hle]
  linarith

theorem tpart_second_diff_pos {n : ℕ} (u : Submission.Mostow.E n) (i : Fin n) {ε : ℝ}
    (hε : ε ≠ 0) :
    0 < Submission.Mostow.tpart (u + ε • EuclideanSpace.single i (1 : ℝ)) +
        Submission.Mostow.tpart (u - ε • EuclideanSpace.single i (1 : ℝ)) -
        2 * Submission.Mostow.tpart u := by
  have hA : ‖u + ε • EuclideanSpace.single i (1 : ℝ)‖ ^ 2
      = ‖u‖ ^ 2 + 2 * u i * ε + ε ^ 2 := by
    rw [norm_add_sq_real, inner_smul_right, EuclideanSpace.inner_single_right]
    rw [norm_smul, PiLp.norm_single 2 (fun _ : Fin n => ℝ) i (1 : ℝ), norm_one, mul_one]
    ring_nf
    simp
  have hB : ‖u - ε • EuclideanSpace.single i (1 : ℝ)‖ ^ 2
      = ‖u‖ ^ 2 - 2 * u i * ε + ε ^ 2 := by
    rw [norm_sub_sq_real, inner_smul_right, EuclideanSpace.inner_single_right]
    rw [norm_smul, PiLp.norm_single 2 (fun _ : Fin n => ℝ) i (1 : ℝ), norm_one, mul_one]
    ring_nf
    simp
  have hc : (u i) ^ 2 < 1 + ‖u‖ ^ 2 := by
    have h1 : ‖u i‖ ≤ ‖u‖ := PiLp.norm_apply_le u i
    have h2 : |u i| ≤ |‖u‖| := by simpa [Real.norm_eq_abs] using h1
    have h3 : (u i) ^ 2 ≤ ‖u‖ ^ 2 := sq_le_sq.mpr h2
    nlinarith [sq_nonneg (‖u‖ : ℝ)]
  have key := sqrt_secondDiff_pos (a := 1 + ‖u‖ ^ 2) (c := u i) (ε := ε) hc hε
  have e1 : Submission.Mostow.tpart (u + ε • EuclideanSpace.single i (1 : ℝ))
      = Real.sqrt (1 + ‖u‖ ^ 2 + 2 * u i * ε + ε ^ 2) := by
    rw [Submission.Mostow.tpart, hA]
    congr 1
    ring
  have e2 : Submission.Mostow.tpart (u - ε • EuclideanSpace.single i (1 : ℝ))
      = Real.sqrt (1 + ‖u‖ ^ 2 - 2 * u i * ε + ε ^ 2) := by
    rw [Submission.Mostow.tpart, hB]
    congr 1
    ring
  have e3 : Submission.Mostow.tpart u = Real.sqrt (1 + ‖u‖ ^ 2) := rfl
  rw [e1, e2, e3]
  exact key

end Work.Mostow
