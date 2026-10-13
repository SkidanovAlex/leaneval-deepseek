import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS.H2.DivQ.Defs
import Submission.Work.FTS.H2.DivQ.aCoeff_bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.DivQ

/-! ### A single uniform constant for the finitely many coefficients `aCoeff n m`, `1 ≤ n ≤ 4`

`aCoeff_bounds n` (proved in the sibling file) supplies, for each *fixed* `n`, a constant bounding
all `|aCoeff n m|` with `m ≤ n` on `[0,xNear]`, and (for `n ≥ 1`) a constant with
`|aCoeff n 0 x| ≤ C x²`.  The present statement asks for a *single* constant that works for all
`n ∈ {1,2,3,4}` at once, which is a finite maximum — taken here as a sum of nonnegative
witnesses (so that all the comparisons are `linarith`-linear and no `max`-bookkeeping is needed). -/

theorem exists_Cm_aCoeffBnd :
    ∃ Cm : ℝ, 0 ≤ Cm ∧
      (∀ (n m : ℕ), 1 ≤ n → n ≤ 4 → m ≤ n →
        ∀ x ∈ Set.Icc (0 : ℝ) xNear, |aCoeff n m x| ≤ Cm) ∧
      (∀ (n : ℕ), 1 ≤ n → n ≤ 4 →
        ∀ x ∈ Set.Icc (0 : ℝ) xNear, |aCoeff n 0 x| ≤ Cm * x ^ 2) := by
  obtain ⟨c1, hc1nn, hc1⟩ := (aCoeff_bounds 1).2.1
  obtain ⟨c2, hc2nn, hc2⟩ := (aCoeff_bounds 2).2.1
  obtain ⟨c3, hc3nn, hc3⟩ := (aCoeff_bounds 3).2.1
  obtain ⟨c4, hc4nn, hc4⟩ := (aCoeff_bounds 4).2.1
  obtain ⟨d1, hd1nn, hd1⟩ := (aCoeff_bounds 1).2.2 le_rfl
  obtain ⟨d2, hd2nn, hd2⟩ := (aCoeff_bounds 2).2.2 (by norm_num)
  obtain ⟨d3, hd3nn, hd3⟩ := (aCoeff_bounds 3).2.2 (by norm_num)
  obtain ⟨d4, hd4nn, hd4⟩ := (aCoeff_bounds 4).2.2 (by norm_num)
  set Cm : ℝ := c1 + c2 + c3 + c4 + d1 + d2 + d3 + d4 with hCm
  have hCmnn : 0 ≤ Cm := by rw [hCm]; linarith
  have hc1le : c1 ≤ Cm := by rw [hCm]; linarith
  have hc2le : c2 ≤ Cm := by rw [hCm]; linarith
  have hc3le : c3 ≤ Cm := by rw [hCm]; linarith
  have hc4le : c4 ≤ Cm := by rw [hCm]; linarith
  have hd1le : d1 ≤ Cm := by rw [hCm]; linarith
  have hd2le : d2 ≤ Cm := by rw [hCm]; linarith
  have hd3le : d3 ≤ Cm := by rw [hCm]; linarith
  have hd4le : d4 ≤ Cm := by rw [hCm]; linarith
  refine ⟨Cm, hCmnn, ?_, ?_⟩
  · intro n m hn1 hn4 hmn x hx
    interval_cases n
    · exact le_trans (hc1 m hmn x hx) hc1le
    · exact le_trans (hc2 m hmn x hx) hc2le
    · exact le_trans (hc3 m hmn x hx) hc3le
    · exact le_trans (hc4 m hmn x hx) hc4le
  · intro n hn1 hn4 x hx
    have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
    interval_cases n
    · exact le_trans (hd1 x hx) (mul_le_mul_of_nonneg_right hd1le hx2)
    · exact le_trans (hd2 x hx) (mul_le_mul_of_nonneg_right hd2le hx2)
    · exact le_trans (hd3 x hx) (mul_le_mul_of_nonneg_right hd3le hx2)
    · exact le_trans (hd4 x hx) (mul_le_mul_of_nonneg_right hd4le hx2)

end Work.FTS.H2.DivQ
