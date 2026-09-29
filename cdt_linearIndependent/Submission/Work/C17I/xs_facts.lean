import Mathlib
import Submission.Work.C17I.defs
import Submission.Work.CLoc.gap_delta
import Submission.Work.C17.seventeen_defs
import Submission.Work.C17.xs_adm_bounds

namespace Work.C17I

/-- Arithmetic core of `xs_facts`.  Under the gap hypothesis `10⁶·|m − n| ≤ n` (with `m < n`) the
ratio `(4m+1)/(4n+2)` is at least `1 − 10⁻⁵`.

Write `g = n − m ≥ 1`; the hypothesis is `10⁶ g ≤ n = m + g`, i.e. `(10⁶−1) g ≤ m`.  Hence
`2m ≥ 2·(10⁶−1)·g = 1999998·g ≥ 199998·g + 49999` (the last step since `g ≥ 1` and
`1800000 ≥ 49999`), which is exactly the inequality obtained by clearing denominators in
`1 − 10⁻⁵ ≤ (4m+1)/(4n+2)`. -/
lemma ratio_ge_of_gap (m n : ℕ) (hlt : m < n)
    (hgap : 10 ^ 6 * ((m : ℤ) - n).natAbs ≤ n) :
    (1 : ℝ) - 1 / 100000 ≤ (4 * (m : ℝ) + 1) / (4 * (n : ℝ) + 2) := by
  have hmn : m ≤ n := le_of_lt hlt
  have hg : ((m : ℤ) - n).natAbs = n - m := by
    rw [show ((m : ℤ) - n) = -((n : ℤ) - (m : ℤ)) by ring, Int.natAbs_neg]
    rw [← Nat.cast_sub hmn, Int.natAbs_natCast]
  rw [hg] at hgap
  have harith : 199998 * (n - m) + 49999 ≤ 2 * m := by omega
  have harithR : (199998 : ℝ) * ((n - m : ℕ) : ℝ) + 49999 ≤ 2 * (m : ℝ) := by
    exact_mod_cast harith
  have hnm : ((n : ℝ) - (m : ℝ)) = ((n - m : ℕ) : ℝ) := by rw [Nat.cast_sub hmn]
  -- `199998·n + 49999 ≤ 200000·m`
  have hkey : (199998 : ℝ) * (n : ℝ) + 49999 ≤ 200000 * (m : ℝ) := by
    rw [← hnm] at harithR
    linarith
  -- clearing denominators: `99999·(4n+2) ≤ 100000·(4m+1)`
  have hnum : (99999 : ℝ) * (4 * (n : ℝ) + 2) ≤ 100000 * (4 * (m : ℝ) + 1) := by linarith
  have hle : (1 - 1 / 100000 : ℝ) * (4 * (n : ℝ) + 2) ≤ 4 * (m : ℝ) + 1 := by
    have heq : (1 - 1 / 100000 : ℝ) * (4 * (n : ℝ) + 2)
        = 99999 * (4 * (n : ℝ) + 2) / 100000 := by ring
    rw [heq, div_le_iff₀ (by norm_num : (0 : ℝ) < 100000)]
    linarith
  exact (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (n : ℝ) + 2)).mpr hle

/-- The lower bound `(2a−1)/(2b) ≤ xs a b`, specialised to the admissible pair
`a = 2m+1`, `b = 2n+1`: `(4m+1)/(4n+2) ≤ xsOf m n`. -/
lemma four_mul_ratio_le_xsOf (m n : ℕ) (hm : 1 ≤ m) (hlt : m < n) :
    (4 * (m : ℝ) + 1) / (4 * (n : ℝ) + 2) ≤ Work.C17.xsOf m n := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by
    have h : 1 ≤ n := le_trans hm (le_of_lt hlt)
    exact_mod_cast h
  have hcusp := Work.C17.cusp_lower_bound (2 * (m : ℝ) + 1) (2 * (n : ℝ) + 1)
    (by linarith) (by linarith)
  have hnum : 2 * (2 * (m : ℝ) + 1) - 1 = 4 * (m : ℝ) + 1 := by ring
  have hden : 2 * (2 * (n : ℝ) + 1) = 4 * (n : ℝ) + 2 := by ring
  rw [hnum, hden] at hcusp
  simpa only [Work.C17.xsOf] using hcusp

/-- **The cusp `x_s = xsOf m n` of an admissible pair.**  Under the gap hypothesis
`10⁶·|m − n| ≤ n` the cusp is positive, at most `1`, and at least `1 − 10⁻⁵`.

Positivity and `< 1` are `Work.C17.xsOf_pos`/`Work.C17.xsOf_lt_one`; the lower bound combines the
elementary estimate `(4m+1)/(4n+2) ≤ xsOf m n` with the arithmetic of `ratio_ge_of_gap`. -/
theorem xs_facts (m n : ℕ) (hm : 1 ≤ m) (hlt : m < n)
    (hgap : 10 ^ 6 * ((m : ℤ) - n).natAbs ≤ n) :
    0 < Work.C17.xsOf m n ∧ Work.C17.xsOf m n ≤ 1 ∧ 1 - 1 / 100000 ≤ Work.C17.xsOf m n := by
  refine ⟨Work.C17.xsOf_pos m n hm hlt, le_of_lt (Work.C17.xsOf_lt_one m n hm hlt), ?_⟩
  exact le_trans (ratio_ge_of_gap m n hlt hgap) (four_mul_ratio_le_xsOf m n hm hlt)

end Work.C17I
