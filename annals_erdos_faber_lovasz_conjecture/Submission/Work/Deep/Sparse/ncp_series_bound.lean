/-
# The tail of the class-sum series is negligible

The class-sum statistic `occSlice` writes the truncated statistic as
`∑_{2 ≤ j ≤ J} occW j · #{c : j ≤ colourClassCount G f v c}` with the increment
`occW j = (j-1)(4-j)/2` (`NcpDefs.lean`).  Below the truncation level `J` only the
terms `j ≤ J` appear, and the contribution of the levels `j ≥ 19` is bounded by

  `∑_{19 ≤ j ≤ D} |occW j| · 2^j/j!  ≤  1/10^7`,

uniformly in `D`.  The series decays like `2^j/j!` after the polynomial factor
`|occW j| = (j-1)(j-4)/2`, and this file proves the bound by comparing it to a
geometric series of ratio `1/4`, starting from the term `j = 19`.

## The argument

For `j ≥ 5` one has `|occW j| = (j-1)(j-4)/2 ≤ j²`, so it suffices to bound the
auxiliary series `u j = j² · 2^j/j!`.  The ratio of consecutive terms is

  `u (j+1)/u j = 2 (j+1)/j² ≤ 1/4   for j ≥ 9`,

so `u (19+m) ≤ (1/4)^m u 19`, and summing the geometric series gives

  `∑_{19 ≤ j ≤ D} u j ≤ (4/3) · (1 - (1/4)^(D-18)) · u 19 ≤ (4/3) · u 19`
  `= 361 · 2^19 / 19! ≤ 2.1·10⁻⁹ ≤ 10⁻⁷`.

The final numerical step is `(4/3)·361·524288 ≤ 3·19!·10⁻⁷`, which `norm_num`
checks.
-/
import Submission.Work.Deep.Sparse.Prelude
import Submission.Work.Deep.Sparse.ncpTailDefs
import Submission.Work.Deep.Sparse.NcpDefs

open scoped BigOperators

namespace Work.Deep.Sparse

/-- The auxiliary majorant `u j = j² · 2^j / j!` of `|occW j| · 2^j / j!`. -/
private noncomputable def u (j : ℕ) : ℝ := (j : ℝ) ^ 2 * ((2 : ℝ) ^ j / (j.factorial : ℝ))

private lemma u_nonneg (j : ℕ) : 0 ≤ u j := by
  unfold u
  exact mul_nonneg (sq_nonneg _) (div_nonneg (pow_nonneg (by norm_num) j) (Nat.cast_nonneg _))

/-- For `j ≥ 5` the increment `occW j` is negative and `|occW j| = (j-1)(j-4)/2`. -/
private lemma abs_occW_eq (j : ℕ) (hj : 5 ≤ j) :
    |occW j| = ((j : ℝ) - 1) * ((j : ℝ) - 4) / 2 := by
  have hjR : (5 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have h1 : (0 : ℝ) ≤ (j : ℝ) - 1 := by linarith
  have h4 : (0 : ℝ) ≤ (j : ℝ) - 4 := by linarith
  unfold occW
  rw [abs_div, abs_mul, abs_of_nonneg h1, abs_sub_comm, abs_of_nonneg h4,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]

/-- The polynomial factor is dominated by `j²`. -/
private lemma abs_occW_le (j : ℕ) (hj : 5 ≤ j) : |occW j| ≤ (j : ℝ) ^ 2 := by
  have hjR : (5 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  rw [abs_occW_eq j hj]
  have h1 : ((j : ℝ) - 1) ≤ (j : ℝ) := by linarith
  have h4 : ((j : ℝ) - 4) ≤ (j : ℝ) := by linarith
  have h1' : (0 : ℝ) ≤ ((j : ℝ) - 1) := by linarith
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := by linarith
  have hprod : ((j : ℝ) - 1) * ((j : ℝ) - 4) ≤ (j : ℝ) * (j : ℝ) := by
    calc ((j : ℝ) - 1) * ((j : ℝ) - 4) ≤ ((j : ℝ) - 1) * (j : ℝ) :=
          mul_le_mul_of_nonneg_left h4 h1'
      _ ≤ (j : ℝ) * (j : ℝ) := by
          rw [mul_comm ((j : ℝ) - 1) (j : ℝ)]
          exact mul_le_mul_of_nonneg_left h1 hj0
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  nlinarith [hprod, sq_nonneg (j : ℝ)]

/-- The cancelled form of `u (j+1)`: the factor `j+1` of the factorial cancels. -/
private lemma u_succ_eq (j : ℕ) :
    u (j+1) = (2 * ((j : ℝ) + 1)) * ((2 : ℝ) ^ j / (j.factorial : ℝ)) := by
  unfold u
  rw [pow_succ, Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-- The ratio bound: `u (j+1) ≤ u j / 4` for `j ≥ 9`. -/
private lemma u_ratio (j : ℕ) (hj : 9 ≤ j) : u (j+1) ≤ (1/4) * u j := by
  have hjR : (9 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hF : (0 : ℝ) ≤ (j.factorial : ℝ) := Nat.cast_nonneg _
  have hk : (0 : ℝ) ≤ (2 : ℝ) ^ j / (j.factorial : ℝ) :=
    div_nonneg (pow_nonneg (by norm_num) j) hF
  have hkey : 2 * ((j : ℝ) + 1) ≤ (1/4) * ((j : ℝ) ^ 2) := by nlinarith [hjR]
  have huj : u j = ((j : ℝ) ^ 2) * ((2 : ℝ) ^ j / (j.factorial : ℝ)) := rfl
  rw [u_succ_eq, huj]
  calc (2 * ((j : ℝ) + 1)) * ((2 : ℝ) ^ j / (j.factorial : ℝ))
      ≤ ((1/4) * ((j : ℝ) ^ 2)) * ((2 : ℝ) ^ j / (j.factorial : ℝ)) :=
        mul_le_mul_of_nonneg_right hkey hk
    _ = (1/4) * ((j : ℝ) ^ 2 * ((2 : ℝ) ^ j / (j.factorial : ℝ))) := by ring

/-- Iterating the ratio bound: `u (19+m) ≤ (1/4)^m u 19`. -/
private lemma u_iter (m : ℕ) : u (19 + m) ≤ (1/4) ^ m * u 19 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hstep := u_ratio (19 + m) (by omega : 9 ≤ 19 + m)
    calc u (19 + (m + 1)) = u (19 + m + 1) := rfl
      _ ≤ (1/4) * u (19 + m) := hstep
      _ ≤ (1/4) * ((1/4) ^ m * u 19) := by
            exact mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = (1/4) ^ (m + 1) * u 19 := by rw [pow_succ]; ring

/-- The geometric sum bound for the majorant. -/
private lemma u_sum_le (n : ℕ) :
    ∑ j ∈ Finset.Icc 19 (19 + n), u j ≤ (4/3) * (1 - (1/4) ^ (n + 1)) * u 19 := by
  induction n with
  | zero =>
    have hset : Finset.Icc 19 (19 + 0) = {19} := by
      ext j; simp only [Finset.mem_Icc, Finset.mem_singleton]; omega
    rw [hset, Finset.sum_singleton]
    norm_num
  | succ n ih =>
    have hins : Finset.Icc 19 (19 + (n + 1)) =
        insert (19 + (n + 1)) (Finset.Icc 19 (19 + n)) := by
      ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot : (19 + (n + 1)) ∉ Finset.Icc 19 (19 + n) := by
      simp only [Finset.mem_Icc]; omega
    rw [hins, Finset.sum_insert hnot]
    have hu := u_iter (n + 1)
    have hcombine : u (19 + (n + 1)) + ∑ j ∈ Finset.Icc 19 (19 + n), u j
        ≤ (1/4) ^ (n + 1) * u 19 + (4/3) * (1 - (1/4) ^ (n + 1)) * u 19 :=
      add_le_add hu ih
    refine le_trans hcombine (le_of_eq ?_)
    rw [show (1/4 : ℝ) ^ (n + 2) = (1/4) ^ (n + 1) * (1/4) from by
      rw [show (n + 2) = (n + 1) + 1 from rfl, pow_succ]]
    ring

theorem ncp_series_bound (D : ℕ) : ∑ j ∈ Finset.Icc 19 D, |occW j| * ((2 : ℝ) ^ j / (j.factorial : ℝ)) ≤ (1 : ℝ) / 10000000 := by
  rcases Nat.lt_or_ge D 19 with hlt | hge
  · rw [Finset.Icc_eq_empty_of_lt hlt]; simp
  · obtain ⟨n, hn⟩ : ∃ n, D = 19 + n := ⟨D - 19, by omega⟩
    subst hn
    have hcmp : ∑ j ∈ Finset.Icc 19 (19 + n), |occW j| * ((2 : ℝ) ^ j / (j.factorial : ℝ))
        ≤ ∑ j ∈ Finset.Icc 19 (19 + n), u j := by
      apply Finset.sum_le_sum
      intro j hj
      have hj5 : 5 ≤ j := by have := (Finset.mem_Icc.mp hj).1; omega
      have hle : |occW j| ≤ (j : ℝ) ^ 2 := abs_occW_le j hj5
      have hnn : (0 : ℝ) ≤ (2 : ℝ) ^ j / (j.factorial : ℝ) :=
        div_nonneg (pow_nonneg (by norm_num) j) (Nat.cast_nonneg _)
      calc |occW j| * ((2 : ℝ) ^ j / (j.factorial : ℝ))
          ≤ (j : ℝ) ^ 2 * ((2 : ℝ) ^ j / (j.factorial : ℝ)) :=
            mul_le_mul_of_nonneg_right hle hnn
        _ = u j := rfl
    have h1 : ∑ j ∈ Finset.Icc 19 (19 + n), |occW j| * ((2 : ℝ) ^ j / (j.factorial : ℝ))
        ≤ (4/3) * (1 - (1/4) ^ (n + 1)) * u 19 := le_trans hcmp (u_sum_le n)
    have h2 : (4/3 : ℝ) * (1 - (1/4) ^ (n + 1)) * u 19 ≤ (4/3) * u 19 := by
      have hq0 : (0 : ℝ) ≤ (1/4) ^ (n + 1) := by positivity
      have h1' : (1 : ℝ) - (1/4) ^ (n + 1) ≤ 1 := by linarith
      have h2' : (4/3 : ℝ) * (1 - (1/4) ^ (n + 1)) ≤ (4/3) * 1 :=
        mul_le_mul_of_nonneg_left h1' (by norm_num)
      calc (4/3) * (1 - (1/4) ^ (n + 1)) * u 19
          ≤ ((4/3) * 1) * u 19 := mul_le_mul_of_nonneg_right h2' (u_nonneg 19)
        _ = (4/3) * u 19 := by ring
    have h3 : (4/3 : ℝ) * u 19 ≤ 1 / 10000000 := by
      unfold u
      norm_num
    exact le_trans h1 (le_trans h2 h3)

end Work.Deep.Sparse
