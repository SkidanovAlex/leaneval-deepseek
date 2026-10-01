import Mathlib
import Submission.Work.LinnikAreas.Density4.thetaDiag_eval_defs

/-!
# The telescoping increment bound `tdDg M n ≤ tdG M n + 1`

For `g n = tdG M n = min (log n) M` and the backward difference
`tdDg M n = n g(n) - (n-1) g(n-1)` one has
`n g(n) - (n-1) g(n-1) = g(n) + (n-1)(g(n) - g(n-1))`,
and `g(n) - g(n-1) ≤ log n - log(n-1) ≤ 1/(n-1)` because `min · M` is 1-Lipschitz
and `log(1 + 1/(n-1)) ≤ 1/(n-1)`.  Hence `tdDg M n ≤ g(n) + 1`.
-/

open scoped BigOperators
noncomputable section

namespace Work.LinnikAreas.Density4

/-- For `y ≤ x`, the map `min · M` satisfies `min x M - min y M ≤ x - y`. -/
private lemma td_min_sub_min_le_sub (x y M : ℝ) (h : y ≤ x) :
    min x M - min y M ≤ x - y := by
  have h1 : min x M - min y M ≤ |min x M - min y M| := le_abs_self _
  have h2 : |min x M - min y M| ≤ max |x - y| |M - M| := abs_min_sub_min_le_max x M y M
  have h3 : max |x - y| |M - M| = |x - y| := by simp
  have h4 : |x - y| = x - y := abs_of_nonneg (sub_nonneg.mpr h)
  linarith [h1, h2, h3, h4]

/-- `log n - log (n-1) ≤ 1/(n-1)` for `n ≥ 2`. -/
private lemma td_log_sub_le (n : ℕ) (hn : 2 ≤ n) :
    Real.log (n:ℝ) - Real.log ((n-1:ℕ):ℝ) ≤ 1/((n:ℝ)-1) := by
  have hn1 : 1 ≤ n := by omega
  have hcast : ((n-1:ℕ):ℝ) = (n:ℝ) - 1 := by
    rw [Nat.cast_sub hn1]; norm_num
  rw [hcast]
  set m : ℝ := (n:ℝ) - 1 with hm
  have hmpos : 0 < m := by
    have : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    rw [hm]; linarith
  have hnm : (n:ℝ) = m + 1 := by rw [hm]; ring
  rw [hnm]
  have hlog : Real.log (m+1) - Real.log m = Real.log ((m+1)/m) :=
    (Real.log_div (by positivity) (ne_of_gt hmpos)).symm
  rw [hlog]
  have hle := Real.log_le_sub_one_of_pos (show (0:ℝ) < (m+1)/m by positivity)
  have heq : (m+1)/m - 1 = 1/m := by field_simp; ring
  linarith [hle, heq]

theorem thetaDiag_Dg_le (M : ℝ) (hM : 0 < M) (n : ℕ) (hn : 2 ≤ n) :
    Work.LinnikAreas.Density4.tdDg M n ≤ Work.LinnikAreas.Density4.tdG M n + 1 := by
  have hn1 : 1 ≤ n := by omega
  -- step 1 : `g n - g (n-1) ≤ log n - log (n-1)`
  have hg : tdG M n - tdG M (n-1) ≤ Real.log (n:ℝ) - Real.log ((n-1:ℕ):ℝ) := by
    have hle : Real.log ((n-1:ℕ):ℝ) ≤ Real.log (n:ℝ) := by
      apply Real.log_le_log
      · exact_mod_cast (show 0 < n - 1 by omega)
      · exact_mod_cast (Nat.sub_le n 1)
    simp only [tdG]
    exact td_min_sub_min_le_sub _ _ _ hle
  -- step 2 : combine with the logarithmic bound
  have hkey : tdG M n - tdG M (n-1) ≤ 1/((n:ℝ)-1) :=
    hg.trans (td_log_sub_le n hn)
  have hnpos : (0:ℝ) < (n:ℝ) - 1 := by
    have : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    linarith
  rw [tdDg]
  have hsplit : (n:ℝ)*tdG M n - ((n:ℝ)-1)*tdG M (n-1)
      = tdG M n + ((n:ℝ)-1)*(tdG M n - tdG M (n-1)) := by ring
  rw [hsplit]
  have hmul : ((n:ℝ)-1)*(tdG M n - tdG M (n-1)) ≤ ((n:ℝ)-1)*(1/((n:ℝ)-1)) :=
    mul_le_mul_of_nonneg_left hkey (le_of_lt hnpos)
  have hone : ((n:ℝ)-1)*(1/((n:ℝ)-1)) = 1 := by field_simp
  linarith [hmul, hone]

end Work.LinnikAreas.Density4
