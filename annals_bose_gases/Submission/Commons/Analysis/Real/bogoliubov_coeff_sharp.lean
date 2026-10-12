import Mathlib.Algebra.Order.Star.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.Analysis.Real

/-- **Sharp two-term Bogoliubov coefficient bound.**
For `0 < A` and `B ^ 2 ≤ A ^ 2` (i.e. `|B| ≤ A`),
`(A − √(A² − B²))/2 ≤ B²/(4A) + B⁴/(4A³)`. -/
theorem bogoliubov_coeff_sharp {A B : ℝ} (hA : 0 < A) (hB : B ^ 2 ≤ A ^ 2) :
    (A - Real.sqrt (A ^ 2 - B ^ 2)) / 2 ≤ B ^ 2 / (4 * A) + B ^ 4 / (4 * A ^ 3) := by
  have hD : 0 ≤ A ^ 2 - B ^ 2 := by linarith
  set S := Real.sqrt (A ^ 2 - B ^ 2) with hS
  have hSsq : S ^ 2 = A ^ 2 - B ^ 2 := by rw [hS]; exact Real.sq_sqrt hD
  have hSnn : 0 ≤ S := by rw [hS]; exact Real.sqrt_nonneg _
  have hfac : (A - S) * (A + S) = B ^ 2 := by
    have h : (A - S) * (A + S) = A ^ 2 - S ^ 2 := by ring
    rw [h, hSsq]; ring
  have hASnn : 0 ≤ A - S := by
    have hpos : 0 < A + S := by linarith
    have h2 : 0 ≤ (A - S) * (A + S) := by rw [hfac]; exact sq_nonneg B
    exact (mul_nonneg_iff_of_pos_right hpos).mp h2
  set u := A - S with hu
  have hu_nn : 0 ≤ u := by rw [hu]; exact hASnn
  have hu_le : u ≤ A := by rw [hu]; linarith
  have hB2 : B ^ 2 = u * (2 * A - u) := by
    rw [hu]
    have h2 : 2 * A - (A - S) = A + S := by ring
    rw [h2]
    exact hfac.symm
  have hA3 : 0 < 4 * A ^ 3 := by positivity
  have hsum : B ^ 2 / (4 * A) + B ^ 4 / (4 * A ^ 3) = (A ^ 2 * B ^ 2 + B ^ 4) / (4 * A ^ 3) := by
    field_simp
  rw [hsum, le_div_iff₀ hA3]
  have hclean : u / 2 * (4 * A ^ 3) = 2 * A ^ 3 * u := by ring
  rw [hclean]
  have hprod : 0 ≤ u ^ 2 * (A - u) * (3 * A - u) := by
    have h1 : 0 ≤ u ^ 2 := sq_nonneg u
    have h2 : 0 ≤ A - u := by linarith
    have h3 : 0 ≤ 3 * A - u := by linarith
    exact mul_nonneg (mul_nonneg h1 h2) h3
  have key : A ^ 2 * B ^ 2 + B ^ 4 - 2 * A ^ 3 * u = u ^ 2 * (A - u) * (3 * A - u) := by
    have h4 : B ^ 4 = (B ^ 2) ^ 2 := by ring
    rw [h4, hB2]
    ring
  have hkey : 0 ≤ A ^ 2 * B ^ 2 + B ^ 4 - 2 * A ^ 3 * u := by
    rw [key]; exact hprod
  linarith

end Commons.Analysis.Real