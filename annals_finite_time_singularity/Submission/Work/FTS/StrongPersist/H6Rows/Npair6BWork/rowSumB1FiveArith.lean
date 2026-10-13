import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

/-- The purely numerical form of the coefficient bound used in `rowSumB1FiveArith`:
for `0 < α ≤ 1` one has `√3 · √(4/π + 200/(γ-1)) ≤ 100 α^{-1/2}`, where `γ = gam α = 1 + α/10`.

Since `γ - 1 = α/10`, the bracket is `4/π + 2000/α`; it is enough that
`3 · (4/π + 2000/α) ≤ 10000/α`, which holds because `α ≤ 1` and `π > 3`. -/
private lemma sqrt_three_mul_sqrt_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Real.sqrt 3 * Real.sqrt (4 / Real.pi + 200 / (Work.Spaces.gam α - 1))
      ≤ 100 * α ^ (-(1 / 2 : ℝ)) := by
  have hg : Work.Spaces.gam α - 1 = α / 10 := Work.Spaces.gam_sub_one α
  rw [hg]
  have h200 : 200 / (α / 10) = 2000 / α := by field_simp; norm_num
  rw [h200]
  rw [← Real.sqrt_mul (show (0 : ℝ) ≤ 3 by norm_num)]
  have hS : (0 : ℝ) ≤ 100 * α ^ (-(1 / 2 : ℝ)) := by positivity
  rw [Real.sqrt_le_left hS]
  have hSsq : (100 * α ^ (-(1 / 2 : ℝ))) ^ 2 = 10000 / α := by
    rw [mul_pow]
    have h2 : (α ^ (-(1 / 2 : ℝ))) ^ 2 = α ^ (-(1 : ℝ)) := by
      rw [sq, ← Real.rpow_add hα]
      norm_num
    rw [h2, Real.rpow_neg_one]
    norm_num
    field_simp
  rw [hSsq]
  have h3 : 3 * (4 / Real.pi + 2000 / α) ≤ 10000 / α := by
    have h1 : 3 * (4 / Real.pi + 2000 / α) ≤ 3 * (10000 / (3 * α)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      field_simp
      nlinarith [Real.pi_gt_three, Real.pi_pos]
    have h2 : 3 * (10000 / (3 * α)) = 10000 / α := by field_simp
    linarith
  exact h3

theorem rowSumB1FiveArith {α M K6 N P Q : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hM : 0 ≤ M) (hK6 : 0 ≤ K6) (hN : 0 ≤ N)
    (hP : P ≤ (4 / Real.pi + 200 / (Work.Spaces.gam α - 1)) * K6 ^ 2)
    (hQ : Q ≤ N ^ 2) :
    Real.sqrt 3 * M * (Real.sqrt P * Real.sqrt Q)
      ≤ 100 * α ^ (-(1 / 2 : ℝ)) * M * K6 * N := by
  set Cf : ℝ := 4 / Real.pi + 200 / (Work.Spaces.gam α - 1) with hCf
  have hgam : (0 : ℝ) < Work.Spaces.gam α - 1 := by
    rw [Work.Spaces.gam_sub_one α]; linarith
  have hCf_nonneg : 0 ≤ Cf := by
    rw [hCf]
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    positivity
  -- bound `√P` by `√Cf · K6` and `√Q` by `N`
  have hP' : Real.sqrt P ≤ Real.sqrt Cf * K6 := by
    have h1 : Real.sqrt P ≤ Real.sqrt (Cf * K6 ^ 2) := Real.sqrt_le_sqrt hP
    rwa [Real.sqrt_mul hCf_nonneg, Real.sqrt_sq hK6] at h1
  have hQ' : Real.sqrt Q ≤ N := by
    have h1 : Real.sqrt Q ≤ Real.sqrt (N ^ 2) := Real.sqrt_le_sqrt hQ
    rwa [Real.sqrt_sq hN] at h1
  have hcoef : Real.sqrt 3 * Real.sqrt Cf ≤ 100 * α ^ (-(1 / 2 : ℝ)) := by
    rw [hCf]
    exact sqrt_three_mul_sqrt_le hα hα1
  have hsqrtCKN : 0 ≤ Real.sqrt Cf * K6 := mul_nonneg (Real.sqrt_nonneg Cf) hK6
  have hSM : 0 ≤ Real.sqrt 3 * M := mul_nonneg (Real.sqrt_nonneg 3) hM
  have hcoef_nonneg : 0 ≤ 100 * α ^ (-(1 / 2 : ℝ)) := by positivity
  calc Real.sqrt 3 * M * (Real.sqrt P * Real.sqrt Q)
      ≤ Real.sqrt 3 * M * (Real.sqrt Cf * K6 * N) := by
        apply mul_le_mul_of_nonneg_left _ hSM
        exact mul_le_mul hP' hQ' (Real.sqrt_nonneg Q) hsqrtCKN
    _ = (Real.sqrt 3 * Real.sqrt Cf) * (M * K6 * N) := by ring
    _ ≤ (100 * α ^ (-(1 / 2 : ℝ))) * (M * K6 * N) :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = 100 * α ^ (-(1 / 2 : ℝ)) * M * K6 * N := by ring

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
