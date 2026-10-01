import Mathlib
import Submission.Work.LinnikAreas.Density4.ExpSqrtLogAux
import Submission.Work.LinnikAreas.Density4.Est.exp_neg_quad_ineq

namespace Work.LinnikAreas.Density4.Est

/-- `Gq c` is a primitive of the decreasing envelope `Fq c` on `[0, ∞)`; hence on any `[a,b]` with
`0 ≤ a ≤ b` the increment `Gq c b - Gq c a` dominates `Fq c b * (b - a)`.

The change of variables `u = c√b`, `v = c√a` turns this into the elementary inequality
`e^{-u}(u²-v²) ≤ 2(1+v)e^{-v} - 2(1+u)e^{-u}` for `0 ≤ v ≤ u`
(`exp_neg_quad_ineq`), which is the `w = u - v ≥ 0` case of `e^w ≥ 1 + w + w²/2`. -/
theorem Fq_mul_sub_le_Gq (c : ℝ) (hc : 0 < c) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    Work.LinnikAreas.Density4.Fq c b * (b - a) ≤ Work.LinnikAreas.Density4.Gq c b - Work.LinnikAreas.Density4.Gq c a := by
  have hb : 0 ≤ b := le_trans ha hab
  set u : ℝ := c * Real.sqrt b with hu
  set v : ℝ := c * Real.sqrt a with hv
  have hv0 : 0 ≤ v := by rw [hv]; positivity
  have hvu : v ≤ u := by
    rw [hv, hu]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hab) hc.le
  have hsqb : u ^ 2 = c ^ 2 * b := by rw [hu, mul_pow, Real.sq_sqrt hb]
  have hsqa : v ^ 2 = c ^ 2 * a := by rw [hv, mul_pow, Real.sq_sqrt ha]
  have hba : b - a = (u ^ 2 - v ^ 2) / c ^ 2 := by
    rw [hsqb, hsqa]
    field_simp
  have hFq : Work.LinnikAreas.Density4.Fq c b = Real.exp (-u) := by
    rw [Work.LinnikAreas.Density4.Fq, ← hu]
  have hGb : Work.LinnikAreas.Density4.Gq c b = -(2 / c ^ 2) * (1 + u) * Real.exp (-u) := by
    rw [Work.LinnikAreas.Density4.Gq, ← hu]
  have hGa : Work.LinnikAreas.Density4.Gq c a = -(2 / c ^ 2) * (1 + v) * Real.exp (-v) := by
    rw [Work.LinnikAreas.Density4.Gq, ← hv]
  have hC : Real.exp (-u) * ((u ^ 2 - v ^ 2) / c ^ 2) ≤
      (2 / c ^ 2) * ((1 + v) * Real.exp (-v) - (1 + u) * Real.exp (-u)) := by
    have h1 : Real.exp (-u) * (u ^ 2 - v ^ 2) ≤
        2 * ((1 + v) * Real.exp (-v) - (1 + u) * Real.exp (-u)) := by
      linarith [exp_neg_quad_ineq hv0 hvu]
    have h2 := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ 1 / c ^ 2)
    have L : (Real.exp (-u) * (u ^ 2 - v ^ 2)) * (1 / c ^ 2) =
        Real.exp (-u) * ((u ^ 2 - v ^ 2) / c ^ 2) := by
      rw [div_eq_mul_inv]; ring
    have R : (2 * ((1 + v) * Real.exp (-v) - (1 + u) * Real.exp (-u))) * (1 / c ^ 2) =
        (2 / c ^ 2) * ((1 + v) * Real.exp (-v) - (1 + u) * Real.exp (-u)) := by
      rw [div_eq_mul_inv]; ring
    rwa [L, R] at h2
  rw [hFq, hGb, hGa, hba]
  have heq : (2 / c ^ 2) * ((1 + v) * Real.exp (-v) - (1 + u) * Real.exp (-u)) =
      -(2 / c ^ 2) * (1 + u) * Real.exp (-u) - -(2 / c ^ 2) * (1 + v) * Real.exp (-v) := by
    ring
  exact hC.trans_eq heq

end Work.LinnikAreas.Density4.Est
