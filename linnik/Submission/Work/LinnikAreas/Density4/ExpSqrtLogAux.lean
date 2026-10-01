import Mathlib

namespace Work.LinnikAreas.Density4

/-- The antitone envelope `t ↦ exp (-(c √t))`; for `t < 0` Lean's `Real.sqrt` is `0`, so the
function is constantly `1` there. -/
noncomputable def Fq (c : ℝ) (t : ℝ) : ℝ := Real.exp (-(c * Real.sqrt t))

/-- A primitive, valid on `[0, ∞)`, of `Fq c`: `t ↦ -(2/c²)(1 + c√t) exp (-(c√t))`.
Its (right) derivative at `0` is also `Fq c 0 = 1`. -/
noncomputable def Gq (c : ℝ) (t : ℝ) : ℝ :=
  -(2/c^2) * (1 + c * Real.sqrt t) * Real.exp (-(c * Real.sqrt t))

lemma Fq_antitone (c : ℝ) (hc : 0 < c) : AntitoneOn (Fq c) (Set.Ici 0) := by
  intro x hx y hy hxy
  simp only [Fq]
  apply Real.exp_le_exp.mpr
  have : Real.sqrt x ≤ Real.sqrt y := Real.sqrt_le_sqrt hxy
  nlinarith [mul_le_mul_of_nonneg_left this (le_of_lt hc)]

lemma Fq_le_one (c : ℝ) (hc : 0 < c) {t : ℝ} (ht : 0 ≤ t) : Fq c t ≤ 1 := by
  simp only [Fq]
  rw [Real.exp_le_one_iff]
  have : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  nlinarith [mul_nonneg (le_of_lt hc) this]

lemma Fq_zero (c : ℝ) : Fq c 0 = 1 := by
  simp [Fq]

lemma Gq_zero (c : ℝ) (hc : 0 < c) : Gq c 0 = -(2/c^2) := by
  simp [Gq]

lemma Gq_nonpos (c : ℝ) (hc : 0 < c) {t : ℝ} (ht : 0 ≤ t) : Gq c t ≤ 0 := by
  have hc2 : (0:ℝ) < c^2 := by positivity
  have h1 : (0:ℝ) < 1 + c * Real.sqrt t := by
    have : 0 ≤ c * Real.sqrt t := mul_nonneg (le_of_lt hc) (Real.sqrt_nonneg t)
    linarith
  have h2 : (0:ℝ) < Real.exp (-(c * Real.sqrt t)) := Real.exp_pos _
  have h3 : -(2/c^2) ≤ 0 := by
    have : 0 < 2/c^2 := by positivity
    linarith
  simp only [Gq]
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg h3 (le_of_lt h1)) (le_of_lt h2)

end Work.LinnikAreas.Density4
