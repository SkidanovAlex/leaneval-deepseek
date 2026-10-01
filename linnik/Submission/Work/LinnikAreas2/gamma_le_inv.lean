import Mathlib

namespace Work.LinnikAreas2

/-- Convexity of `Γ` on the positive reals, together with `Γ 1 = Γ 2 = 1`, gives `Γ x ≤ 1`
for every `x ∈ [1, 2]` (a convex function on an interval is bounded above by the maximum of
its endpoint values). -/
theorem gamma_le_one_of_mem_Icc (x : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 2) :
    Real.Gamma x ≤ 1 := by
  have ha : (0 : ℝ) ≤ 2 - x := by linarith
  have hb : (0 : ℝ) ≤ x - 1 := by linarith
  have hab : (2 - x) + (x - 1) = 1 := by ring
  have h1 : (1 : ℝ) ∈ Set.Ioi (0 : ℝ) := by norm_num
  have h2 : (2 : ℝ) ∈ Set.Ioi (0 : ℝ) := by norm_num
  have h := Real.convexOn_Gamma.2 h1 h2 ha hb hab
  rw [smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul, Real.Gamma_one, Real.Gamma_two] at h
  have hkey : (2 - x) * 1 + (x - 1) * 2 = x := by ring
  rw [hkey] at h
  linarith

theorem gamma_le_inv (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) : Real.Gamma σ ≤ 1 / σ := by
  have hle1 : (1 : ℝ) ≤ σ + 1 := by linarith
  have hle2 : σ + 1 ≤ 2 := by linarith
  have ha : (0 : ℝ) ≤ 2 - (σ + 1) := by linarith
  have hb : (0 : ℝ) ≤ (σ + 1) - 1 := by linarith
  have hab : (2 - (σ + 1)) + ((σ + 1) - 1) = 1 := by ring
  have h1 : (1 : ℝ) ∈ Set.Ioi (0 : ℝ) := by norm_num
  have h2 : (2 : ℝ) ∈ Set.Ioi (0 : ℝ) := by norm_num
  have h := Real.convexOn_Gamma.2 h1 h2 ha hb hab
  rw [smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul, Real.Gamma_one, Real.Gamma_two] at h
  have hkey : (2 - (σ + 1)) * 1 + ((σ + 1) - 1) * 2 = σ + 1 := by ring
  rw [hkey] at h
  rw [Real.Gamma_add_one hσ.ne'] at h
  rw [le_div_iff₀ hσ]
  linarith

end Work.LinnikAreas2
