import Mathlib
import Submission.Work.LinnikAreas.Density4.selberg_U_aux

namespace Work.LinnikAreas.Density4.Udecay

/-- On the tail interval `[⌊x⌋₊, x]`, `muRecip t = muRecipSum ⌊x⌋₊` is constant, so the
integral against `dt/t` is the constant times `log x - log ⌊x⌋₊`. -/
theorem muRecip_tail_integral (x : ℝ) (hx : 1 ≤ x) :
    ∫ t in (⌊x⌋₊ : ℝ)..x, Work.LinnikAreas.Density4.muRecip t / t
      = Commons.NumberTheory.Moebius.muRecipSum ⌊x⌋₊ * (Real.log x - Real.log (⌊x⌋₊ : ℝ)) := by
  set c : ℕ := ⌊x⌋₊ with hc
  have hc1 : 1 ≤ c := by
    rw [hc]; exact Nat.le_floor (by simpa using hx)
  have hcp : (0 : ℝ) < (c : ℝ) := by
    have : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc1
    linarith
  have hcne : (c : ℝ) ≠ 0 := ne_of_gt hcp
  have hxpos : 0 < x := by linarith
  have hxne : x ≠ 0 := ne_of_gt hxpos
  have hc_le : (c : ℝ) ≤ x := by
    rw [hc]; exact Nat.floor_le (by linarith)
  have hxf : x < (c : ℝ) + 1 := by
    rw [hc]; exact Nat.lt_floor_add_one x
  have hcongr : Set.EqOn (fun t : ℝ => Work.LinnikAreas.Density4.muRecip t / t)
      (fun t : ℝ => Commons.NumberTheory.Moebius.muRecipSum c * (1 / t)) (Set.uIcc (c : ℝ) x) := by
    intro t ht
    rw [Set.uIcc_of_le hc_le] at ht
    obtain ⟨htc, htx⟩ := ht
    have hfloor : ⌊t⌋₊ = c := Nat.floor_eq_on_Ico c t ⟨htc, by linarith⟩
    have hmu : Work.LinnikAreas.Density4.muRecip t = Commons.NumberTheory.Moebius.muRecipSum c := by
      rw [Work.LinnikAreas.Density4.muRecip, hfloor]
    simp only [hmu, div_eq_mul_inv, one_mul]
  rw [intervalIntegral.integral_congr hcongr]
  rw [intervalIntegral.integral_const_mul]
  rw [integral_one_div_of_pos hcp hxpos]
  rw [Real.log_div hxne hcne]

end Work.LinnikAreas.Density4.Udecay
