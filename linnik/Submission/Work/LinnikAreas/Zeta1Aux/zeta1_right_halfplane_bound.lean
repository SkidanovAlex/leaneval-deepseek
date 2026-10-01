import Mathlib
import Submission.Work.LinnikAreas.Zeta1Aux.CommonsImports

namespace Work.LinnikAreas.Zeta1Aux

/-- Auxiliary: `riemannZeta₁ w = (w - 1) * riemannZeta w` for `w ≠ 1`, obtained by
clearing the pole factor in Mathlib's identity `ζ(w) = (w - 1)⁻¹ * ζ₁(w)`. -/
private lemma riemannZeta₁_eq_sub_mul {w : ℂ} (hw1 : w ≠ 1) :
    riemannZeta₁ w = (w - 1) * riemannZeta w := by
  have hsub : w - 1 ≠ 0 := sub_ne_zero.mpr hw1
  have key : (w - 1) * riemannZeta w = riemannZeta₁ w := by
    rw [riemannZeta_eq_inv_sub_mul hw1]
    exact mul_inv_cancel_left₀ hsub _
  exact key.symm

/-- Auxiliary real inequality: for `x ≥ 1` and `C ≥ 0`, `x * C ≤ C * x ^ 13`. -/
private lemma mul_le_mul_pow_thirteen {x C : ℝ} (hx : 1 ≤ x) (hC : 0 ≤ C) :
    x * C ≤ C * x ^ 13 := by
  have hx0 : 0 ≤ x := le_trans zero_le_one hx
  have hx12 : 1 ≤ x ^ 12 := one_le_pow₀ hx
  have hx13 : x ^ 13 = x ^ 12 * x := by ring
  calc
    x * C = C * x := by ring
    _ = (C * x) * 1 := by ring
    _ ≤ (C * x) * x ^ 12 := mul_le_mul_of_nonneg_left hx12 (mul_nonneg hC hx0)
    _ = C * x ^ 13 := by rw [hx13]; ring

/-- **Bound for `ζ₁ = (s-1)ζ` in the half-plane `Re s ≥ 3`.** There is a positive
constant `C` with `‖ζ₁(w)‖ ≤ C ‖w - 1‖ ^ 13` for every `w` with `Re w ≥ 3`. -/
theorem zeta1_right_halfplane_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ, 3 ≤ w.re → ‖riemannZeta₁ w‖ ≤ C * ‖w - 1‖ ^ 13 := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Commons.NumberTheory.Zeta.zeta_norm_le_const_of_three_le_re
  refine ⟨C₀, hC₀pos, fun w hw => ?_⟩
  have hw1 : w ≠ 1 := by
    intro h
    rw [h] at hw
    norm_num at hw
  have hnorm : ‖riemannZeta₁ w‖ = ‖w - 1‖ * ‖riemannZeta w‖ := by
    rw [riemannZeta₁_eq_sub_mul hw1, norm_mul]
  have hnorm_ge2 : 2 ≤ ‖w - 1‖ := by
    have hre : (2 : ℝ) ≤ (w - 1).re := by
      rw [Complex.sub_re]
      simp
      linarith
    exact le_trans hre (Complex.re_le_norm _)
  calc
    ‖riemannZeta₁ w‖ = ‖w - 1‖ * ‖riemannZeta w‖ := hnorm
    _ ≤ ‖w - 1‖ * C₀ := mul_le_mul_of_nonneg_left (hC₀ w hw) (norm_nonneg _)
    _ ≤ C₀ * ‖w - 1‖ ^ 13 :=
        mul_le_mul_pow_thirteen (by linarith) hC₀pos.le

end Work.LinnikAreas.Zeta1Aux
