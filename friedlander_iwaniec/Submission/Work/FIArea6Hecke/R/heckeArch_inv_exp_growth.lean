import Mathlib
import Submission.Work.FITop4.Bridge.area5_6_defs
import Submission.Work.FIArea5.S16Hecke.gammaVerticalLowerExp

/-!
# Exponential growth of `1 / heckeArch d 0` on the strip `-1/2 ≤ Re ≤ 3/2`

The archimedean factor of the completed Hecke `L`-function of `ℚ(i)` is

  `heckeArch d m s = (4d/π)^s · Γ(s + |m|/2)`   (`Work.FITop4.Bridge.heckeArch`),

so at `m = 0` it is `heckeArch d 0 s = X^s · Γ(s)`, `X = 4d/π`.

Since `X > 1` for `d ≥ 1` and `s ↦ 1/Γ(s)` is entire of exponential type, the reciprocal is
bounded by `c · exp (C·(1 + |Im s|))` on any fixed vertical strip.  Concretely:

* `‖(X^s)⁻¹‖ = X^{-Re s} ≤ X^{1/2}` for `-1/2 ≤ Re s` (`X ≥ 1`), using
  `Complex.cpow_neg` and `Complex.norm_cpow_eq_rpow_re_of_pos`;
* `‖1/Γ(s)‖ = ‖s‖ · ‖1/Γ(s+1)‖` by the recurrence `Complex.Gamma_add_one`, and the strip
  `Re s ∈ [-1/2, 3/2]` is carried into `Re(s+1) ∈ [1/2, 5/2] ⊂ [0, 5/2]`, where
  `Work.FIArea5.S16Hecke.gammaVerticalLowerExp` gives `‖1/Γ(u+it)‖ ≤ c₁ exp(C₁|t|)`.
  The prefactor `‖s‖ ≤ 2(1+|t|)` is absorbed into the exponential via `x ≤ e^x`.

This is the analytic input `heckeArch_inv_exp_growth` of the strip argument for
`heckeLval_strip_bound` (*FI* (16.18)); it was previously carried as an axiom
`heckeArch_inv_exp_growth'` in `heckeLval_strip_bound_primitive.lean`.
-/

namespace Work.FIArea6Hecke.R

open Complex

theorem heckeArch_inv_exp_growth (d : ℕ) (hd : 1 ≤ d) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ z : ℂ, -1/2 ≤ z.re → z.re ≤ 3/2 →
      ‖(Work.FITop4.Bridge.heckeArch d 0 z)⁻¹‖ ≤ c * Real.exp (C * (1 + |z.im|)) := by
  set X : ℝ := 4 * (d : ℝ) / Real.pi with hXdef
  have hX1 : 1 ≤ X := by
    have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
    rw [hXdef, le_div_iff₀ Real.pi_pos]
    nlinarith [Real.pi_lt_four, hd1]
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX1
  obtain ⟨c1, C1, hc1, hC1, hG⟩ :=
    Work.FIArea5.S16Hecke.gammaVerticalLowerExp (5/2) (by norm_num)
  refine ⟨X ^ (1/2 : ℝ) * (2 * c1), C1 + 2, by positivity, by linarith, ?_⟩
  intro z hz1 hz2
  -- unfold the archimedean factor at `m = 0`
  have hArch : Work.FITop4.Bridge.heckeArch d 0 z = ((X : ℂ) ^ z) * Complex.Gamma z := by
    rw [Work.FITop4.Bridge.heckeArch, hXdef]
    norm_num
  -- the complex power contributes only a constant on the strip
  have hcpow : ‖(((X : ℂ)) ^ z)⁻¹‖ ≤ X ^ (1/2 : ℝ) := by
    rw [← Complex.cpow_neg, Complex.norm_cpow_eq_rpow_re_of_pos hXpos]
    have h : (-z).re = -z.re := by simp
    rw [h]
    exact Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  -- the reciprocal Gamma factor grows at most like `exp (C₁ |Im z|)` times a linear prefactor
  have hGbound : ‖(Complex.Gamma z)⁻¹‖ ≤ 2 * c1 * Real.exp ((C1 + 2) * (1 + |z.im|)) := by
    have h1 : (Complex.Gamma z)⁻¹ = z * (Complex.Gamma (z + 1))⁻¹ :=
      Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one z
    have h2 := hG (z.re + 1) z.im (by linarith) (by linarith)
    have hw : (((z.re + 1 : ℝ) : ℂ) + ((z.im : ℝ) : ℂ) * Complex.I) = z + 1 := by
      apply Complex.ext <;> simp
    rw [hw] at h2
    have hznorm : ‖z‖ ≤ 2 * (1 + |z.im|) := by
      have h := Complex.norm_le_abs_re_add_abs_im z
      have hre : |z.re| ≤ 3/2 := abs_le.mpr ⟨by linarith, hz2⟩
      nlinarith [abs_nonneg z.im, h, hre]
    have hexp : 2 * (1 + |z.im|) ≤ Real.exp (2 * (1 + |z.im|)) := by
      have := Real.add_one_le_exp (2 * (1 + |z.im|))
      linarith
    rw [h1, norm_mul]
    calc ‖z‖ * ‖(Complex.Gamma (z + 1))⁻¹‖
        ≤ (2 * (1 + |z.im|)) * (c1 * Real.exp (C1 * |z.im|)) :=
          mul_le_mul hznorm h2 (norm_nonneg _) (by positivity)
      _ ≤ Real.exp (2 * (1 + |z.im|)) * (c1 * Real.exp (C1 * |z.im|)) :=
          mul_le_mul_of_nonneg_right hexp (by positivity)
      _ = c1 * Real.exp (2 * (1 + |z.im|) + C1 * |z.im|) := by
          rw [Real.exp_add]; ring
      _ ≤ c1 * Real.exp ((C1 + 2) * (1 + |z.im|)) := by
          apply mul_le_mul_of_nonneg_left _ hc1.le
          apply Real.exp_le_exp.mpr
          nlinarith [abs_nonneg z.im, hC1]
      _ ≤ 2 * c1 * Real.exp ((C1 + 2) * (1 + |z.im|)) := by
          have hpos : 0 ≤ c1 * Real.exp ((C1+2)*(1+|z.im|)) := by positivity
          nlinarith
  -- assemble: `(X^z · Γ z)⁻¹ = (X^z)⁻¹ · Γ z⁻¹`
  rw [hArch, mul_inv]
  calc ‖(((X : ℂ)) ^ z)⁻¹ * (Complex.Gamma z)⁻¹‖
      = ‖(((X : ℂ)) ^ z)⁻¹‖ * ‖(Complex.Gamma z)⁻¹‖ := norm_mul _ _
    _ ≤ X ^ (1/2 : ℝ) * (2 * c1 * Real.exp ((C1 + 2) * (1 + |z.im|))) :=
        mul_le_mul hcpow hGbound (norm_nonneg _) (by positivity)
    _ = X ^ (1/2 : ℝ) * (2 * c1) * Real.exp ((C1 + 2) * (1 + |z.im|)) := by ring

end Work.FIArea6Hecke.R
