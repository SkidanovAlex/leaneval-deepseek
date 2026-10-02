import Mathlib
import Submission.Commons.NumberTheory.Zeta.zeta_strip_polyGrowth
import Submission.Commons.NumberTheory.Zeta.zeta_strip_polyGrowth_neg

namespace Work.LinnikAreas.Zeta1Aux

/-!
# Polynomial growth of `ζ₁ = (s-1) ζ(s)` in the strip `-2 ≤ Re s ≤ 3`

`ζ₁ = (s - 1) ζ(s)` (as completed by Mathlib at `s = 1`) is an entire function.  This
file proves the crude polynomial bound

  `∃ C > 0, ∀ w, -2 ≤ Re w → Re w ≤ 3 → 1 ≤ |Im w| → ‖ζ₁ w‖ ≤ C * (|Im w| + 3)^13`

on the strip width `[-2, 3]` at heights `|Im w| ≥ 1`.

Route: in the region the point `w` is never `1`, so `‖ζ₁ w‖ = ‖w - 1‖ * ‖ζ w‖`, and
`‖w - 1‖ ≤ |Im w| + 3`.  For `ζ` itself the strip splits into the already-proved
`zeta_strip_polyGrowth_neg` (`-2 ≤ Re ≤ -1`, degree `12`) and `zeta_strip_polyGrowth`
(`-1 ≤ Re ≤ 3`, degree `4`, hence also degree `12`); the extra factor `‖w - 1‖` raises
the degree by exactly one.
-/

/-- Away from the pole `s = 1` one has `ζ₁ s = (s - 1) * ζ s`. -/
private lemma riemannZeta₁_eq_mul_sub (s : ℂ) (hs : s ≠ 1) :
    riemannZeta₁ s = (s - 1) * riemannZeta s := by
  have h := riemannZeta_eq_inv_sub_mul (s := s) hs
  calc
    riemannZeta₁ s = (s - 1) * ((s - 1)⁻¹ * riemannZeta₁ s) := by
      rw [← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hs), one_mul]
    _ = (s - 1) * riemannZeta s := by rw [h]

theorem zeta1_strip_region_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ, -2 ≤ w.re → w.re ≤ 3 → 1 ≤ |w.im| →
      ‖riemannZeta₁ w‖ ≤ C * (|w.im| + 3) ^ 13 := by
  obtain ⟨Cp, hCppos, hCp⟩ := Commons.NumberTheory.Zeta.zeta_strip_polyGrowth
  obtain ⟨Cn, hCnpos, hCn⟩ := Commons.NumberTheory.Zeta.zeta_strip_polyGrowth_neg
  refine ⟨max Cp Cn, lt_max_of_lt_left hCppos, ?_⟩
  intro w hlo hhi him
  have hKpos : 0 < max Cp Cn := lt_of_lt_of_le hCppos (le_max_left _ _)
  have hCpK : Cp ≤ max Cp Cn := le_max_left _ _
  have hCnK : Cn ≤ max Cp Cn := le_max_right _ _
  -- `w ≠ 1`, since `|Im w| ≥ 1`
  have himne : w.im ≠ 0 := by
    intro h0
    have : |w.im| = 0 := by rw [h0]; simp
    linarith
  have hwne : w ≠ 1 := by
    intro h
    exact himne (by rw [h]; simp)
  have hnorm : ‖riemannZeta₁ w‖ = ‖w - 1‖ * ‖riemannZeta w‖ := by
    rw [riemannZeta₁_eq_mul_sub w hwne, norm_mul]
  -- geometric facts
  have hX1 : (1 : ℝ) ≤ |w.im| + 3 := by linarith [abs_nonneg w.im, him]
  have hw1 : ‖w - 1‖ ≤ |w.im| + 3 := by
    have hre1 : |w.re - 1| ≤ 3 := by
      rw [abs_le]
      exact ⟨by linarith, by linarith⟩
    have hsplit : w - 1 = ((w.re - 1 : ℝ) : ℂ) + Complex.I * (w.im : ℂ) := by
      apply Complex.ext <;> simp
    rw [hsplit]
    calc
      ‖((w.re - 1 : ℝ) : ℂ) + Complex.I * (w.im : ℂ)‖
          ≤ ‖((w.re - 1 : ℝ) : ℂ)‖ + ‖Complex.I * (w.im : ℂ)‖ := norm_add_le _ _
      _ = |w.re - 1| + |w.im| := by
            rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, one_mul,
              Complex.norm_real, Real.norm_eq_abs]
      _ ≤ 3 + |w.im| := by linarith
      _ = |w.im| + 3 := by ring
  -- strip bound for `ζ` itself, degree `12` on the whole strip `[-2, 3]`
  have hz : ‖riemannZeta w‖ ≤ max Cp Cn * (|w.im| + 3) ^ 12 := by
    have hform : w = (w.re : ℂ) + Complex.I * (w.im : ℂ) := by
      apply Complex.ext <;> simp
    have hXpow : (|w.im| + 3) ^ 4 ≤ (|w.im| + 3) ^ 12 :=
      pow_le_pow_right₀ hX1 (by norm_num : (4 : ℕ) ≤ 12)
    have hXnn : (0 : ℝ) ≤ (|w.im| + 3) ^ 12 := by positivity
    by_cases hcase : w.re ≤ -1
    · have hb : ‖riemannZeta w‖ ≤ Cn * (|w.im| + 3) ^ 12 := by
        simpa only [← hform] using hCn w.re w.im hlo hcase him
      exact le_trans hb (mul_le_mul_of_nonneg_right hCnK hXnn)
    · have hcase' : -1 ≤ w.re := by linarith
      have hb : ‖riemannZeta w‖ ≤ Cp * (|w.im| + 3) ^ 4 := by
        simpa only [← hform] using hCp w.re w.im hcase' hhi him
      calc
        ‖riemannZeta w‖ ≤ Cp * (|w.im| + 3) ^ 4 := hb
        _ ≤ Cp * (|w.im| + 3) ^ 12 := mul_le_mul_of_nonneg_left hXpow (le_of_lt hCppos)
        _ ≤ max Cp Cn * (|w.im| + 3) ^ 12 :=
            mul_le_mul_of_nonneg_right hCpK hXnn
  calc
    ‖riemannZeta₁ w‖ = ‖w - 1‖ * ‖riemannZeta w‖ := hnorm
    _ ≤ (|w.im| + 3) * (max Cp Cn * (|w.im| + 3) ^ 12) :=
        mul_le_mul hw1 hz (norm_nonneg _) (by positivity)
    _ = max Cp Cn * (|w.im| + 3) ^ 13 := by ring

end Work.LinnikAreas.Zeta1Aux
