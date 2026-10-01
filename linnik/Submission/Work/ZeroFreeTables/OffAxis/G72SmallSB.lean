import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.G72Base

noncomputable section

namespace Work.ZeroFreeTables.OffAxis

open Work.ZeroFreeTables

/-! ## The closed form of `G72` at a negative real argument -/

lemma A72_ofReal (b : ℝ) (hb : b ≠ 0) :
    A72 (-(b:ℂ)) = (((1/30)*(-32/b + 80/b^3 + 120/b^4 - 120/b^6) : ℝ) : ℂ) := by
  simp only [A72]
  push_cast
  field_simp
  ring

lemma B72_ofReal (b : ℝ) (hb : b ≠ 0) :
    B72 (-(b:ℂ)) = (((4*(1-b)^2/b^6 : ℝ) : ℂ)) := by
  simp only [B72]
  push_cast
  field_simp
  ring

/-- **Closed form of `G72` at a negative real argument.** -/
theorem G72_real_closed (b : ℝ) (hb : b ≠ 0) :
    (G72 (-(b:ℂ))).re = (1/30)*(-32/b + 80/b^3 + 120/b^4 - 120/b^6)
      + Real.exp (2*b) * (4*(1-b)^2/b^6) := by
  have hw : (-(b:ℂ)) ≠ 0 := by simpa using hb
  have h := G72_eq_closed hw
  have h1 := A72_ofReal b hb
  have h2 := B72_ofReal b hb
  have he : Complex.exp (-2*(-(b:ℂ))) = ((Real.exp (2*b) : ℝ) : ℂ) := by
    rw [show -2*(-(b:ℂ)) = ((2*b : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_exp]
  rw [h, h1, h2]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero, he]

/-- **`s ≤ 7/25`**: the crude bound `Isub s σ ≤ ∫₀² (e^{sy}-1) g72`. -/
theorem G72SmallS (s σ : ℝ) (hs : 0 ≤ s) (hs2 : s ≤ 7/25) (hσ : 0 ≤ σ) :
    Work.ZeroFreeTables.OffAxis.Isub s σ ≤ 16/105 := by
  have hI0 : Isub 0 σ ≤ 0 := by
    have h := G72ImagNonneg σ
    have harg : (((-0 : ℝ) : ℂ) + (σ : ℂ) * Complex.I) = (σ : ℂ) * Complex.I := by
      push_cast; ring
    have h0 : Isub 0 σ = -((G72 ((σ:ℂ)*Complex.I)).re) := by
      simp only [Isub]
      rw [harg]
      ring
    rw [h0]
    linarith
  have hkey : Isub s σ = Isub 0 σ
      + ∫ y in (0:ℝ)..2, (Real.exp (s*y) - 1) * Real.cos (σ*y) * g72 y := by
    have h1 : Isub s σ
        = ∫ y in (0:ℝ)..2, (Real.exp (s*y) - 2) * Real.cos (σ*y) * g72 y :=
      Isub_eq_integral s σ
    have h0 : Isub 0 σ
        = ∫ y in (0:ℝ)..2, (Real.exp (0*y) - 2) * Real.cos (σ*y) * g72 y :=
      Isub_eq_integral 0 σ
    rw [h1, h0]
    have hi2 : IntervalIntegrable (fun y : ℝ => (Real.exp (0*y) - 2) * Real.cos (σ*y) * g72 y)
        MeasureTheory.volume (0:ℝ) 2 := by
      apply Continuous.intervalIntegrable
      simp only [Work.ZeroFreeTables.g72]
      fun_prop
    have hi3 : IntervalIntegrable (fun y : ℝ => (Real.exp (s*y) - 1) * Real.cos (σ*y) * g72 y)
        MeasureTheory.volume (0:ℝ) 2 := by
      apply Continuous.intervalIntegrable
      simp only [Work.ZeroFreeTables.g72]
      fun_prop
    rw [← intervalIntegral.integral_add hi2 hi3]
    apply intervalIntegral.integral_congr
    intro y _
    show (Real.exp (s*y) - 2) * Real.cos (σ*y) * g72 y
      = (Real.exp (0*y) - 2) * Real.cos (σ*y) * g72 y
        + (Real.exp (s*y) - 1) * Real.cos (σ*y) * g72 y
    have he : Real.exp (0*y) = 1 := by simp
    rw [he]
    ring
  rw [hkey]
  have h3 : (∫ y in (0:ℝ)..2, (Real.exp (s*y) - 1) * Real.cos (σ*y) * g72 y)
      ≤ ∫ y in (0:ℝ)..2, (Real.exp (s*y) - 1) * g72 y := by
    apply intervalIntegral.integral_mono_on (by norm_num)
    · apply Continuous.intervalIntegrable
      simp only [Work.ZeroFreeTables.g72]
      fun_prop
    · apply Continuous.intervalIntegrable
      simp only [Work.ZeroFreeTables.g72]
      fun_prop
    · intro y hy
      have hy0 : 0 ≤ y := hy.1
      have hg := g72_nonneg hy0 hy.2
      have hcs : Real.cos (σ*y) ≤ 1 := Real.cos_le_one _
      have he1 : 0 ≤ Real.exp (s*y) - 1 := by
        have hh : (1:ℝ) ≤ Real.exp (s*y) := by
          have h0 := Real.exp_le_exp.mpr (mul_nonneg hs hy0)
          simpa using h0
        linarith
      calc (Real.exp (s*y) - 1) * Real.cos (σ*y) * g72 y
          ≤ (Real.exp (s*y) - 1) * 1 * g72 y := by
            apply mul_le_mul_of_nonneg_right _ hg
            exact mul_le_mul_of_nonneg_left hcs he1
        _ = (Real.exp (s*y) - 1) * g72 y := by ring
  have h4 : (∫ y in (0:ℝ)..2, (Real.exp (s*y) - 1) * g72 y)
      ≤ ∫ y in (0:ℝ)..2, (Real.exp ((7/25)*y) - 1) * g72 y := by
    apply intervalIntegral.integral_mono_on (by norm_num)
    · apply Continuous.intervalIntegrable
      simp only [Work.ZeroFreeTables.g72]
      fun_prop
    · apply Continuous.intervalIntegrable
      simp only [Work.ZeroFreeTables.g72]
      fun_prop
    · intro y hy
      have hy0 : 0 ≤ y := hy.1
      have hg := g72_nonneg hy0 hy.2
      have h1 : Real.exp (s*y) ≤ Real.exp ((7/25)*y) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hs2 hy0)
      calc (Real.exp (s*y) - 1) * g72 y ≤ (Real.exp ((7/25)*y) - 1) * g72 y :=
            mul_le_mul_of_nonneg_right (by linarith) hg
        _ = (Real.exp ((7/25)*y) - 1) * g72 y := rfl
  have h5 : (∫ y in (0:ℝ)..2, (Real.exp ((7/25)*y) - 1) * g72 y)
      = (G72 (-((7/25 : ℝ) : ℂ))).re - 8/9 := by
    have hI : (∫ y in (0:ℝ)..2, Real.exp ((7/25)*y) * g72 y)
        = (G72 (-((7/25 : ℝ) : ℂ))).re := by
      rw [G72_re_eq_integral]
      apply intervalIntegral.integral_congr
      intro y _
      simp only [Complex.neg_re, Complex.ofReal_re, Complex.neg_im, Complex.ofReal_im, neg_zero,
        zero_mul, Real.cos_zero, mul_one, neg_mul, neg_neg]
    have hS : (∫ y in (0:ℝ)..2, (Real.exp ((7/25)*y) - 1) * g72 y)
        = (∫ y in (0:ℝ)..2, Real.exp ((7/25)*y) * g72 y)
          - ∫ y in (0:ℝ)..2, g72 y := by
      rw [← intervalIntegral.integral_sub]
      · apply intervalIntegral.integral_congr
        intro y _
        ring
      · apply Continuous.intervalIntegrable
        unfold Work.ZeroFreeTables.g72
        fun_prop
      · apply Continuous.intervalIntegrable
        unfold Work.ZeroFreeTables.g72
        fun_prop
    rw [hS, hI, integral_g72]
  have h6 : (G72 (-((7/25 : ℝ) : ℂ))).re - 8/9 ≤ 16/105 := by
    rw [G72_real_closed (7/25) (by norm_num)]
    have he : Real.exp (2*(7/25)) ≤ 1.750673 := by
      have := Real.exp_bound' (x := 2*(7/25)) (by norm_num) (by norm_num) (n := 9) (by norm_num)
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at this
      norm_num at this ⊢
      linarith
    nlinarith [he]
  have hstep : Isub s σ ≤ Isub 0 σ
      + (∫ y in (0:ℝ)..2, (Real.exp (s*y) - 1) * Real.cos (σ*y) * g72 y) := by rw [hkey]
  linarith [hI0, hstep, h3, h4, h5, h6]

end Work.ZeroFreeTables.OffAxis
