import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Cauchy–Schwarz for interval integrals

A self-contained copy of the elementary L² Cauchy–Schwarz inequality for interval integrals of
nonnegative real functions, used by `Work.BMF.mrlas.kf_cauchy_schwarz`.
-/

open MeasureTheory intervalIntegral

namespace Work.BMF.mrlas

/-- Cauchy–Schwarz for interval integrals of nonnegative real functions. -/
lemma interval_integral_mul_le_sqrt {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ}
    (hf : IntervalIntegrable (fun t => f t ^ 2) volume a b)
    (hg : IntervalIntegrable (fun t => g t ^ 2) volume a b)
    (hfg : IntervalIntegrable (fun t => f t * g t) volume a b)
    (hnf : ∀ t ∈ Set.Icc a b, 0 ≤ f t) (hng : ∀ t ∈ Set.Icc a b, 0 ≤ g t) :
    ∫ t in a..b, f t * g t ≤ Real.sqrt (∫ t in a..b, f t ^ 2) * Real.sqrt (∫ t in a..b, g t ^ 2) := by
  set A : ℝ := ∫ t in a..b, f t ^ 2 with hA
  set B : ℝ := ∫ t in a..b, f t * g t with hB
  set C : ℝ := ∫ t in a..b, g t ^ 2 with hC
  have hA0 : 0 ≤ A := by rw [hA]; exact intervalIntegral.integral_nonneg hab (fun t _ => sq_nonneg _)
  have hC0 : 0 ≤ C := by rw [hC]; exact intervalIntegral.integral_nonneg hab (fun t _ => sq_nonneg _)
  have hB0 : 0 ≤ B := by
    rw [hB]
    exact intervalIntegral.integral_nonneg hab (fun t ht => mul_nonneg (hnf t ht) (hng t ht))
  have hquad : ∀ s : ℝ, 0 ≤ A * s ^ 2 - 2 * B * s + C := by
    intro s
    have h1 : (0:ℝ) ≤ ∫ t in a..b, (s * f t - g t) ^ 2 :=
      intervalIntegral.integral_nonneg hab (fun t _ => sq_nonneg _)
    have h2 : (∫ t in a..b, (s * f t - g t) ^ 2) = A * s ^ 2 - 2 * B * s + C := by
      have hpt : (fun t => (s * f t - g t) ^ 2)
          = (fun t => s ^ 2 * (f t ^ 2) - (2 * s) * (f t * g t) + (g t ^ 2)) := by
        funext t; ring
      rw [hpt, intervalIntegral.integral_add ((hf.const_mul _).sub (hfg.const_mul _)) hg,
        intervalIntegral.integral_sub (hf.const_mul _) (hfg.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      rw [← hA, ← hB, ← hC]
      ring
    linarith
  have hB2 : B ^ 2 ≤ A * C := by
    rcases lt_or_ge 0 A with hpos | hle
    · have h := hquad (B / A)
      have hmin : A * (B / A) ^ 2 - 2 * B * (B / A) + C = C - B ^ 2 / A := by
        field_simp <;> ring
      rw [hmin] at h
      have h2 : B ^ 2 / A ≤ C := by linarith
      rw [div_le_iff₀ hpos] at h2
      linarith
    · have hAz : A = 0 := le_antisymm hle hA0
      have hBz : B = 0 := by
        by_contra hBne
        set s : ℝ := (C + 1) / (2 * B) with hsdef
        have hs : 2 * B * s = C + 1 := by
          rw [hsdef]; field_simp <;> ring
        have h := hquad s
        rw [hAz] at h
        have hzero : (0:ℝ) * s ^ 2 = 0 := by simp
        rw [hzero, hs] at h
        linarith
      rw [hBz, hAz]; simp
  have hfinal : B ≤ Real.sqrt A * Real.sqrt C := by
    calc B ≤ Real.sqrt (A * C) := by
          rw [← Real.sqrt_sq hB0]
          exact Real.sqrt_le_sqrt hB2
      _ = Real.sqrt A * Real.sqrt C := Real.sqrt_mul hA0 C
  rw [hA, hB, hC]
  exact hfinal

end Work.BMF.mrlas
