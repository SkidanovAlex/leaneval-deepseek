import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseBox.sideAt_large
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1.Core.MM

/-!
# `Work.BoseFixB1.Core.MM.mmIneq2OfCoreB`

The pure-arithmetic core of the mean-mismatch payment, in the *"second square root"*
shape: from the "core" bound

`262144 (2π)^3 ce cq cm ℓ² S ≤ 1`

(with `ce, cq, cm, S ≥ 0` and `ℓ > 0`) the two-square-root product

`2 √(cq ℓ⁻²) · √(cm S (2π)^3 ce)`

is at most `1/(256 ℓ²)`.

The constant `262144 = 2^18` is exactly the one that makes the two sides meet: with
`P := cq cm S (2π)^3 ce` the hypothesis is `262144 ℓ² P ≤ 1`, i.e.
`P ≤ 1/(262144 ℓ²) = (1/(512 ℓ))²`, so `√P ≤ 1/(512 ℓ)` and
`2 √(cq ℓ⁻²) √(cm S (2π)^3 ce) = 2 ℓ⁻¹ √P ≤ 2 ℓ⁻¹ /(512 ℓ) = 1/(256 ℓ²)`.

`sqrtProdBoundB` is the abstract statement; `mmIneq2OfCoreB` instantiates it at FS's
box parameters `ℓ = sideAt μ A`, `d = (paramsAt μ A).d` and
`S = (1 + (ℓd)⁻¹ + |log d|)³ ((ℓd)³)⁻¹`, where the hypothesis `hcore` is the
"core smallness" condition supplied by the caller.
-/

/-- **The arithmetic core.**  For nonnegative `ce, cq, cm, S` and `ℓ > 0`,
`262144 (2π)^3 ce cq cm ℓ² S ≤ 1` implies
`2 √(cq ℓ⁻²) √(cm S (2π)³ ce) ≤ 1/(256 ℓ²)`. -/
lemma sqrtProdBoundB {ce cq cm ℓ S : ℝ} (hce : 0 ≤ ce) (hcq : 0 ≤ cq) (hcm : 0 ≤ cm)
    (hℓ : 0 < ℓ) (hS : 0 ≤ S)
    (hcore : 262144 * (2 * Real.pi) ^ 3 * ce * cq * cm * ℓ ^ 2 * S ≤ 1) :
    2 * Real.sqrt (cq * (ℓ⁻¹) ^ 2) * Real.sqrt (cm * S * (2 * Real.pi) ^ 3 * ce)
      ≤ 1 / (256 * ℓ ^ 2) := by
  have hℓne : ℓ ≠ 0 := ne_of_gt hℓ
  -- abbreviate the product `P = cq cm S (2π)³ ce`
  set P : ℝ := cq * cm * S * (2 * Real.pi) ^ 3 * ce with hP
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  -- the hypothesis in the shape `262144 ℓ² P ≤ 1`
  have hcore' : 262144 * ℓ ^ 2 * P ≤ 1 := by
    have heq : 262144 * ℓ ^ 2 * P
        = 262144 * (2 * Real.pi) ^ 3 * ce * cq * cm * ℓ ^ 2 * S := by
      rw [hP]; ring
    rw [heq]; exact hcore
  have hPle : P ≤ 1 / (262144 * ℓ ^ 2) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 262144 * ℓ ^ 2)]
    linarith [hcore']
  -- `1/(262144 ℓ²) = (1/(512 ℓ))²`
  have hPle2 : P ≤ (1 / (512 * ℓ)) ^ 2 := by
    rw [div_pow, one_pow, mul_pow, show (512 : ℝ) ^ 2 = 262144 by norm_num]
    exact hPle
  have hsqrtP : Real.sqrt P ≤ 1 / (512 * ℓ) := by
    calc Real.sqrt P ≤ Real.sqrt ((1 / (512 * ℓ)) ^ 2) := Real.sqrt_le_sqrt hPle2
      _ = 1 / (512 * ℓ) := Real.sqrt_sq (by positivity)
  have hL : Real.sqrt (cq * (ℓ⁻¹) ^ 2) = Real.sqrt cq * ℓ⁻¹ := by
    rw [Real.sqrt_mul hcq, Real.sqrt_sq (inv_nonneg.mpr hℓ.le)]
  have hsq : Real.sqrt cq * Real.sqrt (cm * S * (2 * Real.pi) ^ 3 * ce) = Real.sqrt P := by
    rw [← Real.sqrt_mul hcq]
    congr 1
    rw [hP]; ring
  rw [hL]
  calc 2 * (Real.sqrt cq * ℓ⁻¹) * Real.sqrt (cm * S * (2 * Real.pi) ^ 3 * ce)
      = 2 * (ℓ⁻¹ * Real.sqrt P) := by rw [← hsq]; ring
    _ ≤ 2 * (ℓ⁻¹ * (1 / (512 * ℓ))) := by
        have h := mul_le_mul_of_nonneg_left hsqrtP (inv_nonneg.mpr hℓ.le)
        linarith
    _ = 1 / (256 * ℓ ^ 2) := by
        have h1 : (512 : ℝ) * ℓ ≠ 0 := mul_ne_zero (by norm_num) hℓne
        have h2 : (256 : ℝ) * ℓ ^ 2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hℓne)
        field_simp
        ring

/-- FS's box side `ℓ = sideAt μ A` is positive for `μ, A > 0`. -/
lemma sideAt_pos_of' {A μ : ℝ} (hA : 0 < A) (hμ : 0 < μ) : 0 < Work.BoseBox.sideAt μ A := by
  rw [Work.BoseBox.sideAt_eq_rpow hA hμ]
  exact mul_pos hA (Real.rpow_pos_of_pos (mul_pos hμ (pow_pos hA 3)) _)

/-- FS's parameter `d = (paramsAt μ A).d` is positive for `μ, A > 0`. -/
lemma paramsAt_d_pos_of' {A μ : ℝ} (hA : 0 < A) (hμ : 0 < μ) :
    0 < (Work.BoseBox.paramsAt μ A).d := by
  show 0 < Work.BoseBox.fsXp (μ * A ^ 3) 6
  exact Work.BoseBox.fsXp_pos (mul_pos hμ (pow_pos hA 3))

theorem mmIneq2OfCoreB {A μ Cq Ce Cm : ℝ} (hA : 0 < A) (hμ : 0 < μ)
    (hCq : 0 ≤ Cq) (hCe : 0 ≤ Ce) (hCm : 0 ≤ Cm)
    (hcore : 262144 * (2 * Real.pi) ^ 3 * Ce * Cq * Cm * (Work.BoseBox.sideAt μ A) ^ 2 *
        (1 + ((Work.BoseBox.sideAt μ A) * (Work.BoseBox.paramsAt μ A).d)⁻¹
            + |Real.log ((Work.BoseBox.paramsAt μ A).d)|) ^ 3
        * (((Work.BoseBox.sideAt μ A) * (Work.BoseBox.paramsAt μ A).d) ^ 3)⁻¹ ≤ 1) :
    2 * Real.sqrt (Cq * ((Work.BoseBox.sideAt μ A)⁻¹) ^ 2) *
        Real.sqrt (Cm * (1 + ((Work.BoseBox.sideAt μ A) * (Work.BoseBox.paramsAt μ A).d)⁻¹
                + |Real.log ((Work.BoseBox.paramsAt μ A).d)|) ^ 3
          * (((Work.BoseBox.sideAt μ A) * (Work.BoseBox.paramsAt μ A).d) ^ 3)⁻¹
          * (2 * Real.pi) ^ 3 * Ce)
      ≤ Work.BoseBox.bValue / (16 * (Work.BoseBox.sideAt μ A) ^ 2) := by
  have hℓ : 0 < Work.BoseBox.sideAt μ A := sideAt_pos_of' hA hμ
  have hd : 0 < (Work.BoseBox.paramsAt μ A).d := paramsAt_d_pos_of' hA hμ
  -- the `S`-factor is nonnegative
  have hSnn : 0 ≤ (1 + ((Work.BoseBox.sideAt μ A) * (Work.BoseBox.paramsAt μ A).d)⁻¹
      + |Real.log ((Work.BoseBox.paramsAt μ A).d)|) ^ 3
      * (((Work.BoseBox.sideAt μ A) * (Work.BoseBox.paramsAt μ A).d) ^ 3)⁻¹ := by
    have hX : 0 < (Work.BoseBox.sideAt μ A) * (Work.BoseBox.paramsAt μ A).d := mul_pos hℓ hd
    refine mul_nonneg (pow_nonneg ?_ 3) (inv_nonneg.mpr (pow_nonneg hX.le 3))
    have h1 : 0 < ((Work.BoseBox.sideAt μ A) * (Work.BoseBox.paramsAt μ A).d)⁻¹ :=
      inv_pos.mpr hX
    have h2 : 0 ≤ |Real.log ((Work.BoseBox.paramsAt μ A).d)| := abs_nonneg _
    linarith
  -- the hypothesis in the shape used by `sqrtProdBoundB`
  have hcore' : 262144 * (2 * Real.pi) ^ 3 * Ce * Cq * Cm * (Work.BoseBox.sideAt μ A) ^ 2 *
      ((1 + ((Work.BoseBox.sideAt μ A) * (Work.BoseBox.paramsAt μ A).d)⁻¹
            + |Real.log ((Work.BoseBox.paramsAt μ A).d)|) ^ 3
        * (((Work.BoseBox.sideAt μ A) * (Work.BoseBox.paramsAt μ A).d) ^ 3)⁻¹) ≤ 1 := by
    simpa only [mul_assoc] using hcore
  have key := sqrtProdBoundB (ce := Ce) (cq := Cq) (cm := Cm) (ℓ := Work.BoseBox.sideAt μ A)
    (S := (1 + ((Work.BoseBox.sideAt μ A) * (Work.BoseBox.paramsAt μ A).d)⁻¹
            + |Real.log ((Work.BoseBox.paramsAt μ A).d)|) ^ 3
        * (((Work.BoseBox.sideAt μ A) * (Work.BoseBox.paramsAt μ A).d) ^ 3)⁻¹)
    hCe hCq hCm hℓ hSnn hcore'
  have hb : 1 / (256 * (Work.BoseBox.sideAt μ A) ^ 2)
      = Work.BoseBox.bValue / (16 * (Work.BoseBox.sideAt μ A) ^ 2) := by
    rw [Work.BoseBox.bValue]
    field_simp
    ring
  rw [hb] at key
  simpa only [mul_assoc] using key

end Work.BoseFixB1.Core.MM
