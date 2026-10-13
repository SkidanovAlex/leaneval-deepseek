import Mathlib
import Submission.Work.WilkiesH.Interp.V2Params

/-!
# The dominating polynomial value `qval`

This file introduces the scalar value

`qval μ D g H = CCc μ · (1 + D) · (1 + g)^(Ec μ) · (1 + log H)^(Fc μ)`

which is the evaluation of `qPoly μ` at `(D, g, log H)`, together with the elementary
facts about it (non-negativity, positivity, lower bounds by the individual factors)
that the numerical estimates of `q_bounds` need.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Classical

namespace Work.WilkiesH.Interp.V2qb

open Work.WilkiesH.Interp

/-- `0 ≤ (n : ℝ)`, with the type pinned. -/
lemma nat_cast_nonneg_R (n : ℕ) : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n

lemma one_le_nat_cast_add_one (n : ℕ) : (1 : ℝ) ≤ 1 + (n : ℝ) := by
  have := nat_cast_nonneg_R n; linarith

lemma one_le_one_add_D (D : ℕ) : (1 : ℝ) ≤ 1 + (D : ℝ) := one_le_nat_cast_add_one D

lemma one_le_one_add_g (g : ℕ) : (1 : ℝ) ≤ 1 + (g : ℝ) := one_le_nat_cast_add_one g

lemma one_le_one_add_log (H : ℕ) : (1 : ℝ) ≤ 1 + Real.log H := by
  have := log_nat_nonneg H; linarith

lemma zero_le_one_add_log (H : ℕ) : (0 : ℝ) ≤ 1 + Real.log H := by
  have := log_nat_nonneg H; linarith

lemma one_le_lgNat (H : ℕ) : 1 ≤ lgNat H := lgNat_pos H

lemma one_le_CCc (μ : ℕ) : 1 ≤ CCc μ :=
  Nat.one_le_pow _ _ (by omega)

lemma one_le_EE (μ : ℕ) : 1 ≤ EE μ :=
  Nat.one_le_pow _ _ (by omega)

lemma one_le_Ec (μ : ℕ) : 1 ≤ Ec μ := by
  have hμ : (1:ℕ) ≤ μ + 1 := by omega
  have h4 : (1:ℕ) ≤ (μ + 1) ^ 4 := by
    calc (1:ℕ) = 1 ^ (4:ℕ) := by norm_num
      _ ≤ (μ + 1) ^ 4 := Nat.pow_le_pow_left hμ 4
  simp only [Ec]
  exact le_trans h4 (Nat.le_mul_of_pos_left _ (by norm_num))

lemma one_le_Fc (μ : ℕ) : 1 ≤ Fc μ := one_le_Ec μ

/-- The value of `qPoly μ` at `(D, g, log H)`. -/
noncomputable def qval (μ D g H : ℕ) : ℝ :=
  (CCc μ : ℝ) * (1 + (D : ℝ)) * (1 + (g : ℝ)) ^ (Ec μ) * (1 + Real.log H) ^ (Fc μ)

lemma qval_eq_eval (μ D g H : ℕ) :
    MvPolynomial.eval ![(D : ℝ), (g : ℝ), Real.log H] (qPoly μ) = qval μ D g H := by
  rw [qPoly_eval, qval]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one]

lemma qval_nonneg (μ D g H : ℕ) : 0 ≤ qval μ D g H := by
  have h1 : (0 : ℝ) ≤ (CCc μ : ℝ) := nat_cast_nonneg_R _
  have h2 : (0 : ℝ) ≤ 1 + (D : ℝ) := by have := nat_cast_nonneg_R D; linarith
  have h3 : (0 : ℝ) ≤ 1 + (g : ℝ) := by have := nat_cast_nonneg_R g; linarith
  have h4 : (0 : ℝ) ≤ 1 + Real.log H := zero_le_one_add_log H
  rw [qval]
  exact mul_nonneg (mul_nonneg (mul_nonneg h1 h2) (pow_nonneg h3 _)) (pow_nonneg h4 _)

lemma one_le_qval (μ D g H : ℕ) (hH : 1 ≤ H) : 1 ≤ qval μ D g H := by
  have hCC : (1:ℝ) ≤ (CCc μ : ℝ) := by exact_mod_cast one_le_CCc μ
  have hD := one_le_nat_cast_add_one D
  have hg := one_le_nat_cast_add_one g
  have hHl := one_le_one_add_log H
  have hgp : (1:ℝ) ≤ (1 + (g:ℝ)) ^ (Ec μ) := one_le_pow₀ hg
  have hHp : (1:ℝ) ≤ (1 + Real.log H) ^ (Fc μ) := one_le_pow₀ hHl
  rw [qval]
  exact one_le_mul_of_one_le_of_one_le (M₀ := ℝ)
    (one_le_mul_of_one_le_of_one_le (M₀ := ℝ)
      (one_le_mul_of_one_le_of_one_le (M₀ := ℝ) hCC hD) hgp) hHp

lemma qval_pos (μ D g H : ℕ) (hH : 1 ≤ H) : 0 < qval μ D g H :=
  lt_of_lt_of_le zero_lt_one (one_le_qval μ D g H hH)

/-- `qval` is at least the constant `CCc μ · (1+g)^(Ec μ) · (1+log H)^(Fc μ)`. -/
lemma qval_ge_main (μ D g H : ℕ) :
    (CCc μ : ℝ) * (1 + (g : ℝ)) ^ (Ec μ) * (1 + Real.log H) ^ (Fc μ) ≤ qval μ D g H := by
  have hD : (1 : ℝ) ≤ 1 + (D : ℝ) := one_le_nat_cast_add_one D
  have hnn : 0 ≤ (CCc μ : ℝ) * (1 + (g : ℝ)) ^ (Ec μ) * (1 + Real.log H) ^ (Fc μ) := by
    have h1 : (0:ℝ) ≤ (CCc μ : ℝ) := nat_cast_nonneg_R _
    have h2 : (0 : ℝ) ≤ 1 + (g : ℝ) := by have := nat_cast_nonneg_R g; linarith
    have h3 : (0 : ℝ) ≤ 1 + Real.log H := zero_le_one_add_log H
    exact mul_nonneg (mul_nonneg h1 (pow_nonneg h2 _)) (pow_nonneg h3 _)
  have hq : qval μ D g H
      = ((CCc μ : ℝ) * (1 + (g : ℝ)) ^ (Ec μ) * (1 + Real.log H) ^ (Fc μ)) * (1 + (D : ℝ)) := by
    rw [qval]; ring
  rw [hq]
  calc (CCc μ : ℝ) * (1 + (g : ℝ)) ^ (Ec μ) * (1 + Real.log H) ^ (Fc μ)
      = (CCc μ : ℝ) * (1 + (g : ℝ)) ^ (Ec μ) * (1 + Real.log H) ^ (Fc μ) * 1 := by ring
    _ ≤ (CCc μ : ℝ) * (1 + (g : ℝ)) ^ (Ec μ) * (1 + Real.log H) ^ (Fc μ) * (1 + (D : ℝ)) :=
        mul_le_mul_of_nonneg_left (α := ℝ) hD hnn

/-- `qval` is at least `CCc μ`. -/
lemma qval_ge_CCc (μ D g H : ℕ) : (CCc μ : ℝ) ≤ qval μ D g H := by
  have h1 : (1 : ℝ) ≤ (1 + (g : ℝ)) ^ (Ec μ) := one_le_pow₀ (one_le_nat_cast_add_one g)
  have h2 : (1 : ℝ) ≤ (1 + Real.log H) ^ (Fc μ) := one_le_pow₀ (one_le_one_add_log H)
  have hnn : (0:ℝ) ≤ (CCc μ : ℝ) := nat_cast_nonneg_R _
  have hmain := qval_ge_main μ D g H
  have hstep : (CCc μ : ℝ) * 1 * 1
      ≤ (CCc μ : ℝ) * (1 + (g : ℝ)) ^ (Ec μ) * (1 + Real.log H) ^ (Fc μ) := by
    calc (CCc μ : ℝ) * 1 * 1 = (CCc μ : ℝ) * 1 := by ring
      _ ≤ (CCc μ : ℝ) * (1 + (g : ℝ)) ^ (Ec μ) := mul_le_mul_of_nonneg_left (α := ℝ) h1 hnn
      _ ≤ (CCc μ : ℝ) * (1 + (g : ℝ)) ^ (Ec μ) * (1 + Real.log H) ^ (Fc μ) :=
          le_mul_of_one_le_right (α := ℝ)
            (mul_nonneg hnn (pow_nonneg (by have := nat_cast_nonneg_R g; linarith) _)) h2
  calc (CCc μ : ℝ) = (CCc μ : ℝ) * 1 * 1 := by ring
    _ ≤ (CCc μ : ℝ) * (1 + (g : ℝ)) ^ (Ec μ) * (1 + Real.log H) ^ (Fc μ) := hstep
    _ ≤ qval μ D g H := hmain

/-- `qval` is at least `(1+g)^(Ec μ)`. -/
lemma qval_ge_gpow (μ D g H : ℕ) : (1 + (g : ℝ)) ^ (Ec μ) ≤ qval μ D g H := by
  have hCC : (1:ℝ) ≤ (CCc μ : ℝ) := by exact_mod_cast one_le_CCc μ
  have hD := one_le_nat_cast_add_one D
  have h2 : (1 : ℝ) ≤ (1 + Real.log H) ^ (Fc μ) := one_le_pow₀ (one_le_one_add_log H)
  have hnn : (0:ℝ) ≤ (1 + (g : ℝ)) ^ (Ec μ) := by
    have : (0 : ℝ) ≤ 1 + (g : ℝ) := by have := nat_cast_nonneg_R g; linarith
    exact pow_nonneg this _
  have hq : qval μ D g H
      = ((1 + (g : ℝ)) ^ (Ec μ)) * ((CCc μ : ℝ) * (1 + (D : ℝ)) * (1 + Real.log H) ^ (Fc μ)) := by
    rw [qval]; ring
  rw [hq]
  have h3 : (1:ℝ) ≤ (CCc μ : ℝ) * (1 + (D : ℝ)) * (1 + Real.log H) ^ (Fc μ) :=
    one_le_mul_of_one_le_of_one_le (M₀ := ℝ)
      (one_le_mul_of_one_le_of_one_le (M₀ := ℝ) hCC hD) h2
  calc (1 + (g : ℝ)) ^ (Ec μ)
      = (1 + (g : ℝ)) ^ (Ec μ) * 1 := by ring
    _ ≤ (1 + (g : ℝ)) ^ (Ec μ)
          * ((CCc μ : ℝ) * (1 + (D : ℝ)) * (1 + Real.log H) ^ (Fc μ)) :=
        mul_le_mul_of_nonneg_left (α := ℝ) h3 hnn

end Work.WilkiesH.Interp.V2qb
