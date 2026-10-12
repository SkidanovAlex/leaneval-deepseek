import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# D1 scalar bookkeeping (SESSION-284, continuation)

The arithmetic half of the D1 target `lm_appbogolubov_pWord`: the four scalar comparisons
(`main`, `log`, `quartic`, `interior`) that turn the integral bounds of
`SmallBoxD1Assembly` into the error terms of FS's `eq:refinedaprioribog` with the single
universal constant `C = d1TargetC Ct chiR0 chiSup d1Ks`.

All the statements are polynomial/`Real.log` comparisons in the displayed corpus quantities;
they are stated with `Real.pi` and the box parameters as free variables so that they can be
checked independently of the corpus.
-/

namespace Submission
namespace BoseGases

variable {M s R c0 Ct av C chi0 Z GW : ℝ}

/-- `(R/s)² ≤ chi0·(R/s)` under `R/s ≤ chi0` and `0 ≤ R/s`. -/
lemma d1_sq_le_mul (hRs : R / s ≤ chi0) (hRs0 : 0 ≤ R / s) :
    (R / s) ^ 2 ≤ chi0 * (R / s) := by
  calc (R / s) ^ 2 = (R / s) * (R / s) := by ring
    _ ≤ chi0 * (R / s) := mul_le_mul_of_nonneg_right hRs hRs0

/-- **The pointwise bracket comparison** `(1+6c₀a)(1+6C_t(R/s)²) ≤ (1+C(R/s))(1+Cc₀a)`
(from `C ≥ 6`, `C ≥ 6C_t chi0` and `C² ≥ 36C_t chi0`). -/
lemma d1_K1 (hRs : R / s ≤ chi0) (hRs0 : 0 ≤ R / s)
    (hCt : 0 ≤ Ct) (hav : 0 ≤ av) (hc0 : 0 ≤ c0)
    (hC6 : 6 ≤ C) (hCchi : 6 * Ct * chi0 ≤ C) (hCchi2 : 36 * Ct * chi0 ≤ C ^ 2) :
    (1 + 6 * c0 * av) * (1 + 6 * Ct * (R / s) ^ 2) ≤ (1 + C * (R / s)) * (1 + C * c0 * av) := by
  have hsq : (R / s) ^ 2 ≤ chi0 * (R / s) := d1_sq_le_mul hRs hRs0
  have hc0av0 : 0 ≤ c0 * av := mul_nonneg hc0 hav
  have ha : 6 * c0 * av ≤ C * c0 * av := by
    have h : 0 ≤ (C - 6) * (c0 * av) := mul_nonneg (by linarith) hc0av0
    nlinarith [h]
  have hb : 6 * Ct * (R / s) ^ 2 ≤ C * (R / s) := by
    have h1 : 6 * Ct * (R / s) ^ 2 ≤ 6 * Ct * chi0 * (R / s) := by
      have h := mul_le_mul_of_nonneg_left hsq (by linarith : (0 : ℝ) ≤ 6 * Ct)
      nlinarith [h]
    have h2 : 6 * Ct * chi0 * (R / s) ≤ C * (R / s) :=
      mul_le_mul_of_nonneg_right hCchi hRs0
    linarith [h1, h2]
  have hc : 36 * Ct * c0 * av * (R / s) ^ 2 ≤ C ^ 2 * c0 * av * (R / s) := by
    have h1 : 36 * Ct * c0 * av * (R / s) ^ 2 ≤ 36 * Ct * chi0 * (c0 * av * (R / s)) := by
      have h := mul_le_mul_of_nonneg_left hsq
        (by positivity : (0 : ℝ) ≤ 36 * Ct * c0 * av)
      nlinarith [h]
    have h2 : 36 * Ct * chi0 * (c0 * av * (R / s)) ≤ C ^ 2 * (c0 * av * (R / s)) :=
      mul_le_mul_of_nonneg_right hCchi2 (by positivity)
    linarith [h1, h2]
  have e1 : (1 + 6 * c0 * av) * (1 + 6 * Ct * (R / s) ^ 2)
      = 1 + 6 * c0 * av + 6 * Ct * (R / s) ^ 2 + 36 * Ct * c0 * av * (R / s) ^ 2 := by
    ring
  have e2 : (1 + C * (R / s)) * (1 + C * c0 * av)
      = 1 + C * (R / s) + C * c0 * av + C ^ 2 * c0 * av * (R / s) := by
    ring
  rw [e1, e2]
  linarith [ha, hb, hc]

/-- **The main-term comparison**: the M1 input `Z ≤ 2(1+6C_t(R/s)²)·GW` gives the Bogoliubov
main term `½(1+C(R/s))(1+Cc₀a)·GW·M²/s³`. -/
lemma d1_main_arith (hs : 0 < s) (hM2 : 2 ≤ M) (hRs : R / s ≤ chi0) (hRs0 : 0 ≤ R / s)
    (hav : 0 ≤ av) (hc0 : 0 ≤ c0) (hCt : 0 ≤ Ct) (hGW : 0 ≤ GW)
    (hC6 : 6 ≤ C) (hCchi : 6 * Ct * chi0 ≤ C) (hCchi2 : 36 * Ct * chi0 ≤ C ^ 2)
    (hZ : Z ≤ 2 * (1 + 6 * Ct * (R / s) ^ 2) * GW) :
    M * (M / (4 * s ^ 3 * (M - 1))) * (1 + 6 * c0 * av) * Z
      ≤ (1 / 2) * (1 + C * (R / s)) * (1 + C * c0 * av) * GW * (M * M / s ^ 3) := by
  have hM0 : (0 : ℝ) < M := by linarith
  have hM1 : (0 : ℝ) < M - 1 := by linarith
  have hK1 := d1_K1 (s := s) (R := R) (c0 := c0) (Ct := Ct) (av := av) (C := C)
    (chi0 := chi0) hRs hRs0 hCt hav hc0 hC6 hCchi hCchi2
  have hcoef : 0 ≤ M * (M / (4 * s ^ 3 * (M - 1))) * (1 + 6 * c0 * av) := by
    have h1 : 0 ≤ M / (4 * s ^ 3 * (M - 1)) := by
      apply div_nonneg (le_of_lt hM0)
      positivity
    have h2 : 0 ≤ 1 + 6 * c0 * av := by nlinarith [mul_nonneg hc0 hav]
    exact mul_nonneg (mul_nonneg (le_of_lt hM0) h1) h2
  have hA0 : 0 ≤ (1 + 6 * c0 * av) * (1 + 6 * Ct * (R / s) ^ 2) := by
    have h2 : 0 ≤ 1 + 6 * c0 * av := by nlinarith [mul_nonneg hc0 hav]
    have h3 : 0 ≤ 1 + 6 * Ct * (R / s) ^ 2 := by nlinarith [sq_nonneg (R / s), hCt]
    positivity
  have hkey : (1 + 6 * c0 * av) * (1 + 6 * Ct * (R / s) ^ 2)
      ≤ (M - 1) * ((1 + C * (R / s)) * (1 + C * c0 * av)) := by
    have h1 : (1 + 6 * c0 * av) * (1 + 6 * Ct * (R / s) ^ 2)
        ≤ (M - 1) * ((1 + 6 * c0 * av) * (1 + 6 * Ct * (R / s) ^ 2)) := by
      nlinarith [hA0, hM1, mul_nonneg hA0 (by linarith : (0 : ℝ) ≤ M - 2)]
    have h2 := mul_le_mul_of_nonneg_left hK1 (le_of_lt hM1)
    linarith [h1, h2]
  have hhalf : (1 + 6 * c0 * av) * (1 + 6 * Ct * (R / s) ^ 2) / (2 * (M - 1))
      ≤ (1 / 2) * ((1 + C * (R / s)) * (1 + C * c0 * av)) := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (M - 1))]
    nlinarith [hkey]
  calc M * (M / (4 * s ^ 3 * (M - 1))) * (1 + 6 * c0 * av) * Z
      ≤ M * (M / (4 * s ^ 3 * (M - 1))) * (1 + 6 * c0 * av) * (2 * (1 + 6 * Ct * (R / s) ^ 2) * GW) :=
        mul_le_mul_of_nonneg_left hZ hcoef
    _ = (M * M / s ^ 3) * GW
          * ((1 + 6 * c0 * av) * (1 + 6 * Ct * (R / s) ^ 2) / (2 * (M - 1))) := by
        field_simp
        ring
    _ ≤ (M * M / s ^ 3) * GW * ((1 / 2) * ((1 + C * (R / s)) * (1 + C * c0 * av))) :=
        mul_le_mul_of_nonneg_left hhalf (by positivity)
    _ = (1 / 2) * (1 + C * (R / s)) * (1 + C * c0 * av) * GW * (M * M / s ^ 3) := by ring

/-- **The logarithmic error comparison.** -/
lemma d1_log_arith (hs : 0 < s) (hM2 : 2 ≤ M) (hc0 : 0 < c0) (hav : 0 < av)
    (hdil : 2 * c0 * av ≤ 1) (hC : 192 * (1 + Real.log 2) ≤ C) :
    M * (M / (4 * s ^ 3 * (M - 1)))
        * (((2 * Real.pi) ^ 3)⁻¹
            * (6 * c0 * (16 * Real.pi * av) ^ 2 * (4 * Real.pi * Real.log ((2 * c0 * av)⁻¹))))
      ≤ C * (av ^ 2 * c0 * Real.log ((c0 * av)⁻¹) * (M * M / s ^ 3)) := by
  have hM1 : (0 : ℝ) < M - 1 := by linarith
  have hc0av : 0 < c0 * av := mul_pos hc0 hav
  have hL : 0 ≤ Real.log ((c0 * av)⁻¹) := by
    refine Real.log_nonneg ?_
    rw [one_le_inv₀ hc0av]
    linarith
  have hlog : Real.log ((2 * c0 * av)⁻¹) ≤ (1 + Real.log 2) * Real.log ((c0 * av)⁻¹) := by
    have h1 : (2 * c0 * av)⁻¹ = 2⁻¹ * (c0 * av)⁻¹ := by
      have h2 : 2 * c0 * av = 2 * (c0 * av) := by ring
      rw [h2, mul_inv]
    rw [h1, Real.log_mul (by norm_num) (by positivity)]
    rw [Real.log_inv]
    have hprod : 0 ≤ Real.log 2 * Real.log ((c0 * av)⁻¹) :=
      mul_nonneg (le_of_lt (Real.log_pos (by norm_num))) hL
    nlinarith [hprod, Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hlog2 : 0 ≤ Real.log ((2 * c0 * av)⁻¹) := by
    refine Real.log_nonneg ?_
    rw [one_le_inv₀ (by positivity)]
    linarith
  have hnorm : M * (M / (4 * s ^ 3 * (M - 1)))
        * (((2 * Real.pi) ^ 3)⁻¹
            * (6 * c0 * (16 * Real.pi * av) ^ 2 * (4 * Real.pi * Real.log ((2 * c0 * av)⁻¹))))
      = 192 * (M * M / (s ^ 3 * (M - 1))) * (c0 * av ^ 2) * Real.log ((2 * c0 * av)⁻¹) := by
    field_simp; try ring
  rw [hnorm]
  have hMfac : M * M / (s ^ 3 * (M - 1)) ≤ M * M / s ^ 3 := by
    have h1 : M * M / (M - 1) ≤ M * M := by
      rw [div_le_iff₀ hM1]
      nlinarith [hM1, le_of_lt (show (0:ℝ) < M by linarith)]
    calc M * M / (s ^ 3 * (M - 1)) = (M * M / (M - 1)) / s ^ 3 := by
          field_simp; try ring
      _ = (M * M / (M - 1)) * (s ^ 3)⁻¹ := rfl
      _ ≤ (M * M) * (s ^ 3)⁻¹ := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = M * M / s ^ 3 := rfl
  have hstep1 : 192 * (M * M / (s ^ 3 * (M - 1))) * (c0 * av ^ 2) * Real.log ((2 * c0 * av)⁻¹)
      ≤ 192 * (M * M / s ^ 3) * (c0 * av ^ 2) * Real.log ((2 * c0 * av)⁻¹) := by
    have hc : 0 ≤ 192 * (c0 * av ^ 2) * Real.log ((2 * c0 * av)⁻¹) := by
      have h2 : 0 ≤ c0 * av ^ 2 := by positivity
      positivity
    have h := mul_le_mul_of_nonneg_right hMfac hc
    nlinarith [h]
  have hstep2 : 192 * (M * M / s ^ 3) * (c0 * av ^ 2) * Real.log ((2 * c0 * av)⁻¹)
      ≤ 192 * (M * M / s ^ 3) * (c0 * av ^ 2) * ((1 + Real.log 2) * Real.log ((c0 * av)⁻¹)) := by
    have hc : 0 ≤ 192 * (M * M / s ^ 3) * (c0 * av ^ 2) := by positivity
    have h := mul_le_mul_of_nonneg_left hlog hc
    nlinarith [h]
  have hstep3 : 192 * (M * M / s ^ 3) * (c0 * av ^ 2) * ((1 + Real.log 2) * Real.log ((c0 * av)⁻¹))
      ≤ C * (av ^ 2 * c0 * Real.log ((c0 * av)⁻¹) * (M * M / s ^ 3)) := by
    have hc : 0 ≤ c0 * av ^ 2 * Real.log ((c0 * av)⁻¹) * (M * M / s ^ 3) := by
      have h2 : 0 ≤ c0 * av ^ 2 := by positivity
      positivity
    have h := mul_le_mul_of_nonneg_right hC hc
    nlinarith [h]
  linarith [hstep1, hstep2, hstep3]

/-- **The quartic error comparison.** -/
lemma d1_quart_arith (hs : 0 < s) (hM2 : 2 ≤ M) (hc0 : 0 < c0) (hav : 0 < av)
    (hC : (16 * Real.pi) ^ 4 / (3 * Real.pi ^ 2) ≤ C) :
    M * ((2 * Real.pi) ^ 3)⁻¹
        * ((M ^ 3 / (4 * s ^ 9 * (M - 1) ^ 3))
            * (64 * (16 * Real.pi * av) ^ 4 * ((4 / 3 : ℝ) * Real.pi * ((2 * c0) ^ 3)⁻¹)))
      ≤ C * (av ^ 4 * (c0 ^ 3)⁻¹ * (((M / s ^ 3) ^ 3) * ((M / s ^ 3)) * s ^ 3)) := by
  have hM1 : (0 : ℝ) < M - 1 := by linarith
  have hM0 : (0 : ℝ) < M := by linarith
  have hnorm : M * ((2 * Real.pi) ^ 3)⁻¹
        * ((M ^ 3 / (4 * s ^ 9 * (M - 1) ^ 3))
            * (64 * (16 * Real.pi * av) ^ 4 * ((4 / 3 : ℝ) * Real.pi * ((2 * c0) ^ 3)⁻¹)))
      = ((16 * Real.pi) ^ 4 / (3 * Real.pi ^ 2)) * (M ^ 4 / (s ^ 9 * (M - 1) ^ 3))
          * (av ^ 4 * (c0 ^ 3)⁻¹) := by
    field_simp; try ring
  rw [hnorm]
  have hfac : M ^ 4 / (s ^ 9 * (M - 1) ^ 3) ≤ M ^ 4 / s ^ 9 := by
    have h1 : M ^ 4 / ((M - 1) ^ 3) ≤ M ^ 4 := by
      have h3 : (1 : ℝ) ≤ (M - 1) ^ 3 := one_le_pow₀ (by linarith : (1 : ℝ) ≤ M - 1)
      rw [div_le_iff₀ (by positivity)]
      nlinarith [h3, sq_nonneg (M ^ 2), sq_nonneg M]
    calc M ^ 4 / (s ^ 9 * (M - 1) ^ 3) = (M ^ 4 / ((M - 1) ^ 3)) / s ^ 9 := by
          field_simp; try ring
      _ = (M ^ 4 / ((M - 1) ^ 3)) * (s ^ 9)⁻¹ := rfl
      _ ≤ M ^ 4 * (s ^ 9)⁻¹ := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = M ^ 4 / s ^ 9 := rfl
  have h3 : C * (av ^ 4 * (c0 ^ 3)⁻¹ * (((M / s ^ 3) ^ 3) * ((M / s ^ 3)) * s ^ 3))
      = C * (M ^ 4 / s ^ 9) * (av ^ 4 * (c0 ^ 3)⁻¹) := by
    field_simp; try ring
  rw [h3]
  have hcst : 0 ≤ (16 * Real.pi) ^ 4 / (3 * Real.pi ^ 2) := by positivity
  have hc : 0 ≤ av ^ 4 * (c0 ^ 3)⁻¹ := by positivity
  have hstep1 : ((16 * Real.pi) ^ 4 / (3 * Real.pi ^ 2)) * (M ^ 4 / (s ^ 9 * (M - 1) ^ 3))
        * (av ^ 4 * (c0 ^ 3)⁻¹)
      ≤ C * (M ^ 4 / s ^ 9) * (av ^ 4 * (c0 ^ 3)⁻¹) := by
    have h1 : ((16 * Real.pi) ^ 4 / (3 * Real.pi ^ 2)) * (M ^ 4 / (s ^ 9 * (M - 1) ^ 3))
        ≤ C * (M ^ 4 / s ^ 9) := by
      have h2 := mul_le_mul_of_nonneg_right hfac hcst
      have h4 : (M ^ 4 / s ^ 9) * ((16 * Real.pi) ^ 4 / (3 * Real.pi ^ 2))
          ≤ (M ^ 4 / s ^ 9) * C := mul_le_mul_of_nonneg_left hC (by positivity)
      nlinarith [h2, h4]
    exact mul_le_mul_of_nonneg_right h1 hc
  linarith [hstep1]

/-- **The interior error comparison.** -/
lemma d1_int_arith (hs : 0 < s) (hc0 : 0 < c0) (hav : 0 < av) (hM0 : 0 ≤ M)
    (hC : 10 / (3 * Real.pi) ≤ C) :
    M * ((2 * Real.pi) ^ 3)⁻¹
        * ((2 * Real.pi * av + Real.pi / 2 * av) * ((4 / 3 : ℝ) * Real.pi * (2 * c0) ^ 3))
      ≤ C * (av * c0 ^ 3 * ((M / s ^ 3) * s ^ 3)) := by
  have hnorm : M * ((2 * Real.pi) ^ 3)⁻¹
        * ((2 * Real.pi * av + Real.pi / 2 * av) * ((4 / 3 : ℝ) * Real.pi * (2 * c0) ^ 3))
      = (10 / (3 * Real.pi)) * (M * (av * c0 ^ 3)) := by
    field_simp; try ring
  have h3 : C * (av * c0 ^ 3 * ((M / s ^ 3) * s ^ 3)) = C * (M * (av * c0 ^ 3)) := by
    field_simp; try ring
  rw [hnorm, h3]
  exact mul_le_mul_of_nonneg_right hC (by positivity)

end BoseGases
end Submission
