import Mathlib
import Submission.Work.ADcl.asym_setup

/-! scratch: the ODE for `H` in `ℚ((x))` -/

open Polynomial PowerSeries

namespace Work.ADcl

noncomputable section

lemma coe_aZ : ((aZ : Polynomial ℚ) : PowerSeries ℚ) =
    PowerSeries.X - PowerSeries.C 10 * PowerSeries.X ^ 2 + PowerSeries.C 9 * PowerSeries.X ^ 3 := by
  simp only [aZ, Polynomial.coe_add, Polynomial.coe_sub, Polynomial.coe_mul, Polynomial.coe_pow,
    Polynomial.coe_C, Polynomial.coe_X]

lemma coe_bZ : ((bZ : Polynomial ℚ) : PowerSeries ℚ) =
    1 - PowerSeries.C 20 * PowerSeries.X + PowerSeries.C 27 * PowerSeries.X ^ 2 := by
  simp only [bZ, Polynomial.coe_add, Polynomial.coe_sub, Polynomial.coe_mul, Polynomial.coe_pow,
    Polynomial.coe_C, Polynomial.coe_X, Polynomial.coe_one]

lemma coe_cZ : ((cZ : Polynomial ℚ) : PowerSeries ℚ) =
    -PowerSeries.C 3 + PowerSeries.C 9 * PowerSeries.X := by
  simp only [cZ, Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_X,
    Polynomial.coe_neg]

lemma HA_odeLHS_eq (y : PowerSeries ℚ) :
    Submission.CDT.HA_odeLHS y =
      ((aZ : Polynomial ℚ) : PowerSeries ℚ) * (PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) y)
      + ((bZ : Polynomial ℚ) : PowerSeries ℚ) * (PowerSeries.derivative (R := ℚ)) y
      + ((cZ : Polynomial ℚ) : PowerSeries ℚ) * y := by
  simp only [Submission.CDT.HA_odeLHS, coe_aZ, coe_bZ, coe_cZ]

lemma algMap_HA_odeLHS (y : PowerSeries ℚ) :
    algebraMap (PowerSeries ℚ) Work.CDcl.LF (Submission.CDT.HA_odeLHS y)
      = Work.CDcl.toL aK * Work.CDcl.dL (Work.CDcl.dL (algebraMap (PowerSeries ℚ) Work.CDcl.LF y))
        + Work.CDcl.toL bK * Work.CDcl.dL (algebraMap (PowerSeries ℚ) Work.CDcl.LF y)
        + Work.CDcl.toL cK * algebraMap (PowerSeries ℚ) Work.CDcl.LF y := by
  rw [HA_odeLHS_eq]
  simp only [map_add, map_mul]
  rw [Work.CDcl.dL_algebraMap, Work.CDcl.dL_algebraMap, ← Work.CDcl.toL_algebraMap aZ,
    ← Work.CDcl.toL_algebraMap bZ, ← Work.CDcl.toL_algebraMap cZ]
  rfl

lemma one_sub_xK_ne_zero : (1 - Work.CDcl.xK : RatFunc ℚ) ≠ 0 := by
  have hx1 : Work.CDcl.xK ≠ 1 := by
    intro h; exact Work.CDcl.xK_sub_one_ne_zero (by rw [h]; ring)
  intro h; exact hx1 (by linear_combination -h)

lemma PS_one_sub_X_ne_zero : PowerSeries.constantCoeff ((1 : PowerSeries ℚ) - PowerSeries.X) ≠ 0 := by
  simp

lemma algMap_X : algebraMap (PowerSeries ℚ) Work.CDcl.LF (PowerSeries.X : PowerSeries ℚ)
    = Work.CDcl.toL Work.CDcl.xK := by
  rw [show (PowerSeries.X : PowerSeries ℚ) = ((Polynomial.X : Polynomial ℚ) : PowerSeries ℚ) from
      Polynomial.coe_X.symm,
    ← Work.CDcl.toL_algebraMap Polynomial.X, RatFunc.algebraMap_X]
  rfl

lemma algMap_one_sub_X :
    algebraMap (PowerSeries ℚ) Work.CDcl.LF ((1 : PowerSeries ℚ) - PowerSeries.X)
      = Work.CDcl.toL (1 - Work.CDcl.xK) := by
  rw [map_sub, map_one, algMap_X, Work.CDcl.toL_sub, Work.CDcl.toL_one]

lemma algMap_inv_one_sub_X :
    algebraMap (PowerSeries ℚ) Work.CDcl.LF (((1 : PowerSeries ℚ) - PowerSeries.X)⁻¹)
      = Work.CDcl.toL ((1 - Work.CDcl.xK)⁻¹) := by
  have hmul : algebraMap (PowerSeries ℚ) Work.CDcl.LF (((1 : PowerSeries ℚ) - PowerSeries.X)⁻¹)
      * algebraMap (PowerSeries ℚ) Work.CDcl.LF ((1 : PowerSeries ℚ) - PowerSeries.X) = 1 := by
    rw [← map_mul, PowerSeries.inv_mul_cancel _ PS_one_sub_X_ne_zero, map_one]
  rw [eq_inv_of_mul_eq_one_left hmul, algMap_one_sub_X, map_inv₀]

lemma algMap_C_rat (b : ℚ) :
    algebraMap (PowerSeries ℚ) Work.CDcl.LF (PowerSeries.C b) = Work.CDcl.toL (b : RatFunc ℚ) := by
  rw [Work.CDcl.toL_ratCast, ← map_ratCast (algebraMap ℚ Work.CDcl.LF) b]
  exact Work.CDcl.algebraMap_PS_C b

lemma algMap_rhs (b c : ℚ) :
    algebraMap (PowerSeries ℚ) Work.CDcl.LF
        (PowerSeries.C b + PowerSeries.C c * ((1 : PowerSeries ℚ) - PowerSeries.X)⁻¹)
      = Work.CDcl.toL (rK b c) := by
  rw [map_add, map_mul, algMap_C_rat b, algMap_C_rat c, algMap_inv_one_sub_X]
  rw [rK, Work.CDcl.toL_add, Work.CDcl.toL_div]
  rw [map_inv₀]
  ring

lemma aZ_ne_zero : aZ ≠ 0 := by
  intro h
  have h2 := congrArg (fun p : Polynomial ℚ => p.eval 2) h
  simp [aZ] at h2
  norm_num at h2

lemma aK_ne_zero : aK ≠ 0 := by
  intro h
  have h'' : ((aZ : RatFunc ℚ)) = 0 := h
  have h3 : (algebraMap (Polynomial ℚ) (RatFunc ℚ)) aZ
      = algebraMap (Polynomial ℚ) (RatFunc ℚ) 0 := by rw [map_zero]; exact h''
  exact aZ_ne_zero (IsFractionRing.injective (Polynomial ℚ) (RatFunc ℚ) h3)

lemma toL_aK_ne_zero : Work.CDcl.toL aK ≠ 0 := by
  have h : Work.CDcl.toL aK
      = algebraMap (PowerSeries ℚ) Work.CDcl.LF ((aZ : Polynomial ℚ) : PowerSeries ℚ) := by
    rw [show aK = (aZ : RatFunc ℚ) from rfl, RatFunc.coePolynomial, Work.CDcl.toL_algebraMap]
  rw [h]
  intro hh
  have hh' : (algebraMap (PowerSeries ℚ) Work.CDcl.LF) ((aZ : Polynomial ℚ) : PowerSeries ℚ)
      = algebraMap (PowerSeries ℚ) Work.CDcl.LF 0 := by rw [hh, map_zero]
  exact aZ_ne_zero (Polynomial.coe_injective ℚ
    (IsFractionRing.injective (PowerSeries ℚ) Work.CDcl.LF hh'))

theorem ode_H (a b c : ℚ) :
    Work.CDcl.dL (Work.CDcl.dL (Hfun a b c))
      = Work.CDcl.toL alphaA * Work.CDcl.dL (Hfun a b c)
        + Work.CDcl.toL betaA * Hfun a b c + Work.CDcl.toL (gammaA b c) := by
  have h := congrArg (algebraMap (PowerSeries ℚ) Work.CDcl.LF)
    (Submission.CDT.functionsH_ode a b c)
  rw [algMap_HA_odeLHS, algMap_rhs] at h
  have h' : Work.CDcl.toL aK * Work.CDcl.dL (Work.CDcl.dL (Hfun a b c))
      + Work.CDcl.toL bK * Work.CDcl.dL (Hfun a b c)
      + Work.CDcl.toL cK * Hfun a b c = Work.CDcl.toL (rK b c) := h
  have h2 : Work.CDcl.toL aK * Work.CDcl.dL (Work.CDcl.dL (Hfun a b c))
      = Work.CDcl.toL (rK b c) - Work.CDcl.toL bK * Work.CDcl.dL (Hfun a b c)
        - Work.CDcl.toL cK * Hfun a b c := by
    rw [← h']
    ring
  have hD : Work.CDcl.toL aK ≠ 0 := toL_aK_ne_zero
  have h3 : Work.CDcl.dL (Work.CDcl.dL (Hfun a b c))
      = (Work.CDcl.toL (rK b c) - Work.CDcl.toL bK * Work.CDcl.dL (Hfun a b c)
          - Work.CDcl.toL cK * Hfun a b c) / Work.CDcl.toL aK := by
    rw [eq_div_iff hD, mul_comm]
    exact h2
  rw [h3]
  rw [alphaA, betaA, gammaA]
  simp only [map_div₀, map_neg]
  field_simp
  ring

end

end Work.ADcl
