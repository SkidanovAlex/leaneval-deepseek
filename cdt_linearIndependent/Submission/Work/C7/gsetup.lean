import Mathlib
import Submission.Work.C7.xdefs
import Submission.Work.Pure.b4_theta_defs
import Submission.Commons.RingTheory.PowerSeries.coeff_mul_eq_sum_range

/-!
# Area C7 — the `x`-side setup for the pullback identities of `B₂`, `B₃`, `B₄`

This module collects the elementary facts about the symmetrization data in the variable `x`
(`u = (x−1)⁻¹ = gU`, `y = x²/(x−1) = Work.C7.yps`, `w = x − φ = Work.C7.cfun`,
`L = log(1−x) = Work.C7.Lps`, `Li₂ = Work.C7.Li2ps`) that are needed to prove the three
pullback identities of `Work.C7.g_form`:

```
g 1 = 2*yps - cfun*Lps,   g 2 = -(1/2)*Lps^2,   g 3 = (X - φ)*(2*Li2ps + (1/2)*Lps^2).
```

All statements are about `PowerSeries ℚ`; `φ = Submission.CDT.sympPhi = x/(x−1)` is the
involutive Möbius map and `Work.C7.yps = Submission.CDT.sympY`.
-/

namespace Work.C7

open PowerSeries

noncomputable section

/-- `u = (x−1)⁻¹`, the unit of `ℚ⟦x⟧` in which the symmetrization is written. -/
abbrev gU : PowerSeries ℚ := ((PowerSeries.X : PowerSeries ℚ) - 1)⁻¹

/-! ## The unit `u` -/

lemma gU_mul : gU * ((PowerSeries.X : PowerSeries ℚ) - 1) = 1 :=
  PowerSeries.inv_mul_cancel _ (by simp)

lemma mul_gU : ((PowerSeries.X : PowerSeries ℚ) - 1) * gU = 1 :=
  PowerSeries.mul_inv_cancel _ (by simp)

lemma gU_ne_zero : gU ≠ 0 := by
  intro h
  have hh := gU_mul
  rw [h, zero_mul] at hh
  exact one_ne_zero hh.symm

lemma sub_one_ne_zero : ((PowerSeries.X : PowerSeries ℚ) - 1) ≠ 0 := Work.Pure.sub_one_ne_zero

lemma X_ne_zero : (PowerSeries.X : PowerSeries ℚ) ≠ 0 := by
  intro h
  have h0 := congrArg (fun f => PowerSeries.coeff 1 f) h
  rw [PowerSeries.coeff_one_X] at h0
  simp at h0

lemma X_sub_two_ne_zero : ((PowerSeries.X : PowerSeries ℚ) - 2) ≠ 0 := Work.Pure.X_sub_two_ne_zero

lemma coeff_zero_gU : PowerSeries.coeff 0 gU = -1 := by
  have h := Submission.CDT.coeff_inv_X_sub_one 0
  simpa [gU] using h

/-! ## Small coefficient helpers -/

lemma coeff_one_X_mul (φ : PowerSeries ℚ) :
    PowerSeries.coeff 1 (PowerSeries.X * φ) = PowerSeries.coeff 0 φ := by
  simpa using PowerSeries.coeff_succ_X_mul (R := ℚ) 0 φ

lemma coeff_two_mul (d : ℕ) (φ : PowerSeries ℚ) :
    PowerSeries.coeff d (2 * φ) = 2 * PowerSeries.coeff d φ := by
  rw [show (2 : PowerSeries ℚ) = PowerSeries.C 2 from rfl, PowerSeries.coeff_C_mul]

lemma coeff_zero_sub (f g : PowerSeries ℚ) :
    PowerSeries.coeff 0 (f - g) = PowerSeries.coeff 0 f - PowerSeries.coeff 0 g := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_sub,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply]

lemma coeff_zero_add (f g : PowerSeries ℚ) :
    PowerSeries.coeff 0 (f + g) = PowerSeries.coeff 0 f + PowerSeries.coeff 0 g := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_add,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply]

lemma coeff_one_sub (f g : PowerSeries ℚ) :
    PowerSeries.coeff 1 (f - g) = PowerSeries.coeff 1 f - PowerSeries.coeff 1 g :=
  map_sub _ f g

/-! ## The basic series -/

lemma Lps_eq : Lps = Work.Pure.b4L := by
  ext n
  rw [Lps, Work.Pure.b4L, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  simp only [one_div]

lemma Li2ps_eq : Li2ps = Work.Pure.b4Li2 := by
  ext n
  rw [Li2ps, Work.Pure.b4Li2, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  simp only [one_div]

lemma sympW_eq_X_sub_phi :
    Submission.CDT.sympW = (PowerSeries.X : PowerSeries ℚ) - Submission.CDT.sympPhi := rfl

lemma cfun_eq_sympW : cfun = Submission.CDT.sympW := by
  have h1 : cfun * ((PowerSeries.X : PowerSeries ℚ) - 1)
      = (PowerSeries.X : PowerSeries ℚ) * ((PowerSeries.X : PowerSeries ℚ) - 2) := by
    rw [cfun, show (PowerSeries.X : PowerSeries ℚ) * ((PowerSeries.X : PowerSeries ℚ) - 2)
        * ((PowerSeries.X : PowerSeries ℚ) - 1)⁻¹ * ((PowerSeries.X : PowerSeries ℚ) - 1)
        = (PowerSeries.X : PowerSeries ℚ) * ((PowerSeries.X : PowerSeries ℚ) - 2)
          * (gU * ((PowerSeries.X : PowerSeries ℚ) - 1)) by ring]
    rw [gU_mul, mul_one]
  have h2 : Submission.CDT.sympW * ((PowerSeries.X : PowerSeries ℚ) - 1)
      = (PowerSeries.X : PowerSeries ℚ) * ((PowerSeries.X : PowerSeries ℚ) - 2) := by
    rw [sympW_eq_X_sub_phi, Submission.CDT.sympPhi]
    rw [sub_mul, mul_assoc, gU_mul, mul_one]
    ring
  have h3 : (cfun - Submission.CDT.sympW) * ((PowerSeries.X : PowerSeries ℚ) - 1) = 0 := by
    rw [sub_mul, h1, h2, sub_self]
  have h4 : cfun - Submission.CDT.sympW = 0 :=
    (mul_eq_zero.mp h3).resolve_right sub_one_ne_zero
  exact sub_eq_zero.mp h4

lemma cfun_eq : cfun = (PowerSeries.X : PowerSeries ℚ) * ((PowerSeries.X : PowerSeries ℚ) - 2) * gU := rfl

lemma cfun_ne_zero : cfun ≠ 0 := by
  rw [cfun_eq_sympW]
  exact Work.Pure.sympW_ne_zero

lemma yps_eq_sympY : yps = Submission.CDT.sympY := rfl

/-! ## Derivatives -/

lemma deriv_two : (PowerSeries.derivative (R := ℚ)) (2 : PowerSeries ℚ) = 0 := by
  rw [show (2 : PowerSeries ℚ) = PowerSeries.C 2 from rfl, PowerSeries.derivative_C]

lemma derivative_gU : (PowerSeries.derivative (R := ℚ)) gU = -(gU ^ 2) := Work.Pure.derivative_b4Unit

/-- `L' = u`. -/
lemma deriv_Lps_gU : PowerSeries.derivative (R := ℚ) Lps = gU := by
  have h : ((PowerSeries.X : PowerSeries ℚ) - 1) * PowerSeries.derivative (R := ℚ) Lps = 1 := by
    rw [show ((PowerSeries.X : PowerSeries ℚ) - 1) = -((1 : PowerSeries ℚ) - PowerSeries.X) by ring,
      neg_mul, deriv_Lps]
    ring
  calc PowerSeries.derivative (R := ℚ) Lps
      = gU * (((PowerSeries.X : PowerSeries ℚ) - 1) * PowerSeries.derivative (R := ℚ) Lps) := by
        rw [← mul_assoc, gU_mul, one_mul]
    _ = gU := by rw [h, mul_one]

/-- `(X-2)·u = 1 - u`. -/
lemma two_sub_X_mul_gU : ((PowerSeries.X : PowerSeries ℚ) - 2) * gU = 1 - gU := by
  have h : (((PowerSeries.X : PowerSeries ℚ) - 2) * gU - (1 - gU))
      * ((PowerSeries.X : PowerSeries ℚ) - 1) = 0 := by
    linear_combination ((PowerSeries.X : PowerSeries ℚ) - 1) * gU_mul
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right sub_one_ne_zero)

/-- `w' = (2x-2)u - w·u`. -/
lemma deriv_cfun : PowerSeries.derivative (R := ℚ) cfun = (2 * PowerSeries.X - 2) * gU - cfun * gU := by
  have hA : PowerSeries.derivative (R := ℚ)
      ((PowerSeries.X : PowerSeries ℚ) * ((PowerSeries.X : PowerSeries ℚ) - 2))
      = 2 * PowerSeries.X - 2 := by
    rw [Derivation.leibniz, map_sub, PowerSeries.derivative_X, deriv_two, sub_zero,
      smul_eq_mul, mul_one]
    ring
  rw [cfun_eq, Work.Pure.b4_deriv_mul, hA, derivative_gU]
  ring

lemma yps_eq : yps = (PowerSeries.X : PowerSeries ℚ) ^ 2 * gU := by
  rw [yps_eq_sympY, Work.Pure.sympY_eq_Xsq, Work.Pure.b4Unit]

/-- `y' = w·u`. -/
lemma deriv_yps : PowerSeries.derivative (R := ℚ) yps = cfun * gU := by
  have h := Work.Pure.derivative_sympY
  rw [← cfun_eq_sympW] at h
  rw [← yps_eq_sympY] at h
  simpa [gU, Work.Pure.b4Unit] using h

lemma yps_mul_four_sub : yps * (4 - yps) = -(cfun ^ 2) := by
  rw [yps_eq_sympY, cfun_eq_sympW]
  exact Work.Pure.sympY_mul_four_sub

lemma two_X_eq : 2 * (PowerSeries.X : PowerSeries ℚ) = cfun + yps := by
  rw [cfun_eq_sympW, sympW_eq_X_sub_phi, yps_eq_sympY, ← Submission.CDT.symp_x_add_phi]
  ring

lemma four_sub_yps : 4 - yps = -((PowerSeries.X : PowerSeries ℚ) - 2) ^ 2 * gU := by
  have h : (4 - yps) * ((PowerSeries.X : PowerSeries ℚ) - 1)
      = -((PowerSeries.X : PowerSeries ℚ) - 2) ^ 2 := by
    have h1 : (4 - yps) * ((PowerSeries.X : PowerSeries ℚ) - 1)
        = 4 * ((PowerSeries.X : PowerSeries ℚ) - 1) - (PowerSeries.X : PowerSeries ℚ) ^ 2 := by
      rw [sub_mul, yps_eq, mul_assoc, gU_mul, mul_one]
    rw [h1]
    ring
  have h2 : ((4 - yps) * ((PowerSeries.X : PowerSeries ℚ) - 1)) * gU
      = (-((PowerSeries.X : PowerSeries ℚ) - 2) ^ 2) * gU := by rw [h]
  rw [mul_assoc, mul_gU, mul_one] at h2
  exact h2

/-- `x(2−x)·y' = y(4−y)`, the identity that converts the `y`-ODE into its `x`-form. -/
lemma X_mul_two_sub_mul_deriv_yps :
    (PowerSeries.X : PowerSeries ℚ) * (2 - PowerSeries.X) * PowerSeries.derivative (R := ℚ) yps
      = yps * (4 - yps) := by
  rw [deriv_yps, yps_mul_four_sub, cfun_eq]
  ring

/-! ## Low coefficients -/

lemma coeff_zero_cfun : PowerSeries.coeff 0 cfun = 0 := by
  have h : cfun = PowerSeries.X * (((PowerSeries.X : PowerSeries ℚ) - 2) * gU) := by
    rw [cfun_eq]; ring
  rw [h, PowerSeries.coeff_zero_X_mul]

lemma coeff_one_cfun : PowerSeries.coeff 1 cfun = 2 := by
  have h : cfun = PowerSeries.X * (((PowerSeries.X : PowerSeries ℚ) - 2) * gU) := by
    rw [cfun_eq]; ring
  rw [h, coeff_one_X_mul, two_sub_X_mul_gU,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, map_sub, map_one,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_zero_gU]
  norm_num

lemma coeff_zero_yps : PowerSeries.coeff 0 yps = 0 := by
  rw [yps_eq, PowerSeries.coeff_X_pow_mul']
  simp

lemma coeff_one_yps : PowerSeries.coeff 1 yps = 0 := by
  rw [yps_eq, PowerSeries.coeff_X_pow_mul']
  simp

lemma constantCoeff_yps : PowerSeries.constantCoeff yps = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact coeff_zero_yps

lemma constantCoeff_Lps : PowerSeries.constantCoeff Lps = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact coeff_zero_Lps

lemma constantCoeff_Li2ps : PowerSeries.constantCoeff Li2ps = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact coeff_zero_Li2ps

/-- The first two coefficients of `y^k * Z` vanish for `k ≥ 1`. -/
lemma coeff_zero_one_yps_pow_mul {k : ℕ} (hk : 1 ≤ k) (Z : PowerSeries ℚ) :
    PowerSeries.coeff 0 (yps ^ k * Z) = 0 ∧ PowerSeries.coeff 1 (yps ^ k * Z) = 0 := by
  have hpow0 : PowerSeries.coeff 0 (yps ^ k) = 0 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_zero_yps, zero_pow (by omega)]
  have hpow1 : PowerSeries.coeff 1 (yps ^ k) = 0 :=
    Submission.CDT.coeff_pow_lt_two coeff_zero_yps coeff_one_yps (by omega)
  constructor
  · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply, hpow0, zero_mul]
  · rw [Commons.RingTheory.PowerSeries.coeff_mul_eq_sum_range]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hi2 : i = 0 ∨ i = 1 := by
      have := Finset.mem_range.mp hi; omega
    rcases hi2 with rfl | rfl
    · rw [hpow0, zero_mul]
    · rw [hpow1, zero_mul]

/-- `X ^ k * mk (coeff (· + k) f) = f` when the first `k` coefficients of `f` vanish. -/
lemma X_pow_mul_tq {f : PowerSeries ℚ} {k : ℕ} (h : ∀ n < k, PowerSeries.coeff n f = 0) :
    (PowerSeries.X : PowerSeries ℚ) ^ k * PowerSeries.mk (fun n => PowerSeries.coeff (n + k) f) = f := by
  ext n
  rw [PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_mk]
  by_cases hk : k ≤ n
  · rw [if_pos hk, Nat.sub_add_cancel hk]
  · rw [if_neg hk]
    exact (h n (by omega)).symm

lemma subst_yps_hasSubst : PowerSeries.HasSubst yps := Submission.CDT.sympY_hasSubst

lemma coeff_zero_B2 : PowerSeries.coeff 0 Submission.CDTPlan.B2 = 0 := by
  rw [Submission.CDTPlan.B2, PowerSeries.coeff_mk]
  norm_num

lemma coeff_one_B2 : PowerSeries.coeff 1 Submission.CDTPlan.B2 = 0 := by
  rw [Submission.CDTPlan.B2, PowerSeries.coeff_mk]
  norm_num

lemma coeff_zero_B3 : PowerSeries.coeff 0 Submission.CDTPlan.B3 = 0 := by
  rw [Submission.CDTPlan.B3, PowerSeries.coeff_mk]
  norm_num

lemma coeff_zero_B4 : PowerSeries.coeff 0 Submission.CDTPlan.B4 = 0 := by
  rw [Submission.CDTPlan.B4, PowerSeries.coeff_mk]
  norm_num

lemma B2_eq : Submission.CDTPlan.B2
    = (PowerSeries.X : PowerSeries ℚ) ^ 2
      * PowerSeries.mk (fun n => PowerSeries.coeff (n + 2) Submission.CDTPlan.B2) :=
  (X_pow_mul_tq (f := Submission.CDTPlan.B2) (k := 2) (fun n hn => by
    have h : n = 0 ∨ n = 1 := by omega
    rcases h with rfl | rfl
    · exact coeff_zero_B2
    · exact coeff_one_B2)).symm

lemma B3_eq : Submission.CDTPlan.B3
    = (PowerSeries.X : PowerSeries ℚ) ^ 1
      * PowerSeries.mk (fun n => PowerSeries.coeff (n + 1) Submission.CDTPlan.B3) :=
  (X_pow_mul_tq (f := Submission.CDTPlan.B3) (k := 1) (fun n hn => by
    have h : n = 0 := by omega
    subst h
    exact coeff_zero_B3)).symm

lemma B4_eq : Submission.CDTPlan.B4
    = (PowerSeries.X : PowerSeries ℚ) ^ 1
      * PowerSeries.mk (fun n => PowerSeries.coeff (n + 1) Submission.CDTPlan.B4) :=
  (X_pow_mul_tq (f := Submission.CDTPlan.B4) (k := 1) (fun n hn => by
    have h : n = 0 := by omega
    subst h
    exact coeff_zero_B4)).symm

lemma coeff_zero_B2subst : PowerSeries.coeff 0 (Submission.CDTPlan.B2.subst yps) = 0 := by
  rw [B2_eq, PowerSeries.subst_mul subst_yps_hasSubst,
    PowerSeries.subst_pow subst_yps_hasSubst, PowerSeries.subst_X subst_yps_hasSubst]
  exact (coeff_zero_one_yps_pow_mul (k := 2) (by norm_num) _).1

lemma coeff_one_B2subst : PowerSeries.coeff 1 (Submission.CDTPlan.B2.subst yps) = 0 := by
  rw [B2_eq, PowerSeries.subst_mul subst_yps_hasSubst,
    PowerSeries.subst_pow subst_yps_hasSubst, PowerSeries.subst_X subst_yps_hasSubst]
  exact (coeff_zero_one_yps_pow_mul (k := 2) (by norm_num) _).2

lemma coeff_zero_B3subst : PowerSeries.coeff 0 (Submission.CDTPlan.B3.subst yps) = 0 := by
  rw [B3_eq, PowerSeries.subst_mul subst_yps_hasSubst, PowerSeries.subst_pow subst_yps_hasSubst,
    PowerSeries.subst_X subst_yps_hasSubst]
  exact (coeff_zero_one_yps_pow_mul (k := 1) (by norm_num) _).1

lemma coeff_zero_B4subst : PowerSeries.coeff 0 (Submission.CDTPlan.B4.subst yps) = 0 := by
  rw [B4_eq, PowerSeries.subst_mul subst_yps_hasSubst, PowerSeries.subst_pow subst_yps_hasSubst,
    PowerSeries.subst_X subst_yps_hasSubst]
  exact (coeff_zero_one_yps_pow_mul (k := 1) (by norm_num) _).1

lemma coeff_one_B4subst : PowerSeries.coeff 1 (Submission.CDTPlan.B4.subst yps) = 0 := by
  rw [B4_eq, PowerSeries.subst_mul subst_yps_hasSubst, PowerSeries.subst_pow subst_yps_hasSubst,
    PowerSeries.subst_X subst_yps_hasSubst]
  exact (coeff_zero_one_yps_pow_mul (k := 1) (by norm_num) _).2

/-! ## Low coefficients of the `x`-side right-hand sides -/

lemma coeff_zero_R1 : PowerSeries.coeff 0 (2 * yps - cfun * Lps) = 0 := by
  have h1 : PowerSeries.coeff 0 (2 * yps) = 0 := by rw [coeff_two_mul, coeff_zero_yps, mul_zero]
  have hc : cfun * Lps = PowerSeries.X * (((PowerSeries.X : PowerSeries ℚ) - 2) * gU * Lps) := by
    rw [cfun_eq]; ring
  have h2 : PowerSeries.coeff 0 (cfun * Lps) = 0 := by
    rw [hc, PowerSeries.coeff_zero_X_mul]
  rw [coeff_zero_sub, h1, h2, sub_zero]

lemma coeff_one_R1 : PowerSeries.coeff 1 (2 * yps - cfun * Lps) = 0 := by
  have h1 : PowerSeries.coeff 1 (2 * yps) = 0 := by rw [coeff_two_mul, coeff_one_yps, mul_zero]
  have hc : cfun * Lps = PowerSeries.X * (((PowerSeries.X : PowerSeries ℚ) - 2) * gU * Lps) := by
    rw [cfun_eq]; ring
  have h2 : PowerSeries.coeff 1 (cfun * Lps) = 0 := by
    rw [hc, coeff_one_X_mul, Commons.RingTheory.PowerSeries.coeff_mul_eq_sum_range,
      Finset.sum_range_one]
    simp only [Nat.sub_zero, coeff_zero_Lps, mul_zero]
  rw [coeff_one_sub, h1, h2, sub_zero]

lemma coeff_zero_Lsq : PowerSeries.coeff 0 ((Lps : PowerSeries ℚ) ^ 2) = 0 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_zero_Lps]
  ring

lemma coeff_zero_R2 : PowerSeries.coeff 0 (-(PowerSeries.C (1 / 2 : ℚ)) * Lps ^ 2) = 0 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, map_neg, PowerSeries.constantCoeff_C,
    map_pow, constantCoeff_Lps]
  ring

lemma coeff_one_R2 : PowerSeries.coeff 1 (-(PowerSeries.C (1 / 2 : ℚ)) * Lps ^ 2) = 0 := by
  have hC : -(PowerSeries.C (1 / 2 : ℚ)) = PowerSeries.C (-(1 / 2) : ℚ) := by simp
  have h2 : PowerSeries.coeff 1 ((Lps : PowerSeries ℚ) * Lps) = 0 := by
    rw [Commons.RingTheory.PowerSeries.coeff_mul_eq_sum_range, Finset.sum_range_succ,
      Finset.sum_range_one]
    simp only [Nat.sub_zero, Nat.sub_self, coeff_zero_Lps, coeff_one_Lps, mul_zero, zero_mul,
      add_zero]
  rw [show (Lps : PowerSeries ℚ) ^ 2 = Lps * Lps by ring, hC, PowerSeries.coeff_C_mul, h2,
    mul_zero]

lemma coeff_zero_B_Li2 : PowerSeries.coeff 0 (2 * Li2ps + PowerSeries.C (1 / 2 : ℚ) * Lps ^ 2) = 0 := by
  rw [coeff_zero_add, coeff_two_mul, coeff_zero_Li2ps, PowerSeries.coeff_C_mul, coeff_zero_Lsq]
  ring

lemma coeff_zero_R3 :
    PowerSeries.coeff 0 ((PowerSeries.X - Submission.CDT.sympPhi)
      * (2 * Li2ps + PowerSeries.C (1 / 2 : ℚ) * Lps ^ 2)) = 0 := by
  have h : (PowerSeries.X : PowerSeries ℚ) - Submission.CDT.sympPhi = cfun := cfun_eq_sympW.symm
  rw [h, cfun_eq, show (PowerSeries.X : PowerSeries ℚ) * ((PowerSeries.X : PowerSeries ℚ) - 2) * gU
      * (2 * Li2ps + PowerSeries.C (1 / 2 : ℚ) * Lps ^ 2)
      = PowerSeries.X * (((PowerSeries.X : PowerSeries ℚ) - 2) * gU
          * (2 * Li2ps + PowerSeries.C (1 / 2 : ℚ) * Lps ^ 2)) by ring,
    PowerSeries.coeff_zero_X_mul]

lemma coeff_one_R3 :
    PowerSeries.coeff 1 ((PowerSeries.X - Submission.CDT.sympPhi)
      * (2 * Li2ps + PowerSeries.C (1 / 2 : ℚ) * Lps ^ 2)) = 0 := by
  have h : (PowerSeries.X : PowerSeries ℚ) - Submission.CDT.sympPhi = cfun := cfun_eq_sympW.symm
  rw [h, cfun_eq, show (PowerSeries.X : PowerSeries ℚ) * ((PowerSeries.X : PowerSeries ℚ) - 2) * gU
      * (2 * Li2ps + PowerSeries.C (1 / 2 : ℚ) * Lps ^ 2)
      = PowerSeries.X * (((PowerSeries.X : PowerSeries ℚ) - 2) * gU
          * (2 * Li2ps + PowerSeries.C (1 / 2 : ℚ) * Lps ^ 2)) by ring,
    coeff_one_X_mul, Commons.RingTheory.PowerSeries.coeff_mul_eq_sum_range]
  rw [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [Nat.sub_zero, zero_add, coeff_one_cfun, zero_mul, coeff_zero_B_Li2, mul_zero,
    add_zero]

lemma subst_Lps_sympPhi : Lps.subst Submission.CDT.sympPhi = -Lps := by
  rw [Lps_eq, ← Work.Pure.b4L_subst_sympPhi]

end

end Work.C7
