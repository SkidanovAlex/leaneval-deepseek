import Mathlib
import Submission.Work.ADcl.asym_setup
import Submission.Work.ADcl.ode_H
import Submission.Work.CDcl.xco_ode_Pw_alt
import Submission.Work.CDcl.xco_pw_defs
import Submission.Commons.RingTheory.PowerSeries.subst_polynomial_ne_zero


namespace Work.ADcl

/-! Guidance (area ADcl of `cdt_linearIndependent`, Theorem A template).  This file should be in
`namespace Work.ADcl`.

`Work.ADcl.Hwfun a b c = algebraMap (PowerSeries ℚ) LF ((ZagierH a b c).subst sympPhi)` is the
pullback `H(x/(x-1))` of `H = a·H_A + b·H_B + c·H_C` (`Work.ADcl.Hfun`), viewed in
`LF = ℚ((x)) = Frac ℚ⟦x⟧`.  `H` satisfies Zagier's order-two inhomogeneous ODE
`aZ·H'' + bZ·H' + cZ·H = b + c/(1-x)` (`Submission.CDT.functionsH_ode`), put in normal form
`H'' = α H' + β H + γ` in `Work.ADcl.ode_H` (α = `alphaA`, β = `betaA`, γ = `gammaA b c`).
**Claim of this statement**: `Hw` satisfies the conjugate (`φ`-pullback) normal form
`Hw'' = α̃ Hw' + β̃ Hw + γ̃` (definitions `alphaAt = tK/sK - bPhiK*sK/aPhiK`,
`betaAt = -(cPhiK*sK^2/aPhiK)`, `gammaAt b c = sK^2*(b + c*(1-x))/aPhiK`, where
`sK = dRat phiK = φ'`, `tK = dRat sK = φ''`, `aPhiK/bPhiK/cPhiK` = the polynomials
`aZ/bZ/cZ` evaluated at `phiK`).
-/

noncomputable section

open Polynomial PowerSeries

/-! ## Auxiliary facts -/

/-- Substitution of the constant series `1`. -/
lemma subst_one_sympPhi : (1 : PowerSeries ℚ).subst Submission.CDT.sympPhi = 1 := by
  rw [← PowerSeries.coe_substAlgHom Submission.CDT.sympPhi_hasSubst]
  exact map_one (PowerSeries.substAlgHom Submission.CDT.sympPhi_hasSubst)

/-- `sig` of a constant power series. -/
lemma sig_C (r : ℚ) :
    Work.CDcl.sig (PowerSeries.C r) = Work.CDcl.toL (r : RatFunc ℚ) := by
  rw [Work.CDcl.sig_apply, PowerSeries.subst_C]
  exact algMap_C_rat r

/-- `sig (1 - X) = 1 - φ`. -/
lemma sig_one_sub_X :
    Work.CDcl.sig ((1 : PowerSeries ℚ) - PowerSeries.X) = 1 - Work.CDcl.toL Work.CDcl.phiK := by
  rw [Work.CDcl.sig_apply, PowerSeries.subst_sub Submission.CDT.sympPhi_hasSubst, subst_one_sympPhi,
    PowerSeries.subst_X Submission.CDT.sympPhi_hasSubst, map_sub, map_one, ← Work.CDcl.toL_phiK]

/-- `(1 - φ)·(1 - x) = 1` in `ℚ(x)`. -/
lemma one_sub_phiK_mul : ((1 : RatFunc ℚ) - Work.CDcl.phiK) * (1 - Work.CDcl.xK) = 1 := by
  have hx1 : (Work.CDcl.xK - 1 : RatFunc ℚ) ≠ 0 := Work.CDcl.xK_sub_one_ne_zero
  rw [Work.CDcl.phiK, div_eq_mul_inv]
  field_simp
  ring

/-- `(1 - φ)⁻¹ = 1 - x`. -/
lemma inv_one_sub_phiK : ((1 : RatFunc ℚ) - Work.CDcl.phiK)⁻¹ = 1 - Work.CDcl.xK :=
  inv_eq_of_mul_eq_one_left (by rw [mul_comm]; exact one_sub_phiK_mul)

/-- `sig ((1-X)⁻¹) = 1 - x`. -/
lemma sig_inv_one_sub_X :
    Work.CDcl.sig (((1 : PowerSeries ℚ) - PowerSeries.X)⁻¹) = Work.CDcl.toL (1 - Work.CDcl.xK) := by
  have hmul : Work.CDcl.sig (((1 : PowerSeries ℚ) - PowerSeries.X)⁻¹)
      * (1 - Work.CDcl.toL Work.CDcl.phiK) = 1 := by
    rw [← sig_one_sub_X, ← map_mul]
    rw [PowerSeries.inv_mul_cancel _ PS_one_sub_X_ne_zero, map_one]
  have h2 : Work.CDcl.sig (((1 : PowerSeries ℚ) - PowerSeries.X)⁻¹)
      = (1 - Work.CDcl.toL Work.CDcl.phiK)⁻¹ := eq_inv_of_mul_eq_one_left hmul
  have h3 : ((1 : Work.CDcl.LF) - Work.CDcl.toL Work.CDcl.phiK)
      = Work.CDcl.toL ((1 : RatFunc ℚ) - Work.CDcl.phiK) := by
    rw [Work.CDcl.toL_sub, Work.CDcl.toL_one]
  rw [h2, h3, ← Work.CDcl.toL_inv, inv_one_sub_phiK]

/-- The right hand side of the `H`-ODE, one side of the pullback equation. -/
lemma sig_ode_rhs (b c : ℚ) :
    Work.CDcl.sig (PowerSeries.C b + PowerSeries.C c * ((1 : PowerSeries ℚ) - PowerSeries.X)⁻¹)
      = Work.CDcl.toL ((b : RatFunc ℚ) + (c : RatFunc ℚ) * (1 - Work.CDcl.xK)) := by
  rw [map_add, map_mul, sig_C b, sig_C c, sig_inv_one_sub_X, ← Work.CDcl.toL_mul,
    ← Work.CDcl.toL_add]

/-- The constant coefficient of `sympPhi` vanishes. -/
lemma sympPhi_constantCoeff_zero : PowerSeries.constantCoeff Submission.CDT.sympPhi = 0 := by
  rw [show Submission.CDT.sympPhi
      = (PowerSeries.X : PowerSeries ℚ) * ((PowerSeries.X : PowerSeries ℚ) - 1)⁻¹ from rfl,
    map_mul]
  rw [show PowerSeries.constantCoeff (PowerSeries.X : PowerSeries ℚ) = 0 from by
    rw [show (PowerSeries.X : PowerSeries ℚ) = MvPowerSeries.X () from rfl]
    exact MvPowerSeries.constantCoeff_X ()]
  rw [zero_mul]

/-- `toL aPhiK ≠ 0`. -/
lemma toL_aPhiK_ne_zero : Work.CDcl.toL aPhiK ≠ 0 := by
  have h0 : PowerSeries.constantCoeff Submission.CDT.sympPhi = 0 := sympPhi_constantCoeff_zero
  intro h
  have hs : Work.CDcl.sig ((aZ : Polynomial ℚ) : PowerSeries ℚ) = 0 := by
    rw [Work.CDcl.sig_poly aZ]
    rw [show (Polynomial.eval₂ (algebraMap ℚ Work.CDcl.K) Work.CDcl.phiK aZ : RatFunc ℚ) = aPhiK
        from rfl]
    exact h
  have h2 : ((aZ : Polynomial ℚ) : PowerSeries ℚ).subst Submission.CDT.sympPhi = 0 := by
    apply IsFractionRing.injective (PowerSeries ℚ) Work.CDcl.LF
    rw [map_zero]
    exact (Work.CDcl.sig_apply ((aZ : Polynomial ℚ) : PowerSeries ℚ)).symm.trans hs
  exact (Commons.RingTheory.PowerSeries.subst_polynomial_ne_zero Work.CDcl.sympPhi_ne_zero h0
    aZ_ne_zero) h2


/-! ## The conjugate ODE -/

theorem ode_Hw (a b c : ℚ) :
    Work.CDcl.dL (Work.CDcl.dL (Work.ADcl.Hwfun a b c))
      = Work.CDcl.toL Work.ADcl.alphaAt * Work.CDcl.dL (Work.ADcl.Hwfun a b c)
        + Work.CDcl.toL Work.ADcl.betaAt * Work.ADcl.Hwfun a b c
        + Work.CDcl.toL (Work.ADcl.gammaAt b c) := by
  set H : PowerSeries ℚ := Submission.CDT.ZagierH a b c with hH
  -- the `x`-side ODE, in `ℚ⟦x⟧`
  have hODE : ((aZ : Polynomial ℚ) : PowerSeries ℚ)
        * (PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) H))
      + ((bZ : Polynomial ℚ) : PowerSeries ℚ) * (PowerSeries.derivative (R := ℚ) H)
      + ((cZ : Polynomial ℚ) : PowerSeries ℚ) * H
      = PowerSeries.C b + PowerSeries.C c * ((1 : PowerSeries ℚ) - PowerSeries.X)⁻¹ := by
    have h := Submission.CDT.functionsH_ode a b c
    rw [HA_odeLHS_eq] at h
    rw [hH]
    exact h
  -- apply `sig`
  have hσ : Work.CDcl.toL aPhiK * Work.CDcl.sig (PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) H))
        + Work.CDcl.toL bPhiK * Work.CDcl.sig (PowerSeries.derivative (R := ℚ) H)
        + Work.CDcl.toL cPhiK * Work.CDcl.sig H
      = Work.CDcl.toL ((b : RatFunc ℚ) + (c : RatFunc ℚ) * (1 - Work.CDcl.xK)) := by
    have h := congrArg Work.CDcl.sig hODE
    simp only [map_add, map_mul] at h
    rw [Work.CDcl.sig_poly aZ, Work.CDcl.sig_poly bZ, Work.CDcl.sig_poly cZ] at h
    rw [sig_C b, sig_C c, sig_inv_one_sub_X, ← Work.CDcl.toL_mul, ← Work.CDcl.toL_add] at h
    simpa only [aPhiK, bPhiK, cPhiK] using h
  -- the chain rules
  have hsP : Work.CDcl.sig H = Hwfun a b c := by
    rw [Hwfun]
    exact Work.CDcl.sig_apply (Submission.CDT.ZagierH a b c)
  have hu : Work.CDcl.dL (Hwfun a b c)
      = Work.CDcl.sig (PowerSeries.derivative (R := ℚ) H) * Work.CDcl.PsiL := by
    rw [← hsP]
    exact Work.CDcl.dL_sig H
  have hv : Work.CDcl.dL (Work.CDcl.dL (Hwfun a b c))
      = Work.CDcl.sig (PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) H)) * Work.CDcl.PsiL ^ 2
        + Work.CDcl.sig (PowerSeries.derivative (R := ℚ) H) * Work.CDcl.dL Work.CDcl.PsiL := by
    rw [← hsP]
    exact Work.CDcl.dL_dL_sig H
  have hP : Work.CDcl.PsiL ≠ 0 := Work.CDcl.PsiL_ne_zero
  have hA : Work.CDcl.toL aPhiK ≠ 0 := toL_aPhiK_ne_zero
  have hS1 : Work.CDcl.sig (PowerSeries.derivative (R := ℚ) H)
      = Work.CDcl.dL (Hwfun a b c) / Work.CDcl.PsiL := by
    rw [eq_div_iff hP]
    exact hu.symm
  have hS2 : Work.CDcl.sig (PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) H))
      = (Work.CDcl.dL (Work.CDcl.dL (Hwfun a b c))
          - (Work.CDcl.dL (Hwfun a b c) / Work.CDcl.PsiL) * Work.CDcl.dL Work.CDcl.PsiL)
        / Work.CDcl.PsiL ^ 2 := by
    rw [eq_div_iff (pow_ne_zero 2 hP)]
    rw [hv, hS1]
    ring
  -- the intermediate form of the pulled-back ODE
  have hmain : Work.CDcl.dL (Work.CDcl.dL (Hwfun a b c))
      = (Work.CDcl.dL Work.CDcl.PsiL / Work.CDcl.PsiL
            - Work.CDcl.PsiL * Work.CDcl.toL bPhiK / Work.CDcl.toL aPhiK)
          * Work.CDcl.dL (Hwfun a b c)
        - (Work.CDcl.PsiL ^ 2 * Work.CDcl.toL cPhiK / Work.CDcl.toL aPhiK * Hwfun a b c)
        + Work.CDcl.PsiL ^ 2
            * Work.CDcl.toL ((b : RatFunc ℚ) + (c : RatFunc ℚ) * (1 - Work.CDcl.xK))
            / Work.CDcl.toL aPhiK := by
    have h' : (Work.CDcl.dL (Work.CDcl.dL (Hwfun a b c))
          - (Work.CDcl.dL (Hwfun a b c) / Work.CDcl.PsiL) * Work.CDcl.dL Work.CDcl.PsiL)
        = Work.CDcl.PsiL ^ 2
          * (Work.CDcl.toL ((b : RatFunc ℚ) + (c : RatFunc ℚ) * (1 - Work.CDcl.xK))
              - Work.CDcl.toL bPhiK * (Work.CDcl.dL (Hwfun a b c) / Work.CDcl.PsiL)
              - Work.CDcl.toL cPhiK * Hwfun a b c)
          / Work.CDcl.toL aPhiK := by
      have h := hσ
      rw [hS1, hS2, hsP] at h
      rw [eq_div_iff hA]
      field_simp at h ⊢
      linear_combination h
    rw [sub_eq_iff_eq_add] at h'
    rw [h']
    field_simp
    ring
  -- identify the coefficients
  have hc1 : Work.CDcl.dL Work.CDcl.PsiL / Work.CDcl.PsiL
        - Work.CDcl.PsiL * Work.CDcl.toL bPhiK / Work.CDcl.toL aPhiK = Work.CDcl.toL alphaAt := by
    have hrat : Submission.CDT.dRat (Submission.CDT.dRat Work.CDcl.phiK)
          / Submission.CDT.dRat Work.CDcl.phiK
        - Submission.CDT.dRat Work.CDcl.phiK * bPhiK / aPhiK = alphaAt := by
      rw [alphaAt, tK, sK]
      ring
    have hL : Work.CDcl.dL Work.CDcl.PsiL / Work.CDcl.PsiL
          - Work.CDcl.PsiL * Work.CDcl.toL bPhiK / Work.CDcl.toL aPhiK
        = Work.CDcl.toL (Submission.CDT.dRat (Submission.CDT.dRat Work.CDcl.phiK)
            / Submission.CDT.dRat Work.CDcl.phiK
            - Submission.CDT.dRat Work.CDcl.phiK * bPhiK / aPhiK) := by
      rw [Work.CDcl.dL_PsiL_eq, Work.CDcl.PsiL_eq, ← Work.CDcl.toL_div, ← Work.CDcl.toL_mul,
        ← Work.CDcl.toL_div, ← Work.CDcl.toL_sub]
    rw [hL, hrat]
  have hc2 : Work.CDcl.PsiL ^ 2 * Work.CDcl.toL cPhiK / Work.CDcl.toL aPhiK
      = -Work.CDcl.toL betaAt := by
    have hb : cPhiK * sK ^ 2 / aPhiK = -betaAt := by
      rw [betaAt]
      ring
    rw [Work.CDcl.PsiL_eq, ← Work.CDcl.toL_neg, ← hb, ← Work.CDcl.toL_pow, ← Work.CDcl.toL_mul,
      ← Work.CDcl.toL_div]
    congr 1
    rw [sK]
    ring
  have hc3 : Work.CDcl.PsiL ^ 2
        * Work.CDcl.toL ((b : RatFunc ℚ) + (c : RatFunc ℚ) * (1 - Work.CDcl.xK))
        / Work.CDcl.toL aPhiK = Work.CDcl.toL (gammaAt b c) := by
    rw [Work.CDcl.PsiL_eq, gammaAt, ← Work.CDcl.toL_pow, ← Work.CDcl.toL_mul, ← Work.CDcl.toL_div]
    rfl
  rw [hmain, hc1, hc3, hc2]
  ring

end

end Work.ADcl
