import Mathlib
import Submission.Work.CDcl.xrel_defs
import Submission.Work.CDcl.xco_ode_P
import Submission.Work.CDcl.xco_pw_defs
import Submission.Work.CDcl.xco_pw_coef

/-!
# `Work.CDcl.xco_ode_Pw`: the pulled-back ODE for `Pw = P∘φ`

Transporting `P₂P'' + P₁P' + P₀P = p` (the `x`-side ODE of `Submission.CDT.logP_ode`) along the
involution `φ = x/(x-1)` gives an order-two equation for `Pw = P∘φ` with coefficients
`α̃ = -Q₁/Q₂`, `β̃ = -Q₀/Q₂`, `γ̃ = (p∘φ)/Q₂` (`setup.lean`).
-/

noncomputable section

open Polynomial PowerSeries

namespace Work.CDcl

theorem PsiL_ne_zero : PsiL ≠ 0 := by
  rw [PsiL_eq]
  intro h
  have h1 : Submission.CDT.dRat phiK = 0 := toL_injective (by rw [h, map_zero])
  rw [dRat_phiK_val] at h1
  have h2 : (-1 : RatFunc ℚ) = 0 := by
    have hh := congrArg (fun z : RatFunc ℚ => z * (xK - 1) ^ 2) h1
    rw [div_mul_cancel₀] at hh
    · simpa using hh
    · exact pow_ne_zero 2 xK_sub_one_ne_zero
  norm_num at h2

theorem toL_p2phiK_ne_zero (a b : ℚ) : toL (p2phiK a b) ≠ 0 := by
  intro h
  exact p2phiK_ne_zero a b (toL_injective (by rw [h, map_zero]))

set_option maxHeartbeats 1600000 in
theorem xco_ode_Pw (a b : ℚ) (ra rb rab r0 : ℤ) :
    dL (dL (Pwfun a b ra rb rab r0))
      = alphaLt a b * dL (Pwfun a b ra rb rab r0)
        + betaLt a b * Pwfun a b ra rb rab r0 + gammaLt a b ra rb rab r0 := by
  set P : PowerSeries ℚ := Submission.CDT.logP a b ra rb rab r0 with hP
  -- the `x`-side ODE, in `ℚ⟦x⟧`
  have hODE : ((p2poly a b : Polynomial ℚ) : PowerSeries ℚ)
        * (PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) P))
      + ((p1poly a b : Polynomial ℚ) : PowerSeries ℚ) * (PowerSeries.derivative (R := ℚ) P)
      + ((p0poly a b : Polynomial ℚ) : PowerSeries ℚ) * P
      = ((ppoly a b ra rb rab r0 : Polynomial ℚ) : PowerSeries ℚ) := by
    have h := Submission.CDT.logP_ode a b ra rb rab r0
    simp only [Submission.CDT.logPAODE] at h
    rw [← coe_ppoly, ← coe_p2poly, ← coe_p1poly, ← coe_p0poly] at h
    rw [hP]
    exact h
  -- apply σ
  have hσ : toL (p2phiK a b)
        * sig ((PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) P))
      + toL (p1phiK a b) * sig ((PowerSeries.derivative (R := ℚ)) P)
      + toL (p0phiK a b) * sig P = toL (pphiK a b ra rb rab r0) := by
    have h := congrArg sig hODE
    rw [map_add, map_add, map_mul, map_mul, map_mul] at h
    rw [sig_poly (p2poly a b), sig_poly (p1poly a b), sig_poly (p0poly a b),
      sig_poly (ppoly a b ra rb rab r0)] at h
    simpa only [p2phiK, p1phiK, p0phiK, pphiK] using h
  -- the chain rules
  have hsP : sig P = Pwfun a b ra rb rab r0 := (Pwfun_eq_sig a b ra rb rab r0).symm
  have hd1 : dL (Pwfun a b ra rb rab r0) = sig ((PowerSeries.derivative (R := ℚ)) P) * PsiL := by
    rw [← hsP]
    exact dL_sig P
  have hd2 : dL (dL (Pwfun a b ra rb rab r0))
      = sig ((PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) P)) * PsiL ^ 2
        + sig ((PowerSeries.derivative (R := ℚ)) P) * dL PsiL := by
    rw [← hsP]
    exact dL_dL_sig P
  have hΨ0 : PsiL ≠ 0 := PsiL_ne_zero
  have hS1 : sig ((PowerSeries.derivative (R := ℚ)) P) = dL (Pwfun a b ra rb rab r0) / PsiL := by
    rw [hd1]
    field_simp
  have hS2 : sig ((PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) P))
      = (dL (dL (Pwfun a b ra rb rab r0))
          - (dL (Pwfun a b ra rb rab r0) / PsiL) * dL PsiL) / PsiL ^ 2 := by
    rw [hd2]
    field_simp
    rw [hd1]
    ring
  -- the intermediate form of the pulled-back ODE
  have hmain : dL (dL (Pwfun a b ra rb rab r0))
      = (dL PsiL / PsiL - PsiL * toL (p1phiK a b) / toL (p2phiK a b))
          * dL (Pwfun a b ra rb rab r0)
        - (PsiL ^ 2 * toL (p0phiK a b) / toL (p2phiK a b) * Pwfun a b ra rb rab r0)
        + PsiL ^ 2 * toL (pphiK a b ra rb rab r0) / toL (p2phiK a b) := by
    have hB : toL (p2phiK a b) ≠ 0 := toL_p2phiK_ne_zero a b
    have h' : (dL (dL (Pwfun a b ra rb rab r0))
          - (dL (Pwfun a b ra rb rab r0) / PsiL) * dL PsiL)
        = PsiL ^ 2 * (toL (pphiK a b ra rb rab r0)
            - toL (p1phiK a b) * (dL (Pwfun a b ra rb rab r0) / PsiL)
            - toL (p0phiK a b) * Pwfun a b ra rb rab r0) / toL (p2phiK a b) := by
      have h := hσ
      rw [hS1, hS2, hsP] at h
      rw [eq_div_iff hB]
      field_simp at h ⊢
      linear_combination h
    rw [sub_eq_iff_eq_add] at h'
    rw [h']
    field_simp
    ring
  -- identify the coefficients
  have hc1 : dL PsiL / PsiL - PsiL * toL (p1phiK a b) / toL (p2phiK a b) = alphaLt a b := by
    rw [dL_PsiL_eq, PsiL_eq]
    rw [show toL (Submission.CDT.dRat (Submission.CDT.dRat phiK))
            / toL (Submission.CDT.dRat phiK)
          - toL (Submission.CDT.dRat phiK) * toL (p1phiK a b) / toL (p2phiK a b)
        = toL (Submission.CDT.dRat (Submission.CDT.dRat phiK) / Submission.CDT.dRat phiK
            - Submission.CDT.dRat phiK * p1phiK a b / p2phiK a b) from by
      rw [toL_sub, toL_div, toL_div, toL_mul]]
    rw [coef_alphaKt a b]
    rfl
  have hc2 : PsiL ^ 2 * toL (p0phiK a b) / toL (p2phiK a b) = -betaLt a b := by
    have hcoef : -(PsiL ^ 2 * toL (p0phiK a b) / toL (p2phiK a b)) = betaLt a b := by
      rw [PsiL_eq]
      rw [show -(toL (Submission.CDT.dRat phiK) ^ 2 * toL (p0phiK a b) / toL (p2phiK a b))
          = toL (-((Submission.CDT.dRat phiK) ^ 2 * p0phiK a b / p2phiK a b)) from by
        rw [toL_neg, toL_div, toL_mul, toL_pow]]
      rw [coef_betaKt a b]
      rfl
    rw [← hcoef]
    ring
  have hc3 : PsiL ^ 2 * toL (pphiK a b ra rb rab r0) / toL (p2phiK a b)
      = gammaLt a b ra rb rab r0 := by
    rw [PsiL_eq]
    rw [show toL (Submission.CDT.dRat phiK) ^ 2 * toL (pphiK a b ra rb rab r0)
            / toL (p2phiK a b)
        = toL ((Submission.CDT.dRat phiK) ^ 2 * pphiK a b ra rb rab r0 / p2phiK a b) from by
      rw [toL_div, toL_mul, toL_pow]]
    rw [coef_gammaKt a b ra rb rab r0]
    rfl
  rw [hmain, hc1, hc3, hc2]
  ring

end Work.CDcl
