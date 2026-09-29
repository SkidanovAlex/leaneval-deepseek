import Mathlib
import Submission.Work.CDcl.xrel_defs
import Submission.Work.CDcl.xco_ode_P
import Submission.Commons.RingTheory.PowerSeries.subst_injective_of_constantCoeff_eq_zero


/-!
# `Work.CDcl.g_ode_Pw`: the pulled-back order-two ODE for `Pw = P ∘ φ`

Independent (second) proof of the order-two ODE satisfied by the pullback
`Pwfun = Φ(P ∘ φ)` of the unlikely `G`-function `P = logP a b ra rb rab r0` under the
involution `φ = X/(X-1)`, with the pulled-back coefficients `alphaKt, betaKt, gammaKt` of
`Submission.Work.CDcl.setup`.

Route: `Φ(q ∘ φ) = toL (q(φK))` for `q ∈ ℚ[x]` (`gPhi_subst`); the twisted derivative
`ψ·d/dX` with `ψ = -(X-1)² = 1/φ'` interchanges with the substitution
(`iterate_subst_deriv_scaled`-style chain rule, proved here as `gpsi_mul_deriv_eq`,
`gpsi_mul_deriv2_eq`), so substituting `φ` into the order-two ODE `P₂P'' + P₁P' + P₀P = p`
of `logP_ode` produces the pullback ODE in `ℚ((x))`.
-/

noncomputable section

open Polynomial PowerSeries

namespace Work.CDcl

local notation "Φ" => algebraMap (PowerSeries ℚ) LF

/-! ## 1. `Φ` on `φ` and on polynomials composed with `φ` -/

lemma gphiK_eq : phiK = xK * (xK - 1)⁻¹ := by
  rw [phiK, div_eq_mul_inv]

lemma gPhi_X : Φ (PowerSeries.X : PowerSeries ℚ) = toL xK := toL_X.symm

lemma gPhi_sub_one : Φ ((PowerSeries.X : PowerSeries ℚ) - 1) = toL (xK - 1) := by
  rw [map_sub, gPhi_X, map_one, ← toL_one, ← toL_sub]

lemma gxK_sub_one_ne_zero : xK - (1 : K) ≠ 0 := by
  intro h
  have h1 : algebraMap (Polynomial ℚ) K (Polynomial.X - Polynomial.C 1) = xK - 1 := by
    rw [Polynomial.C_1, map_sub, map_one, RatFunc.algebraMap_X]
    rfl
  exact Polynomial.X_sub_C_ne_zero 1
    (IsFractionRing.injective (Polynomial ℚ) K (by rw [h1, h, map_zero]))

lemma gtoL_sub_one_inv : toL (xK - 1) * toL ((xK - 1)⁻¹) = 1 := by
  rw [← toL_mul, mul_inv_cancel₀ gxK_sub_one_ne_zero, toL_one]

lemma gPhi_sympPhi : Φ Submission.CDT.sympPhi = toL phiK := by
  have h : Φ Submission.CDT.sympPhi * toL (xK - 1) = toL xK := by
    have h1 := congrArg (fun z : PowerSeries ℚ => Φ z) Submission.CDT.sympPhi_mul_sub_one
    simpa only [map_mul, gPhi_X, gPhi_sub_one] using h1
  calc Φ Submission.CDT.sympPhi
      = Φ Submission.CDT.sympPhi * 1 := by rw [mul_one]
    _ = Φ Submission.CDT.sympPhi * (toL (xK - 1) * toL ((xK - 1)⁻¹)) := by rw [gtoL_sub_one_inv]
    _ = (Φ Submission.CDT.sympPhi * toL (xK - 1)) * toL ((xK - 1)⁻¹) := by rw [mul_assoc]
    _ = toL xK * toL ((xK - 1)⁻¹) := by rw [h]
    _ = toL (xK * (xK - 1)⁻¹) := by rw [← toL_mul]
    _ = toL phiK := by rw [gphiK_eq]

lemma gPhi_C (c : ℚ) : Φ (MvPowerSeries.C c : PowerSeries ℚ) = toL (algebraMap ℚ K c) := by
  have h1 : Φ (MvPowerSeries.C c : PowerSeries ℚ)
      = Φ (((Polynomial.C c : Polynomial ℚ)) : PowerSeries ℚ) := by
    congr 1
    exact (Polynomial.coe_C c).symm
  rw [h1, ← toL_algebraMap (Polynomial.C c), Polynomial.C_eq_algebraMap c,
    ← IsScalarTower.algebraMap_apply ℚ (Polynomial ℚ) K c]

lemma gPhi_subst (q : Polynomial ℚ) :
    Φ ((q : PowerSeries ℚ).subst Submission.CDT.sympPhi) = toL (Polynomial.aeval phiK q) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [Polynomial.coe_add, map_add, PowerSeries.subst_add Submission.CDT.sympPhi_hasSubst,
        map_add, map_add, hp, hq]
  | monomial n a =>
      have hcoe : ((Polynomial.monomial n a : Polynomial ℚ) : PowerSeries ℚ)
          = PowerSeries.C a * (PowerSeries.X : PowerSeries ℚ) ^ n := by
        rw [← Polynomial.C_mul_X_pow_eq_monomial]
        push_cast
        ring
      rw [hcoe, PowerSeries.subst_mul Submission.CDT.sympPhi_hasSubst,
        PowerSeries.subst_C, PowerSeries.subst_pow Submission.CDT.sympPhi_hasSubst,
        PowerSeries.subst_X Submission.CDT.sympPhi_hasSubst,
        map_mul, map_pow, gPhi_C, gPhi_sympPhi, ← map_pow toL, ← toL_mul]
      congr 1
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      simp only [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]

/-! ## 2. The twisted derivative `ψ·d/dX` -/

/-- `ψ = -(X-1)² = 1/(d/dX φ)`. -/
def gpsi : PowerSeries ℚ := -((PowerSeries.X : PowerSeries ℚ) - 1) ^ 2

lemma g_deriv_sympPhi : PowerSeries.derivative (R := ℚ) Submission.CDT.sympPhi
    = -((((PowerSeries.X : PowerSeries ℚ) - 1)⁻¹)) ^ 2 := by
  let W : PowerSeries ℚ := ((PowerSeries.X : PowerSeries ℚ) - 1)⁻¹
  have hW : (PowerSeries.derivative (R := ℚ)) W = -(W ^ 2) := by
    dsimp [W]
    rw [PowerSeries.derivative_inv']
    simp
  have hXW : (PowerSeries.X : PowerSeries ℚ) * W = 1 + W := by
    have h2 : ((PowerSeries.X : PowerSeries ℚ) - 1) * W = 1 := by
      dsimp [W]
      exact PowerSeries.mul_inv_cancel _ Submission.CDT.symp_sub_one_constant_ne
    linear_combination h2
  have hdef : Submission.CDT.sympPhi = (PowerSeries.X : PowerSeries ℚ) * W := rfl
  calc (PowerSeries.derivative (R := ℚ)) Submission.CDT.sympPhi
      = (PowerSeries.derivative (R := ℚ)) ((PowerSeries.X : PowerSeries ℚ) * W) := by rw [hdef]
    _ = (PowerSeries.X : PowerSeries ℚ) * (PowerSeries.derivative (R := ℚ)) W + W := by
          rw [Derivation.leibniz]; simp
    _ = (PowerSeries.X : PowerSeries ℚ) * (-(W ^ 2)) + W := by rw [hW]
    _ = -(W ^ 2) := by
          have h : (PowerSeries.X : PowerSeries ℚ) * (-(W ^ 2)) + W
              = -((PowerSeries.X : PowerSeries ℚ) * W) * W + W := by ring
          rw [h, hXW]; ring
    _ = -((((PowerSeries.X : PowerSeries ℚ) - 1)⁻¹)) ^ 2 := by rfl

lemma gpsi_mul_deriv_sympPhi : gpsi * PowerSeries.derivative (R := ℚ) Submission.CDT.sympPhi = 1 := by
  rw [g_deriv_sympPhi]
  unfold gpsi
  rw [neg_mul_neg, ← mul_pow, PowerSeries.mul_inv_cancel _ Submission.CDT.symp_sub_one_constant_ne,
    one_pow]

/-- `ψ·(P∘φ)' = P'∘φ`. -/
lemma gpsi_mul_deriv_eq (a b : ℚ) (ra rb rab r0 : ℤ) :
    gpsi * PowerSeries.derivative (R := ℚ)
        ((Submission.CDT.logP a b ra rb rab r0).subst Submission.CDT.sympPhi)
      = (PowerSeries.derivative (R := ℚ) (Submission.CDT.logP a b ra rb rab r0)).subst
          Submission.CDT.sympPhi := by
  rw [PowerSeries.derivative_subst Submission.CDT.sympPhi_hasSubst]
  rw [show gpsi * (PowerSeries.subst Submission.CDT.sympPhi
        (PowerSeries.derivative (R := ℚ) (Submission.CDT.logP a b ra rb rab r0))
          * PowerSeries.derivative (R := ℚ) Submission.CDT.sympPhi)
      = (PowerSeries.subst Submission.CDT.sympPhi
          (PowerSeries.derivative (R := ℚ) (Submission.CDT.logP a b ra rb rab r0)))
        * (gpsi * PowerSeries.derivative (R := ℚ) Submission.CDT.sympPhi) by ring,
    gpsi_mul_deriv_sympPhi, mul_one]

/-- `ψ·d/dX (ψ·(P∘φ)') = P''∘φ`. -/
lemma gpsi_mul_deriv2_eq (a b : ℚ) (ra rb rab r0 : ℤ) :
    gpsi * PowerSeries.derivative (R := ℚ)
        (gpsi * PowerSeries.derivative (R := ℚ)
          ((Submission.CDT.logP a b ra rb rab r0).subst Submission.CDT.sympPhi))
      = (PowerSeries.derivative (R := ℚ)
          (PowerSeries.derivative (R := ℚ) (Submission.CDT.logP a b ra rb rab r0))).subst
          Submission.CDT.sympPhi := by
  rw [gpsi_mul_deriv_eq a b ra rb rab r0]
  rw [PowerSeries.derivative_subst Submission.CDT.sympPhi_hasSubst]
  rw [show gpsi * (PowerSeries.subst Submission.CDT.sympPhi
        (PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) (Submission.CDT.logP a b ra rb rab r0)))
          * PowerSeries.derivative (R := ℚ) Submission.CDT.sympPhi)
      = (PowerSeries.subst Submission.CDT.sympPhi
          (PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) (Submission.CDT.logP a b ra rb rab r0))))
        * (gpsi * PowerSeries.derivative (R := ℚ) Submission.CDT.sympPhi) by ring,
    gpsi_mul_deriv_sympPhi, mul_one]

/-! ## 3. The pulled-back order-two ODE in `ℚ[[X]]` -/

lemma g_pullback_ps (a b : ℚ) (ra rb rab r0 : ℤ) :
    (((p2poly a b : Polynomial ℚ)) : PowerSeries ℚ).subst Submission.CDT.sympPhi
        * (PowerSeries.derivative (R := ℚ)
            (PowerSeries.derivative (R := ℚ) (Submission.CDT.logP a b ra rb rab r0))).subst
            Submission.CDT.sympPhi
      + (((p1poly a b : Polynomial ℚ)) : PowerSeries ℚ).subst Submission.CDT.sympPhi
        * (PowerSeries.derivative (R := ℚ) (Submission.CDT.logP a b ra rb rab r0)).subst
            Submission.CDT.sympPhi
      + (((p0poly a b : Polynomial ℚ)) : PowerSeries ℚ).subst Submission.CDT.sympPhi
        * (Submission.CDT.logP a b ra rb rab r0).subst Submission.CDT.sympPhi
      = (((ppoly a b ra rb rab r0 : Polynomial ℚ)) : PowerSeries ℚ).subst
          Submission.CDT.sympPhi := by
  have h := Submission.CDT.logP_ode a b ra rb rab r0
  simp only [Submission.CDT.logPAODE] at h
  rw [← coe_p2poly a b, ← coe_p1poly a b, ← coe_p0poly a b,
    ← coe_ppoly a b ra rb rab r0] at h
  have h2 := congrArg (fun z : PowerSeries ℚ => z.subst Submission.CDT.sympPhi) h
  simpa only [PowerSeries.subst_add Submission.CDT.sympPhi_hasSubst,
    PowerSeries.subst_mul Submission.CDT.sympPhi_hasSubst] using h2

/-! ## 4. The ODE for `Pwfun` in `ℚ((x))` -/

lemma gsubst_zero : PowerSeries.subst Submission.CDT.sympPhi (0 : PowerSeries ℚ) = 0 := by
  rw [← PowerSeries.coe_substAlgHom Submission.CDT.sympPhi_hasSubst]
  exact map_zero _

lemma gsubst_inj : Function.Injective
    (fun f : PowerSeries ℚ => PowerSeries.subst Submission.CDT.sympPhi f) := by
  refine Commons.RingTheory.PowerSeries.subst_injective_of_constantCoeff_eq_zero ?_ ?_
  · simpa using Submission.CDT.coeff_sympPhi_zero
  · rw [Submission.CDT.coeff_sympPhi_one]
    exact isUnit_iff_ne_zero.mpr (by norm_num)

lemma gp2phiK_ne_zero (a b : ℚ) : p2phiK a b ≠ 0 := by
  have hcoe : toL (p2phiK a b)
      = Φ ((((p2poly a b : Polynomial ℚ)) : PowerSeries ℚ).subst Submission.CDT.sympPhi) := by
    rw [show p2phiK a b = Polynomial.aeval phiK (p2poly a b) from rfl,
      gPhi_subst (p2poly a b)]
  intro h0
  have h1 : Φ ((((p2poly a b : Polynomial ℚ)) : PowerSeries ℚ).subst Submission.CDT.sympPhi)
      = 0 := by rw [← hcoe, h0, map_zero]
  have h2 : ((((p2poly a b : Polynomial ℚ)) : PowerSeries ℚ).subst Submission.CDT.sympPhi) = 0 :=
    IsFractionRing.injective (PowerSeries ℚ) LF (by rw [h1, map_zero])
  have h3 : (((p2poly a b : Polynomial ℚ)) : PowerSeries ℚ) = 0 :=
    gsubst_inj (by
      change PowerSeries.subst Submission.CDT.sympPhi (((p2poly a b : Polynomial ℚ)) : PowerSeries ℚ)
        = PowerSeries.subst Submission.CDT.sympPhi (0 : PowerSeries ℚ)
      rw [h2, gsubst_zero])
  exact p2poly_ne_zero a b (Polynomial.coe_injective ℚ h3)

theorem g_ode_Pw (a b : ℚ) (ra rb rab r0 : ℤ) :
    dL (dL (Pwfun a b ra rb rab r0))
      = alphaLt a b * dL (Pwfun a b ra rb rab r0)
        + betaLt a b * Pwfun a b ra rb rab r0 + gammaLt a b ra rb rab r0 := by
  have hps := g_pullback_ps a b ra rb rab r0
  have hmap := congrArg (fun z : PowerSeries ℚ => Φ z) hps
  simp only [map_add, map_mul] at hmap
  have hA2 : Φ ((((p2poly a b : Polynomial ℚ)) : PowerSeries ℚ).subst Submission.CDT.sympPhi)
      = toL (p2phiK a b) := by
    rw [show p2phiK a b = Polynomial.aeval phiK (p2poly a b) from rfl,
      gPhi_subst (p2poly a b)]
  have hA1 : Φ ((((p1poly a b : Polynomial ℚ)) : PowerSeries ℚ).subst Submission.CDT.sympPhi)
      = toL (p1phiK a b) := by
    rw [show p1phiK a b = Polynomial.aeval phiK (p1poly a b) from rfl,
      gPhi_subst (p1poly a b)]
  have hA0 : Φ ((((p0poly a b : Polynomial ℚ)) : PowerSeries ℚ).subst Submission.CDT.sympPhi)
      = toL (p0phiK a b) := by
    rw [show p0phiK a b = Polynomial.aeval phiK (p0poly a b) from rfl,
      gPhi_subst (p0poly a b)]
  have hAp : Φ ((((ppoly a b ra rb rab r0 : Polynomial ℚ)) : PowerSeries ℚ).subst
        Submission.CDT.sympPhi) = toL (pphiK a b ra rb rab r0) := by
    rw [show pphiK a b ra rb rab r0 = Polynomial.aeval phiK (ppoly a b ra rb rab r0) from rfl,
      gPhi_subst (ppoly a b ra rb rab r0)]
  rw [hA2, hA1, hA0, hAp] at hmap
  have hchain : Φ (PowerSeries.derivative (R := ℚ)
        ((Submission.CDT.logP a b ra rb rab r0).subst Submission.CDT.sympPhi))
      = dL (Pwfun a b ra rb rab r0) := by
    rw [← dL_algebraMap]
    rfl
  have hD1 : Φ ((PowerSeries.derivative (R := ℚ) (Submission.CDT.logP a b ra rb rab r0)).subst
        Submission.CDT.sympPhi) = Φ gpsi * dL (Pwfun a b ra rb rab r0) := by
    rw [← gpsi_mul_deriv_eq a b ra rb rab r0, map_mul, hchain]
  have hD2 : Φ ((PowerSeries.derivative (R := ℚ)
        (PowerSeries.derivative (R := ℚ) (Submission.CDT.logP a b ra rb rab r0))).subst
        Submission.CDT.sympPhi) = Φ gpsi * dL (Φ gpsi * dL (Pwfun a b ra rb rab r0)) := by
    rw [← gpsi_mul_deriv2_eq a b ra rb rab r0, map_mul]
    congr 1
    rw [← dL_algebraMap, map_mul, hchain]
  rw [hD1, hD2] at hmap
  have hPw : Φ ((Submission.CDT.logP a b ra rb rab r0).subst Submission.CDT.sympPhi)
      = Pwfun a b ra rb rab r0 := rfl
  rw [hPw] at hmap
  -- identify `Φ gpsi` and its derivative
  have hgpsi : Φ gpsi = -(toL (xK - 1)) ^ 2 := by
    unfold gpsi
    rw [map_neg, map_pow, gPhi_sub_one]
  have hdlE : dL (toL (xK - 1)) = 1 := by
    rw [← gPhi_sub_one, dL_algebraMap]
    have h1 : PowerSeries.derivative (R := ℚ) ((PowerSeries.X : PowerSeries ℚ) - 1) = 1 := by
      rw [Derivation.map_sub, PowerSeries.derivative_X, PowerSeries.derivative_one, sub_zero]
    rw [h1, map_one]
  have hdlgpsi : dL (Φ gpsi) = -2 * toL (xK - 1) := by
    rw [hgpsi, pow_two, dL_neg, dL_mul, hdlE]
    ring
  -- expand the second derivative term
  rw [dL_mul] at hmap
  rw [hdlgpsi, hgpsi] at hmap
  -- the coefficient identities for `Q2K, Q1K, Q0K`
  have hQ2 : toL (Q2K a b) = toL (p2phiK a b) * (toL (xK - 1)) ^ 4 := by
    unfold Q2K
    rw [toL_mul, toL_pow]
  have hQ1 : toL (Q1K a b)
      = 2 * toL (p2phiK a b) * (toL (xK - 1)) ^ 3 - toL (p1phiK a b) * (toL (xK - 1)) ^ 2 := by
    unfold Q1K
    simp only [map_add, map_mul, map_pow, map_neg, map_ofNat]
    ring
  have hQ0 : toL (Q0K a b) = toL (p0phiK a b) := rfl
  have key : toL (Q2K a b) * dL (dL (Pwfun a b ra rb rab r0))
      + toL (Q1K a b) * dL (Pwfun a b ra rb rab r0)
      + toL (Q0K a b) * Pwfun a b ra rb rab r0 = toL (pphiK a b ra rb rab r0) := by
    rw [hQ2, hQ1, hQ0]
    linear_combination hmap
  have hQ2ne : toL (Q2K a b) ≠ 0 := by
    rw [hQ2]
    refine mul_ne_zero ?_ (pow_ne_zero 4 ?_)
    · intro h
      exact gp2phiK_ne_zero a b (toL_injective (by rw [h, map_zero]))
    · intro h
      exact gxK_sub_one_ne_zero (toL_injective (by rw [h, map_zero]))
  have hkey' : toL (Q2K a b) * dL (dL (Pwfun a b ra rb rab r0))
      = -toL (Q1K a b) * dL (Pwfun a b ra rb rab r0)
        - toL (Q0K a b) * Pwfun a b ra rb rab r0 + toL (pphiK a b ra rb rab r0) := by
    linear_combination key
  have hTA : toL (Q2K a b) * (alphaLt a b * dL (Pwfun a b ra rb rab r0)
        + betaLt a b * Pwfun a b ra rb rab r0 + gammaLt a b ra rb rab r0)
      = -toL (Q1K a b) * dL (Pwfun a b ra rb rab r0)
        - toL (Q0K a b) * Pwfun a b ra rb rab r0 + toL (pphiK a b ra rb rab r0) := by
    simp only [alphaLt, betaLt, gammaLt, alphaKt, betaKt, gammaKt, toL_neg, toL_div]
    field_simp [hQ2ne]
    ring
  exact mul_left_cancel₀ hQ2ne (hkey'.trans hTA.symm)

end Work.CDcl
