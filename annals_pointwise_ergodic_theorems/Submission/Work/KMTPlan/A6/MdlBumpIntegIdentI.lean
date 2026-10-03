/-
# The integration-by-parts identity (i) at the level of the modulated bumps

This module proves `Work.KMTPlan.A6.MdlBumpIntegIdentI`, the *bump-level* form of the
integration-by-parts identity (i) of Krause--Mirek--Tao §6 (Lemma `integ-ident`(i)):

  `∫_{1/2}^1 φ_{N,t}(ξ₁) φ̃_{N,t}(ξ₂) dt
     = 2^{-k₁} (2πi)^{-1} ( φ_{N,j=-1}(1,ξ₁) φ̃_{N}(1,ξ₂)
                          - φ_{N,j=-1}(1/2,ξ₁) φ̃_{N}(1/2,ξ₂) )
       - 2^{d k₂ - k₁} ∫_{1/2}^1 φ_{N,j=-1}(t,ξ₁) φ̃_{N,j=1}(t,ξ₂) (P'(Nt)/N^{d-1}) dt`,

where `φ_{N,t}(ξ) = φ_N(ξ) e(Ntξ)`, `φ̃_{N,t}(ξ) = φ̃_N(ξ) e(P(Nt)ξ)`,
`φ_{N,t,j}(ξ) = (2^{-k}Nξ)^j φ_{N,t}(ξ)`, `φ̃_{N,t,j}(ξ) = (2^{-dk}N^dξ)^j φ̃_{N,t}(ξ)`,
`d = P.natDegree`, and the weight `P'(Nt)/N^{d-1}` is `mdlW3`.

It is the integration-by-parts identity (i) `integIdent_i_core` of `A6/IntegIdent.lean`
(`∫Φ = Φ(1)/(2πiξ₁N) - Φ(1/2)/(2πiξ₁N) - (ξ₂/ξ₁)∫Φ·P'(Nt)`) applied to the *product* of the
modulated bumps: the product `φ_{N,t}(ξ₁)φ̃_{N,t}(ξ₂)` is the constant
`φ_N(ξ₁)φ̃_N(ξ₂)` times the oscillatory integral `Φ(t) = e(ξ₁Nt + P(Nt)ξ₂)`, the modified bumps
`φ_{N,·,-1}` and `φ̃_{N,·,1}` are exactly the factors by which the boundary and middle terms of
`integIdent_i_core` are multiplied, and the constants combine by the coefficient identities

* `2^{-k₁}(2πi)^{-1}(2^{-k₁}Nξ₁)^{-1} = (2πiξ₁N)^{-1}` (`mdlScaleF_mul_inv`),
* `2^{dk₂-k₁}(2^{-k₁}Nξ₁)^{-1}(2^{-dk₂}N^dξ₂)(P'(Nt)/N^{d-1}) = (ξ₂/ξ₁)P'(Nt)`
  (`mdlMidCoeff_proved`); when `d = 0` both sides of the second identity vanish because
  `P' ≡ 0` (see `PderivR_eq_zero_of_natDegree_eq_zero`), which is why the truncated natural
  subtraction in `N^{d-1}` causes no difficulty.

Nothing here is postulated: the only external input is the elementary `integIdent_i_core`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.MdlDefs

set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators Interval
open Work.KMTAreas.A7

/-! ## The character `ee` and the phase `Φ` -/

private lemma ee_add_I (x y : ℝ) : ee (x + y) = ee x * ee y := by
  rw [ee, ee, ee, ← Complex.exp_add]; congr 1; push_cast; ring

private lemma Phi_eq_I (P : ℤ[X]) (N ξ₁ ξ₂ t : ℝ) :
    Phi P N ξ₁ ξ₂ t = ee (ξ₁ * N * t + PevalR P (N * t) * ξ₂) := by
  simp only [Phi_apply, phase_apply, chi, ee]

/-! ## The pointwise identities for the three integrands -/

/-- The integrand of the left-hand side is the constant `φ_N(ξ₁)φ̃_N(ξ₂)` times `Φ`. -/
private lemma varphiNt_mul_varphitildeNt (P : ℤ[X]) (N k₁ k₂ : ℕ) (t ξ₁ ξ₂ : ℝ) :
    varphiNt N k₁ t ξ₁ * varphitildeNt P P.natDegree N k₂ t ξ₂
      = (varphiN N k₁ ξ₁ * varphitildeN P.natDegree N k₂ ξ₂) * Phi P N ξ₁ ξ₂ t := by
  rw [varphiNt, varphitildeNt, Phi_eq_I, ee_add_I]
  have h : ee ((N:ℝ) * t * ξ₁) = ee (ξ₁ * (N:ℝ) * t) := by congr 1; ring
  rw [h]; ring

/-- The boundary integrand, with the modified bump `φ_{N,·,-1}`. -/
private lemma varphiNtj_mul_varphitildeNt (P : ℤ[X]) (N k₁ k₂ : ℕ) (t ξ₁ ξ₂ : ℝ) :
    varphiNtj N k₁ (-1) t ξ₁ * varphitildeNt P P.natDegree N k₂ t ξ₂
      = ((((2:ℝ)^(-(k₁:ℝ)) * (N:ℝ) * ξ₁ : ℝ)) : ℂ)⁻¹
        * ((varphiN N k₁ ξ₁ * varphitildeN P.natDegree N k₂ ξ₂) * Phi P N ξ₁ ξ₂ t) := by
  rw [varphiNtj, zpow_neg_one, ← varphiNt_mul_varphitildeNt]
  ring

/-! ## The two coefficient identities -/

/-- `P' ≡ 0` for a polynomial of degree `0` (the case in which the truncated subtraction in
`N^(P.natDegree - 1)` does not cancel). -/
private lemma PderivR_eq_zero_of_natDegree_eq_zero (P : Polynomial ℤ) (h : P.natDegree = 0)
    (t : ℝ) : PderivR P t = 0 := by
  have hder : P.derivative = 0 := Polynomial.derivative_eq_zero.mpr h
  simp [PderivR, hder]

/-- The coefficient identity of the boundary term: `2^{-k₁}(2πi)^{-1}(2^{-k₁}Nξ₁)^{-1}
= (2πiξ₁N)^{-1}`. -/
private lemma mdlScaleF_mul_inv (N k₁ : ℕ) (ξ₁ : ℝ) (hξ₁ : ξ₁ ≠ 0) :
    (mdlScaleF k₁ : ℂ) * mdlIota * ((((2:ℝ)^(-(k₁:ℝ)) * (N:ℝ) * ξ₁ : ℝ)) : ℂ)⁻¹
      = (cnorm₁ ξ₁ (N:ℝ))⁻¹ := by
  have h2 : (((2:ℝ)^(-(k₁:ℝ)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.rpow_pos_of_pos (x := 2) (by norm_num) (-(k₁:ℝ))))
  have hx : ((ξ₁:ℝ) : ℂ) ≠ 0 := by exact_mod_cast hξ₁
  simp only [mdlScaleF, mdlIota, cnorm₁_apply]
  push_cast
  field_simp

/-- The real form of the coefficient identity of the middle term. -/
private lemma mdlMidCoeff_real (P : ℤ[X]) (N k₁ k₂ : ℕ) (hN : 1 ≤ N) (x ξ₁ ξ₂ : ℝ)
    (hξ₁ : ξ₁ ≠ 0) :
    (2:ℝ)^((P.natDegree:ℝ)*(k₂:ℝ) - (k₁:ℝ))
      * ((2:ℝ)^(-(k₁:ℝ)) * (N:ℝ) * ξ₁)⁻¹
      * ((2:ℝ)^(-((P.natDegree:ℝ)*(k₂:ℝ))) * (N:ℝ)^(P.natDegree) * ξ₂)
      * (PderivR P x / (N:ℝ)^(P.natDegree - 1))
    = (ξ₂/ξ₁) * PderivR P x := by
  by_cases hd : P.natDegree = 0
  · have hP' : PderivR P x = 0 := PderivR_eq_zero_of_natDegree_eq_zero P hd _
    rw [hP', zero_div, mul_zero, mul_zero]
  · have h1 : (2:ℝ)^((P.natDegree:ℝ)*(k₂:ℝ) - (k₁:ℝ))
        = ((2:ℝ)^P.natDegree)^k₂ * ((2:ℝ)^k₁)⁻¹ := by
      rw [Real.rpow_sub (by norm_num : (0:ℝ) < 2), Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),
        Real.rpow_natCast, Real.rpow_natCast, Real.rpow_natCast, div_eq_mul_inv]
    have h3 : (2:ℝ)^(-(k₁:ℝ)) = ((2:ℝ)^k₁)⁻¹ := by
      rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), Real.rpow_natCast]
    have h4 : (2:ℝ)^(-((P.natDegree:ℝ)*(k₂:ℝ))) = (((2:ℝ)^P.natDegree)^k₂)⁻¹ := by
      rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),
        Real.rpow_natCast, Real.rpow_natCast]
    have hNp : (N:ℝ)^P.natDegree = (N:ℝ) * (N:ℝ)^(P.natDegree - 1) := by
      have hsp : P.natDegree - 1 + 1 = P.natDegree := by omega
      conv_lhs => rw [← hsp]
      rw [pow_succ]; ring
    rw [h1, h3, h4, hNp]
    field_simp

/-- The coefficient identity of the middle term, in the form used by the identity:
`2^{dk₂-k₁}(2^{-k₁}Nξ₁)^{-1}(2^{-dk₂}N^dξ₂)(P'(Nt)/N^{d-1}) = (ξ₂/ξ₁)P'(Nt)`. -/
private lemma mdlMidCoeff_proved (P : ℤ[X]) (N k₁ k₂ : ℕ) (hN : 1 ≤ N) (t ξ₁ ξ₂ : ℝ)
    (hξ₁ : ξ₁ ≠ 0) :
    (mdlScaleFG P k₁ k₂ : ℂ)
        * ((((2 : ℝ) ^ (-(k₁ : ℝ)) * (N : ℝ) * ξ₁ : ℝ)) : ℂ)⁻¹
        * ((((2 : ℝ) ^ (-((P.natDegree : ℝ) * (k₂ : ℝ)))
              * (N : ℝ) ^ (P.natDegree) * ξ₂ : ℝ)) : ℂ)
        * mdlW3 P N t
      = ((ξ₂ / ξ₁ : ℝ) : ℂ) * ((PderivR P ((N : ℝ) * t) : ℝ) : ℂ) := by
  rw [mdlScaleFG, mdlW3]
  have h := mdlMidCoeff_real P N k₁ k₂ hN ((N:ℝ)*t) ξ₁ ξ₂ hξ₁
  exact_mod_cast h

/-! ## The boundary and middle integrands of the target -/

/-- The boundary term of the target, rewritten as `φ_N(ξ₁)φ̃_N(ξ₂)·Φ(s)/cnorm₁`. -/
private lemma mdlScaleF_mul_boundary (P : ℤ[X]) (N k₁ k₂ : ℕ) (s ξ₁ ξ₂ : ℝ) (hξ₁ : ξ₁ ≠ 0) :
    (mdlScaleF k₁ : ℂ) * mdlIota
        * (varphiNtj N k₁ (-1) s ξ₁ * varphitildeNt P P.natDegree N k₂ s ξ₂)
      = (varphiN N k₁ ξ₁ * varphitildeN P.natDegree N k₂ ξ₂)
        * (Phi P N ξ₁ ξ₂ s / cnorm₁ ξ₁ (N:ℝ)) := by
  rw [varphiNtj_mul_varphitildeNt]
  have h : (mdlScaleF k₁ : ℂ) * mdlIota
        * (((((2:ℝ)^(-(k₁:ℝ)) * (N:ℝ) * ξ₁ : ℝ)) : ℂ)⁻¹
          * ((varphiN N k₁ ξ₁ * varphitildeN P.natDegree N k₂ ξ₂) * Phi P N ξ₁ ξ₂ s))
      = ((mdlScaleF k₁ : ℂ) * mdlIota * ((((2:ℝ)^(-(k₁:ℝ)) * (N:ℝ) * ξ₁ : ℝ)) : ℂ)⁻¹)
        * ((varphiN N k₁ ξ₁ * varphitildeN P.natDegree N k₂ ξ₂) * Phi P N ξ₁ ξ₂ s) := by ring
  rw [h, mdlScaleF_mul_inv N k₁ ξ₁ hξ₁]
  ring

/-- The middle integrand of the target: the coefficient identity turns
`φ_{N,·,-1}(s)φ̃_{N,·,1}(s)mdlW3(s)` into `(ξ₂/ξ₁)P'(Ns)·(φ_N(ξ₁)φ̃_N(ξ₂)·Φ(s))`. -/
private lemma mdlScaleFG_mul_middle (P : ℤ[X]) (N k₁ k₂ : ℕ) (hN : 1 ≤ N) (s ξ₁ ξ₂ : ℝ)
    (hξ₁ : ξ₁ ≠ 0) :
    (mdlScaleFG P k₁ k₂ : ℂ)
        * (varphiNtj N k₁ (-1) s ξ₁ * varphitildeNtj P N k₂ 1 s ξ₂ * mdlW3 P N s)
      = ((ξ₂/ξ₁:ℝ):ℂ) * ((varphiN N k₁ ξ₁ * varphitildeN P.natDegree N k₂ ξ₂)
          * (Phi P N ξ₁ ξ₂ s * ((PderivR P ((N:ℝ)*s):ℝ):ℂ))) := by
  have h1 : (mdlScaleFG P k₁ k₂ : ℂ)
        * (varphiNtj N k₁ (-1) s ξ₁ * varphitildeNtj P N k₂ 1 s ξ₂ * mdlW3 P N s)
      = ((mdlScaleFG P k₁ k₂ : ℂ)
          * ((((2:ℝ)^(-(k₁:ℝ)) * (N:ℝ) * ξ₁ : ℝ)) : ℂ)⁻¹
          * ((((2:ℝ)^(-((P.natDegree:ℝ)*(k₂:ℝ))) * (N:ℝ)^(P.natDegree) * ξ₂ : ℝ)) : ℂ)
          * mdlW3 P N s)
          * (varphiNt N k₁ s ξ₁ * varphitildeNt P P.natDegree N k₂ s ξ₂) := by
    rw [varphiNtj, varphitildeNtj, zpow_neg_one, zpow_one]; ring
  rw [h1, mdlMidCoeff_proved P N k₁ k₂ hN s ξ₁ ξ₂ hξ₁, varphiNt_mul_varphitildeNt]
  ring

/-! ## The identity -/

theorem MdlBumpIntegIdentI (P : Polynomial ℤ) (N k₁ k₂ : ℕ) (hN : 1 ≤ N) :
    ∀ ξ₁ ξ₂ : ℝ, ξ₁ ≠ 0 →
      (∫ t in (1 / 2 : ℝ)..1,
          Work.KMTAreas.A7.varphiNt N k₁ t ξ₁ * Work.KMTAreas.A7.varphitildeNt P P.natDegree N k₂ t ξ₂)
        = (Work.KMTPlan.A6.mdlScaleF k₁ : ℂ) * Work.KMTPlan.A6.mdlIota
            * (Work.KMTPlan.A6.varphiNtj N k₁ (-1) 1 ξ₁
                * Work.KMTAreas.A7.varphitildeNt P P.natDegree N k₂ 1 ξ₂
              - Work.KMTPlan.A6.varphiNtj N k₁ (-1) (1 / 2) ξ₁
                * Work.KMTAreas.A7.varphitildeNt P P.natDegree N k₂ (1 / 2) ξ₂)
          - (Work.KMTPlan.A6.mdlScaleFG P k₁ k₂ : ℂ)
              * (∫ t in (1 / 2 : ℝ)..1, Work.KMTPlan.A6.varphiNtj N k₁ (-1) t ξ₁
                  * Work.KMTPlan.A6.varphitildeNtj P N k₂ 1 t ξ₂ * Work.KMTPlan.A6.mdlW3 P N t) := by
  intro ξ₁ ξ₂ hξ₁
  have hNR : ((N:ℝ)) ≠ 0 := by
    have : (0:ℝ) < N := by exact_mod_cast hN
    exact ne_of_gt this
  have hPhi := integIdent_i_core P (N := (N:ℝ)) (ξ₁ := ξ₁) (ξ₂ := ξ₂) hNR hξ₁
  have hLHS : (∫ t in (1/2:ℝ)..1, varphiNt N k₁ t ξ₁ * varphitildeNt P P.natDegree N k₂ t ξ₂)
      = (varphiN N k₁ ξ₁ * varphitildeN P.natDegree N k₂ ξ₂)
        * (∫ t in (1/2:ℝ)..1, Phi P N ξ₁ ξ₂ t) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr
      (fun t _ => varphiNt_mul_varphitildeNt P N k₁ k₂ t ξ₁ ξ₂)
  have hBdry : (mdlScaleF k₁ : ℂ) * mdlIota
        * (varphiNtj N k₁ (-1) 1 ξ₁ * varphitildeNt P P.natDegree N k₂ 1 ξ₂
          - varphiNtj N k₁ (-1) (1/2) ξ₁ * varphitildeNt P P.natDegree N k₂ (1/2) ξ₂)
      = (varphiN N k₁ ξ₁ * varphitildeN P.natDegree N k₂ ξ₂)
          * (Phi P N ξ₁ ξ₂ 1 / cnorm₁ ξ₁ (N:ℝ))
        - (varphiN N k₁ ξ₁ * varphitildeN P.natDegree N k₂ ξ₂)
          * (Phi P N ξ₁ ξ₂ (1/2) / cnorm₁ ξ₁ (N:ℝ)) := by
    rw [mul_sub, mdlScaleF_mul_boundary P N k₁ k₂ 1 ξ₁ ξ₂ hξ₁,
      mdlScaleF_mul_boundary P N k₁ k₂ (1/2) ξ₁ ξ₂ hξ₁]
  have hMid : (mdlScaleFG P k₁ k₂ : ℂ)
        * (∫ t in (1/2:ℝ)..1, varphiNtj N k₁ (-1) t ξ₁ * varphitildeNtj P N k₂ 1 t ξ₂ * mdlW3 P N t)
      = (((ξ₂/ξ₁:ℝ):ℂ) * (varphiN N k₁ ξ₁ * varphitildeN P.natDegree N k₂ ξ₂))
        * (∫ t in (1/2:ℝ)..1, Phi P N ξ₁ ξ₂ t * ((PderivR P ((N:ℝ)*t):ℝ):ℂ)) := by
    have hpt : ∀ t ∈ Set.uIcc (1/2:ℝ) 1, (mdlScaleFG P k₁ k₂ : ℂ)
          * (varphiNtj N k₁ (-1) t ξ₁ * varphitildeNtj P N k₂ 1 t ξ₂ * mdlW3 P N t)
        = (((ξ₂/ξ₁:ℝ):ℂ) * (varphiN N k₁ ξ₁ * varphitildeN P.natDegree N k₂ ξ₂))
          * (Phi P N ξ₁ ξ₂ t * ((PderivR P ((N:ℝ)*t):ℝ):ℂ)) := by
      intro t _
      rw [mdlScaleFG_mul_middle P N k₁ k₂ hN t ξ₁ ξ₂ hξ₁]
      ring
    rw [← intervalIntegral.integral_const_mul, intervalIntegral.integral_congr hpt,
      intervalIntegral.integral_const_mul]
  rw [hLHS, hBdry, hMid, hPhi]
  ring

end

end Work.KMTPlan.A6
