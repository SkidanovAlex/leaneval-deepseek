/-
# The kernel-level integration-by-parts identity (ii) at `(k₁, k₂ ≥ 1)`

The `cw`-level (frequency-coefficient) form of identity (ii) is
`Work.KMTPlan.A6.MdlCwIntegIdent`:

`∫_{1/2}^1 cw φ_{N,t}(z₁) · cw φ̃_{N,t}(z₂) dt`
`  = c₀·(cw φ_{N,1}(z₁)·cw φ̃_{N,·,-1}(1,z₂)·W₁(1) - cw φ_{N,1/2}(z₁)·cw φ̃_{N,·,-1}(1/2,z₂)·W₁(1/2))`
`    - c₁·∫_{1/2}^1 cw φ_{N,·,1}(t,z₁)·cw φ̃_{N,·,-1}(t,z₂)·W₁(t) dt`
`    + c₀·∫_{1/2}^1 cw φ_{N,t}(z₁)·cw φ̃_{N,·,-1}(t,z₂)·W₂(t) dt`,

with `c₀ = mdlScale P k₂ · mdlIota`, `c₁ = mdlScaleFe P k₁ k₂`.

The present statement is the *kernel-level* form of this identity, in which `cw` is replaced by the
convolution kernel `mdlIWKer` of the Ionescu--Wainger multiplier `Tle`: the two differ by the
`t`-independent *arithmetic character* product `T = arithChar ρ l₁ (-z₁) · arithChar ρ l₂ (-z₂)`
(`mdlIWKer_eq_cw`), which factors out of every term.  This is the form consumed by the
operator-level transfer of the identity to the model tuple `mdlPartJ` with modified bumps.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.MdlCwIntegIdent
import Submission.Work.KMTPlan.A6.MdlKerLowHigh
import Submission.Work.KMTAreas.A7.Tle_varphitildeNt_bounded

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators Interval
open Work.KMTAreas.A7

theorem MdlKerIdentLowHigh (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ N k₁ k₂ : ℕ) (hk₂ : 1 ≤ k₂)
    (hN : 1 ≤ N)
    (hP : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, Work.KMTPlan.A6.PderivR P ((N : ℝ) * t) ≠ 0)
    (z₁ z₂ : ℤ) :
    (∫ t in (1 / 2 : ℝ)..1,
        Work.KMTPlan.A6.mdlIWKer ρ l₁ (Work.KMTAreas.A7.varphiNt N k₁ t) z₁
          * Work.KMTPlan.A6.mdlIWKer ρ l₂
              (Work.KMTAreas.A7.varphitildeNt P P.natDegree N k₂ t) z₂)
      = (Work.KMTPlan.A6.mdlScale P k₂ : ℂ) * Work.KMTPlan.A6.mdlIota
          * (Work.KMTPlan.A6.mdlW1 P N 1
                * (Work.KMTPlan.A6.mdlIWKer ρ l₁ (Work.KMTAreas.A7.varphiNt N k₁ 1) z₁
                    * Work.KMTPlan.A6.mdlIWKer ρ l₂
                        (Work.KMTPlan.A6.varphitildeNtj P N k₂ (-1) 1) z₂)
              - Work.KMTPlan.A6.mdlW1 P N (1 / 2)
                * (Work.KMTPlan.A6.mdlIWKer ρ l₁ (Work.KMTAreas.A7.varphiNt N k₁ (1 / 2)) z₁
                    * Work.KMTPlan.A6.mdlIWKer ρ l₂
                        (Work.KMTPlan.A6.varphitildeNtj P N k₂ (-1) (1 / 2)) z₂))
        - (Work.KMTPlan.A6.mdlScaleFe P k₁ k₂ : ℂ)
            * (∫ t in (1 / 2 : ℝ)..1, Work.KMTPlan.A6.mdlW1 P N t
                * (Work.KMTPlan.A6.mdlIWKer ρ l₁
                      (Work.KMTPlan.A6.varphiNtj N k₁ 1 t) z₁
                    * Work.KMTPlan.A6.mdlIWKer ρ l₂
                        (Work.KMTPlan.A6.varphitildeNtj P N k₂ (-1) t) z₂))
        + (Work.KMTPlan.A6.mdlScale P k₂ : ℂ) * Work.KMTPlan.A6.mdlIota
            * (∫ t in (1 / 2 : ℝ)..1, Work.KMTPlan.A6.mdlW2 P N t
                * (Work.KMTPlan.A6.mdlIWKer ρ l₁ (Work.KMTAreas.A7.varphiNt N k₁ t) z₁
                    * Work.KMTPlan.A6.mdlIWKer ρ l₂
                        (Work.KMTPlan.A6.varphitildeNtj P N k₂ (-1) t) z₂)) := by
  have hcw := MdlCwIntegIdent P N k₁ k₂ hN hk₂ hP
  set T : ℂ := arithChar ρ l₁ (-z₁) * arithChar ρ l₂ (-z₂) with hT
  have hmem1 : (1 : ℝ) ∈ Set.Icc (1 / 2 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
  have hmem2 : (1 / 2 : ℝ) ∈ Set.Icc (1 / 2 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have hIcc : ∀ t ∈ Set.uIcc (1 / 2 : ℝ) 1, t ∈ Set.Icc (1 / 2 : ℝ) 1 := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] at ht
    exact ht
  have hL : (∫ t in (1 / 2 : ℝ)..1,
        mdlIWKer ρ l₁ (varphiNt N k₁ t) z₁
          * mdlIWKer ρ l₂ (varphitildeNt P P.natDegree N k₂ t) z₂)
      = T * (∫ t in (1 / 2 : ℝ)..1,
          cw (varphiNt N k₁ t) z₁ * cw (varphitildeNt P P.natDegree N k₂ t) z₂) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [mdlIWKer_eq_cw ρ l₁ (integrable_varphiNt N k₁ t) z₁,
        mdlIWKer_eq_cw ρ l₂ (integrable_varphitildeNt_aux P P.natDegree N k₂ t) z₂, hT]
    ring
  have hM1 : (∫ t in (1 / 2 : ℝ)..1, mdlW1 P N t
        * (mdlIWKer ρ l₁ (varphiNtj N k₁ 1 t) z₁
          * mdlIWKer ρ l₂ (varphitildeNtj P N k₂ (-1) t) z₂))
      = T * (∫ t in (1 / 2 : ℝ)..1,
          cw (varphiNtj N k₁ 1 t) z₁ * cw (varphitildeNtj P N k₂ (-1) t) z₂
            * mdlW1 P N t) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t ht => ?_
    have ht' := hIcc t ht
    rw [mdlIWKer_eq_cw ρ l₁ ((mdlKerVarphiNtjOne ρ l₁ N k₁).1 t ht') z₁,
        mdlIWKer_eq_cw ρ l₂ ((mdlKerVarphitildeNtjNeg ρ l₂ P N k₂ hk₂).1 t ht') z₂, hT]
    ring
  have hM2 : (∫ t in (1 / 2 : ℝ)..1, mdlW2 P N t
        * (mdlIWKer ρ l₁ (varphiNt N k₁ t) z₁
          * mdlIWKer ρ l₂ (varphitildeNtj P N k₂ (-1) t) z₂))
      = T * (∫ t in (1 / 2 : ℝ)..1,
          cw (varphiNt N k₁ t) z₁ * cw (varphitildeNtj P N k₂ (-1) t) z₂
            * mdlW2 P N t) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t ht => ?_
    have ht' := hIcc t ht
    rw [mdlIWKer_eq_cw ρ l₁ (integrable_varphiNt N k₁ t) z₁,
        mdlIWKer_eq_cw ρ l₂ ((mdlKerVarphitildeNtjNeg ρ l₂ P N k₂ hk₂).1 t ht') z₂, hT]
    ring
  have hB1 : mdlIWKer ρ l₁ (varphiNt N k₁ 1) z₁
        * mdlIWKer ρ l₂ (varphitildeNtj P N k₂ (-1) 1) z₂
      = T * (cw (varphiNt N k₁ 1) z₁ * cw (varphitildeNtj P N k₂ (-1) 1) z₂) := by
    rw [mdlIWKer_eq_cw ρ l₁ (integrable_varphiNt N k₁ 1) z₁,
        mdlIWKer_eq_cw ρ l₂ ((mdlKerVarphitildeNtjNeg ρ l₂ P N k₂ hk₂).1 1 hmem1) z₂, hT]
    ring
  have hB2 : mdlIWKer ρ l₁ (varphiNt N k₁ (1 / 2)) z₁
        * mdlIWKer ρ l₂ (varphitildeNtj P N k₂ (-1) (1 / 2)) z₂
      = T * (cw (varphiNt N k₁ (1 / 2)) z₁
          * cw (varphitildeNtj P N k₂ (-1) (1 / 2)) z₂) := by
    rw [mdlIWKer_eq_cw ρ l₁ (integrable_varphiNt N k₁ (1 / 2)) z₁,
        mdlIWKer_eq_cw ρ l₂ ((mdlKerVarphitildeNtjNeg ρ l₂ P N k₂ hk₂).1 (1 / 2) hmem2) z₂,
        hT]
    ring
  rw [hL, hM1, hM2, hB1, hB2, hcw z₁ z₂]
  ring

end

end Work.KMTPlan.A6
