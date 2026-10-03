/-
# The `ℓ¹(ℤ²)` mass of the §6 symbol difference `symD` at the mixed heights `(0,l₂)`, for every `ρ ≤ 1`

`Work.Analysis.LoMixedPorts.symDMassLeOne`-style port: verbatim copy of the proof of
`Work.KMTAreas.A7.LpSymDMassBound` with the range `ρ ≤ 1/8` widened to `ρ ≤ 1` (the `1/8`
is only used there to obtain `ρ ≤ 1` before calling `symD_deriv_bound`).
-/
import Mathlib
import Submission.Work.KMTAreas.A7.LpSymDMass

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger Work.Analysis.EndVar

/-- **The `ℓ¹(ℤ²)` mass of the coefficient kernel of `symD` at the mixed heights `(0,l₂)`**, for every `0 < ρ ≤ 1.** -/
theorem symDMassLeOne (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) :
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∃ D C : ℝ, 0 < D ∧ 1 ≤ C ∧
      ∀ (N l₂ k₁ k₂ : ℕ), 1 ≤ l₂ → 1 ≤ N →
      (max k₁ k₂ + 2 * Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂) + 1
          ≤ (Work.Analysis.EndVar.logN N).toNat) →
      (Summable fun q : ℤ × ℤ =>
          ‖Work.KMTPlan.A6.coeff2 (Work.KMTPlan.A6.symD ρ P N 0 l₂ k₁ k₂) q.1 q.2‖) ∧
      (∑' q : ℤ × ℤ,
          ‖Work.KMTPlan.A6.coeff2 (Work.KMTPlan.A6.symD ρ P N 0 l₂ k₁ k₂) q.1 q.2‖)
        ≤ D * Work.KMTAreas.A7.smallScaleWeight C ρ 0 l₂ k₁ k₂ * (N : ℝ)⁻¹ := by
  intro ρ hρ hρ1
  have hb := Work.KMTPlan.A6.symD_deriv_bound P hd
  obtain ⟨K, D, hK, hD, hder⟩ := hb ρ hρ hρ1
  refine ⟨max (40 * D) 1, max 1 (2 * K + 2 * (P.natDegree : ℝ) + 5),
    lt_of_lt_of_le (by norm_num) (le_max_right _ _), le_max_left _ _, ?_⟩
  intro N l₂ k₁ k₂ hl₂ hN1 hC2
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  set Y : ℝ := (2 : ℝ) ^ (ρ * ((Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂ : ℕ) : ℝ)) with hY
  have hY1 : (1 : ℝ) ≤ Y := by
    rw [hY]; exact Real.one_le_rpow (by norm_num) (by positivity)
  have hYpos : (0 : ℝ) < Y := lt_of_lt_of_le one_pos hY1
  set C0 : ℝ := D * (2 : ℝ) ^ (K * (Y + ((Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂ : ℕ) : ℝ)))
      * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 * ((N : ℝ))⁻¹) with hC0
  set Acr : ℝ := C0 * ((N : ℝ))⁻¹ with hAcr
  have hC0nn : 0 ≤ C0 := by
    rw [hC0]
    refine mul_nonneg (mul_nonneg (le_of_lt hD) (by positivity)) ?_
    have : (0 : ℝ) ≤ (Work.A7.Sval P k₁ k₂) ^ 2 * ((N : ℝ))⁻¹ :=
      mul_nonneg (sq_nonneg _) (inv_nonneg.mpr hNpos.le)
    linarith
  have hAcrnn : 0 ≤ Acr := mul_nonneg hC0nn (inv_nonneg.mpr hNpos.le)
  have hr₁ : 0 < ((N : ℝ))⁻¹ := inv_pos.mpr hNpos
  have hr₁1 : ((N : ℝ))⁻¹ ≤ 1 := by
    rw [inv_le_one₀ hNpos]; exact_mod_cast hN1
  have hr₂ : 0 < (((N : ℝ)) ^ P.natDegree)⁻¹ :=
    inv_pos.mpr (by positivity : (0 : ℝ) < (N : ℝ) ^ P.natDegree)
  have hr₂1 : (((N : ℝ)) ^ P.natDegree)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (by positivity)]
    exact one_le_pow₀ (by exact_mod_cast hN1)
  have hder' : ∀ j₁ j₂ : ℕ, j₁ ≤ 2 → j₂ ≤ 2 →
      (∫⁻ x in Set.Icc (0 : ℝ) 1, ∫⁻ y in Set.Icc (0 : ℝ) 1,
          ENNReal.ofReal
            ‖Work.KMTPlan.A6.dp j₁ j₂ (Work.KMTPlan.A6.symD ρ P N 0 l₂ k₁ k₂) x y‖)
        ≤ ENNReal.ofReal (Acr * ((N : ℝ))⁻¹ ^ ((1 : ℝ) - (j₁ : ℝ))
            * (((N : ℝ) ^ P.natDegree)⁻¹) ^ ((1 : ℝ) - (j₂ : ℝ))) := by
    intro j₁ j₂ hj₁ hj₂
    refine (hder N 0 l₂ k₁ k₂ hN1 (by simpa using hC2) j₁ j₂ hj₁ hj₂).trans ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have hprod := Work.KMTPlan.A6.inv_rpow_prod N P.natDegree j₁ j₂ hN1
    rw [hAcr, hC0, hY, ← hprod]
    exact le_of_eq (by ring)
  obtain ⟨hsumD, hmassD⟩ := Work.KMTPlan.A6.SymToolbox_tsum_coeff2_le
    (fun x y => Work.KMTPlan.A6.symD ρ P N 0 l₂ k₁ k₂ x y)
    (fun x y => (Work.KMTPlan.A6.symD_period_contDiff P ρ N 0 l₂ k₁ k₂).1 x y)
    (fun x y => (Work.KMTPlan.A6.symD_period_contDiff P ρ N 0 l₂ k₁ k₂).2.1 x y)
    (Work.KMTPlan.A6.symD_period_contDiff P ρ N 0 l₂ k₁ k₂).2.2
    hr₁ hr₁1 hr₂ hr₂1 hAcrnn hder'
  refine ⟨hsumD, ?_⟩
  refine hmassD.trans ?_
  have hSval : 1 + (Work.A7.Sval P k₁ k₂) ^ 2 * ((N : ℝ))⁻¹
      ≤ (2 : ℝ) ^ (((2 * (k₁ + P.natDegree * k₂) + 3 : ℕ)) : ℝ) := by
    rw [Real.rpow_natCast]
    simpa only [div_eq_mul_inv] using
      Work.KMTPlan.A6.one_add_Sval_sq_div_le P N k₁ k₂ hN1
  have hk1L : k₁ ≤ Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂ :=
    le_trans (le_max_left k₁ k₂) (le_max_right _ _)
  have hk2L : k₂ ≤ Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂ :=
    le_trans (le_max_right k₁ k₂) (le_max_right _ _)
  have hLnn : (0 : ℝ) ≤ ((Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂ : ℕ) : ℝ) := by positivity
  have hexp : (((2 * (k₁ + P.natDegree * k₂) + 3 : ℕ)) : ℝ)
      ≤ 2 * ((P.natDegree : ℝ) + 1) * ((Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂ : ℕ) : ℝ) + 3 := by
    have h1 : (k₁ : ℝ) ≤ ((Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂ : ℕ) : ℝ) := by exact_mod_cast hk1L
    have h2 : (k₂ : ℝ) ≤ ((Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂ : ℕ) : ℝ) := by exact_mod_cast hk2L
    have hd1 : (1 : ℝ) ≤ (P.natDegree : ℝ) := by
      have : 1 ≤ P.natDegree := le_trans (by norm_num) hd
      exact_mod_cast this
    push_cast
    nlinarith [h1, h2, hd1, hLnn]
  have hSval2 : (2 : ℝ) ^ (((2 * (k₁ + P.natDegree * k₂) + 3 : ℕ)) : ℝ)
      ≤ (2 : ℝ) ^ (2 * ((P.natDegree : ℝ) + 1)
          * ((Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂ : ℕ) : ℝ) + 3) :=
    Real.rpow_le_rpow_of_exponent_le (x := 2) (by norm_num) hexp
  have hkey : 40 * C0 ≤ max (40 * D) 1
      * (2 : ℝ) ^ (max 1 (2 * K + 2 * (P.natDegree : ℝ) + 5)
          * max Y ((Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂ : ℕ) : ℝ)) := by
    rw [hC0]
    have hmaxY : (1 : ℝ) ≤ max Y ((Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂ : ℕ) : ℝ) :=
      le_trans hY1 (le_max_left _ _)
    have hLle : ((Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂ : ℕ) : ℝ)
        ≤ max Y ((Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂ : ℕ) : ℝ) := le_max_right _ _
    have hYle : Y ≤ max Y ((Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂ : ℕ) : ℝ) := le_max_left _ _
    have hstep1 : (1 + (Work.A7.Sval P k₁ k₂) ^ 2 * ((N : ℝ))⁻¹)
        ≤ (2 : ℝ) ^ (2 * ((P.natDegree : ℝ) + 1)
            * ((Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂ : ℕ) : ℝ) + 3) :=
      hSval.trans hSval2
    have hprod : (2 : ℝ) ^ (K * (Y + ((Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂ : ℕ) : ℝ)))
          * (2 : ℝ) ^ (2 * (P.natDegree + 1)
              * ((Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂ : ℕ) : ℝ) + 3)
        ≤ (2 : ℝ) ^ ((2 * K + 2 * (P.natDegree + 1) + 3)
            * max Y ((Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂ : ℕ) : ℝ)) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      refine Real.rpow_le_rpow_of_exponent_le (x := 2) (by norm_num) ?_
      nlinarith [hYle, hLle, hK, hY1, hYpos, hLnn]
    have hD40 : 40 * D ≤ max (40 * D) 1 := le_max_left _ _
    have hcle : (2 : ℝ) ^ ((2 * K + 2 * (P.natDegree + 1) + 3)
            * max Y ((Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂ : ℕ) : ℝ))
        ≤ (2 : ℝ) ^ (max 1 (2 * K + 2 * (P.natDegree : ℝ) + 5)
            * max Y ((Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂ : ℕ) : ℝ)) := by
      refine Real.rpow_le_rpow_of_exponent_le (x := 2) (by norm_num) ?_
      have hcoef : 2 * K + 2 * ((P.natDegree : ℝ) + 1) + 3
          ≤ max 1 (2 * K + 2 * (P.natDegree : ℝ) + 5) := by
        refine le_trans (le_of_eq ?_) (le_max_right _ _)
        ring
      exact mul_le_mul_of_nonneg_right hcoef (le_trans (by norm_num) hmaxY)
    calc 40 * (D * (2 : ℝ) ^ (K * (Y + ((Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂ : ℕ) : ℝ)))
          * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 * ((N : ℝ))⁻¹))
        = 40 * D * ((2 : ℝ) ^ (K * (Y + ((Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂ : ℕ) : ℝ)))
            * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 * ((N : ℝ))⁻¹)) := by ring
      _ ≤ 40 * D * ((2 : ℝ) ^ (K * (Y + ((Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂ : ℕ) : ℝ)))
            * (2 : ℝ) ^ (2 * (P.natDegree + 1)
                * ((Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂ : ℕ) : ℝ) + 3)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left hstep1 (by positivity)
      _ ≤ 40 * D * (2 : ℝ) ^ ((2 * K + 2 * (P.natDegree + 1) + 3)
            * max Y ((Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂ : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hprod (by positivity)
      _ ≤ max (40 * D) 1 * (2 : ℝ) ^ ((2 * K + 2 * (P.natDegree + 1) + 3)
            * max Y ((Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂ : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right hD40 (by positivity)
      _ ≤ max (40 * D) 1 * (2 : ℝ) ^ (max 1 (2 * K + 2 * (P.natDegree : ℝ) + 5)
            * max Y ((Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂ : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hcle (by positivity)
  have hfinal : 40 * Acr ≤ max (40 * D) 1
      * Work.KMTAreas.A7.smallScaleWeight (max 1 (2 * K + 2 * (P.natDegree : ℝ) + 5))
          ρ 0 l₂ k₁ k₂
      * (N : ℝ)⁻¹ := by
    rw [hAcr, smallScaleWeight, lp_lmaxR_eq_lcL]
    have h1 := mul_le_mul_of_nonneg_right hkey (inv_nonneg.mpr hNpos.le)
    calc 40 * (C0 * (N : ℝ)⁻¹)
        = (40 * C0) * (N : ℝ)⁻¹ := by ring
      _ ≤ (max (40 * D) 1 * (2 : ℝ) ^ (max 1 (2 * K + 2 * (P.natDegree : ℝ) + 5)
              * max Y ((Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂ : ℕ) : ℝ))) * (N : ℝ)⁻¹ := h1
      _ = max (40 * D) 1 * (2 : ℝ) ^ (max 1 (2 * K + 2 * (P.natDegree : ℝ) + 5)
              * max ((2 : ℝ) ^ (ρ * ((Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂ : ℕ) : ℝ)))
                ((Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂ : ℕ) : ℝ)) * (N : ℝ)⁻¹ := by rw [hY]
  exact hfinal

end

end Work.KMTAreas.A7
