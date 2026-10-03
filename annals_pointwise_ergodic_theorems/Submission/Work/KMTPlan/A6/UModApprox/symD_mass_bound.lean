/-
# The `ℓ¹(ℤ²)` mass bound for the §6 symbol difference `symD` (general arithmetic heights)

`Work.KMTPlan.A6.UModApprox.symD_mass_bound`: the paper's `crude-mult`(ii) for the *general*
arithmetic heights `(l₁,l₂)`: the coefficient kernel of the §6 symbol difference `symD` has
`ℓ¹(ℤ²)` mass `≤ C · modelWeight A ρ l₁ l₂ k₁ k₂ · N⁻¹`, uniformly on the scales satisfying the
strict plateau `max k₁ k₂ + 2 · uScale ρ (lcL l₁ l₂ k₁ k₂) + 1 ≤ logN N`.

Assembled from the proved `Work.KMTPlan.A6.symD_deriv_bound` (the paper's single-scale symbol
estimate for `symD`) and the proved `SymToolbox_tsum_coeff2_le` (the `crude-mult`
derivative-to-coefficient passage), exactly as in the small-scale twin `lowSmallModelApprox`
(where the same block appears inline, specialised to a finite `N`); the weight arithmetic uses
`Work.KMTPlan.A6.modelWeight_absorbs_symD`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.lowSmallModelApprox

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTPlan.A6.UModApprox

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger
open Work.KMTAreas.A7
open Work.Analysis.EndVar

/-- `lmaxR l₁ l₂ k₁ k₂` is the real cast of `lcL l₁ l₂ k₁ k₂`. -/
lemma lmaxR_eq_lcL (l₁ l₂ k₁ k₂ : ℕ) :
    Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂
      = ((Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ : ℕ) : ℝ) := by
  rw [Work.KMTAreas.A7.lmaxR, Work.KMTPlan.A6.lcL, Work.Analysis.EndVar.lmax]
  push_cast
  ring

/-- **The `ℓ¹(ℤ²)` mass of the coefficient kernel of the §6 symbol difference `symD`.** -/
theorem symD_mass_bound (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ρ₀ ≤ 1 ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ A : ℝ, 0 ≤ A ∧
      ∃ C : ℝ, 1 ≤ C ∧ ∀ (N l₁ l₂ k₁ k₂ : ℕ), 1 ≤ N →
        (max k₁ k₂ + 2 * Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) + 1
            ≤ (Work.Analysis.EndVar.logN N).toNat) →
        (Summable fun q : ℤ × ℤ =>
            ‖Work.KMTPlan.A6.coeff2 (Work.KMTPlan.A6.symD ρ P N l₁ l₂ k₁ k₂) q.1 q.2‖) ∧
        (∑' q : ℤ × ℤ,
            ‖Work.KMTPlan.A6.coeff2 (Work.KMTPlan.A6.symD ρ P N l₁ l₂ k₁ k₂) q.1 q.2‖)
          ≤ C * Work.KMTAreas.A7.modelWeight A ρ l₁ l₂ k₁ k₂ * (N : ℝ)⁻¹ := by
  have hb := Work.KMTPlan.A6.symD_deriv_bound P hd
  refine ⟨1, one_pos, le_rfl, fun ρ hρ hρ1 => ?_⟩
  obtain ⟨K, D, hK, hD, hder⟩ := hb ρ hρ hρ1
  obtain ⟨A₁, hA₁, habs⟩ :=
    Work.KMTPlan.A6.modelWeight_absorbs_symD P ρ hρ K (40 * D) hK (by linarith)
  refine ⟨A₁, hA₁, 1, le_rfl, fun N l₁ l₂ k₁ k₂ hN1 hC2 => ?_⟩
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  set C0 : ℝ := D * (2 : ℝ) ^ (K * (2 ^ (ρ * ((Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ : ℕ) : ℝ))
        + ((Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ : ℕ) : ℝ)))
      * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 * ((N : ℝ))⁻¹) with hC0
  set Acr : ℝ := C0 * ((N : ℝ))⁻¹ with hAcr
  have hC0nn : 0 ≤ C0 := by
    rw [hC0]
    exact mul_nonneg (mul_nonneg (le_of_lt hD) (by positivity)) (by positivity)
  have hAcrnn : 0 ≤ Acr := by
    rw [hAcr]
    exact mul_nonneg hC0nn (inv_nonneg.mpr (le_of_lt hNpos))
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
            ‖Work.KMTPlan.A6.dp j₁ j₂ (Work.KMTPlan.A6.symD ρ P N l₁ l₂ k₁ k₂) x y‖)
        ≤ ENNReal.ofReal (Acr * ((N : ℝ))⁻¹ ^ ((1 : ℝ) - (j₁ : ℝ))
            * (((N : ℝ) ^ P.natDegree)⁻¹) ^ ((1 : ℝ) - (j₂ : ℝ))) := by
    intro j₁ j₂ hj₁ hj₂
    refine (hder N l₁ l₂ k₁ k₂ hN1 hC2 j₁ j₂ hj₁ hj₂).trans ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have hprod := Work.KMTPlan.A6.inv_rpow_prod N P.natDegree j₁ j₂ hN1
    rw [hAcr, hC0]
    refine le_of_eq ?_
    rw [← hprod]
    ring
  obtain ⟨hsumD, hmassD⟩ := Work.KMTPlan.A6.SymToolbox_tsum_coeff2_le
    (fun x y => Work.KMTPlan.A6.symD ρ P N l₁ l₂ k₁ k₂ x y)
    (fun x y => (Work.KMTPlan.A6.symD_period_contDiff P ρ N l₁ l₂ k₁ k₂).1 x y)
    (fun x y => (Work.KMTPlan.A6.symD_period_contDiff P ρ N l₁ l₂ k₁ k₂).2.1 x y)
    (Work.KMTPlan.A6.symD_period_contDiff P ρ N l₁ l₂ k₁ k₂).2.2
    hr₁ hr₁1 hr₂ hr₂1 hAcrnn hder'
  refine ⟨hsumD, ?_⟩
  have hkey : 40 * C0 ≤ Work.KMTAreas.A7.modelWeight A₁ ρ l₁ l₂ k₁ k₂ := by
    rw [hC0]
    have hs : 1 + (Work.A7.Sval P k₁ k₂) ^ 2 * ((N : ℝ))⁻¹
        ≤ (2 : ℝ) ^ (2 * (k₁ + P.natDegree * k₂) + 3) := by
      simpa only [div_eq_mul_inv] using Work.KMTPlan.A6.one_add_Sval_sq_div_le P N k₁ k₂ hN1
    have hstep : 40 * (D * (2 : ℝ) ^ (K * (2 ^ (ρ * ((Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ : ℕ) : ℝ))
          + ((Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ : ℕ) : ℝ)))
          * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 * ((N : ℝ))⁻¹))
        ≤ 40 * (D * (2 : ℝ) ^ (K * (2 ^ (ρ * ((Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ : ℕ) : ℝ))
          + ((Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ : ℕ) : ℝ)))
          * (2 : ℝ) ^ (2 * (k₁ + P.natDegree * k₂) + 3)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      exact mul_le_mul_of_nonneg_left hs (by positivity)
    refine hstep.trans ?_
    have heq : (40 : ℝ) * (D * (2 : ℝ) ^ (K * (2 ^ (ρ * ((Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ : ℕ) : ℝ))
          + ((Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ : ℕ) : ℝ)))
          * (2 : ℝ) ^ (2 * (k₁ + P.natDegree * k₂) + 3))
        = 40 * D * (2 : ℝ) ^ (K * (2 ^ (ρ * ((Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ : ℕ) : ℝ))
          + ((Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ : ℕ) : ℝ)))
          * (2 : ℝ) ^ (2 * (k₁ + P.natDegree * k₂) + 3) := by ring
    rw [heq]
    exact habs l₁ l₂ k₁ k₂
  calc (∑' q : ℤ × ℤ,
        ‖Work.KMTPlan.A6.coeff2 (Work.KMTPlan.A6.symD ρ P N l₁ l₂ k₁ k₂) q.1 q.2‖)
      ≤ 40 * Acr := hmassD
    _ = 40 * C0 * ((N : ℝ))⁻¹ := by rw [hAcr]; ring
    _ ≤ Work.KMTAreas.A7.modelWeight A₁ ρ l₁ l₂ k₁ k₂ * (N : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_right hkey (inv_nonneg.mpr (le_of_lt hNpos))
    _ = 1 * Work.KMTAreas.A7.modelWeight A₁ ρ l₁ l₂ k₁ k₂ * (N : ℝ)⁻¹ := by ring

end

end Work.KMTPlan.A6.UModApprox
