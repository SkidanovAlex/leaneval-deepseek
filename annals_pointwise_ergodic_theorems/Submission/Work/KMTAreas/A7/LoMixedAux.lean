/-
# Auxiliary lemmas for the mixed case `(l₁,l₂) = (0,l₂)` of the §8 model estimate

Small, self-contained inputs of `Work.KMTAreas.A7.LoMixedModel`:

* `variationalNorm_mul_le_one` — the variational product rule with constant `1` (the existential
  form is `Work.KMTAreas.A7.variationalNorm_mul_le`, whose proof in fact gives `C = 1`; the explicit
  form is what the assembly consumes, to avoid carrying a constant through the bookkeeping);
* the elementary arithmetic of the loss weight `lossWeight c ρ l₁ l₂ k₁ k₂ = ⟨L⟩^c 2^{cρL}`:
  non-negativity, `≥ 1`, and multiplicativity in the exponent.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.variationalNorm_mul_le

set_option autoImplicit false

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.EndVar

/-- **The variational norm is submultiplicative for the pointwise product, with constant `1`.**
This is the explicit-constant form of `Work.KMTAreas.A7.variationalNorm_mul_le`. -/
theorem variationalNorm_mul_le_one (r : NNReal) (hr : 1 ≤ r) (u v : ℕ → ℂ) :
    PointwiseErgodicTheorems.variationalNorm r (fun n => u n * v n)
      ≤ PointwiseErgodicTheorems.variationalNorm r u
        * PointwiseErgodicTheorems.variationalNorm r v := by
  have hvar := varPart_mul_le hr u v
  rw [Submission.PointwiseErgodicTheorems.variationalNorm_eq_add r (fun n => u n * v n),
      Submission.PointwiseErgodicTheorems.variationalNorm_eq_add r u,
      Submission.PointwiseErgodicTheorems.variationalNorm_eq_add r v]
  calc (⨆ n, ‖u n * v n‖ₑ) + Submission.PointwiseErgodicTheorems.varPart r (fun n => u n * v n)
      ≤ ((⨆ n, ‖u n‖ₑ) * (⨆ n, ‖v n‖ₑ))
          + ((⨆ n, ‖v n‖ₑ) * Submission.PointwiseErgodicTheorems.varPart r u
              + (⨆ n, ‖u n‖ₑ) * Submission.PointwiseErgodicTheorems.varPart r v) :=
        add_le_add (iSup_enorm_mul_le u v) hvar
    _ ≤ ((⨆ n, ‖u n‖ₑ) + Submission.PointwiseErgodicTheorems.varPart r u)
          * ((⨆ n, ‖v n‖ₑ) + Submission.PointwiseErgodicTheorems.varPart r v) := by
        calc ((⨆ n, ‖u n‖ₑ) * (⨆ n, ‖v n‖ₑ))
              + ((⨆ n, ‖v n‖ₑ) * Submission.PointwiseErgodicTheorems.varPart r u
                  + (⨆ n, ‖u n‖ₑ) * Submission.PointwiseErgodicTheorems.varPart r v)
            ≤ ((⨆ n, ‖u n‖ₑ) * (⨆ n, ‖v n‖ₑ))
              + ((⨆ n, ‖v n‖ₑ) * Submission.PointwiseErgodicTheorems.varPart r u
                  + (⨆ n, ‖u n‖ₑ) * Submission.PointwiseErgodicTheorems.varPart r v)
              + (Submission.PointwiseErgodicTheorems.varPart r u
                  * Submission.PointwiseErgodicTheorems.varPart r v) := le_add_right le_rfl
          _ = ((⨆ n, ‖u n‖ₑ) + Submission.PointwiseErgodicTheorems.varPart r u)
                * ((⨆ n, ‖v n‖ₑ) + Submission.PointwiseErgodicTheorems.varPart r v) := by ring

/-- `lmaxR` is non-negative. -/
theorem lmaxR_nonneg_local (l₁ l₂ k₁ k₂ : ℕ) : (0 : ℝ) ≤ lmaxR l₁ l₂ k₁ k₂ := by
  rw [lmaxR]
  have h : (0 : ℤ) ≤ lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) := by
    rw [Work.Analysis.EndVar.lmax]
    exact le_trans (Int.natCast_nonneg l₁)
      (le_trans (le_max_left _ _) (le_max_left _ _))
  exact_mod_cast h

/-- `1 + lmaxR` is positive. -/
theorem one_add_lmaxR_pos_local (l₁ l₂ k₁ k₂ : ℕ) : (0 : ℝ) < 1 + lmaxR l₁ l₂ k₁ k₂ := by
  have := lmaxR_nonneg_local l₁ l₂ k₁ k₂
  linarith

/-- The loss weight is non-negative for non-negative exponents. -/
theorem lossWeight_nonneg_local {c ρ : ℝ} (hc : 0 ≤ c) (l₁ l₂ k₁ k₂ : ℕ) :
    0 ≤ lossWeight c ρ l₁ l₂ k₁ k₂ := by
  rw [lossWeight]
  exact mul_nonneg (Real.rpow_nonneg (le_of_lt (one_add_lmaxR_pos_local l₁ l₂ k₁ k₂)) _)
    (Real.rpow_nonneg (by norm_num) _)

/-- The loss weight is at least `1` for `c ≥ 0`, `ρ ≥ 0`. -/
theorem one_le_lossWeight_local {c ρ : ℝ} (hc : 0 ≤ c) (hρ : 0 ≤ ρ) (l₁ l₂ k₁ k₂ : ℕ) :
    1 ≤ lossWeight c ρ l₁ l₂ k₁ k₂ := by
  have hL := lmaxR_nonneg_local l₁ l₂ k₁ k₂
  have h1 : (1 : ℝ) ≤ (1 + lmaxR l₁ l₂ k₁ k₂) ^ c := Real.one_le_rpow (by linarith) hc
  have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ (c * ρ * lmaxR l₁ l₂ k₁ k₂) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  rw [lossWeight]
  exact one_le_mul_of_one_le_of_one_le h1 h2

/-- **Multiplicativity of the loss weight in its exponent.** -/
theorem lossWeight_mul_local (a b ρ : ℝ) (l₁ l₂ k₁ k₂ : ℕ) :
    lossWeight a ρ l₁ l₂ k₁ k₂ * lossWeight b ρ l₁ l₂ k₁ k₂
      = lossWeight (a + b) ρ l₁ l₂ k₁ k₂ := by
  have h1 := one_add_lmaxR_pos_local l₁ l₂ k₁ k₂
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hexp : a * ρ * lmaxR l₁ l₂ k₁ k₂ + b * ρ * lmaxR l₁ l₂ k₁ k₂
      = (a + b) * ρ * lmaxR l₁ l₂ k₁ k₂ := by ring
  rw [lossWeight, lossWeight, lossWeight, mul_mul_mul_comm, ← Real.rpow_add h1,
    ← Real.rpow_add h2, hexp]

end

end Work.KMTAreas.A7
