/-
# The assembly of Area A6 from its two cases

Area A6 (`AreaA6 = ∀ P, 2 ≤ P.natDegree → AreaA1 → ImprovKMT P → VarpL2KMT P`) is proved from
the two cases of the §6 decomposition of the §5 columns:

* the **high–high case** `CaseHH` (`1 ≤ k₁ ∧ 1 ≤ k₂`), the paper's Proposition `high-high-l2`
  together with the inner products/improvisation of §6 (`Work.KMTPlan.A6.highHighCase`);
* the **remaining case** `CaseRest` (`k₁ = 0 ∨ k₂ = 0`), the paper's reduction to the model
  operators of §6 and the model estimates of §7/§8 (`Work.KMTPlan.A6.lowCase`).

Both cases are stated with the exponential gain `2^{-c·lmax}` (`lmax = max(max l₁ l₂)(max s₁ s₂)`)
and their own constants `c, ρ₀`; the assembly takes the minimum of the two constants and combines
the two case-restricted bounds with `pieceBound_of_hh_and_rest`.
-/
import Submission.Work.KMTPlan.Model
import Submission.Work.KMTContract.Areas

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal PNat BigOperators
open PointwiseErgodicTheorems
open Submission.PointwiseErgodicTheorems
open Work.Analysis.EndVar
open Work.KMTContract
open Work.KMTPlan

/-- The gain weight of Area A6: `2^{-c·lmax l₁ l₂ s₁ s₂}`. -/
def gainW (c : ℝ) : ℕ → ℕ → ℕ → ℕ → ℝ :=
  fun l₁ l₂ s₁ s₂ => (2 : ℝ) ^ (-(c * (lmax l₁ l₂ (s₁ : ℤ) (s₂ : ℤ) : ℝ)))

/-- The weight `gainW c` is antitone in `c` on `c ≥ 0` in the relevant sense: if `c' ≤ c` then
`gainW c ≤ gainW c'`. -/
theorem gainW_le_of_le {c c' : ℝ} (hc' : 0 ≤ c')
    (h : ∀ l₁ l₂ (s₁ s₂ : ℕ), 0 ≤ (lmax l₁ l₂ (s₁ : ℤ) (s₂ : ℤ) : ℝ)) (hcc : c' ≤ c) :
    ∀ l₁ l₂ s₁ s₂, gainW c l₁ l₂ s₁ s₂ ≤ gainW c' l₁ l₂ s₁ s₂ := by
  intro l₁ l₂ s₁ s₂
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  have := h l₁ l₂ s₁ s₂
  nlinarith

/-- `lmax l₁ l₂ s₁ s₂` is nonnegative. -/
theorem lmax_cast_nonneg (l₁ l₂ s₁ s₂ : ℕ) :
    0 ≤ (lmax l₁ l₂ (s₁ : ℤ) (s₂ : ℤ) : ℝ) := by
  have h : (0 : ℤ) ≤ lmax l₁ l₂ (s₁ : ℤ) (s₂ : ℤ) := by
    rw [Work.Analysis.EndVar.lmax]
    exact le_trans (Int.natCast_nonneg l₁)
      (le_trans (le_max_left _ _) (le_max_left _ _))
  exact_mod_cast h

/-- **The assembly of Area A6 from its two cases.**  Given the high–high case and the remaining
case, each with the exponential gain and its own constants, `AreaA6` follows. -/
theorem areaA6_of_cases
    (hh : ∀ (P : ℤ[X]), 2 ≤ P.natDegree → AreaA1 → ImprovKMT P →
      ∀ (C₀ : ℕ) (r : ℝ≥0), 1 ≤ C₀ → (2 : ℝ≥0) < r →
        ∃ c : ℝ, 0 < c ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
          PieceBoundOn ρ P C₀ 2 2 1 r (gainW c) CaseHH)
    (hl : ∀ (P : ℤ[X]), 2 ≤ P.natDegree → AreaA1 → ImprovKMT P →
      ∀ (C₀ : ℕ) (r : ℝ≥0), 1 ≤ C₀ → (2 : ℝ≥0) < r →
        ∃ c : ℝ, 0 < c ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
          PieceBoundOn ρ P C₀ 2 2 1 r (gainW c) CaseRest) :
    AreaA6 := by
  intro P hd hA1 hI C₀ r hC₀ hr
  obtain ⟨ch, hch, ρh, hρh, Hh⟩ := hh P hd hA1 hI C₀ r hC₀ hr
  obtain ⟨cl, hcl, ρl, hρl, Hl⟩ := hl P hd hA1 hI C₀ r hC₀ hr
  refine ⟨min ch cl, lt_min hch hcl, min ρh ρl, lt_min hρh hρl, fun ρ hρ0 hρ => ?_⟩
  refine pieceBound_of_hh_and_rest ?_ ?_
  · refine pieceBoundOn_mono_weight
      (w := gainW (min ch cl)) (w' := gainW ch) ?_
      (Hh ρ hρ0 (le_trans hρ (min_le_left _ _)))
    exact gainW_le_of_le (lt_min hch hcl).le lmax_cast_nonneg (min_le_left _ _)
  · refine pieceBoundOn_mono_weight
      (w := gainW (min ch cl)) (w' := gainW cl) ?_
      (Hl ρ hρ0 (le_trans hρ (min_le_right _ _)))
    exact gainW_le_of_le (lt_min hch hcl).le lmax_cast_nonneg (min_le_right _ _)

end

end Work.KMTPlan.A6
