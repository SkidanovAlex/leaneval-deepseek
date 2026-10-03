/-
# The `ℓ¹(ℤ²)`-mass of the bounded-height model kernel `mdlKernel`

`Work.KMTPlan.A6.PieceBoundedH.mdlKernel ρ P l₁ l₂ k₁ k₂` is the kernel of the §6 twisted
bilinear multiplier `Btwist` of Krause--Mirek--Tao (Annals 195 (3) 2022),

  `K(j₁,j₂) = arithKernel ρ P Q_L l₁ l₂ j₁ j₂ · cw m_* j₁ · cw m̃_* j₂`,
  `m_* = mStarF u`, `m̃_* = mStargF P.natDegree u`, `u = uScale ρ (lcL l₁ l₂ k₁ k₂)`,

and this file proves `KernelMassBound ρ P B`: the `ℓ¹(ℤ²)`-mass `∑'_{j₁,j₂} ‖K(j₁,j₂)‖` is
finite and bounded by a constant depending only on `ρ` and `B`, uniformly over the quadruples
`(l₁,l₂,k₁,k₂)` with `lcL l₁ l₂ k₁ k₂ ≤ B`.

## The three ingredients

* the arithmetic kernel is bounded *uniformly in the summation variables* by the product of the
  cardinalities of the two arithmetic frequency sets,
  `‖arithKernel … j₁ j₂‖ ≤ |(ℚ/ℤ)_{≤l₁}| · |(ℚ/ℤ)_{≤l₂}|`
  (`Work.KMTPlan.A6.vpc_summable_arithKernel_cw`, `vpc_tsum_norm_arithKernel_cw_le`);
* the two coefficient kernels `cw m_*`, `cw m̃_*` are `ℓ¹(ℤ)` with masses bounded **uniformly in
  `u`** by the single constant `Cs` of `Work.KMTPlan.A6.vpc_exists_cw_mStarF_tsum_le`
  (this is the paper's `crude-mult`(ii) applied to the rescaled cutoff; here the second factor is
  eliminated with the identity `mStargF d u = mStarF (d·u)`,
  `Work.KMTAreas.A7.mStargF_eq_mStarF`);
* the height hypothesis `lcL l₁ l₂ k₁ k₂ ≤ B` gives `l₁, l₂ ≤ B`, so by monotonicity of the
  arithmetic frequency sets (`iwArithFreqs_mono`, which needs `0 < ρ ≤ 1` — precisely the two
  hypotheses of the statement) the two cardinalities are at most `|(ℚ/ℤ)_{≤B}|`.

The constant is therefore `max 1 (|(ℚ/ℤ)_{≤B}|² · Cs²)`, which indeed depends only on `ρ` and `B`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.PieceBoundedH.Defs
import Submission.Work.KMTPlan.A6.vpc_tsum_norm_arithKernel_cw_le
import Submission.Work.KMTPlan.A6.vpc_exists_cw_mStarF_tsum_le
import Submission.Work.KMTAreas.A7.FibrePlumbing

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6.PieceBoundedH

noncomputable section

open scoped BigOperators
open Work.KMTAreas.A7

/-- The arithmetic frequency set `(ℚ/ℤ)_{≤L}`, abbreviated. -/
local notation "AF" => Work.Analysis.IonescuWainger.iwArithFreqs

theorem kernelMassBound (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (P : Polynomial ℤ) (B : ℕ) : Work.KMTPlan.A6.PieceBoundedH.KernelMassBound ρ P B := by
  -- the uniform `ℓ¹`-mass of the coefficients of the window `m_* = mStarF u`
  obtain ⟨Cs, hCs0, hCs⟩ := Work.KMTPlan.A6.vpc_exists_cw_mStarF_tsum_le
  have hCsnn : 0 ≤ Cs := hCs0.le
  refine ⟨max 1 (((AF ρ B).card : ℝ) ^ 2 * Cs * Cs),
    lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro l₁ l₂ k₁ k₂ hLB
  -- the height hypothesis controls the two arithmetic heights
  have hl₁ : l₁ ≤ B := le_trans (le_trans (le_max_left l₁ l₂) (le_max_left _ _)) hLB
  have hl₂ : l₂ ≤ B := le_trans (le_trans (le_max_right l₁ l₂) (le_max_left _ _)) hLB
  have hc₁ : (((AF ρ l₁).card : ℕ) : ℝ) ≤ (((AF ρ B).card : ℕ) : ℝ) := by
    exact_mod_cast Finset.card_le_card
      (Work.Analysis.IonescuWainger.iwArithFreqs_mono hρ hρ1 hl₁)
  have hc₂ : (((AF ρ l₂).card : ℕ) : ℝ) ≤ (((AF ρ B).card : ℕ) : ℝ) := by
    exact_mod_cast Finset.card_le_card
      (Work.Analysis.IonescuWainger.iwArithFreqs_mono hρ hρ1 hl₂)
  -- the two coefficient kernels, with masses bounded by the single `u`-independent constant `Cs`
  have hu₁ : Summable (fun j : ℤ => ‖cw (mStarF (uScale ρ (lcL l₁ l₂ k₁ k₂))) j‖) := (hCs _).1
  have hu₁b : (∑' j : ℤ, ‖cw (mStarF (uScale ρ (lcL l₁ l₂ k₁ k₂))) j‖) ≤ Cs := (hCs _).2
  have huw : mStargF P.natDegree (uScale ρ (lcL l₁ l₂ k₁ k₂))
      = mStarF (P.natDegree * uScale ρ (lcL l₁ l₂ k₁ k₂)) :=
    mStargF_eq_mStarF P _
  have hu₂ : Summable
      (fun j : ℤ => ‖cw (mStarF (P.natDegree * uScale ρ (lcL l₁ l₂ k₁ k₂))) j‖) :=
    (hCs (P.natDegree * uScale ρ (lcL l₁ l₂ k₁ k₂))).1
  have hu₂b :
      (∑' j : ℤ, ‖cw (mStarF (P.natDegree * uScale ρ (lcL l₁ l₂ k₁ k₂))) j‖) ≤ Cs :=
    (hCs (P.natDegree * uScale ρ (lcL l₁ l₂ k₁ k₂))).2
  constructor
  · -- summability of the kernel mass
    have hs : Summable fun p : ℤ × ℤ =>
        ‖Work.KMTAreas.A7.arithKernel ρ P (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) l₁ l₂
            p.1 p.2 * cw (mStarF (uScale ρ (lcL l₁ l₂ k₁ k₂))) p.1
          * cw (mStarF (P.natDegree * uScale ρ (lcL l₁ l₂ k₁ k₂))) p.2‖ :=
      Work.KMTPlan.A6.vpc_summable_arithKernel_cw ρ P l₁ l₂
        (m₁ := mStarF (uScale ρ (lcL l₁ l₂ k₁ k₂)))
        (m₂ := mStarF (P.natDegree * uScale ρ (lcL l₁ l₂ k₁ k₂))) hu₁ hu₂
    simpa only [mdlKernel, huw] using hs
  · -- the `ℓ¹(ℤ²)`-mass bound
    have hb := Work.KMTPlan.A6.vpc_tsum_norm_arithKernel_cw_le ρ P l₁ l₂
      (m₁ := mStarF (uScale ρ (lcL l₁ l₂ k₁ k₂)))
      (m₂ := mStarF (P.natDegree * uScale ρ (lcL l₁ l₂ k₁ k₂)))
      (A := Cs) (B := Cs) hu₁ hu₁b hu₂ hu₂b hCsnn hCsnn
    have hb' : (∑' p : ℤ × ℤ, ‖mdlKernel ρ P l₁ l₂ k₁ k₂ p.1 p.2‖)
        ≤ (((AF ρ l₁).card : ℕ) : ℝ) * (((AF ρ l₂).card : ℕ) : ℝ) * Cs * Cs := by
      simpa only [mdlKernel, huw] using hb
    calc (∑' p : ℤ × ℤ, ‖mdlKernel ρ P l₁ l₂ k₁ k₂ p.1 p.2‖)
        ≤ (((AF ρ l₁).card : ℕ) : ℝ) * (((AF ρ l₂).card : ℕ) : ℝ) * Cs * Cs := hb'
      _ ≤ (((AF ρ B).card : ℕ) : ℝ) ^ 2 * Cs * Cs := by
          have h1 : (((AF ρ l₁).card : ℕ) : ℝ) * (((AF ρ l₂).card : ℕ) : ℝ)
              ≤ (((AF ρ B).card : ℕ) : ℝ) * (((AF ρ B).card : ℕ) : ℝ) :=
            mul_le_mul hc₁ hc₂ (Nat.cast_nonneg _) (le_trans (Nat.cast_nonneg _) hc₁)
          have h3 : (((AF ρ l₁).card : ℕ) : ℝ) * (((AF ρ l₂).card : ℕ) : ℝ) * Cs * Cs
              ≤ (((AF ρ B).card : ℕ) : ℝ) * (((AF ρ B).card : ℕ) : ℝ) * Cs * Cs :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hCsnn) hCsnn
          have h4 : (((AF ρ B).card : ℕ) : ℝ) * (((AF ρ B).card : ℕ) : ℝ) * Cs * Cs
              = (((AF ρ B).card : ℕ) : ℝ) ^ 2 * Cs * Cs := by ring
          exact h3.trans (le_of_eq h4)
      _ ≤ max 1 (((AF ρ B).card : ℝ) ^ 2 * Cs * Cs) := le_max_right _ _

end

end Work.KMTPlan.A6.PieceBoundedH
