import Mathlib
import Submission.Work.FIArea4.A4varbounds
import Submission.Work.FIArea4.Vflip.Vvar_flip_mid
import Submission.Work.FIArea4.Vflip.Vflip_large_full

/-!
# FI Proposition 12.1 (12.3)–(12.4), assembled

This module assembles the *proved* pieces into the all-`ε` form of Friedlander–Iwaniec's
Proposition 12.1:

`Work.FIArea4.p12_all : Work.FIArea4.p14Prop121All`.

The two halves are
* `Work.FIArea4.Vflip.Vvar_flip_mid` (the range `D ≤ R*S`: the FI §12 "flipping of moduli"
  argument via `Vflip_large_full`/`Vflip_large_dyadic`, using `h11 : p14Prop111All`), and
* `Work.FIArea4.Vflip.vlf_Vvar_le_of_mul_lt_D` (the range `R*S < D`, where the crude bound
  `Vvar ≤ 33·D·L₂` already suffices).

The hypothesis `p14Prop111All` is supplied by the *proved* module
`Submission.Work.FIArea4.prop_11_1_box`.
-/

namespace Work.FIArea4

open Finset
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-- `p14T12 D R S ε ≥ D` for `1 ≤ D`.  Only the first term of the bracket is used. -/
lemma p12_T12_ge_D (D R S : ℕ) (hD : 1 ≤ D) (hR : 1 ≤ R) (hS : 1 ≤ S) (ε : ℝ) :
    (D : ℝ) ≤ p14T12 D R S ε := by
  have hDnn : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hS1 : (1 : ℝ) ≤ (S : ℝ) := by exact_mod_cast hS
  have hRS1 : (1 : ℝ) ≤ (R : ℝ) * (S : ℝ) := by nlinarith
  have hlog : 0 ≤ Real.log (2 * (R : ℝ) * (S : ℝ)) + 1 := by
    have h1 : (1 : ℝ) ≤ 2 * (R : ℝ) * (S : ℝ) := by linarith
    have := Real.log_nonneg h1
    linarith
  have hRSnn : (0 : ℝ) ≤ (R : ℝ) * (S : ℝ) := by linarith
  have hterm1 : 0 ≤ (D : ℝ) ^ ((1 : ℝ) / 3) * ((R : ℝ) * (S : ℝ)) ^ ((2 : ℝ) / 3)
      * (Real.log (2 * (R : ℝ) * (S : ℝ)) + 1) ^ (4 : ℕ) := by positivity
  have hterm2 : 0 ≤ ((D : ℝ)⁻¹ * ((R : ℝ) * (S : ℝ)) ^ ((3 : ℝ) / 2)
      + (R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4) + (S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4))
      * (((R : ℝ) * (S : ℝ)) ^ ε) := by
    have h1 : 0 ≤ (R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4) := by positivity
    have h2 : 0 ≤ (S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4) := by positivity
    have h3 : 0 ≤ (D : ℝ)⁻¹ * ((R : ℝ) * (S : ℝ)) ^ ((3 : ℝ) / 2) := by positivity
    have h4 : 0 ≤ ((R : ℝ) * (S : ℝ)) ^ ε := Real.rpow_nonneg hRSnn ε
    exact mul_nonneg (by linarith) h4
  rw [p14T12]
  linarith

/-- `p14T12 D R S ε > 0` for `1 ≤ D`. -/
lemma p12_T12_pos (D R S : ℕ) (hD : 1 ≤ D) (hR : 1 ≤ R) (hS : 1 ≤ S) (ε : ℝ) :
    0 < p14T12 D R S ε := by
  have h1 : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  exact lt_of_lt_of_le h1 (p12_T12_ge_D D R S hD hR hS ε)

/-- **FI Proposition 12.1 (12.3)–(12.4), all-`ε` form**, conditional on Proposition 11.1 in its
all-`ε` form (which is what the §12 argument needs; the *unconditional* form is
`Work.FIArea4.p12_all` in `Submission/Work/FIArea4/p12_uncond.lean`, fed by the proved
`Work.FIArea4.prop_11_1_box`). -/
theorem p12_all_of_h11 (h11 : Work.FIArea4.p14Prop111All) : Work.FIArea4.p14Prop121All := by
  intro ε hε
  obtain ⟨C₁, hC₁, h₁⟩ := Vflip.Vvar_flip_mid ε hε h11
  refine ⟨max C₁ 33 + 1, by positivity, ?_⟩
  intro D R S α hD hR hS hcop
  have hTpos : (0 : ℝ) < p14T12 D R S ε := p12_T12_pos D R S hD hR hS ε
  have hTge : (D : ℝ) ≤ p14T12 D R S ε := p12_T12_ge_D D R S hD hR hS ε
  have hEnn : (0 : ℝ) ≤ p14Ener R S α := by
    rw [p14Ener]
    exact Finset.sum_nonneg (fun r _ => Finset.sum_nonneg (fun s _ =>
      mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)))
  have hLnn : (0 : ℝ) ≤ p14L2 R S α := by
    rw [p14L2]
    exact Finset.sum_nonneg (fun r _ => Finset.sum_nonneg (fun s _ => Complex.normSq_nonneg _))
  have hLE : p14L2 R S α ≤ p14Ener R S α := Vflip.p14L2_le_p14Ener R S α
  by_cases hDS : D ≤ R * S
  · refine (h₁ D R S α hD hR hS hDS hcop).trans ?_
    have hC1le : C₁ ≤ max C₁ 33 + 1 := by
      have : C₁ ≤ max C₁ 33 := le_max_left _ _
      linarith
    have : 0 ≤ p14T12 D R S ε * p14Ener R S α := mul_nonneg hTpos.le hEnn
    nlinarith [this]
  · have hlt : R * S < D := lt_of_not_ge hDS
    have h₂ := Vflip.vlf_Vvar_le_of_mul_lt_D D R S α hD hR hS hlt hcop
    refine h₂.trans ?_
    have hmax : (33 : ℝ) ≤ max C₁ 33 + 1 := by
      have : (33 : ℝ) ≤ max C₁ 33 := le_max_right _ _
      linarith
    have hDnn : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
    -- `33 * D * L2 ≤ (max C₁ 33 + 1) * T12 * Ener`
    have step : (33 : ℝ) * (D : ℝ) * p14L2 R S α
        ≤ (max C₁ 33 + 1) * p14T12 D R S ε * p14Ener R S α := by
      have h1 : (33 : ℝ) * (D : ℝ) * p14L2 R S α
          ≤ (max C₁ 33 + 1) * (D : ℝ) * p14L2 R S α := by
        have : (0 : ℝ) ≤ (D : ℝ) * p14L2 R S α := mul_nonneg hDnn hLnn
        nlinarith [this]
      have h2 : (max C₁ 33 + 1) * (D : ℝ) * p14L2 R S α
          ≤ (max C₁ 33 + 1) * p14T12 D R S ε * p14Ener R S α := by
        have hMw : (0 : ℝ) ≤ max C₁ 33 + 1 := by linarith [hmax]
        have hDLE : (D : ℝ) * p14L2 R S α ≤ p14T12 D R S ε * p14Ener R S α := by
          calc (D : ℝ) * p14L2 R S α ≤ p14T12 D R S ε * p14L2 R S α :=
                mul_le_mul_of_nonneg_right hTge hLnn
            _ ≤ p14T12 D R S ε * p14Ener R S α :=
                mul_le_mul_of_nonneg_left hLE hTpos.le
        calc (max C₁ 33 + 1) * (D : ℝ) * p14L2 R S α
            = (max C₁ 33 + 1) * ((D : ℝ) * p14L2 R S α) := by ring
          _ ≤ (max C₁ 33 + 1) * (p14T12 D R S ε * p14Ener R S α) :=
                mul_le_mul_of_nonneg_left hDLE hMw
          _ = (max C₁ 33 + 1) * p14T12 D R S ε * p14Ener R S α := by ring
      exact h1.trans h2
    exact step

end

end Work.FIArea4
