/-
# The good-scale non-aliasing input for the `F`-side vanishing

This file proves `Work.KMTPlan.A6.hhVanishingF`.  Exactly as in `hhVanishingG.lean`, the point of
the lemma is the *scale arithmetic* converting the good-scale condition `hhGood R ρ M N` plus the
size-driven non-aliasing hypothesis `hNA` into the two hypotheses of the contract's
`Work.KMTPlan.Sub.VanishingF`:

* the height hypothesis `max k₁ L + 2 ≤ Log N`, and
* the non-aliasing of `(ℚ/ℤ)_{≤l₁} ∪ (ℚ/ℤ)_{≤L}` at the scale `max k₁ L - Log N + 1`.

Here the rescaling factor of the `G`-side is `d = 1`, which is why the scale requested by
`Sub.VanishingF` is `max k₁ L - Log N + 1` (no factor `d`); with `LN = Log N`, `m = max k₁ L`,
`M' = max l₁ L` the good-scale condition gives `M + R·2^{ρM} + 2 ≤ LN`, hence `m + 2 ≤ M + 2 ≤ LN`
and

  `m - LN + 1 + C·2^{ρM'} ≤ M - LN + 1 + R·2^{ρM}`
      `≤ M - (M + R·2^{ρM} + 2) + 1 + R·2^{ρM} = -1 < 0`,

using `C ≤ R`, `2^{ρM'} ≤ 2^{ρM}` and `M' ≤ M`.  Thus `hNA` applies at the very scale requested by
`VanishingF`, and `hvanF` gives the conclusion.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.HHBasic

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators

/-- **The height hypothesis of `Sub.VanishingF`.**  The good-scale condition at a height `M`
dominating `k₁` and `L` gives `max k₁ L + 2 ≤ Log N`. -/
theorem hhVanishingF_height {R ρ : ℝ} (hR0 : 0 ≤ R) (hρ0 : 0 ≤ ρ) {M N L k₁ : ℕ}
    (hLM : L ≤ M) (hkM : k₁ ≤ M)
    (hgood : (M : ℝ) + R * (2 : ℝ) ^ (ρ * (M : ℝ)) + 2
        ≤ ((Work.Analysis.EndVar.logN N : ℤ) : ℝ)) :
    max (k₁ : ℤ) (L : ℤ) + 2 ≤ Work.Analysis.EndVar.logN N := by
  -- the good-scale condition implies `M + 2 ≤ Log N` as integers
  have hML : (M : ℤ) + 2 ≤ Work.Analysis.EndVar.logN N := by
    have h := mul_nonneg hR0 (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (ρ * (M : ℝ)))
    have h' : ((M : ℤ) : ℝ) + 2 ≤ ((Work.Analysis.EndVar.logN N : ℤ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast h'
  have hmM : max k₁ L ≤ M := max_le hkM hLM
  have hle : max (k₁ : ℤ) (L : ℤ) ≤ (M : ℤ) := by
    have hcast : ((max k₁ L : ℕ) : ℤ) = max (k₁ : ℤ) (L : ℤ) := by simp only [Nat.cast_max]
    rw [← hcast]
    exact_mod_cast hmM
  linarith

/-- **The scale arithmetic behind `hhVanishingF`.**  Under the good-scale condition at the height
`M`, the size-driven non-aliasing threshold `-C·2^{ρ·max l₁ L}` for the frequency set
`(ℚ/ℤ)_{≤l₁} ∪ (ℚ/ℤ)_{≤L}` sits strictly above the scale `max k₁ L - Log N + 1` of
`Sub.VanishingF`. -/
theorem hhVanishingF_arith {ρ R C : ℝ} {M N l₁ L k₁ : ℕ}
    (hρ : 0 < ρ) (hR1 : 1 ≤ R) (hRC : C ≤ R)
    (hlM : l₁ ≤ M) (hLM : L ≤ M) (hkM : k₁ ≤ M)
    (hgood : (M : ℝ) + R * (2 : ℝ) ^ (ρ * (M : ℝ)) + 2
        ≤ ((Work.Analysis.EndVar.logN N : ℤ) : ℝ)) :
    (((max (k₁ : ℤ) (L : ℤ) - Work.Analysis.EndVar.logN N + 1 : ℤ)) : ℝ)
        + C * (2 : ℝ) ^ (ρ * (max l₁ L : ℝ)) < 0 := by
  have hR0 : (0 : ℝ) ≤ R := le_trans zero_le_one hR1
  -- the good-scale condition implies `M + 2 ≤ Log N`
  have hML : (M : ℝ) + 2 ≤ ((Work.Analysis.EndVar.logN N : ℤ) : ℝ) := by
    have h := mul_nonneg hR0 (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (ρ * (M : ℝ)))
    linarith
  have hmk : max (k₁ : ℝ) (L : ℝ) ≤ (M : ℝ) := by
    have hcast : ((max k₁ L : ℕ) : ℝ) = max (k₁ : ℝ) (L : ℝ) := by push_cast; ring
    rw [← hcast]; exact_mod_cast (max_le hkM hLM)
  have hml : max (l₁ : ℝ) (L : ℝ) ≤ (M : ℝ) := by
    have hcast : ((max l₁ L : ℕ) : ℝ) = max (l₁ : ℝ) (L : ℝ) := by push_cast; ring
    rw [← hcast]; exact_mod_cast (max_le hlM hLM)
  -- monotonicity of the rpow and of the factor `R`
  have hpow_le : (2 : ℝ) ^ (ρ * (max l₁ L : ℝ)) ≤ (2 : ℝ) ^ (ρ * (M : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_left hml hρ.le)
  have hCpow : C * (2 : ℝ) ^ (ρ * (max l₁ L : ℝ)) ≤ R * (2 : ℝ) ^ (ρ * (M : ℝ)) :=
    (mul_le_mul_of_nonneg_right hRC (Real.rpow_nonneg (by norm_num) _)).trans
      (mul_le_mul_of_nonneg_left hpow_le hR0)
  have hcast : ((max (k₁ : ℤ) (L : ℤ) - Work.Analysis.EndVar.logN N + 1 : ℤ) : ℝ)
      = max (k₁ : ℝ) (L : ℝ) - ((Work.Analysis.EndVar.logN N : ℤ) : ℝ) + 1 := by
    push_cast
    ring
  rw [hcast]
  linarith

/-- **The `F`-side good-scale non-aliasing input.**  From the size-driven non-aliasing hypothesis
`hNA` and the good-scale condition `hhGood R ρ M N` at a height `M` dominating `l₁`, `k₁` and `L`,
the contract's `Sub.VanishingF` hypothesis applies: the IW projection at the coupled height
`(L, -Log N + L)` kills the difference piece `F^{0,l₁,k₁}_N f`. -/
theorem hhVanishingF (ρ R C : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hR1 : 1 ≤ R) (hRC : C ≤ R)
    (hNA : ∀ (l₁ L : ℕ) (K : ℤ), (K : ℝ) + C * (2 : ℝ) ^ (ρ * (max l₁ L : ℝ)) < 0 →
      Work.Analysis.IonescuWainger.NonAliasing K
        (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁
          ∪ Work.Analysis.IonescuWainger.iwArithFreqs ρ L))
    (hvanF : Work.KMTPlan.Sub.VanishingF)
    (l₁ k₁ L N M : ℕ) (f : ℤ → ℂ) (hk₁ : 1 ≤ k₁) (hcase : L < l₁ ∨ L + 2 ≤ k₁)
    (hLM : L ≤ M) (hkM : k₁ ≤ M) (hlM : l₁ ≤ M) (hgood : Work.KMTPlan.A6.hhGood R ρ M N)
    (hf : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count) :
    Work.KMTContract.kmtProj ρ L (-(Work.Analysis.EndVar.logN N) + (L : ℤ))
      (Work.Analysis.EndVar.Fpiece (Work.KMTContract.kmtPj ρ) 0 l₁ (k₁ : ℤ) N f) = 0 := by
  have hgood' : (M : ℝ) + R * (2 : ℝ) ^ (ρ * (M : ℝ)) + 2
      ≤ ((Work.Analysis.EndVar.logN N : ℤ) : ℝ) := by
    simpa only [Work.KMTPlan.A6.hhGood] using hgood
  -- the height hypothesis of `Sub.VanishingF`
  have hw := hhVanishingF_height (le_trans zero_le_one hR1) hρ.le hLM hkM hgood'
  -- the non-aliasing scale requested by `Sub.VanishingF` is within the range of `hNA`
  have hKineq := hhVanishingF_arith (ρ := ρ) (R := R) (C := C) (M := M) (N := N)
    (l₁ := l₁) (L := L) (k₁ := k₁) hρ hR1 hRC hlM hLM hkM hgood'
  have hNAK : Work.Analysis.IonescuWainger.NonAliasing
      (max (k₁ : ℤ) (L : ℤ) - Work.Analysis.EndVar.logN N + 1)
      (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁
        ∪ Work.Analysis.IonescuWainger.iwArithFreqs ρ L) :=
    hNA l₁ L _ hKineq
  exact hvanF ρ hρ hρ1 l₁ k₁ L N f hk₁ hcase hw hNAK hf

end

end Work.KMTPlan.A6
