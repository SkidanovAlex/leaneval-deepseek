/-
# The good-scale non-aliasing input for the `G`-side vanishing

This file proves `Work.KMTPlan.A6.hhVanishingG`.  The point of the lemma is the *scale
arithmetic* converting the good-scale condition of `Work.KMTPlan.A6.hhGood` plus the
size-driven non-aliasing hypothesis `hNA` into the two hypotheses of the contract's
`Work.KMTPlan.Sub.VanishingG`:

* the height hypothesis `max k₂ L + 2 ≤ Log N`, and
* the non-aliasing of `(ℚ/ℤ)_{≤l₂} ∪ (ℚ/ℤ)_{≤L}` at the *rescaled* scale
  `d·(-Log N + max k₂ L) + 1`, `d = P.natDegree ≥ 2`.

The dependence on `d ≥ 2` is what makes the latter work: writing `LN = Log N`, `m = max k₂ L`,
`M` the height of the good-scale condition and `M' = max l₂ L`, the good-scale condition gives
`M + R·2^{ρM} + 2 ≤ LN` and hence `m + 2 ≤ M + 2 ≤ LN - 2`, so `-LN + m ≤ -2 < 0` and, since
`d ≥ 2`,

  `d·(-LN + m) + 1 + C·2^{ρM'} ≤ 2·(-LN + m) + 1 + R·2^{ρM}
      ≤ (-2LN + 2M) + 1 + (LN - M - 2) = -LN + M - 1 ≤ -3 < 0`,

using `C ≤ R`, `2^{ρM'} ≤ 2^{ρM}` and `M' ≤ M`.  Thus `hNA` applies at the very scale requested
by `VanishingG`.
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

/-- **The scale arithmetic behind `hhVanishingG`.**  Under the good-scale condition at the height
`M`, the size-driven non-aliasing threshold `-C·2^{ρ·max l₂ L}` for the frequency set
`(ℚ/ℤ)_{≤l₂} ∪ (ℚ/ℤ)_{≤L}` sits strictly above the rescaled scale
`d·(-Log N + max k₂ L) + 1` of `Sub.VanishingG`, for every `d ≥ 2`. -/
theorem hhVanishingG_arith {ρ R C : ℝ} {M N l₂ L k₂ : ℕ} {d : ℤ}
    (hρ : 0 < ρ) (hR1 : 1 ≤ R) (hRC : C ≤ R) (hd : 2 ≤ d)
    (hlM : l₂ ≤ M) (hLM : L ≤ M) (hkM : k₂ ≤ M)
    (hgood : (M : ℝ) + R * (2 : ℝ) ^ (ρ * (M : ℝ)) + 2
        ≤ ((Work.Analysis.EndVar.logN N : ℤ) : ℝ)) :
    ((d * (-(Work.Analysis.EndVar.logN N) + (max k₂ L : ℤ)) + 1 : ℤ) : ℝ)
        + C * (2 : ℝ) ^ (ρ * (max l₂ L : ℝ)) < 0 := by
  have hR0 : (0 : ℝ) ≤ R := le_trans zero_le_one hR1
  have hpowM : (0 : ℝ) ≤ R * (2 : ℝ) ^ (ρ * (M : ℝ)) :=
    mul_nonneg hR0 (Real.rpow_nonneg (by norm_num) _)
  -- the good-scale condition implies `M + 2 ≤ Log N`
  have hML : (M : ℝ) + 2 ≤ ((Work.Analysis.EndVar.logN N : ℤ) : ℝ) := by linarith
  have hm_le : (max k₂ L : ℝ) ≤ (M : ℝ) := by exact_mod_cast (max_le hkM hLM)
  have hml_le : (max l₂ L : ℝ) ≤ (M : ℝ) := by exact_mod_cast (max_le hlM hLM)
  -- hence `-Log N + max k₂ L ≤ -2 ≤ 0`
  have ha : -(((Work.Analysis.EndVar.logN N : ℤ) : ℝ)) + (max k₂ L : ℝ) ≤ -2 := by linarith
  have ha0 : -(((Work.Analysis.EndVar.logN N : ℤ) : ℝ)) + (max k₂ L : ℝ) ≤ 0 := by linarith
  -- monotonicity of the rpow and of the factor `R`
  have hpow_le : (2 : ℝ) ^ (ρ * (max l₂ L : ℝ)) ≤ (2 : ℝ) ^ (ρ * (M : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_left hml_le hρ.le)
  have hCpow : C * (2 : ℝ) ^ (ρ * (max l₂ L : ℝ)) ≤ R * (2 : ℝ) ^ (ρ * (M : ℝ)) :=
    (mul_le_mul_of_nonneg_right hRC (Real.rpow_nonneg (by norm_num) _)).trans
      (mul_le_mul_of_nonneg_left hpow_le hR0)
  have hRpow : R * (2 : ℝ) ^ (ρ * (M : ℝ))
      ≤ ((Work.Analysis.EndVar.logN N : ℤ) : ℝ) - (M : ℝ) - 2 := by linarith
  -- `d ≥ 2` makes the (negative) factor `-Log N + max k₂ L` more negative
  have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdmul : (d : ℝ) * (-(((Work.Analysis.EndVar.logN N : ℤ) : ℝ)) + (max k₂ L : ℝ))
      ≤ 2 * (-(((Work.Analysis.EndVar.logN N : ℤ) : ℝ)) + (max k₂ L : ℝ)) :=
    mul_le_mul_of_nonpos_right hd2 ha0
  have hcast : ((d * (-(Work.Analysis.EndVar.logN N) + (max k₂ L : ℤ)) + 1 : ℤ) : ℝ)
      = (d : ℝ) * (-(((Work.Analysis.EndVar.logN N : ℤ) : ℝ)) + (max k₂ L : ℝ)) + 1 := by
    push_cast
    ring
  rw [hcast]
  linarith

/-- **The `G`-side good-scale non-aliasing input.**  From the size-driven non-aliasing hypothesis
`hNA` and the good-scale condition `hhGood R ρ M N` at a height `M` dominating `l₂`, `k₂` and `L`,
the contract's `Sub.VanishingG` hypothesis applies: the IW projection at the rescaled coupled
height kills the piece `G^{0,l₂,k₂}_N g`. -/
theorem hhVanishingG (ρ R C : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hR1 : 1 ≤ R) (hRC : C ≤ R)
    (hNA : ∀ (l₂ L : ℕ) (K : ℤ), (K : ℝ) + C * (2 : ℝ) ^ (ρ * (max l₂ L : ℝ)) < 0 →
      Work.Analysis.IonescuWainger.NonAliasing K
        (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂
          ∪ Work.Analysis.IonescuWainger.iwArithFreqs ρ L))
    (hvanG : Work.KMTPlan.Sub.VanishingG)
    (P : Polynomial ℤ) (hd : 2 ≤ Polynomial.natDegree P)
    (l₂ k₂ L N M : ℕ) (g : ℤ → ℂ) (hk₂ : 1 ≤ k₂) (hcase : L < l₂ ∨ L + 2 ≤ k₂)
    (hLM : L ≤ M) (hkM : k₂ ≤ M) (hlM : l₂ ≤ M) (hgood : Work.KMTPlan.A6.hhGood R ρ M N)
    (hg : MeasureTheory.MemLp g 2 MeasureTheory.Measure.count) :
    Work.KMTContract.kmtProj ρ L
      ((Polynomial.natDegree P : ℤ) * (-(Work.Analysis.EndVar.logN N) + (L : ℤ)))
      (Work.Analysis.EndVar.Gpiece (Work.KMTContract.kmtPj ρ) (Polynomial.natDegree P : ℤ) 0 l₂
        (k₂ : ℤ) N g) = 0 := by
  have hgood' : (M : ℝ) + R * (2 : ℝ) ^ (ρ * (M : ℝ)) + 2
      ≤ ((Work.Analysis.EndVar.logN N : ℤ) : ℝ) := by
    simpa only [Work.KMTPlan.A6.hhGood] using hgood
  have hpowM : (0 : ℝ) ≤ R * (2 : ℝ) ^ (ρ * (M : ℝ)) :=
    mul_nonneg (le_trans zero_le_one hR1) (Real.rpow_nonneg (by norm_num) _)
  -- `M + 2 ≤ Log N` as integers
  have hM_LN : ((M : ℤ) : ℝ) + 2 ≤ ((Work.Analysis.EndVar.logN N : ℤ) : ℝ) := by
    push_cast
    linarith
  have hM_LN' : (M : ℤ) + 2 ≤ Work.Analysis.EndVar.logN N := by
    exact_mod_cast hM_LN
  -- the height hypothesis of `Sub.VanishingG`
  have hmM : max k₂ L ≤ M := max_le hkM hLM
  have hheight : max (k₂ : ℤ) (L : ℤ) + 2 ≤ Work.Analysis.EndVar.logN N := by
    have hcast : ((max k₂ L : ℕ) : ℤ) = max (k₂ : ℤ) (L : ℤ) := by
      simp only [Nat.cast_max]
    have hle : max (k₂ : ℤ) (L : ℤ) ≤ (M : ℤ) := by
      rw [← hcast]; exact_mod_cast hmM
    linarith
  -- the non-aliasing scale requested by `Sub.VanishingG` is within the range of `hNA`
  have hKineq := hhVanishingG_arith (ρ := ρ) (R := R) (C := C) (M := M) (N := N)
    (l₂ := l₂) (L := L) (k₂ := k₂) (d := (Polynomial.natDegree P : ℤ))
    hρ hR1 hRC (by exact_mod_cast hd) hlM hLM hkM hgood'
  have hNAK : Work.Analysis.IonescuWainger.NonAliasing
      ((Polynomial.natDegree P : ℤ) * (-(Work.Analysis.EndVar.logN N) + (max k₂ L : ℤ)) + 1)
      (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂
        ∪ Work.Analysis.IonescuWainger.iwArithFreqs ρ L) :=
    hNA l₂ L _ hKineq
  exact hvanG ρ hρ hρ1 P l₂ k₂ L N g hk₂ hcase hheight hNAK hg

end

end Work.KMTPlan.A6
