/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Mathlib
import Submission.Work.Peluse.Nodes

/-!
# Assembly helpers for `Work.Peluse.ulowering_of`

The conclusion of `PeluseULowering` is a display with two parameters `C, K`; the three chapters
that prove it (`Ulower/small_shift`, `Ulower/gap_regime`, and the two balanced chapters
`Ulower/degree_lowering_v2` + `Ulower/U2_to_progression`) produce it with different constants.
`Display` names the inner claim once and for all, and `display_mono` shows that it is *monotone*
in `(C,K)`: increasing `K` decreases the two left-hand sides (all bases are `≤ 1`) and increases
the right-hand sides (all bases are `≥ 1`).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped BigOperators
open Polynomial

namespace Work.Peluse.Ulower

noncomputable section

open Work.Peluse

/-- The inner claim of `PeluseULowering` for fixed constants `C,K` and data `A',N,N₀,D,f₁,δ`:
`DisplayAt` at the scale `N ^ P.natDegree`. -/
def Display (P : Polynomial ℤ) (C K : ℕ) (A' : ℝ) (N N₀ D : ℕ) (f₁ : ℤ → ℂ) (δ : ℝ) : Prop :=
  ∃ q N' : ℕ, 1 ≤ q ∧
    (q : ℝ) ≤ (C : ℝ) * A' ^ K * ((N : ℝ) ^ P.natDegree / (D : ℝ)) ^ K * (δ⁻¹) ^ K ∧
    1 ≤ N' ∧ N' ≤ N ∧
    δ ^ K * ((D : ℝ) / (N : ℝ) ^ P.natDegree) ^ K * (N : ℝ) ≤
      (C : ℝ) * A' ^ K * ((N : ℝ) ^ P.natDegree / (D : ℝ)) ^ K * (δ⁻¹) ^ K * (N' : ℝ) ∧
    δ ^ K * ((D : ℝ) / (N : ℝ) ^ P.natDegree) ^ K * (N₀ : ℝ) ≤
      (C : ℝ) * A' ^ K * ((N : ℝ) ^ P.natDegree / (D : ℝ)) ^ K * (δ⁻¹) ^ K *
        progAvgSum N' (q : ℤ) f₁

/-- The two bases of the display are monotone in the exponent, in opposite directions. -/
private lemma display_mono {P : Polynomial ℤ} {C C' K K' : ℕ} {A' : ℝ} {N N₀ D : ℕ}
    {f₁ : ℤ → ℂ} {δ : ℝ}
    (hA' : 1 ≤ A') (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hN : 1 ≤ N) (hD1 : 1 ≤ D)
    (hDle : (D : ℝ) ≤ (N : ℝ) ^ P.natDegree) (hC : C ≤ C') (hK : K ≤ K')
    (h : Display P C K A' N N₀ D f₁ δ) : Display P C' K' A' N N₀ D f₁ δ := by
  obtain ⟨q, N', hq1, hq, hN'1, hN'N, h2, h3⟩ := h
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD1)
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hdiv1 : (1 : ℝ) ≤ (N : ℝ) ^ P.natDegree / (D : ℝ) := by
    rw [le_div_iff₀ hDpos]
    simpa using hDle
  have hinv1 : (1 : ℝ) ≤ δ⁻¹ := by rw [one_le_inv₀ hδ0]; exact hδ1
  have hA1 : (1 : ℝ) ≤ A' := hA'
  set b : ℝ := A' * ((N : ℝ) ^ P.natDegree / (D : ℝ)) * δ⁻¹ with hbdef
  set c : ℝ := δ * ((D : ℝ) / (N : ℝ) ^ P.natDegree) with hcdef
  have hb1 : (1 : ℝ) ≤ b := by
    rw [hbdef]
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hA1 hdiv1) hinv1
  have hb0 : (0 : ℝ) < b := lt_of_lt_of_le one_pos hb1
  have hc0 : (0 : ℝ) < c := by
    rw [hcdef]; exact mul_pos hδ0 (div_pos hDpos (pow_pos hNpos _))
  have hc1 : c ≤ 1 := by
    rw [hcdef]
    have hdivle : (D : ℝ) / (N : ℝ) ^ P.natDegree ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact hDle
    nlinarith [hδ1, hdivle, hδ0]
  have hbK : b ^ K ≤ b ^ K' := pow_le_pow_right₀ hb1 hK
  have hcK : c ^ K' ≤ c ^ K := pow_le_pow_of_le_one (le_of_lt hc0) hc1 hK
  have hC' : (C : ℝ) ≤ (C' : ℝ) := by exact_mod_cast hC
  have hbk0 : (0 : ℝ) ≤ b ^ K := by positivity
  have hbk'0 : (0 : ℝ) ≤ b ^ K' := by positivity
  have hck0 : (0 : ℝ) ≤ c ^ K := by positivity
  have hck'0 : (0 : ℝ) ≤ c ^ K' := by positivity
  have hps : (0 : ℝ) ≤ progAvgSum N' (q : ℤ) f₁ := by rw [progAvgSum]; positivity
  have hN0 : (0 : ℝ) ≤ (N₀ : ℝ) := by positivity
  have hN'0 : (0 : ℝ) ≤ (N' : ℝ) := by positivity
  refine ⟨q, N', hq1, ?_, hN'1, hN'N, ?_, ?_⟩
  · -- the bound on `q`, with the larger constants
    have eK : (C : ℝ) * A' ^ K * ((N : ℝ) ^ P.natDegree / (D : ℝ)) ^ K * (δ⁻¹) ^ K
        = (C : ℝ) * b ^ K := by rw [hbdef]; ring
    have eK' : (C' : ℝ) * A' ^ K' * ((N : ℝ) ^ P.natDegree / (D : ℝ)) ^ K' * (δ⁻¹) ^ K'
        = (C' : ℝ) * b ^ K' := by rw [hbdef]; ring
    rw [eK] at hq
    rw [eK']
    calc (q : ℝ) ≤ (C : ℝ) * b ^ K := hq
      _ ≤ (C' : ℝ) * b ^ K := mul_le_mul_of_nonneg_right hC' hbk0
      _ ≤ (C' : ℝ) * b ^ K' := mul_le_mul_of_nonneg_left hbK (by positivity)
  · -- the second conjunct
    have e1 : δ ^ K' * ((D : ℝ) / (N : ℝ) ^ P.natDegree) ^ K' * (N : ℝ) = c ^ K' * (N : ℝ) := by
      rw [hcdef]; ring
    have e2 : (C' : ℝ) * A' ^ K' * ((N : ℝ) ^ P.natDegree / (D : ℝ)) ^ K' * (δ⁻¹) ^ K' *
          (N' : ℝ) = (C' : ℝ) * b ^ K' * (N' : ℝ) := by rw [hbdef]; ring
    have f2 : δ ^ K * ((D : ℝ) / (N : ℝ) ^ P.natDegree) ^ K * (N : ℝ) = c ^ K * (N : ℝ) := by
      rw [hcdef]; ring
    have g2 : (C : ℝ) * A' ^ K * ((N : ℝ) ^ P.natDegree / (D : ℝ)) ^ K * (δ⁻¹) ^ K * (N' : ℝ)
        = (C : ℝ) * b ^ K * (N' : ℝ) := by rw [hbdef]; ring
    rw [f2, g2] at h2
    rw [e1, e2]
    calc c ^ K' * (N : ℝ) ≤ c ^ K * (N : ℝ) := mul_le_mul_of_nonneg_right hcK hNpos.le
      _ ≤ (C : ℝ) * b ^ K * (N' : ℝ) := h2
      _ ≤ (C' : ℝ) * b ^ K' * (N' : ℝ) := by
          calc (C : ℝ) * b ^ K * (N' : ℝ) ≤ (C' : ℝ) * b ^ K * (N' : ℝ) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC' hbk0) hN'0
            _ = (C' : ℝ) * (b ^ K * (N' : ℝ)) := by ring
            _ ≤ (C' : ℝ) * (b ^ K' * (N' : ℝ)) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hbK hN'0) (by positivity)
            _ = (C' : ℝ) * b ^ K' * (N' : ℝ) := by ring
  · -- the last conjunct
    have e1 : δ ^ K' * ((D : ℝ) / (N : ℝ) ^ P.natDegree) ^ K' * (N₀ : ℝ) = c ^ K' * (N₀ : ℝ) := by
      rw [hcdef]; ring
    have e2 : (C' : ℝ) * A' ^ K' * ((N : ℝ) ^ P.natDegree / (D : ℝ)) ^ K' * (δ⁻¹) ^ K' *
          progAvgSum N' (q : ℤ) f₁
        = (C' : ℝ) * b ^ K' * progAvgSum N' (q : ℤ) f₁ := by rw [hbdef]; ring
    have f2 : δ ^ K * ((D : ℝ) / (N : ℝ) ^ P.natDegree) ^ K * (N₀ : ℝ) = c ^ K * (N₀ : ℝ) := by
      rw [hcdef]; ring
    have g2 : (C : ℝ) * A' ^ K * ((N : ℝ) ^ P.natDegree / (D : ℝ)) ^ K * (δ⁻¹) ^ K *
          progAvgSum N' (q : ℤ) f₁
        = (C : ℝ) * b ^ K * progAvgSum N' (q : ℤ) f₁ := by rw [hbdef]; ring
    rw [f2, g2] at h3
    rw [e1, e2]
    calc c ^ K' * (N₀ : ℝ) ≤ c ^ K * (N₀ : ℝ) := mul_le_mul_of_nonneg_right hcK hN0
      _ ≤ (C : ℝ) * b ^ K * progAvgSum N' (q : ℤ) f₁ := h3
      _ ≤ (C' : ℝ) * b ^ K' * progAvgSum N' (q : ℤ) f₁ := by
          calc (C : ℝ) * b ^ K * progAvgSum N' (q : ℤ) f₁
              ≤ (C' : ℝ) * b ^ K * progAvgSum N' (q : ℤ) f₁ :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC' hbk0) hps
            _ = (C' : ℝ) * (b ^ K * progAvgSum N' (q : ℤ) f₁) := by ring
            _ ≤ (C' : ℝ) * (b ^ K' * progAvgSum N' (q : ℤ) f₁) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hbK hps) (by positivity)
            _ = (C' : ℝ) * b ^ K' * progAvgSum N' (q : ℤ) f₁ := by ring

end

end Work.Peluse.Ulower
