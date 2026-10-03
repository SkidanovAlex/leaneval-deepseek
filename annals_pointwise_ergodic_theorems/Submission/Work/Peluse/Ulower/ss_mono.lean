/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team.
-/
import Mathlib
import Submission.Work.Peluse.Ulower.ss_defs

/-!
# Monotonicity of the display `DisplayAt` in the constants `C, K`

`DisplayAt P C K A' M N N₀ D f₁ δ` is the three-part display of `PeluseULowering` at an
arbitrary scale `M`:

```
q ≤ C A'^K (M/D)^K δ^{-K},     N' ≤ N,
δ^K (D/M)^K N  ≤ C A'^K (M/D)^K δ^{-K} N',
δ^K (D/M)^K N₀ ≤ C A'^K (M/D)^K δ^{-K} progAvgSum N' q f₁ .
```

Since the hypotheses put the bases `A'`, `M/D`, `δ⁻¹` all at least `1`, while `D/M ≤ 1`:
increasing `K` to `K' ≥ K` makes the left-hand sides (which carry `(D/M)^K`, `δ^K` with
`δ ≤ 1`, `D ≤ M`) *decrease*, and makes the right-hand sides (`A'^K`, `(M/D)^K`, `δ^{-K}`)
*increase*; increasing `C` to `C' ≥ C` also increases the right-hand sides.  So the same
witnesses `q, N'` certify the display for the larger constants.  This is the bookkeeping used
when an assembly raises the exponent `K` by taking the maximum of the exponents produced by
several chapters.

The statement is *not* true without `(D : ℝ) ≤ (M : ℝ)` (then `D/M > 1` and the left-hand
sides grow with `K`) nor without `1 ≤ A'`, `δ ≤ 1` (then `A'^K`, `δ^{-K}` need not be
monotone); all four hypotheses are present.
-/

set_option autoImplicit false

open scoped BigOperators
open Polynomial

namespace Work.Peluse.Ulower

noncomputable section

open Work.Peluse

/-! ## Elementary monotonicity of the coefficient `C A'^K (M/D)^K δ^{-K}` -/

/-- The coefficient of the display is monotone in `C` and in `K`, provided the bases
`A'`, `a`, `s` are `≥ 1`. -/
private lemma ss_coeff_mono {C C' K K' : ℕ} {A' a s : ℝ}
    (hC : C ≤ C') (hA : 1 ≤ A') (ha : 1 ≤ a) (hs : 1 ≤ s) (hK : K ≤ K') :
    (C : ℝ) * A' ^ K * a ^ K * s ^ K ≤ (C' : ℝ) * A' ^ K' * a ^ K' * s ^ K' := by
  have hA0 : (0 : ℝ) ≤ A' := le_trans zero_le_one hA
  have ha0 : (0 : ℝ) ≤ a := le_trans zero_le_one ha
  have hs0 : (0 : ℝ) ≤ s := le_trans zero_le_one hs
  have h1 : A' ^ K ≤ A' ^ K' := pow_le_pow_right₀ hA hK
  have h2 : a ^ K ≤ a ^ K' := pow_le_pow_right₀ ha hK
  have h3 : s ^ K ≤ s ^ K' := pow_le_pow_right₀ hs hK
  have hX : A' ^ K * a ^ K * s ^ K ≤ A' ^ K' * a ^ K' * s ^ K' := by
    calc A' ^ K * a ^ K * s ^ K = (A' ^ K * a ^ K) * s ^ K := by ring
      _ ≤ (A' ^ K' * a ^ K') * s ^ K := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul h1 h2 (pow_nonneg ha0 K) (pow_nonneg hA0 K')) (pow_nonneg hs0 K)
      _ ≤ (A' ^ K' * a ^ K') * s ^ K' :=
            mul_le_mul_of_nonneg_left h3 (mul_nonneg (pow_nonneg hA0 K') (pow_nonneg ha0 K'))
      _ = A' ^ K' * a ^ K' * s ^ K' := by ring
  have h0X : (0 : ℝ) ≤ A' ^ K * a ^ K * s ^ K :=
    mul_nonneg (mul_nonneg (pow_nonneg hA0 K) (pow_nonneg ha0 K)) (pow_nonneg hs0 K)
  calc (C : ℝ) * A' ^ K * a ^ K * s ^ K
      = (C : ℝ) * (A' ^ K * a ^ K * s ^ K) := by ring
    _ ≤ (C' : ℝ) * (A' ^ K' * a ^ K' * s ^ K') :=
          mul_le_mul (by exact_mod_cast hC) hX h0X (by positivity)
    _ = (C' : ℝ) * A' ^ K' * a ^ K' * s ^ K' := by ring

/-- **Monotonicity of `DisplayAt` in `C` and `K`.**  If the display holds for the constants
`C, K` then it holds for any `C' ≥ C`, `K' ≥ K` (with the same witnesses `q, N'`), because
raising `K` decreases the left-hand sides (`(D/M)^K` with `D ≤ M`, and `δ^K` with `δ ≤ 1`) and
increases every factor of the right-hand side (`A' ≥ 1`, `M/D ≥ 1`, `δ⁻¹ ≥ 1`). -/
theorem ss_mono {P : Polynomial ℤ} {C C' K K' : ℕ} (hC : C ≤ C') (hK : K ≤ K') :
    ∀ (A' : ℝ) (M N N₀ D : ℕ) (f₁ : ℤ → ℂ) (δ : ℝ),
      1 ≤ A' → 0 < δ → δ ≤ 1 → 1 ≤ N → 1 ≤ D → (D : ℝ) ≤ (M : ℝ) →
      Work.Peluse.Ulower.DisplayAt P C K A' M N N₀ D f₁ δ →
      Work.Peluse.Ulower.DisplayAt P C' K' A' M N N₀ D f₁ δ := by
  intro A' M N N₀ D f₁ δ hA' hδ hδ1 hN hD hDM hdisp
  obtain ⟨q, N', hq1, hq2, hN'1, hN'le, h3, h4⟩ := hdisp
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hMpos : (0 : ℝ) < (M : ℝ) := by
    have h1 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
    linarith
  -- `M/D ≥ 1`, `D/M ≤ 1`, `δ⁻¹ ≥ 1`
  have hMD1 : (1 : ℝ) ≤ (M : ℝ) / (D : ℝ) := (one_le_div hDpos).mpr hDM
  have hDM1 : (D : ℝ) / (M : ℝ) ≤ 1 := (div_le_one hMpos).mpr hDM
  have hDM0 : (0 : ℝ) ≤ (D : ℝ) / (M : ℝ) := by positivity
  have hδinv : (1 : ℝ) ≤ δ⁻¹ := by
    rw [← one_div]
    exact (one_le_div hδ).mpr hδ1
  have hd0 : (0 : ℝ) ≤ δ := le_of_lt hδ
  -- the coefficient increases
  have hcoef := ss_coeff_mono (A' := A') (a := (M : ℝ) / (D : ℝ)) (s := δ⁻¹)
    hC hA' hMD1 hδinv hK
  -- the left-hand side decreases (both bases are in `[0,1]`)
  have hanti : δ ^ K' * ((D : ℝ) / (M : ℝ)) ^ K' ≤ δ ^ K * ((D : ℝ) / (M : ℝ)) ^ K :=
    mul_le_mul (pow_le_pow_of_le_one hd0 hδ1 hK) (pow_le_pow_of_le_one hDM0 hDM1 hK)
      (pow_nonneg hDM0 K') (pow_nonneg hd0 K)
  have hprog : (0 : ℝ) ≤ Work.Peluse.progAvgSum N' q f₁ := by
    rw [Work.Peluse.progAvgSum]
    exact tsum_nonneg (fun x => norm_nonneg _)
  refine ⟨q, N', hq1, le_trans hq2 hcoef, hN'1, hN'le, ?_, ?_⟩
  · calc δ ^ K' * ((D : ℝ) / (M : ℝ)) ^ K' * (N : ℝ)
        ≤ δ ^ K * ((D : ℝ) / (M : ℝ)) ^ K * (N : ℝ) :=
          mul_le_mul_of_nonneg_right hanti (Nat.cast_nonneg N)
      _ ≤ (C : ℝ) * A' ^ K * ((M : ℝ) / (D : ℝ)) ^ K * (δ⁻¹) ^ K * (N' : ℝ) := h3
      _ ≤ (C' : ℝ) * A' ^ K' * ((M : ℝ) / (D : ℝ)) ^ K' * (δ⁻¹) ^ K' * (N' : ℝ) :=
          mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg N')
  · calc δ ^ K' * ((D : ℝ) / (M : ℝ)) ^ K' * (N₀ : ℝ)
        ≤ δ ^ K * ((D : ℝ) / (M : ℝ)) ^ K * (N₀ : ℝ) :=
          mul_le_mul_of_nonneg_right hanti (Nat.cast_nonneg N₀)
      _ ≤ (C : ℝ) * A' ^ K * ((M : ℝ) / (D : ℝ)) ^ K * (δ⁻¹) ^ K *
            Work.Peluse.progAvgSum N' (q : ℤ) f₁ := h4
      _ ≤ (C' : ℝ) * A' ^ K' * ((M : ℝ) / (D : ℝ)) ^ K' * (δ⁻¹) ^ K' *
            Work.Peluse.progAvgSum N' (q : ℤ) f₁ :=
          mul_le_mul_of_nonneg_right hcoef hprog

end

end Work.Peluse.Ulower
