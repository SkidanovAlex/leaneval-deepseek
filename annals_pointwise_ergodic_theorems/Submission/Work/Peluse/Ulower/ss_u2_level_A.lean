/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team.
-/
import Mathlib
import Submission.Work.Peluse.Ulower.ss_char_entry_A
import Submission.Work.Peluse.Ulower.ss_corr_to_prog_A
import Submission.Work.Peluse.Ulower.ss_defs

/-!
# `Work.Peluse.Ulower.ss_u2_level_A` — Peluse's §9 at the `U²` level, unbalanced (`N^d ≍_A Ns`)

This is `Work.Peluse.Ulower.ss_u2_level` with the two-sided scale hypothesis
`Scaled Ns N P.natDegree` (`N^d/2 ≤ Ns ≤ 2 N^d`) replaced by the *unbalanced* relation
`N^d ≤ A·Ns` and `Ns ≤ A·N^d`, the constant `A` being quantified **before** `C, K` (so that
`C, K` may depend on `A`).  Only the lower bound `N^d ≤ A·Ns` is actually used, and only through the
two chapters:

* `Work.Peluse.Ulower.ss_char_entry_A` — the `U²`-inverse entry with the constant
  `ssAmaxA P A = 3 + coeffSum P · A` in place of `ssAmax P`;
* `Work.Peluse.Ulower.ss_corr_to_prog_A` — Peluse's §9 at the correlation level, whose proof does
  not use the scale relation at all.

The bookkeeping (`γ := min 1 (C₀ δ^{K₀} (D/Ns)^{K₀})`, `K := max 1 (K₀K₂)`,
`C := max ⌈C₂/(min 1 C₀)^{K₂}⌉ 1`) is copied verbatim from `ss_u2_level`.
-/

set_option autoImplicit false

open scoped BigOperators
open Polynomial

namespace Work.Peluse.Ulower

noncomputable section

open Work.Peluse

theorem ss_u2_level_A {P : Polynomial ℤ} (hd : 2 ≤ P.natDegree)
    (h1 : Work.Peluse.PeluseU2Inverse) (h2 : Work.Peluse.PeluseMajorArc P) :
    ∀ A : ℕ, 1 ≤ A → ∃ C K : ℕ, 1 ≤ C ∧ 1 ≤ K ∧
      ∀ (Ns N D : ℕ) (f₀ f₁ : ℤ → ℂ) (δ : ℝ),
        2 ≤ P.natDegree → 1 ≤ N → 1 ≤ Ns → 1 ≤ D →
        (N : ℝ) ≤ (Ns : ℝ) →
        (N : ℝ) ^ P.natDegree ≤ (A : ℝ) * (Ns : ℝ) →
        (Ns : ℝ) ≤ (A : ℝ) * (N : ℝ) ^ P.natDegree →
        (D : ℝ) ≤ (Ns : ℝ) →
        Work.Peluse.SupportIn f₀ Ns → Work.Peluse.SupportIn f₁ Ns →
        (∀ x : ℤ, ‖f₀ x‖ ≤ 1) → (∀ x : ℤ, ‖f₁ x‖ ≤ 1) →
        0 < δ → δ ≤ 1 →
        δ ≤ Work.Peluse.uNormPow 2 (Work.Peluse.arithIcc P.leadingCoeff D)
          (Work.Peluse.symIcc (Work.Peluse.dSup P Ns N)) (Work.Peluse.dualFn N P f₀ f₁) →
        Work.Peluse.Ulower.DisplayAt P C K 1 Ns N Ns D f₁ δ := by
  intro A hA
  obtain ⟨C₀, hC₀pos, K₀, _hK₀1, hentry⟩ := ss_char_entry_A (P := P) hd h1 A hA
  obtain ⟨C₂, K₂, hC₂1, _hK₂1, hcorr⟩ := ss_corr_to_prog_A (P := P) hd h1 h2
  -- the constant with which `γ` may be capped
  set cmin : ℝ := min 1 C₀ with hcmindef
  have hcminpos : 0 < cmin := by rw [hcmindef]; exact lt_min one_pos hC₀pos
  -- the constant `C` absorbing `C₂ / cmin^{K₂}`
  obtain ⟨Cc, hCc⟩ : ∃ Cc : ℕ, (C₂ : ℝ) / cmin ^ K₂ ≤ (Cc : ℝ) :=
    ⟨⌈(C₂ : ℝ) / cmin ^ K₂⌉₊, Nat.le_ceil _⟩
  set K : ℕ := max 1 (K₀ * K₂) with hKdef
  set C : ℕ := max Cc 1 with hCdef
  have hK1 : 1 ≤ K := by rw [hKdef]; exact le_max_left _ _
  have hKm : K₀ * K₂ ≤ K := by rw [hKdef]; exact le_max_right _ _
  have hC1 : 1 ≤ C := by rw [hCdef]; exact le_max_right _ _
  have hCbig : (C₂ : ℝ) / cmin ^ K₂ ≤ (C : ℝ) := by
    refine le_trans hCc ?_
    rw [hCdef]; exact_mod_cast le_max_left Cc 1
  have hC₂0 : (0 : ℝ) < (C₂ : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hC₂1)
  have hC₂nn : (0 : ℝ) ≤ (C₂ : ℝ) := hC₂0.le
  have hCnn : (0 : ℝ) ≤ (C : ℝ) := Nat.cast_nonneg C
  refine ⟨C, K, hC1, hK1, ?_⟩
  intro Ns N D f₀ f₁ δ hd2 hN hNs hD1 hNNsR hsc hNsA hDNs hf0 hf1 hb0 hb1 hδ0 hδ1 hhyp
  have hNNs : N ≤ Ns := Nat.cast_le.mp hNNsR
  -- ## notation
  have hNs0 : (0 : ℝ) < (Ns : ℝ) := by exact_mod_cast hNs
  have hD0 : (0 : ℝ) < (D : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD1)
  set a : ℝ := (Ns : ℝ) / (D : ℝ) with hadef
  set b : ℝ := (D : ℝ) / (Ns : ℝ) with hbdef
  have ha0 : 0 < a := by rw [hadef]; positivity
  have ha1 : 1 ≤ a := by rw [hadef]; exact (one_le_div hD0).mpr hDNs
  have hbp0 : 0 < b := by rw [hbdef]; positivity
  have hbp1 : b ≤ 1 := by rw [hbdef]; exact (div_le_one hNs0).mpr hDNs
  have hδinv1 : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ0).mpr hδ1
  have hδinv0 : 0 < δ⁻¹ := inv_pos.mpr hδ0
  set t : ℝ := δ * b with htdef
  have ht0 : 0 < t := by rw [htdef]; exact mul_pos hδ0 hbp0
  have ht1 : t ≤ 1 := by rw [htdef]; nlinarith [hδ0, hδ1, hbp0, hbp1]
  have htnn : (0 : ℝ) ≤ t := ht0.le
  -- ## the `U²`-inverse entry
  obtain ⟨ξ, hξ⟩ :=
    hentry Ns N D f₀ f₁ δ hN hNs hD1 hNNs hsc hDNs hf0 hf1 hb0 hb1 hδ0 hδ1 hhyp
  rw [← hbdef] at hξ
  set Y : ℝ := δ ^ K₀ * b ^ K₀ with hYdef
  have hYpos : 0 < Y := by rw [hYdef]; positivity
  have hYle1 : Y ≤ 1 := by
    rw [hYdef]
    have h1 : δ ^ K₀ ≤ 1 := pow_le_one₀ hδ0.le hδ1
    have h2 : b ^ K₀ ≤ 1 := pow_le_one₀ hbp0.le hbp1
    have h3 : (0 : ℝ) ≤ b ^ K₀ := pow_nonneg hbp0.le K₀
    nlinarith
  have hξY : C₀ * Y * (Ns : ℝ) ≤
      ‖∑' x : ℤ, Work.Peluse.dualFn N P f₀ f₁ x *
        Complex.exp (2 * Real.pi * Complex.I * ξ * (x : ℝ))‖ := by
    have he : C₀ * Y * (Ns : ℝ) = C₀ * δ ^ K₀ * b ^ K₀ * (Ns : ℝ) := by rw [hYdef]; ring
    rw [he]; exact hξ
  -- ## the capped correlation level
  set γ : ℝ := min 1 (C₀ * Y) with hγdef
  have hγpos : 0 < γ := by rw [hγdef]; exact lt_min one_pos (mul_pos hC₀pos hYpos)
  have hγle1 : γ ≤ 1 := by rw [hγdef]; exact min_le_left _ _
  have hγle : γ ≤ C₀ * Y := by rw [hγdef]; exact min_le_right _ _
  have hγge : cmin * Y ≤ γ := by
    rw [hγdef, hcmindef]
    by_cases hle : C₀ ≤ 1
    · have hCY : C₀ * Y ≤ 1 := by nlinarith [hYle1, hC₀pos, hle]
      rw [min_eq_right hle, min_eq_right hCY]
    · have hlt : 1 < C₀ := not_le.mp hle
      rw [min_eq_left hlt.le, one_mul]
      exact le_min hYle1 (le_mul_of_one_le_left hYpos.le hlt.le)
  have hcorr_hyp : ∃ ξ : ℝ, γ * (Ns : ℝ) ≤
      ‖∑' x : ℤ, Work.Peluse.dualFn N P f₀ f₁ x *
        Complex.exp (2 * Real.pi * Complex.I * ξ * (x : ℝ))‖ :=
    ⟨ξ, le_trans (mul_le_mul_of_nonneg_right hγle (Nat.cast_nonneg Ns)) hξY⟩
  -- ## Peluse's §9 at the correlation level
  obtain ⟨q, N', hq1, hq, hN'1, hN'N, hN'win, hprog⟩ :=
    hcorr Ns N f₀ f₁ γ hN hNs hNNs hf0 hf1 hb0 hb1 hγpos hγle1 hcorr_hyp
  -- ## the power bounds
  have heqY : (cmin * Y) ^ K₂ = cmin ^ K₂ * t ^ (K₀ * K₂) := by
    have h2 : Y ^ K₂ = t ^ (K₀ * K₂) := by
      rw [hYdef, mul_pow, ← pow_mul, ← pow_mul, ← mul_pow, ← htdef]
    rw [mul_pow, h2]
  have hγpow : cmin ^ K₂ * t ^ (K₀ * K₂) ≤ γ ^ K₂ := by
    rw [← heqY]
    exact pow_le_pow_left₀ (mul_pos hcminpos hYpos).le hγge K₂
  have h2K : K₀ * K₂ ≤ 2 * K := by omega
  have htmpow : t ^ (2 * K) ≤ t ^ (K₀ * K₂) := pow_le_pow_of_le_one htnn ht1 h2K
  have ht2 : t ^ (2 * K) = t ^ K * t ^ K := by rw [two_mul, pow_add]
  have hC2le : (C₂ : ℝ) ≤ (C : ℝ) * cmin ^ K₂ :=
    (div_le_iff₀ (pow_pos hcminpos K₂)).mp hCbig
  -- `a * δ⁻¹ = t⁻¹`
  have hat : a * δ⁻¹ = t⁻¹ := by
    have hNsne : (Ns : ℝ) ≠ 0 := ne_of_gt hNs0
    have hDne : (D : ℝ) ≠ 0 := ne_of_gt hD0
    have hδne : δ ≠ 0 := ne_of_gt hδ0
    have h : t * (a * δ⁻¹) = 1 := by
      rw [htdef, hadef, hbdef]
      field_simp
    have h2 : t * (a * δ⁻¹) = t * t⁻¹ := by rw [h, mul_inv_cancel₀ (ne_of_gt ht0)]
    exact mul_left_cancel₀ (ne_of_gt ht0) h2
  have hN'ge : cmin ^ K₂ * t ^ (K₀ * K₂) * (N : ℝ) / (C₂ : ℝ) ≤ (N' : ℝ) :=
    calc cmin ^ K₂ * t ^ (K₀ * K₂) * (N : ℝ) / (C₂ : ℝ)
        ≤ γ ^ K₂ * (N : ℝ) / (C₂ : ℝ) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hγpow (Nat.cast_nonneg N)) hC₂nn
      _ ≤ (N' : ℝ) := hN'win
  have hprogge : cmin ^ K₂ * t ^ (K₀ * K₂) * (Ns : ℝ) / (C₂ : ℝ)
      ≤ Work.Peluse.progAvgSum N' (q : ℤ) f₁ :=
    calc cmin ^ K₂ * t ^ (K₀ * K₂) * (Ns : ℝ) / (C₂ : ℝ)
        ≤ γ ^ K₂ * (Ns : ℝ) / (C₂ : ℝ) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hγpow (Nat.cast_nonneg Ns)) hC₂nn
      _ ≤ Work.Peluse.progAvgSum N' (q : ℤ) f₁ := hprog
  -- ## the display
  unfold Work.Peluse.Ulower.DisplayAt
  refine ⟨q, N', hq1, ?_, hN'1, hN'N, ?_, ?_⟩
  · -- the `q`-clause
    simp only [one_pow, mul_one]
    rw [← hadef]
    have hginv : γ⁻¹ ≤ cmin⁻¹ * (δ⁻¹) ^ K₀ * a ^ K₀ := by
      have h1 : γ⁻¹ ≤ (cmin * Y)⁻¹ :=
        (inv_le_inv₀ hγpos (mul_pos hcminpos hYpos)).mpr hγge
      have h2 : (cmin * Y)⁻¹ = cmin⁻¹ * (δ⁻¹) ^ K₀ * a ^ K₀ := by
        have hbinv : b⁻¹ = a := by rw [hadef, hbdef, inv_div]
        rw [mul_inv, hYdef, mul_inv, ← inv_pow, ← inv_pow, hbinv]
        ring
      rw [h2] at h1; exact h1
    have hpow2 : (γ⁻¹) ^ K₂ ≤ (cmin⁻¹ * (δ⁻¹) ^ K₀ * a ^ K₀) ^ K₂ :=
      pow_le_pow_left₀ (le_of_lt (inv_pos.mpr hγpos)) hginv K₂
    have heq2 : (cmin⁻¹ * (δ⁻¹) ^ K₀ * a ^ K₀) ^ K₂
        = (cmin ^ K₂)⁻¹ * (δ⁻¹) ^ (K₀ * K₂) * a ^ (K₀ * K₂) := by
      rw [mul_pow, mul_pow, inv_pow, ← pow_mul, ← pow_mul]
      try ring
    have hδle : (δ⁻¹) ^ (K₀ * K₂) ≤ (δ⁻¹) ^ K := pow_le_pow_right₀ hδinv1 hKm
    have haale : a ^ (K₀ * K₂) ≤ a ^ K := pow_le_pow_right₀ ha1 hKm
    have hstep : (C₂ : ℝ) * (γ⁻¹) ^ K₂ ≤ (C : ℝ) * a ^ K * (δ⁻¹) ^ K := by
      have h1 : (C₂ : ℝ) * (γ⁻¹) ^ K₂
          ≤ (C₂ : ℝ) * ((cmin ^ K₂)⁻¹ * (δ⁻¹) ^ (K₀ * K₂) * a ^ (K₀ * K₂)) :=
        mul_le_mul_of_nonneg_left (le_trans hpow2 (le_of_eq heq2)) hC₂nn
      have h2 : (C₂ : ℝ) * ((cmin ^ K₂)⁻¹ * (δ⁻¹) ^ (K₀ * K₂) * a ^ (K₀ * K₂))
          = ((C₂ : ℝ) * (cmin ^ K₂)⁻¹) * ((δ⁻¹) ^ (K₀ * K₂) * a ^ (K₀ * K₂)) := by ring
      have h3 : (C₂ : ℝ) * (cmin ^ K₂)⁻¹ ≤ (C : ℝ) := by
        have h4 : (cmin ^ K₂)⁻¹ = 1 / cmin ^ K₂ := by rw [one_div]
        rw [h4]
        calc (C₂ : ℝ) * (1 / cmin ^ K₂) = (C₂ : ℝ) / cmin ^ K₂ := by ring
          _ ≤ (C : ℝ) := hCbig
      have h4 : (δ⁻¹) ^ (K₀ * K₂) * a ^ (K₀ * K₂) ≤ (δ⁻¹) ^ K * a ^ K :=
        mul_le_mul hδle haale (pow_nonneg ha0.le _) (pow_nonneg hδinv0.le _)
      calc (C₂ : ℝ) * (γ⁻¹) ^ K₂
          ≤ ((C₂ : ℝ) * (cmin ^ K₂)⁻¹) * ((δ⁻¹) ^ (K₀ * K₂) * a ^ (K₀ * K₂)) := by
            rw [h2] at h1; exact h1
        _ ≤ (C : ℝ) * ((δ⁻¹) ^ K * a ^ K) :=
            mul_le_mul h3 h4 (mul_nonneg (pow_nonneg hδinv0.le _) (pow_nonneg ha0.le _)) hCnn
        _ = (C : ℝ) * a ^ K * (δ⁻¹) ^ K := by ring
    exact le_trans hq hstep
  · -- the `N'`-clause
    simp only [one_pow, mul_one]
    rw [← hadef, ← hbdef]
    have hLHS : δ ^ K * b ^ K * (N : ℝ) = t ^ K * (N : ℝ) := by rw [htdef, mul_pow]
    have hRHS : (C : ℝ) * a ^ K * (δ⁻¹) ^ K * (N' : ℝ)
        = (C : ℝ) * (N' : ℝ) / t ^ K := by
      have h : a ^ K * (δ⁻¹) ^ K = (t ^ K)⁻¹ := by rw [← mul_pow, hat, inv_pow]
      calc (C : ℝ) * a ^ K * (δ⁻¹) ^ K * (N' : ℝ)
          = (C : ℝ) * (a ^ K * (δ⁻¹) ^ K) * (N' : ℝ) := by ring
        _ = (C : ℝ) * (t ^ K)⁻¹ * (N' : ℝ) := by rw [h]
        _ = (C : ℝ) * (N' : ℝ) / t ^ K := by rw [div_eq_mul_inv]; ring
    rw [hLHS, hRHS, le_div_iff₀ (pow_pos ht0 K)]
    have hkey : t ^ (2 * K) * (N : ℝ) ≤ (C : ℝ) * (N' : ℝ) := by
      have hX0 : (0 : ℝ) ≤ t ^ (K₀ * K₂) * (N : ℝ) :=
        mul_nonneg (pow_nonneg htnn _) (Nat.cast_nonneg N)
      have h2 : t ^ (2 * K) * (N : ℝ) ≤ t ^ (K₀ * K₂) * (N : ℝ) :=
        mul_le_mul_of_nonneg_right htmpow (Nat.cast_nonneg N)
      have h3 : t ^ (K₀ * K₂) * (N : ℝ)
          ≤ ((C : ℝ) * cmin ^ K₂) * (t ^ (K₀ * K₂) * (N : ℝ)) / (C₂ : ℝ) := by
        rw [le_div_iff₀ hC₂0]
        calc t ^ (K₀ * K₂) * (N : ℝ) * (C₂ : ℝ)
            ≤ t ^ (K₀ * K₂) * (N : ℝ) * ((C : ℝ) * cmin ^ K₂) :=
              mul_le_mul_of_nonneg_left hC2le hX0
          _ = ((C : ℝ) * cmin ^ K₂) * (t ^ (K₀ * K₂) * (N : ℝ)) := by ring
      have h4 : ((C : ℝ) * cmin ^ K₂) * (t ^ (K₀ * K₂) * (N : ℝ)) / (C₂ : ℝ)
          = (C : ℝ) * (cmin ^ K₂ * t ^ (K₀ * K₂) * (N : ℝ) / (C₂ : ℝ)) := by ring
      have h5 : (C : ℝ) * (cmin ^ K₂ * t ^ (K₀ * K₂) * (N : ℝ) / (C₂ : ℝ)) ≤
          (C : ℝ) * (N' : ℝ) := mul_le_mul_of_nonneg_left hN'ge hCnn
      calc t ^ (2 * K) * (N : ℝ) ≤ t ^ (K₀ * K₂) * (N : ℝ) := h2
        _ ≤ ((C : ℝ) * cmin ^ K₂) * (t ^ (K₀ * K₂) * (N : ℝ)) / (C₂ : ℝ) := h3
        _ = (C : ℝ) * (cmin ^ K₂ * t ^ (K₀ * K₂) * (N : ℝ) / (C₂ : ℝ)) := h4
        _ ≤ (C : ℝ) * (N' : ℝ) := h5
    rw [show t ^ K * (N : ℝ) * t ^ K = t ^ (2 * K) * (N : ℝ) by rw [ht2]; ring]
    exact hkey
  · -- the progression-average clause
    simp only [one_pow, mul_one]
    rw [← hadef, ← hbdef]
    have hLHS : δ ^ K * b ^ K * (Ns : ℝ) = t ^ K * (Ns : ℝ) := by rw [htdef, mul_pow]
    have hRHS : (C : ℝ) * a ^ K * (δ⁻¹) ^ K * Work.Peluse.progAvgSum N' (q : ℤ) f₁
        = (C : ℝ) * Work.Peluse.progAvgSum N' (q : ℤ) f₁ / t ^ K := by
      have h : a ^ K * (δ⁻¹) ^ K = (t ^ K)⁻¹ := by rw [← mul_pow, hat, inv_pow]
      calc (C : ℝ) * a ^ K * (δ⁻¹) ^ K * Work.Peluse.progAvgSum N' (q : ℤ) f₁
          = (C : ℝ) * (a ^ K * (δ⁻¹) ^ K) * Work.Peluse.progAvgSum N' (q : ℤ) f₁ := by ring
        _ = (C : ℝ) * (t ^ K)⁻¹ * Work.Peluse.progAvgSum N' (q : ℤ) f₁ := by rw [h]
        _ = (C : ℝ) * Work.Peluse.progAvgSum N' (q : ℤ) f₁ / t ^ K := by
              rw [div_eq_mul_inv]; ring
    rw [hLHS, hRHS, le_div_iff₀ (pow_pos ht0 K)]
    have hkey : t ^ (2 * K) * (Ns : ℝ) ≤ (C : ℝ) * Work.Peluse.progAvgSum N' (q : ℤ) f₁ := by
      have hX0 : (0 : ℝ) ≤ t ^ (K₀ * K₂) * (Ns : ℝ) :=
        mul_nonneg (pow_nonneg htnn _) (Nat.cast_nonneg Ns)
      have h2 : t ^ (2 * K) * (Ns : ℝ) ≤ t ^ (K₀ * K₂) * (Ns : ℝ) :=
        mul_le_mul_of_nonneg_right htmpow (Nat.cast_nonneg Ns)
      have h3 : t ^ (K₀ * K₂) * (Ns : ℝ)
          ≤ ((C : ℝ) * cmin ^ K₂) * (t ^ (K₀ * K₂) * (Ns : ℝ)) / (C₂ : ℝ) := by
        rw [le_div_iff₀ hC₂0]
        calc t ^ (K₀ * K₂) * (Ns : ℝ) * (C₂ : ℝ)
            ≤ t ^ (K₀ * K₂) * (Ns : ℝ) * ((C : ℝ) * cmin ^ K₂) :=
              mul_le_mul_of_nonneg_left hC2le hX0
          _ = ((C : ℝ) * cmin ^ K₂) * (t ^ (K₀ * K₂) * (Ns : ℝ)) := by ring
      have h4 : ((C : ℝ) * cmin ^ K₂) * (t ^ (K₀ * K₂) * (Ns : ℝ)) / (C₂ : ℝ)
          = (C : ℝ) * (cmin ^ K₂ * t ^ (K₀ * K₂) * (Ns : ℝ) / (C₂ : ℝ)) := by ring
      have h5 : (C : ℝ) * (cmin ^ K₂ * t ^ (K₀ * K₂) * (Ns : ℝ) / (C₂ : ℝ)) ≤
          (C : ℝ) * Work.Peluse.progAvgSum N' (q : ℤ) f₁ :=
        mul_le_mul_of_nonneg_left hprogge hCnn
      calc t ^ (2 * K) * (Ns : ℝ) ≤ t ^ (K₀ * K₂) * (Ns : ℝ) := h2
        _ ≤ ((C : ℝ) * cmin ^ K₂) * (t ^ (K₀ * K₂) * (Ns : ℝ)) / (C₂ : ℝ) := h3
        _ = (C : ℝ) * (cmin ^ K₂ * t ^ (K₀ * K₂) * (Ns : ℝ) / (C₂ : ℝ)) := h4
        _ ≤ (C : ℝ) * Work.Peluse.progAvgSum N' (q : ℤ) f₁ := h5
    rw [show t ^ K * (Ns : ℝ) * t ^ K = t ^ (2 * K) * (Ns : ℝ) by rw [ht2]; ring]
    exact hkey

end

end Work.Peluse.Ulower
