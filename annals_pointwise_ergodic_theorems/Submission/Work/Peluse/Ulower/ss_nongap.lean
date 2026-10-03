/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team.
-/
import Mathlib
import Submission.Work.Peluse.Ulower.ss_transfer
import Submission.Work.Peluse.Ulower.ss_ratio
import Submission.Work.Peluse.Ulower.ss_conversion
import Submission.Work.Peluse.Ulower.ss_u2_level
import Submission.Work.Peluse.Ulower.ss_degree_lowering

/-!
# `Work.Peluse.Ulower.ss_nongap`: the display of `PeluseULowering` outside the gap regime

This is the *non-gap* case of the chapter `Ulower/small_shift` (Peluse's chapter (iii) of
Theorem 3.3), isolated so that it can also serve the assembly `Work.Peluse.ulowering_of`, where the
"large shift" case of the display has to be produced with the *same* technique: the case split
there is on `D`, while the technique below only needs `D ≤ N ^ P.natDegree`.

The hypotheses are those of `Work.Peluse.Ulower.small_shift` with

* the shift bound relaxed from `D ≤ N ^ d / 2` to `D ≤ N ^ d` (so that the *large-shift* case is
  covered as well), and
* the *non-gap* hypothesis `¬(2 * N^d < N₀ ∧ N < 2 * N₀)`, which is what makes the two scales `N^d`
  and `N₀` comparable, so that the *balanced* chapters apply:

* `Work.Peluse.Ulower.ss_degree_lowering` (Peluse's Lemma 3.9, the degree lowering `U^s → U²`);
* `Work.Peluse.Ulower.ss_u2_level` (Peluse's §9 at the `U²` level, i.e. Lemma 2.4 + Lemma 3.10 +
  the van der Corput/periodisation argument);
* `Work.Peluse.Ulower.ss_transfer` (change of the support box) and
  `Work.Peluse.Ulower.ss_conversion` (change of the analysis scale, absorbing the loss
  `(δ D/Ns)^{K₁}` of the degree lowering into the exponent `K` of the display).

The gap regime `2 N^d < N₀ ∧ N < 2 N₀` is *not* covered here; it is the chapter
`Work.Peluse.Ulower.gap_regime`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped BigOperators
open Polynomial

namespace Work.Peluse.Ulower

noncomputable section

open Work.Peluse

/-- `symIcc L` always contains `0`, hence is nonempty. -/
private lemma card_symIcc_pos (L : ℕ) : 0 < (symIcc L).card := by
  rw [symIcc]
  exact Finset.card_pos.mpr ⟨0, by simp⟩

/-- `dSup P · N` is monotone in its first argument. -/
private lemma dSup_mono_left (P : Polynomial ℤ) {a b N : ℕ} (h : a ≤ b) :
    dSup P a N ≤ dSup P b N := by
  rw [dSup, dSup]
  exact Nat.add_le_add_right h _

theorem ss_nongap {P : Polynomial ℤ} (hd : 2 ≤ P.natDegree)
    (h1 : Work.Peluse.PeluseU2Inverse) (h2 : Work.Peluse.PeluseMajorArc P) :
    ∀ s : ℕ, 2 ≤ s → ∃ C K : ℕ, 1 ≤ C ∧ 1 ≤ K ∧
      ∀ (A' : ℝ) (N N₀ D : ℕ) (f₀ f₁ : ℤ → ℂ) (δ : ℝ),
        2 ≤ P.natDegree → 1 ≤ A' → 1 ≤ N → 1 ≤ N₀ →
        (N₀ : ℝ) ≤ A' * (N : ℝ) ^ P.natDegree →
        (N : ℝ) ^ P.natDegree ≤ A' * (δ⁻¹) * (N₀ : ℝ) →
        0 < δ → δ ≤ 1 → 1 ≤ D →
        (D : ℝ) ≤ (N : ℝ) ^ P.natDegree →
        ¬ (2 * (N : ℝ) ^ P.natDegree < (N₀ : ℝ) ∧ (N : ℝ) < 2 * (N₀ : ℝ)) →
        Work.Peluse.SupportIn f₀ N₀ → Work.Peluse.SupportIn f₁ N₀ →
        (∀ x : ℤ, ‖f₀ x‖ ≤ 1) → (∀ x : ℤ, ‖f₁ x‖ ≤ 1) →
        δ ≤ Work.Peluse.uNormPow s (Work.Peluse.arithIcc P.leadingCoeff D)
          (Work.Peluse.symIcc (Work.Peluse.dSup P N₀ N)) (Work.Peluse.dualFn N P f₀ f₁) →
        ∃ q N' : ℕ, 1 ≤ q ∧
          (q : ℝ) ≤ (C : ℝ) * A' ^ K *
            ((N : ℝ) ^ P.natDegree / (D : ℝ)) ^ K * (δ⁻¹) ^ K ∧
          1 ≤ N' ∧ N' ≤ N ∧
          δ ^ K * ((D : ℝ) / (N : ℝ) ^ P.natDegree) ^ K * (N : ℝ) ≤
            (C : ℝ) * A' ^ K * ((N : ℝ) ^ P.natDegree / (D : ℝ)) ^ K * (δ⁻¹) ^ K * (N' : ℝ) ∧
          δ ^ K * ((D : ℝ) / (N : ℝ) ^ P.natDegree) ^ K * (N₀ : ℝ) ≤
            (C : ℝ) * A' ^ K * ((N : ℝ) ^ P.natDegree / (D : ℝ)) ^ K * (δ⁻¹) ^ K *
              Work.Peluse.progAvgSum N' (q : ℤ) f₁ := by
  intro s hs
  obtain ⟨K₁, hK₁, hdlch⟩ := ss_degree_lowering (P := P) hd h1 h2 s hs
  obtain ⟨C₂, K₂, hC₂, hK₂, hU2ch⟩ := ss_u2_level (P := P) hd h1 h2
  obtain ⟨Cc, Kc, hCc, hKc, hconvch⟩ :=
    ss_conversion (P := P) (C₂ := C₂) (K₁ := K₁) (K₂ := K₂)
      (c := (P.leadingCoeff.natAbs : ℝ) / (1 + (P.leadingCoeff.natAbs : ℝ))) hC₂ hK₁ hK₂
      (by
        have hP : P ≠ 0 := by rintro rfl; simp at hd
        have hlc : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
        have h2 : 0 < P.leadingCoeff.natAbs := Int.natAbs_pos.mpr hlc
        have h3 : (0:ℝ) < (P.leadingCoeff.natAbs : ℝ) := by exact_mod_cast h2
        positivity)
  refine ⟨Cc, Kc, hCc, hKc, ?_⟩
  intro A' N N₀ D f₀ f₁ δ hd2 hA' hN hN₀ hsc1 hsc2 hδ0 hδ1 hD1 hDle hng hf0 hf1 hb0 hb1 hhyp
  change Display P Cc Kc A' N N₀ D f₁ δ
  rw [display_iff_displayAt]
  have hNdM : (D : ℝ) ≤ ((N ^ P.natDegree : ℕ) : ℝ) := by
    rw [Nat.cast_pow]; exact hDle
  -- the non-gap hypothesis: `N₀ ≤ 2 N^d`
  have hN₀le : (N₀ : ℝ) ≤ 2 * (N : ℝ) ^ P.natDegree := by
    by_contra hcon
    rw [not_le] at hcon
    have hNlt : ¬ ((N : ℝ) < 2 * (N₀ : ℝ)) := fun hc => hng ⟨hcon, hc⟩
    have h2' : 2 * (N₀ : ℝ) ≤ (N : ℝ) := not_lt.mp hNlt
    have h4 : 4 * (N : ℝ) ^ P.natDegree < (N : ℝ) := by nlinarith
    have h1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hNd : (N : ℝ) ≤ (N : ℝ) ^ P.natDegree := by
      calc (N : ℝ) = (N : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (N : ℝ) ^ P.natDegree := pow_le_pow_right₀ h1' (by omega)
    linarith
  have hN₀le' : N₀ ≤ 2 * N ^ P.natDegree := by
    have : (N₀ : ℝ) ≤ ((2 * N ^ P.natDegree : ℕ) : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]; linarith
    exact_mod_cast this
  -- the balanced scale
  set Ns : ℕ := max N₀ (N ^ P.natDegree) with hNsdef
  have hN₀Ns : N₀ ≤ Ns := le_max_left _ _
  have hNdNs : N ^ P.natDegree ≤ Ns := le_max_right _ _
  have hNsR : (Ns : ℝ) = max (N₀ : ℝ) ((N : ℝ) ^ P.natDegree) := by
    rw [hNsdef, Nat.cast_max, Nat.cast_pow]
  have hNs1 : 1 ≤ Ns := by
    have h1 : 1 ≤ N ^ P.natDegree := Nat.one_le_pow _ _ (by omega)
    omega
  have hM1 : 1 ≤ N ^ P.natDegree := Nat.one_le_pow _ _ (by omega)
  have hNsMnat : Ns ≤ 2 * N ^ P.natDegree := by
    rw [hNsdef]
    exact max_le hN₀le' (by omega)
  have hNleNs : N ≤ Ns := by
    have h1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hNd : (N : ℝ) ≤ (N : ℝ) ^ P.natDegree := by
      calc (N : ℝ) = (N : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (N : ℝ) ^ P.natDegree := pow_le_pow_right₀ h1' (by omega)
    have : (N : ℝ) ≤ (Ns : ℝ) := by
      rw [hNsR]; exact le_trans hNd (le_max_right _ _)
    exact_mod_cast this
  have hDNsnat : D ≤ Ns := by
    have h1 : (D : ℝ) ≤ (Ns : ℝ) := by
      rw [hNsR]
      exact le_trans hDle (le_max_right _ _)
    exact_mod_cast h1
  have hDNsR : (D : ℝ) ≤ (Ns : ℝ) := by exact_mod_cast hDNsnat
  have hScaled : Scaled Ns N P.natDegree := by
    constructor
    · rw [hNsR]
      have := le_max_right (N₀ : ℝ) ((N : ℝ) ^ P.natDegree)
      linarith
    · rw [hNsR]
      exact max_le hN₀le (by linarith)
  -- the support transfer
  set ρ : ℝ := ((symIcc (dSup P N₀ N)).card : ℝ) / ((symIcc (dSup P Ns N)).card : ℝ) with hρdef
  have hρ0 : 0 < ρ := by
    rw [hρdef]
    exact div_pos (by exact_mod_cast card_symIcc_pos _) (by exact_mod_cast card_symIcc_pos _)
  have hρ1 : ρ ≤ 1 := by
    rw [hρdef, div_le_one (by exact_mod_cast card_symIcc_pos (dSup P Ns N))]
    have hsub : symIcc (dSup P N₀ N) ⊆ symIcc (dSup P Ns N) := by
      intro x hx
      simp only [symIcc, Finset.mem_Icc] at hx ⊢
      obtain ⟨h1, h2⟩ := hx
      have hle : ((dSup P N₀ N : ℕ) : ℤ) ≤ ((dSup P Ns N : ℕ) : ℤ) := by
        exact_mod_cast dSup_mono_left P hN₀Ns
      constructor <;> omega
    exact_mod_cast Finset.card_le_card hsub
  have hρc : (P.leadingCoeff.natAbs : ℝ) / (1 + (P.leadingCoeff.natAbs : ℝ)) ≤ ρ := by
    rw [hρdef, hNsdef]
    exact ss_ratio (P := P) hd (N := N) (N₀ := N₀) hN
  have htr : δ * ρ ≤ uNormPow s (arithIcc P.leadingCoeff D) (symIcc (dSup P Ns N))
      (dualFn N P f₀ f₁) :=
    ss_transfer (P := P) (s := s) (N := N) (N₀ := N₀) (Ns := Ns) (Q := arithIcc P.leadingCoeff D)
      (F := dualFn N P f₀ f₁) (δ := δ) (card_symIcc_pos _) (card_symIcc_pos _) hhyp
  -- the degree lowering
  have hf0' : SupportIn f₀ Ns := hf0.mono hN₀Ns
  have hf1' : SupportIn f₁ Ns := hf1.mono hN₀Ns
  have hδρ0 : 0 < δ * ρ := mul_pos hδ0 hρ0
  have hδρ1 : δ * ρ ≤ 1 := by nlinarith [hδ1, hρ1, hδ0, hρ0]
  have hdl : ((δ * ρ) * ((D : ℝ) / (Ns : ℝ))) ^ K₁ ≤
      uNormPow 2 (arithIcc P.leadingCoeff D) (symIcc (dSup P Ns N)) (dualFn N P f₀ f₁) :=
    hdlch Ns N D f₀ f₁ (δ * ρ) hd2 hN hNs1 hScaled hNleNs hD1 hDNsR hf0' hf1' hb0 hb1
      hδρ0 hδρ1 htr
  -- the `U²`-level §9 with threshold `δ₂ := (δρ · D/Ns)^{K₁}`
  set δ₂ : ℝ := (δ * ρ * (D : ℝ) / (Ns : ℝ)) ^ K₁ with hδ₂def
  have hδ₂eq : ((δ * ρ) * ((D : ℝ) / (Ns : ℝ))) ^ K₁ = δ₂ := by
    rw [hδ₂def]; ring_nf
  have hδ₂le : δ₂ ≤ uNormPow 2 (arithIcc P.leadingCoeff D) (symIcc (dSup P Ns N))
      (dualFn N P f₀ f₁) := hδ₂eq ▸ hdl
  have hδ₂0 : 0 < δ₂ := by rw [hδ₂def]; positivity
  have hδ₂1 : δ₂ ≤ 1 := by
    rw [hδ₂def]
    apply pow_le_one₀ (by positivity)
    rw [div_le_one (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hNs1))]
    have hDR0 : (0 : ℝ) ≤ (D : ℝ) := by positivity
    nlinarith [hδρ1, hDR0, hDNsR]
  have hchild : DisplayAt P C₂ K₂ 1 Ns N Ns D f₁ δ₂ :=
    hU2ch Ns N D f₀ f₁ δ₂ hd2 hN hNs1 hScaled hNleNs hD1 hDNsR hf0' hf1' hb0 hb1 hδ₂0 hδ₂1
      hδ₂le
  have hchild' :
      DisplayAt P C₂ K₂ 1 Ns N Ns D f₁ ((δ * ρ * (D : ℝ) / (Ns : ℝ)) ^ K₁) :=
    hδ₂def ▸ hchild
  -- the scale conversion
  have hDMnat : D ≤ N ^ P.natDegree := by
    have h1 : (D : ℝ) ≤ ((N ^ P.natDegree : ℕ) : ℝ) := hNdM
    exact_mod_cast h1
  have hconv := hconvch Ns N N₀ D (N ^ P.natDegree) f₁ δ ρ A' hM1 hNs1 hN hD1 hA' hδ0 hδ1
    hρ0 hρc hρ1 hNdNs hNsMnat hDMnat hDNsnat hN₀Ns hchild'
  exact hconv

end

end Work.Peluse.Ulower
