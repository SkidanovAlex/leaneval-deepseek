/-
# The assembly of `Work.KMTPlan.A6.MdlSlicePktLinF` from its two cases

`Work.KMTPlan.A6.MdlSlicePktLinF` (the paper's `(lin-1)` for the `f`-side packet family of §8 of
Krause--Mirek--Tao, Annals 195 (2022), in the A6 carrier `mdlCore`/`Tle`/`mdlF`/`varphiNtj`) splits
according to the twist `(k₁,j₁)` of the modified bump `varphiNtj`:

* `k₁ ≥ 1` (any `j₁ ∈ {-1,0,1}`) and `(k₁,j₁) = (0,1)`: the signed sums of the modified bumps are
  *pointwise* bounded (the bump either is annulus-supported or vanishes at the frequency origin),
  and the uniform-in-signs Marcinkiewicz--Zygmund transfer applies.  This is
  `Work.KMTPlan.A6.MdlPktVanishingCase` (**proved, axiom-clean**), with the weight
  `lossWeight 2 ρ l₁ l₂ k₁ k₂`;
* `(k₁,j₁) = (0,0)`: the unmodulated bump `varphiNt N 0 t = φ_N e(Nt·)` does *not* vanish at the
  origin (`varphiNt N 0 t (0) = 1`), the uniform-in-signs bound fails, and the paper's
  low-frequency argument is required.  This is the `Prop` `MdlPktZeroZero` of
  `Submission/Work/KMTPlan/A6/MdlPktLinFDefs.lean`;
* the case `(k₁,j₁) = (0,-1)` is excluded by the hypothesis `(k₁ = 0 → j₁ ≠ -1)` (the factor
  `(Nξ)^{-1}` of `varphiNtj` is singular at the origin).

This module performs the *assembly*: the two constants and the two thresholds `ρ₀` are combined by
a `max` (for the loss exponent) and a `min` (for `ρ₀`), using the monotonicity of
`lossWeight · ρ l₁ l₂ k₁ k₂` in its first argument.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.MdlPktLinFDefs
import Submission.Work.KMTPlan.A6.MdlPktVanishingCase

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

open MeasureTheory
open scoped ENNReal NNReal BigOperators
open Work.KMTAreas.A7

noncomputable section

/-- The loss weight is monotone in the exponent: `lossWeight c₁ ρ … ≤ lossWeight c₂ ρ …` for
`c₁ ≤ c₂`. -/
theorem lossWeight_mono_exp {c₁ c₂ ρ : ℝ} (h : c₁ ≤ c₂) (hρ : 0 ≤ ρ) (l₁ l₂ k₁ k₂ : ℕ) :
    Work.KMTAreas.A7.lossWeight c₁ ρ l₁ l₂ k₁ k₂
      ≤ Work.KMTAreas.A7.lossWeight c₂ ρ l₁ l₂ k₁ k₂ := by
  unfold Work.KMTAreas.A7.lossWeight
  have hL : (0 : ℝ) ≤ Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂ :=
    Work.KMTAreas.A7.lmaxR_nonneg l₁ l₂ k₁ k₂
  have h1 : (1 : ℝ) ≤ 1 + Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂ := by linarith
  have ha : (1 + Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂) ^ c₁
      ≤ (1 + Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂) ^ c₂ :=
    Real.rpow_le_rpow_of_exponent_le h1 h
  have hexp : c₁ * ρ * Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂
      ≤ c₂ * ρ * Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h hρ) hL
  have hb : (2 : ℝ) ^ (c₁ * ρ * Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂)
      ≤ (2 : ℝ) ^ (c₂ * ρ * Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  exact mul_le_mul ha hb (Real.rpow_nonneg (by norm_num) _)
    (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ 1 + Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂) _)

/-- **The assembly.**  `MdlSlicePktLinF` follows from its `(k₁,j₁) = (0,0)` case together with the
proved vanishing case `Work.KMTPlan.A6.MdlPktVanishingCase`. -/
theorem MdlSlicePktLinF_of_zeroZero (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (R : NNReal) (hR : 2 < R)
    (j₁ : ℤ) (hj₁ : j₁ ∈ ({-1, 0, 1} : Finset ℤ))
    (hZZ : MdlPktZeroZero C₀ R) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ K : NNReal → NNReal,
        ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (f : ℤ → ℂ),
          1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n : ℕ, 1 ≤ a n) →
          t ∈ Set.Icc (1 / 2 : ℝ) 1 → (k₁ = 0 → j₁ ≠ -1) →
          MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
              (fun n : ℕ =>
                if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n then
                  Work.KMTAreas.A7.Tle ρ l₁ (Work.KMTPlan.A6.varphiNtj (Nat.floor (a n)) k₁ j₁ t)
                    (Work.KMTPlan.A6.mdlF ρ (Work.KMTAreas.A7.uScale ρ
                      (max (max l₁ l₂) (max k₁ k₂))) l₁ f) x
                else 0)) 2 MeasureTheory.Measure.count
            ≤ (K Λ : ENNReal) *
                ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ k₁ k₂) *
                MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
  classical
  obtain ⟨AZ, hAZ, ρZ, hρZ, hZ⟩ := hZZ
  obtain ⟨ρV, hρV, hV⟩ := MdlPktVanishingCase C₀ hC₀ R hR j₁ hj₁
  refine ⟨max AZ 2, le_trans hAZ (le_max_left _ _), min ρZ ρV, lt_min hρZ hρV, ?_⟩
  intro ρ hρ hρ0
  have hρZ' : ρ ≤ ρZ := le_trans hρ0 (min_le_left _ _)
  have hρV' : ρ ≤ ρV := le_trans hρ0 (min_le_right _ _)
  obtain ⟨KZ, hKZ⟩ := hZ ρ hρ hρZ'
  obtain ⟨KV, hKV⟩ := hV ρ hρ hρV'
  refine ⟨fun Λ => max (KZ Λ) (KV Λ), ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ t f hΛ ha ha1 ht hk
  by_cases h00 : k₁ = 0 ∧ j₁ = 0
  · -- the `(0,0)` case: `MdlPktZeroZero`, with the weight upgraded from `AZ` to `max AZ 2`
    obtain ⟨hk₁, hj₀⟩ := h00
    subst hk₁
    subst hj₀
    have hb := hKZ a Λ l₁ l₂ k₂ t f hΛ ha ha1 ht
    refine hb.trans ?_
    have hKK : (KZ Λ : ENNReal) ≤ ((max (KZ Λ) (KV Λ) : NNReal) : ENNReal) :=
      ENNReal.coe_le_coe.mpr (le_max_left _ _)
    have hww : ENNReal.ofReal (Work.KMTAreas.A7.lossWeight AZ ρ l₁ l₂ 0 k₂)
        ≤ ENNReal.ofReal (Work.KMTAreas.A7.lossWeight (max AZ 2) ρ l₁ l₂ 0 k₂) :=
      ENNReal.ofReal_le_ofReal (lossWeight_mono_exp (le_max_left _ _) hρ.le l₁ l₂ 0 k₂)
    exact mul_le_mul' (mul_le_mul' hKK hww) le_rfl
  · -- the vanishing case: `MdlPktVanishingCase`, with the weight upgraded from `2` to `max AZ 2`
    have hk' : k₁ = 0 → j₁ = 1 := by
      intro hk0
      have hne : j₁ ≠ -1 := hk hk0
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj₁
      rcases hj₁ with h | h | h
      · exact absurd h hne
      · exact absurd ⟨hk0, h⟩ h00
      · exact h
    have hb := hKV a Λ l₁ l₂ k₁ k₂ t f hΛ ha ha1 ht hk'
    refine hb.trans ?_
    have hKK : (KV Λ : ENNReal) ≤ ((max (KZ Λ) (KV Λ) : NNReal) : ENNReal) :=
      ENNReal.coe_le_coe.mpr (le_max_right _ _)
    have hww : ENNReal.ofReal (Work.KMTAreas.A7.lossWeight 2 ρ l₁ l₂ k₁ k₂)
        ≤ ENNReal.ofReal (Work.KMTAreas.A7.lossWeight (max AZ 2) ρ l₁ l₂ k₁ k₂) :=
      ENNReal.ofReal_le_ofReal (lossWeight_mono_exp (le_max_right _ _) hρ.le l₁ l₂ k₁ k₂)
    exact mul_le_mul' (mul_le_mul' hKK hww) le_rfl

/-- **The `(0,0)` case splits by the height.**  The height-`0` instance is the bottom-height
low-pass walk (in which the exact-height carrier `Tex ρ 0` vanishes identically, so `HclEstimate2`
gives nothing), while the positive heights are handled by the A7 `Hcl` estimate through the
composite identity. -/
theorem MdlPktZeroZero_of_split (C₀ : ℕ) (R : NNReal)
    (h0 : MdlPktZeroZeroAtZero C₀ R) (hpos : MdlPktZeroZeroPos C₀ R) :
    MdlPktZeroZero C₀ R := by
  classical
  obtain ⟨A0, hA0, ρ0, hρ0, hZ⟩ := h0
  obtain ⟨A1, hA1, ρ1, hρ1, hP⟩ := hpos
  refine ⟨max A0 A1, le_trans hA0 (le_max_left _ _), min ρ0 ρ1, lt_min hρ0 hρ1, ?_⟩
  intro ρ hρ hρ'
  have hρ0' : ρ ≤ ρ0 := le_trans hρ' (min_le_left _ _)
  have hρ1' : ρ ≤ ρ1 := le_trans hρ' (min_le_right _ _)
  obtain ⟨K0, hKZ⟩ := hZ ρ hρ hρ0'
  obtain ⟨K1, hKP⟩ := hP ρ hρ hρ1'
  refine ⟨fun Λ => max (K0 Λ) (K1 Λ), ?_⟩
  intro a Λ l₁ l₂ k₂ t f hΛ ha ha1 ht
  by_cases hl : l₁ = 0
  · subst hl
    have hb := hKZ a Λ l₂ k₂ t f hΛ ha ha1 ht
    refine hb.trans ?_
    have hKK : (K0 Λ : ENNReal) ≤ ((max (K0 Λ) (K1 Λ) : NNReal) : ENNReal) :=
      ENNReal.coe_le_coe.mpr (le_max_left _ _)
    have hww : ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A0 ρ 0 l₂ 0 k₂)
        ≤ ENNReal.ofReal (Work.KMTAreas.A7.lossWeight (max A0 A1) ρ 0 l₂ 0 k₂) :=
      ENNReal.ofReal_le_ofReal (lossWeight_mono_exp (le_max_left _ _) hρ.le 0 l₂ 0 k₂)
    exact mul_le_mul' (mul_le_mul' hKK hww) le_rfl
  · have hl1 : 1 ≤ l₁ := Nat.one_le_iff_ne_zero.mpr hl
    have hb := hKP a Λ l₁ l₂ k₂ t f hΛ ha ha1 ht hl1
    refine hb.trans ?_
    have hKK : (K1 Λ : ENNReal) ≤ ((max (K0 Λ) (K1 Λ) : NNReal) : ENNReal) :=
      ENNReal.coe_le_coe.mpr (le_max_right _ _)
    have hww : ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A1 ρ l₁ l₂ 0 k₂)
        ≤ ENNReal.ofReal (Work.KMTAreas.A7.lossWeight (max A0 A1) ρ l₁ l₂ 0 k₂) :=
      ENNReal.ofReal_le_ofReal (lossWeight_mono_exp (le_max_right _ _) hρ.le l₁ l₂ 0 k₂)
    exact mul_le_mul' (mul_le_mul' hKK hww) le_rfl

end

end Work.KMTPlan.A6
