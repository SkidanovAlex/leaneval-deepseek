/-
# The §8 adelic clauses at `l₁ = 0` (`l₂ ≠ 0`), with the `g`-side regime hypothesis (fresh proof)

This is the `l₁ = 0` branch of the Case-Zero producer: the data with `l₁ = 0 < l₂`.

* the `f`-side family is the **regime-free** height-`0` lift
  `Work.KMTPlan.A6Clean.exists_liftFamilyFZero` (`A6Clean/mdlLiftZeroOfMdlCore.lean`), whose
  vanishing clause is the one off `iwArithFreqs ρ 0 = {0}` and whose band is the input's band
  `2^{k₁ - logN ⌊a n⌋}` (bounded by `1/4` from `mdlCore` alone), with the data bound
  `Work.A6Clean.PacketFamFZeroUniform` (which needs no vanishing hypothesis);
* the `g`-side family is the regime-based lift
  `Work.KMTPlan.A6Clean.exists_liftFamilyGRegime`, with its data bound
  `Work.KMTPlan.A6Clean.PacketFamGUniformAlt`;
* the arithmetic clauses come from the `g`-side alone, which is the *larger* height
  (`l₁ = 0 < l₂`), via `packetFamG_minorArc` at `L = max 0 l₂ - 1 = l₂ - 1` — no case split.

## Why this file exists (and not `A6Clean/adelicClausesCaseZeroFZero`)

The module `Submission/Work/KMTPlan/A6Clean/adelicClausesCaseZeroFZero.lean` states this branch,
but its proof is broken: it takes the packet families `u`, `v` from the existential witness of
`Work.KMTPlan.A6Clean.packetsStructuralClausesGatedBeta` and then asserts the *definitional*
equalities `u = packetFamF ⋯ W₁`, `v = packetFamG ⋯ W₂` (`hu_eq`/`hv_eq`, proved by `rfl`), which
are false for a `Classical.choose`-witness.  Here the structural clauses (1), (2), (3), (9), (10)
are instead proved **directly for the explicit packet families** `packetFamF ⋯ W₁` /
`packetFamG ⋯ W₂`, exactly as the sibling `Work.KMTPlan.A6Lead.adelicClausesCaseZeroGZero` (the
`l₂ = 0` branch) does.

The conditional regime `MdlLiftRegimeG` is supplied by the consumer
(`A6Clean/adelicFormGated.lean`'s degenerate branch has the gate `B ρ ≤ lcL l₁ l₂ k₁ k₂` in scope
and discharges the regime with `Work.A6Clean.MdlWindowLiftRegimeGNoGSB`).
-/
import Mathlib
import Submission.Work.KMTPlan.A6Clean.adelicClausesCaseZeroCorner
import Submission.Work.KMTPlan.A6Lead.adelicClausesCaseZeroGZero
import Submission.Work.KMTPlan.A6Clean.exists_liftFamilyGRegime
import Submission.Work.KMTPlan.A6Clean.packetFamG_minorArc
import Submission.Work.KMTPlan.A6Clean.pfGUniformAlt

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 20000000

namespace Work.KMTPlan.A6Lead

open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger
open Work.KMTAreas.A7
open Work.KMTAreas.A7Rep
open Work.KMTPlan.A6
open Work.KMTPlan.A6Clean

local notation "Circ" => Work.Analysis.IonescuWainger.Circle
local notation "logN" => Work.Analysis.EndVar.logN

noncomputable section

theorem adelicClausesCaseZeroFZeroFresh (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (hI : Work.KMTContract.ImprovKMT P) (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (R : NNReal) (hR : 2 < R) (r : NNReal) (hr : 2 < r) (hrT : (r : ℝ) < Work.KMTPlan.A6.adelicRTop P) (j₁ j₂ : ℤ) (hj₁ : j₁ ∈ ({-1, 0, 1} : Finset ℤ)) (hj₂ : j₂ ∈ ({-1, 0, 1} : Finset ℤ)) :
    ∃ c : ℝ, 0 < c ∧ ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ Cin : NNReal → NNReal,
        ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₂ k₁ k₂ : ℕ) (t : ℝ) (f g : ℤ → ℂ),
          1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n : ℕ, 1 ≤ a n) →
            t ∈ Set.Icc (1 / 2 : ℝ) 1 → (k₁ = 0 → j₁ ≠ -1) → (k₂ = 0 → j₂ ≠ -1) →
            MeasureTheory.MemLp f 2 MeasureTheory.Measure.count →
            MeasureTheory.MemLp g 2 MeasureTheory.Measure.count → l₂ ≠ 0 →
            (∀ n : ℕ, Work.KMTPlan.A6.mdlCore ρ C₀ a 0 l₂ k₁ k₂ n →
              Work.KMTPlan.A6Clean.MdlLiftRegimeG ρ P a 0 l₂ k₁ k₂ j₂ t n) →
            Work.KMTPlan.A6Clean.AdelicClausesAt P ρ R r a Λ 0 l₂ k₁ k₂ t j₁ j₂ f g C₀ c A Cin := by
  classical
  obtain ⟨cb, hcb, hbile⟩ := MdlAdelicBileClausesOr P hd hI r hr hrT
  obtain ⟨AF, hAF, ρF, hρF, hKF⟩ := Work.A6Clean.PacketFamFZeroUniform C₀ hC₀ R hR j₁ hj₁
  obtain ⟨AG, hAG, ρG, hρG, hKG⟩ := Work.A6Clean.PacketFamGUniformAlt P hd C₀ hC₀ R hR j₂ hj₂
  refine ⟨cb, hcb, max AF AG, le_max_of_le_left hAF, min 1 (min ρF ρG),
    lt_min one_pos (lt_min hρF hρG), ?_⟩
  intro ρ hρ hρle
  have hρ1 : ρ ≤ 1 := le_trans hρle (min_le_left _ _)
  have hρF' : ρ ≤ ρF := le_trans hρle (le_trans (min_le_right _ _) (min_le_left _ _))
  have hρG' : ρ ≤ ρG := le_trans hρle (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨Cb, hCbpos, hbileC⟩ := hbile ρ hρ hρ1
  obtain ⟨KF, hKF'⟩ := hKF ρ hρ hρF'
  obtain ⟨KG, hKG'⟩ := hKG ρ hρ hρG'
  let Cin : NNReal → NNReal := fun Λ =>
    ⟨max (max (max ((KF Λ : NNReal) : ℝ) ((KG Λ : NNReal) : ℝ)) (Cb * (2 : ℝ) ^ cb)) 1,
      le_trans zero_le_one (le_max_right _ _)⟩
  refine ⟨Cin, ?_⟩
  intro a Λ l₂ k₁ k₂ t f g hΛ ha ha1 ht hk₁ hk₂ hf hg hl₂ hregG
  -- ## the loss-weight comparisons at the common exponent `max AF AG`
  have hKFi : ENNReal.ofReal (lossWeight AF ρ 0 l₂ k₁ k₂)
      ≤ ENNReal.ofReal (lossWeight (max AF AG) ρ 0 l₂ k₁ k₂) :=
    ENNReal.ofReal_le_ofReal
      (Work.KMTAreas.A7Hi.lossWeight_mono (le_max_left _ _) hAF hρ.le 0 l₂ k₁ k₂)
  have hKGi : ENNReal.ofReal (lossWeight AG ρ 0 l₂ k₁ k₂)
      ≤ ENNReal.ofReal (lossWeight (max AF AG) ρ 0 l₂ k₁ k₂) :=
    ENNReal.ofReal_le_ofReal
      (Work.KMTAreas.A7Hi.lossWeight_mono (le_max_right _ _) hAG hρ.le 0 l₂ k₁ k₂)
  have hpowF : (ENNReal.ofReal (lossWeight AF ρ 0 l₂ k₁ k₂)) ^ (2 : ℕ)
      ≤ (ENNReal.ofReal (lossWeight (max AF AG) ρ 0 l₂ k₁ k₂)) ^ (2 : ℕ) :=
    pow_le_pow_left₀ zero_le hKFi 2
  have hpowG : (ENNReal.ofReal (lossWeight AG ρ 0 l₂ k₁ k₂)) ^ (2 : ℕ)
      ≤ (ENNReal.ofReal (lossWeight (max AF AG) ρ 0 l₂ k₁ k₂)) ^ (2 : ℕ) :=
    pow_le_pow_left₀ zero_le hKGi 2
  have hlwA : (0 : ℝ) ≤ lossWeight (max AF AG) ρ 0 l₂ k₁ k₂ :=
    le_trans zero_le_one
      (Work.KMTAreas.A7Hi.one_le_lossWeight_of_nonneg (max AF AG) ρ
        (le_trans hAF (le_max_left _ _)) hρ.le 0 l₂ k₁ k₂)
  -- ## the two lift families and their bands
  obtain ⟨W₁, hW₁meas, hW₁band, hW₁zero, hW₁samp, hW₁sum, hW₁zeroCore⟩ :=
    exists_liftFamilyFZero ρ hρ hρ1 P hd C₀ a f hf l₂ k₁ k₂ j₁ hj₁ hk₁ t ha1
  obtain ⟨W₂, hW₂meas, hW₂band, hW₂zero, hW₂samp, hW₂sum, hW₂zeroCore⟩ :=
    exists_liftFamilyGRegime ρ hρ hρ1 P hd C₀ a g hg 0 l₂ k₁ k₂ j₂ hj₂ hk₂ t hl₂ hregG
  let δ₁ : ℕ → ℝ := fun n => (2 : ℝ) ^ ((k₁ : ℝ) - ((logN (Nat.floor (a n)) : ℤ) : ℝ))
  let δ₂ : ℕ → ℝ :=
    fun n => (2 : ℝ) ^ ((P.natDegree : ℝ) * ((k₂ : ℝ) - ((logN (Nat.floor (a n)) : ℤ) : ℝ)))
  let β : ℝ := 1 / (8 * (arithQ ρ (max 0 l₂) : ℝ))
  have hβ : ∀ n, goodScale (arithQ ρ (max 0 l₂)) (lcL 0 l₂ k₁ k₂) (Nat.floor (a n)) →
      δ₁ n + δ₂ n ≤ β := by
    intro n hn
    simp only [δ₁, δ₂, β]
    exact goodScale_two_pow_bands_le (arithQ ρ (max 0 l₂)) (lcL 0 l₂ k₁ k₂)
      (Nat.floor (a n)) k₁ k₂ P.natDegree hd (one_le_arithQ ρ (max 0 l₂)) hn
      (le_trans (le_max_left k₁ k₂) (le_max_right _ _))
      (le_trans (le_max_right k₁ k₂) (le_max_right _ _))
  haveI : NeZero (arithQ ρ (max 0 l₂)) :=
    ⟨Nat.pos_iff_ne_zero.mp (arithQ_pos ρ (max 0 l₂))⟩
  -- ## the arithmetic clauses: the `g`-side (the larger height) is minor arc
  have hminor : ∀ (n : ℕ) (X : ℝ), MdlIwMinorArc ρ (max 0 l₂ - 1) (arithQ ρ (max 0 l₂))
      (packetFamG ρ a 0 l₂ k₁ k₂ W₂ n X) := by
    intro n X
    have hmax : max 0 l₂ - 1 = l₂ - 1 := by rw [Nat.max_eq_right (Nat.zero_le l₂)]
    rw [hmax]
    exact packetFamG_minorArc ρ hρ hρ1 a 0 l₂ k₁ k₂ (W₂ n)
      (fun β₂ hβ' => hW₂zero n β₂ hβ') n X
  have hb3 := hbileC (arithQ ρ (max 0 l₂)) (max 0 l₂ - 1)
    (packetFamF ρ a 0 l₂ k₁ k₂ W₁) (packetFamG ρ a 0 l₂ k₁ k₂ W₂) (Or.inr hminor)
  obtain ⟨hbase, hB1, hB2⟩ := hb3
  let M : ℝ := Cb * (2 : ℝ) ^ (-(cb * (((max 0 l₂ - 1 : ℕ)) : ℝ)))
  have hMnn : 0 ≤ M := by
    simp only [M]
    exact mul_nonneg hCbpos.le (Real.rpow_pos_of_pos (by norm_num) _).le
  have hMbound : ENNReal.ofReal M ≤ (Cin Λ : ENNReal)
      * ENNReal.ofReal ((2 : ℝ) ^ (-(cb * max ((0 : ℕ) : ℝ) ((l₂ : ℕ) : ℝ)))) := by
    have hmax1 : 1 ≤ max 0 l₂ := le_trans (Nat.one_le_iff_ne_zero.mpr hl₂) (le_max_right _ _)
    have h2 : (2 : ℝ) ^ (-(cb * (((max 0 l₂ - 1 : ℕ)) : ℝ)))
        = (2 : ℝ) ^ cb * (2 : ℝ) ^ (-(cb * ((max 0 l₂ : ℕ) : ℝ))) := by
      rw [Nat.cast_sub hmax1, Nat.cast_one,
        show -(cb * (((max 0 l₂ : ℕ) : ℝ) - 1))
            = -(cb * ((max 0 l₂ : ℕ) : ℝ)) + cb by ring,
        Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      ring
    have hfac : M = (Cb * (2 : ℝ) ^ cb) * (2 : ℝ) ^ (-(cb * ((max 0 l₂ : ℕ) : ℝ))) := by
      simp only [M]
      rw [h2]
      ring
    rw [hfac, ENNReal.ofReal_mul (by positivity), Nat.cast_max]
    refine mul_le_mul' ?_ le_rfl
    rw [← ENNReal.ofReal_coe_nnreal (p := Cin Λ)]
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [Cin]
    exact le_trans (le_max_right (max ((KF Λ : NNReal) : ℝ) ((KG Λ : NNReal) : ℝ)) _)
      (le_max_left _ _)
  -- ## the `f`-side data bound (height `0`, no vanishing hypothesis)
  have hband₁4 : ∀ (n : ℕ) (α : Circ),
      HasRealFreqSupport (W₁ n α) (Set.Icc (-(1 / 4 : ℝ)) (1 / 4)) := by
    intro n α
    by_cases hc : Work.KMTPlan.A6.mdlCore ρ C₀ a 0 l₂ k₁ k₂ n
    · have hquarter : δ₁ n ≤ 1 / 4 := by
        simp only [δ₁]
        exact two_pow_k_sub_logN_le_quarter ρ hρ C₀ a 0 l₂ k₁ k₂ n hc
      refine hasRealFreqSupport_mono (fun x hx => ?_) (hW₁band n α)
      simp only [Set.mem_Icc] at hx ⊢
      exact ⟨by linarith [hx.1, hquarter], by linarith [hx.2, hquarter]⟩
    · rw [hW₁zeroCore n hc]
      exact hasRealFreqSupport_zero _
  have hFint : ∫⁻ X : ℝ, (VrLiftDataP (R : ℝ) (arithQ ρ (max 0 l₂))
        (fun n : ℕ => packetFamF ρ a 0 l₂ k₁ k₂ W₁ n X)) ^ (2 : ℕ)
      ≤ (KF Λ : ENNReal) ^ (2 : ℕ)
        * (ENNReal.ofReal (lossWeight (max AF AG) ρ 0 l₂ k₁ k₂)) ^ (2 : ℕ)
        * (MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count) ^ (2 : ℕ) := by
    refine le_trans (hKF' a Λ l₂ k₁ k₂ t f W₁ hΛ ha ha1 hf ht hk₁ hband₁4
      (fun n α hα x => hW₁samp n α hα x)) ?_
    exact mul_le_mul' (mul_le_mul_right hpowF ((KF Λ : ENNReal) ^ (2 : ℕ))) le_rfl
  let F₂ : ℝ := (MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count).toReal
  have hF₂ : ENNReal.ofReal F₂ = MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
    simp only [F₂, ENNReal.ofReal_toReal (MeasureTheory.MemLp.eLpNorm_lt_top hf).ne]
  let Ku : ℝ := ((KF Λ : NNReal) : ℝ) * lossWeight (max AF AG) ρ 0 l₂ k₁ k₂ * F₂
  have hKu_nn : 0 ≤ Ku := by
    simp only [Ku]
    exact mul_nonneg (mul_nonneg (NNReal.coe_nonneg _) hlwA) (ENNReal.toReal_nonneg)
  have hKu_eq : ENNReal.ofReal Ku = (KF Λ : ENNReal)
      * ENNReal.ofReal (lossWeight (max AF AG) ρ 0 l₂ k₁ k₂)
      * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
    rw [show Ku = ((KF Λ : NNReal) : ℝ) * lossWeight (max AF AG) ρ 0 l₂ k₁ k₂ * F₂ from rfl,
      ENNReal.ofReal_mul (mul_nonneg (NNReal.coe_nonneg _) hlwA),
      ENNReal.ofReal_mul (NNReal.coe_nonneg _), hF₂, ENNReal.ofReal_coe_nnreal]
  have hKu_bound : ENNReal.ofReal Ku ≤ (Cin Λ : ENNReal)
      * ENNReal.ofReal (lossWeight (max AF AG) ρ 0 l₂ k₁ k₂)
      * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
    have hstep : (KF Λ : ENNReal) ≤ (Cin Λ : ENNReal) := by
      have h1 : ((KF Λ : NNReal) : ℝ) ≤ ((Cin Λ : NNReal) : ℝ) := by
        dsimp only [Cin]
        exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
      calc (KF Λ : ENNReal) = ENNReal.ofReal ((KF Λ : NNReal) : ℝ) :=
            (ENNReal.ofReal_coe_nnreal (p := KF Λ)).symm
        _ ≤ ENNReal.ofReal ((Cin Λ : NNReal) : ℝ) := ENNReal.ofReal_le_ofReal h1
        _ = (Cin Λ : ENNReal) := ENNReal.ofReal_coe_nnreal
    rw [hKu_eq]
    exact mul_le_mul'
      (mul_le_mul_left hstep (ENNReal.ofReal (lossWeight (max AF AG) ρ 0 l₂ k₁ k₂))) le_rfl
  have hKu_int : ∫⁻ X : ℝ, (VrLiftDataP (R : ℝ) (arithQ ρ (max 0 l₂))
        (fun n : ℕ => packetFamF ρ a 0 l₂ k₁ k₂ W₁ n X)) ^ (2 : ℕ)
      ≤ ENNReal.ofReal (Ku ^ 2) := by
    rw [ENNReal.ofReal_pow hKu_nn, hKu_eq, mul_pow, mul_pow]
    exact hFint
  -- ## the `g`-side data bound (regime family)
  have hband₂4 : ∀ (n : ℕ) (α : Circ),
      HasRealFreqSupport (W₂ n α) (Set.Icc (-(1 / 4 : ℝ)) (1 / 4)) := by
    intro n α
    by_cases hc : Work.KMTPlan.A6.mdlCore ρ C₀ a 0 l₂ k₁ k₂ n
    · have hquarter : δ₂ n ≤ 1 / 4 := by
        simp only [δ₂]
        exact two_pow_d_mul_k_sub_logN_le_quarter ρ hρ P hd C₀ a 0 l₂ k₁ k₂ n hc
      refine hasRealFreqSupport_mono (fun x hx => ?_) (hW₂band n α)
      simp only [Set.mem_Icc] at hx ⊢
      exact ⟨by linarith [hx.1, hquarter], by linarith [hx.2, hquarter]⟩
    · rw [hW₂zeroCore n hc]
      exact hasRealFreqSupport_zero _
  have hGint : ∫⁻ X : ℝ, (VrLiftDataP (R : ℝ) (arithQ ρ (max 0 l₂))
        (fun n : ℕ => packetFamG ρ a 0 l₂ k₁ k₂ W₂ n X)) ^ (2 : ℕ)
      ≤ (KG Λ : ENNReal) ^ (2 : ℕ)
        * (ENNReal.ofReal (lossWeight (max AF AG) ρ 0 l₂ k₁ k₂)) ^ (2 : ℕ)
        * (MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count) ^ (2 : ℕ) := by
    refine le_trans (hKG' a Λ 0 l₂ k₁ k₂ t g W₂ hΛ ha ha1 hg ht hk₂ hband₂4
      (fun n β hβ' x => hW₂samp n β (mem_iwArithFreqsNew_le hβ') x)
      (fun n β hβ' => hW₂zero n β hβ')) ?_
    exact mul_le_mul' (mul_le_mul_right hpowG ((KG Λ : ENNReal) ^ (2 : ℕ))) le_rfl
  let G₂ : ℝ := (MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count).toReal
  have hG₂ : ENNReal.ofReal G₂ = MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
    simp only [G₂, ENNReal.ofReal_toReal (MeasureTheory.MemLp.eLpNorm_lt_top hg).ne]
  let Kv : ℝ := ((KG Λ : NNReal) : ℝ) * lossWeight (max AF AG) ρ 0 l₂ k₁ k₂ * G₂
  have hKv_nn : 0 ≤ Kv := by
    simp only [Kv]
    exact mul_nonneg (mul_nonneg (NNReal.coe_nonneg _) hlwA) (ENNReal.toReal_nonneg)
  have hKv_eq : ENNReal.ofReal Kv = (KG Λ : ENNReal)
      * ENNReal.ofReal (lossWeight (max AF AG) ρ 0 l₂ k₁ k₂)
      * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
    rw [show Kv = ((KG Λ : NNReal) : ℝ) * lossWeight (max AF AG) ρ 0 l₂ k₁ k₂ * G₂ from rfl,
      ENNReal.ofReal_mul (mul_nonneg (NNReal.coe_nonneg _) hlwA),
      ENNReal.ofReal_mul (NNReal.coe_nonneg _), hG₂, ENNReal.ofReal_coe_nnreal]
  have hKv_bound : ENNReal.ofReal Kv ≤ (Cin Λ : ENNReal)
      * ENNReal.ofReal (lossWeight (max AF AG) ρ 0 l₂ k₁ k₂)
      * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
    have hstep : (KG Λ : ENNReal) ≤ (Cin Λ : ENNReal) := by
      have h1 : ((KG Λ : NNReal) : ℝ) ≤ ((Cin Λ : NNReal) : ℝ) := by
        dsimp only [Cin]
        exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
      calc (KG Λ : ENNReal) = ENNReal.ofReal ((KG Λ : NNReal) : ℝ) :=
            (ENNReal.ofReal_coe_nnreal (p := KG Λ)).symm
        _ ≤ ENNReal.ofReal ((Cin Λ : NNReal) : ℝ) := ENNReal.ofReal_le_ofReal h1
        _ = (Cin Λ : ENNReal) := ENNReal.ofReal_coe_nnreal
    rw [hKv_eq]
    exact mul_le_mul'
      (mul_le_mul_left hstep (ENNReal.ofReal (lossWeight (max AF AG) ρ 0 l₂ k₁ k₂))) le_rfl
  have hKv_int : ∫⁻ X : ℝ, (VrLiftDataP (R : ℝ) (arithQ ρ (max 0 l₂))
        (fun n : ℕ => packetFamG ρ a 0 l₂ k₁ k₂ W₂ n X)) ^ (2 : ℕ)
      ≤ ENNReal.ofReal (Kv ^ 2) := by
    rw [ENNReal.ofReal_pow hKv_nn, hKv_eq, mul_pow, mul_pow]
    exact hGint
  -- ## the assembly (the structural clauses are proved directly for the packet families)
  refine ⟨(fun (n : ℕ) (X : ℝ) (ρ' : ℤ) =>
      zmodAvg (negReflect P) (arithQ ρ (max 0 l₂))
        (packetFamF ρ a 0 l₂ k₁ k₂ W₁ n X) (packetFamG ρ a 0 l₂ k₁ k₂ W₂ n X)
        (((ρ' : ℤ)) : ZMod (arithQ ρ (max 0 l₂)))),
    packetFamF ρ a 0 l₂ k₁ k₂ W₁, packetFamG ρ a 0 l₂ k₁ k₂ W₂,
    M, Ku, Kv, ?_, ?_, ?_, ⟨hMnn, hMbound⟩, ⟨hKu_nn, hKu_bound⟩, ⟨hKv_nn, hKv_bound⟩,
    hKu_int, hKv_int, ?_, ?_, hbase, hB1, hB2⟩
  · -- clause (1): the band of the `zmodAvg` of the two packet families
    intro n ρ'
    by_cases hg : goodScale (arithQ ρ (max 0 l₂)) (lcL 0 l₂ k₁ k₂) (Nat.floor (a n))
    · have hb₁ : ∀ θ : ZMod (arithQ ρ (max 0 l₂)),
          HasRealFreqSupport (fun X : ℝ => packetFamF ρ a 0 l₂ k₁ k₂ W₁ n X θ)
            (Set.Icc (-(δ₁ n)) (δ₁ n)) := by
        intro θ
        simpa only [packetFamF] using
          hasRealFreqSupport_gatedProfile_nd ρ C₀ a 0 l₂ k₁ k₂ 0 W₁ hW₁band n θ
      have hb₂ : ∀ θ : ZMod (arithQ ρ (max 0 l₂)),
          HasRealFreqSupport (fun X : ℝ => packetFamG ρ a 0 l₂ k₁ k₂ W₂ n X θ)
            (Set.Icc (-(δ₂ n)) (δ₂ n)) := by
        intro θ
        simpa only [packetFamG] using
          hasRealFreqSupport_gatedProfile_nd ρ C₀ a 0 l₂ k₁ k₂ l₂ W₂ hW₂band n θ
      exact hasRealFreqSupport_zmodAvg_packets P (arithQ ρ (max 0 l₂))
        (fun θ X => packetFamF ρ a 0 l₂ k₁ k₂ W₁ n X θ)
        (fun θ X => packetFamG ρ a 0 l₂ k₁ k₂ W₂ n X θ) hb₁ hb₂ (hβ n hg)
        (((ρ' : ℤ)) : ZMod (arithQ ρ (max 0 l₂)))
    · have hzero : (fun X : ℝ => zmodAvg (negReflect P) (arithQ ρ (max 0 l₂))
          (packetFamF ρ a 0 l₂ k₁ k₂ W₁ n X) (packetFamG ρ a 0 l₂ k₁ k₂ W₂ n X)
          (((ρ' : ℤ)) : ZMod (arithQ ρ (max 0 l₂)))) = fun _ : ℝ => (0 : ℂ) := by
        funext X
        simp only [packetFamF, packetFamG, hg, if_false, zmodAvg, mul_zero,
          Finset.sum_const_zero]
      rw [hzero]
      exact hasRealFreqSupport_zero _
  · -- clause (2): the diagonal identity
    intro n x
    by_cases hg : goodScale (arithQ ρ (max 0 l₂)) (lcL 0 l₂ k₁ k₂) (Nat.floor (a n))
    · show zmodAvg (negReflect P) (arithQ ρ (max 0 l₂))
          (packetFamF ρ a 0 l₂ k₁ k₂ W₁ n (x : ℝ)) (packetFamG ρ a 0 l₂ k₁ k₂ W₂ n (x : ℝ))
          (((x % ((arithQ ρ (max 0 l₂) : ℕ) : ℤ) : ℤ)) : ZMod (arithQ ρ (max 0 l₂)))
        = (if goodScale (arithQ ρ (max 0 l₂)) (lcL 0 l₂ k₁ k₂) (Nat.floor (a n)) then
            mdlSliceJ ρ P C₀ a f g 0 l₂ k₁ k₂ j₁ j₂ t n x else 0)
      rw [intCast_emod_eq (arithQ ρ (max 0 l₂)) x]
      exact zmodAvg_gated_packets_eq_slice ρ hρ hρ1 P C₀ a f g 0 l₂ k₁ k₂ j₁ j₂ t n x
        hj₁ hj₂ hk₁ hk₂ (W₁ n) (W₂ n)
        (fun α hα => hW₁samp n α hα x) (fun β hβ₂ => hW₂samp n β hβ₂ x)
        (hW₁sum n) (hW₂sum n)
    · simp only [packetFamF, packetFamG, hg, if_false, zmodAvg, mul_zero,
        Finset.sum_const_zero]
  · -- clause (3): the presentation is definitional
    intro n X ρ'
    rfl
  · -- clause (9): the a.e.-measurability of the `f`-side packet profile
    intro n θ
    simpa only [packetFamF] using
      aemeasurable_packetProfile_nd ρ C₀ a 0 l₂ k₁ k₂ 0 W₁ hW₁meas n θ
  · -- clause (10): the a.e.-measurability of the `g`-side packet profile
    intro n θ
    simpa only [packetFamG] using
      aemeasurable_packetProfile_nd ρ C₀ a 0 l₂ k₁ k₂ l₂ W₂ hW₂meas n θ

end

end Work.KMTPlan.A6Lead
