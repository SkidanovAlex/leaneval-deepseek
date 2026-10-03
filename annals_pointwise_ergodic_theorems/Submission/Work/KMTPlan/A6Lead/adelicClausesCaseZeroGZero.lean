/-
# The §8 adelic clauses at `l₂ = 0` (`l₁ ≠ 0`), with the `f`-side regime hypothesis

This is the `l₂ = 0` branch of the Case-Zero producer (the data with `l₁ ≠ 0`): the mirror image
of the PROVED `Work.KMTPlan.A6Clean.adelicClausesCaseZeroFZero`, with the roles of the two sides
exchanged.

* the `g`-side family is the **regime-free** height-`0` lift
  `Work.KMTPlan.A6Clean.exists_liftFamilyGZero` (`A6Clean/mdlLiftZeroOfMdlCore.lean`), whose
  vanishing clause is the one off `iwArithFreqs ρ 0 = {0}` and whose band is the input's band
  `2^{d·(k₂ - logN ⌊a n⌋)}` (bounded by `1/4` from `mdlCore` alone, see
  `two_pow_d_mul_k_sub_logN_le_quarter` below), with the data bound
  `Work.A6Clean.PacketFamGZeroUniform` (which needs no vanishing hypothesis);
* the `f`-side family is the regime-based lift
  `Work.KMTPlan.A6Clean.exists_liftFamilyFRegime`, with its data bound
  `Work.A6Clean.PacketFamFUniformAlt`;
* the arithmetic clauses come from the `f`-side alone, which is the *larger* height
  (`l₂ = 0 < l₁`), via `packetFamF_minorArc` at `L = max l₁ 0 - 1 = l₁ - 1` — no case split.

The structural clauses (1), (2), (3), (9), (10) of `Work.KMTPlan.A6Clean.AdelicClausesAt` are
proved here *directly for the packet families* `packetFamF`/`packetFamG` of
`Work.KMTPlan.A6Clean.AdelicPacketFam` — verbatim the glue of
`Work.KMTPlan.A6Clean.packetsStructuralClausesGatedBeta`, but with the two packet families
explicit, so that no definitional equality between the existential witness of that lemma and
`packetFamF`/`packetFamG` is ever needed.

The conditional regime `MdlLiftRegimeF` is supplied by the consumer
(`A6Clean/adelicFormGated.lean`'s degenerate branch has the gate `B ρ ≤ lcL l₁ l₂ k₁ k₂` in scope
and discharges the regime with `Work.A6Clean.MdlWindowLiftRegimeNoGSB`).

NOTE (see `NOTES_A6Clean_adelicClausesCaseZero_SESSION2.md`): the *unconditional* statement
(`l₁ = 0 ∨ l₂ = 0` with no regime/gate) is **not** provable: at the bounded-`lcL` data the window
does not separate the arithmetic frequencies and the window pieces cannot be lifted (verified
counterexample in `A6Clean/windowPieceLiftG.lean`), which is exactly what the clause list's
presentation clause (3) plus the arithmetic-gain clauses (4),(11)–(13) force.
-/
import Mathlib
import Submission.Work.KMTPlan.A6Clean.AdelicClausesAt
import Submission.Work.KMTPlan.A6Clean.mdlLiftZeroOfMdlCore
import Submission.Work.KMTPlan.A6Clean.exists_liftFamilyFRegime
import Submission.Work.KMTPlan.A6Clean.pfFUniformAlt
import Submission.Work.A6Clean.PacketFamGZeroUniform

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

/-- The band of the height-`0` `f`-side lift is `≤ 1/4` on the core condition (which is what the
data bound `PacketFamFUniformAlt` consumes).  This is the `≤ 1/4` form of the PROVED
`Work.KMTPlan.A6Clean.two_pow_k_sub_logN_lt_half`; it is reproduced here so that this module does
not have to import its own consumer. -/
theorem two_pow_k_sub_logN_le_quarter (ρ : ℝ) (hρ : 0 < ρ) (C₀ : ℕ) (a : ℕ → NNReal)
    (l₁ l₂ k₁ k₂ : ℕ) (n : ℕ)
    (hmc : Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n) :
    (2 : ℝ) ^ ((k₁ : ℝ) - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ)) ≤ 1 / 4 := by
  have hmain : k₁ + 2 * uScale ρ (max k₁ k₂) ≤
      (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat :=
    ((Work.KMTPlan.A6.mdlCore_iff ρ C₀ a l₁ l₂ k₁ k₂ n).mp hmc).2.2.1
  have hlog0 : (0 : ℤ) ≤ Work.Analysis.EndVar.logN (Nat.floor (a n)) :=
    Work.Analysis.EndVar.logN_nonneg _
  have ht : ((Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat : ℤ)
      = Work.Analysis.EndVar.logN (Nat.floor (a n)) := Int.toNat_of_nonneg hlog0
  have hu : (1 : ℤ) ≤ (uScale ρ (max k₁ k₂) : ℤ) := by
    exact_mod_cast one_le_uScale ρ hρ.le (max k₁ k₂)
  have hexp : (k₁ : ℤ) - Work.Analysis.EndVar.logN (Nat.floor (a n)) ≤ -2 := by
    have h1 : (k₁ : ℤ) + 2 * (uScale ρ (max k₁ k₂) : ℤ)
        ≤ Work.Analysis.EndVar.logN (Nat.floor (a n)) := by
      rw [← ht]
      exact_mod_cast hmain
    omega
  have hcast : ((k₁ : ℝ) - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ))
      = ((((k₁ : ℤ) - Work.Analysis.EndVar.logN (Nat.floor (a n))) : ℤ) : ℝ) := by
    push_cast
    ring
  rw [hcast]
  calc (2 : ℝ) ^ ((((k₁ : ℤ) - Work.Analysis.EndVar.logN (Nat.floor (a n))) : ℤ) : ℝ)
      ≤ (2 : ℝ) ^ (((-2 : ℤ)) : ℝ) := by
        refine (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr ?_
        exact_mod_cast hexp
    _ = 1 / 4 := by norm_num

/-- The band of the height-`0` `g`-side lift is `≤ 1/4` on the core condition (the `d`-scaled
analogue of `two_pow_k_sub_logN_le_quarter` above, which is what the data bound
`PacketFamGZeroUniform` consumes). -/
theorem two_pow_d_mul_k_sub_logN_le_quarter (ρ : ℝ) (hρ : 0 < ρ) (P : Polynomial ℤ)
    (hd : 2 ≤ P.natDegree) (C₀ : ℕ) (a : ℕ → NNReal)
    (l₁ l₂ k₁ k₂ n : ℕ)
    (hmc : Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n) :
    (2 : ℝ) ^ ((P.natDegree : ℝ) *
      ((k₂ : ℝ) - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ))) ≤ 1 / 4 := by
  have hmain : k₂ + 2 * uScale ρ (max k₁ k₂) ≤
      (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat :=
    ((Work.KMTPlan.A6.mdlCore_iff ρ C₀ a l₁ l₂ k₁ k₂ n).mp hmc).2.2.2
  have hlog0 : (0 : ℤ) ≤ Work.Analysis.EndVar.logN (Nat.floor (a n)) :=
    Work.Analysis.EndVar.logN_nonneg _
  have ht : ((Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat : ℤ)
      = Work.Analysis.EndVar.logN (Nat.floor (a n)) := Int.toNat_of_nonneg hlog0
  have hu : (1 : ℤ) ≤ (uScale ρ (max k₁ k₂) : ℤ) := by
    exact_mod_cast one_le_uScale ρ hρ.le (max k₁ k₂)
  have hk₂ : (k₂ : ℤ) - Work.Analysis.EndVar.logN (Nat.floor (a n)) ≤ -2 := by
    have h1 : (k₂ : ℤ) + 2 * (uScale ρ (max k₁ k₂) : ℤ)
        ≤ Work.Analysis.EndVar.logN (Nat.floor (a n)) := by
      rw [← ht]
      exact_mod_cast hmain
    omega
  have hd2 : (2 : ℤ) ≤ (P.natDegree : ℤ) := by exact_mod_cast hd
  have hexp : (P.natDegree : ℤ) * ((k₂ : ℤ) - Work.Analysis.EndVar.logN (Nat.floor (a n)))
      ≤ -4 := by
    have h2 := mul_le_mul_of_nonneg_left hk₂ (by omega : (0 : ℤ) ≤ (P.natDegree : ℤ))
    nlinarith
  have hcast : ((P.natDegree : ℝ) *
      ((k₂ : ℝ) - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ)))
      = ((((P.natDegree : ℤ) *
          ((k₂ : ℤ) - Work.Analysis.EndVar.logN (Nat.floor (a n)))) : ℤ) : ℝ) := by
    push_cast
    ring
  rw [hcast]
  calc (2 : ℝ) ^ ((((P.natDegree : ℤ) *
        ((k₂ : ℤ) - Work.Analysis.EndVar.logN (Nat.floor (a n)))) : ℤ) : ℝ)
      ≤ (2 : ℝ) ^ (((-2 : ℤ)) : ℝ) := by
        refine (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr ?_
        exact_mod_cast (le_trans hexp (by norm_num : (-4 : ℤ) ≤ -2))
    _ = 1 / 4 := by norm_num

/-- **(A6 §8 adelic producer, Case Zero, `l₂ = 0`, `l₁ ≠ 0`)** the clause list
`Work.KMTPlan.A6Clean.AdelicClausesAt` for the data with `l₂ = 0`, `l₁ ≠ 0`, *given* the per-scale
`f`-side regime `MdlLiftRegimeF` on the core scales.  The `g`-side needs no regime (the arithmetic
frequency set at height `0` is the singleton `iwArithFreqs ρ 0 = {0}`, so its separation and
non-aliasing conditions are vacuous and the lift `exists_liftFamilyGZero` exists from `mdlCore`
alone). -/
theorem adelicClausesCaseZeroGZero (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (hI : Work.KMTContract.ImprovKMT P) (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (R : NNReal) (hR : 2 < R) (r : NNReal) (hr : 2 < r) (hrT : (r : ℝ) < Work.KMTPlan.A6.adelicRTop P) (j₁ j₂ : ℤ) (hj₁ : j₁ ∈ ({-1, 0, 1} : Finset ℤ)) (hj₂ : j₂ ∈ ({-1, 0, 1} : Finset ℤ)) :
    ∃ c : ℝ, 0 < c ∧ ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ Cin : NNReal → NNReal,
        ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ k₁ k₂ : ℕ) (t : ℝ) (f g : ℤ → ℂ),
          1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n : ℕ, 1 ≤ a n) →
            t ∈ Set.Icc (1 / 2 : ℝ) 1 → (k₁ = 0 → j₁ ≠ -1) → (k₂ = 0 → j₂ ≠ -1) →
            MeasureTheory.MemLp f 2 MeasureTheory.Measure.count →
            MeasureTheory.MemLp g 2 MeasureTheory.Measure.count → l₁ ≠ 0 →
            (∀ n : ℕ, Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ 0 k₁ k₂ n →
              Work.KMTPlan.A6Clean.MdlLiftRegimeF ρ a l₁ 0 k₁ k₂ j₁ t n) →
            Work.KMTPlan.A6Clean.AdelicClausesAt P ρ R r a Λ l₁ 0 k₁ k₂ t j₁ j₂ f g C₀ c A Cin := by
  classical
  obtain ⟨cb, hcb, hbile⟩ := MdlAdelicBileClausesOr P hd hI r hr hrT
  obtain ⟨AF, hAF, ρF, hρF, hKF⟩ := Work.A6Clean.PacketFamFUniformAlt C₀ hC₀ R hR j₁ hj₁
  obtain ⟨AG, hAG, ρG, hρG, hKG⟩ := Work.A6Clean.PacketFamGZeroUniform P hd C₀ hC₀ R hR j₂ hj₂
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
  intro a Λ l₁ k₁ k₂ t f g hΛ ha ha1 ht hk₁ hk₂ hf hg hl₁ hregF
  -- ## the loss-weight comparisons at the common exponent `max AF AG`
  have hKFi : ENNReal.ofReal (lossWeight AF ρ l₁ 0 k₁ k₂)
      ≤ ENNReal.ofReal (lossWeight (max AF AG) ρ l₁ 0 k₁ k₂) :=
    ENNReal.ofReal_le_ofReal
      (Work.KMTAreas.A7Hi.lossWeight_mono (le_max_left _ _) hAF hρ.le l₁ 0 k₁ k₂)
  have hKGi : ENNReal.ofReal (lossWeight AG ρ l₁ 0 k₁ k₂)
      ≤ ENNReal.ofReal (lossWeight (max AF AG) ρ l₁ 0 k₁ k₂) :=
    ENNReal.ofReal_le_ofReal
      (Work.KMTAreas.A7Hi.lossWeight_mono (le_max_right _ _) hAG hρ.le l₁ 0 k₁ k₂)
  have hpowF : (ENNReal.ofReal (lossWeight AF ρ l₁ 0 k₁ k₂)) ^ (2 : ℕ)
      ≤ (ENNReal.ofReal (lossWeight (max AF AG) ρ l₁ 0 k₁ k₂)) ^ (2 : ℕ) :=
    pow_le_pow_left₀ zero_le hKFi 2
  have hpowG : (ENNReal.ofReal (lossWeight AG ρ l₁ 0 k₁ k₂)) ^ (2 : ℕ)
      ≤ (ENNReal.ofReal (lossWeight (max AF AG) ρ l₁ 0 k₁ k₂)) ^ (2 : ℕ) :=
    pow_le_pow_left₀ zero_le hKGi 2
  have hlwA : (0 : ℝ) ≤ lossWeight (max AF AG) ρ l₁ 0 k₁ k₂ :=
    le_trans zero_le_one
      (Work.KMTAreas.A7Hi.one_le_lossWeight_of_nonneg (max AF AG) ρ
        (le_trans hAF (le_max_left _ _)) hρ.le l₁ 0 k₁ k₂)
  -- ## the two lift families and their bands
  obtain ⟨W₁, hW₁meas, hW₁band, hW₁zero, hW₁samp, hW₁sum, hW₁zeroCore⟩ :=
    exists_liftFamilyFRegime ρ hρ hρ1 P hd C₀ a f hf l₁ 0 k₁ k₂ j₁ hj₁ hk₁ t hl₁ hregF
  obtain ⟨W₂, hW₂meas, hW₂band, hW₂zero, hW₂samp, hW₂sum, hW₂zeroCore⟩ :=
    exists_liftFamilyGZero ρ hρ hρ1 P hd C₀ a g hg l₁ k₁ k₂ j₂ hj₂ hk₂ t ha1
  let δ₁ : ℕ → ℝ := fun n => (2 : ℝ) ^ ((k₁ : ℝ) - ((logN (Nat.floor (a n)) : ℤ) : ℝ))
  let δ₂ : ℕ → ℝ :=
    fun n => (2 : ℝ) ^ ((P.natDegree : ℝ) * ((k₂ : ℝ) - ((logN (Nat.floor (a n)) : ℤ) : ℝ)))
  let β : ℝ := 1 / (8 * (arithQ ρ (max l₁ 0) : ℝ))
  have hβ : ∀ n, goodScale (arithQ ρ (max l₁ 0)) (lcL l₁ 0 k₁ k₂) (Nat.floor (a n)) →
      δ₁ n + δ₂ n ≤ β := by
    intro n hn
    simp only [δ₁, δ₂, β]
    exact goodScale_two_pow_bands_le (arithQ ρ (max l₁ 0)) (lcL l₁ 0 k₁ k₂)
      (Nat.floor (a n)) k₁ k₂ P.natDegree hd (one_le_arithQ ρ (max l₁ 0)) hn
      (le_trans (le_max_left k₁ k₂) (le_max_right _ _))
      (le_trans (le_max_right k₁ k₂) (le_max_right _ _))
  haveI : NeZero (arithQ ρ (max l₁ 0)) :=
    ⟨Nat.pos_iff_ne_zero.mp (arithQ_pos ρ (max l₁ 0))⟩
  -- ## the arithmetic clauses: the `f`-side (the larger height) is minor arc
  have hminor : ∀ (n : ℕ) (X : ℝ), MdlIwMinorArc ρ (max l₁ 0 - 1) (arithQ ρ (max l₁ 0))
      (packetFamF ρ a l₁ 0 k₁ k₂ W₁ n X) := by
    intro n X
    have hmax : max l₁ 0 - 1 = l₁ - 1 := by rw [Nat.max_eq_left (Nat.zero_le l₁)]
    rw [hmax]
    exact packetFamF_minorArc ρ hρ hρ1 a l₁ 0 k₁ k₂ (W₁ n)
      (fun α hα => hW₁zero n α hα) n X
  have hb3 := hbileC (arithQ ρ (max l₁ 0)) (max l₁ 0 - 1)
    (packetFamF ρ a l₁ 0 k₁ k₂ W₁) (packetFamG ρ a l₁ 0 k₁ k₂ W₂) (Or.inl hminor)
  obtain ⟨hbase, hB1, hB2⟩ := hb3
  let M : ℝ := Cb * (2 : ℝ) ^ (-(cb * (((max l₁ 0 - 1 : ℕ)) : ℝ)))
  have hMnn : 0 ≤ M := by
    simp only [M]
    exact mul_nonneg hCbpos.le (Real.rpow_pos_of_pos (by norm_num) _).le
  have hMbound : ENNReal.ofReal M ≤ (Cin Λ : ENNReal)
      * ENNReal.ofReal ((2 : ℝ) ^ (-(cb * max ((l₁ : ℕ) : ℝ) ((0 : ℕ) : ℝ)))) := by
    have hmax1 : 1 ≤ max l₁ 0 := le_trans (Nat.one_le_iff_ne_zero.mpr hl₁) (le_max_left _ _)
    have h2 : (2 : ℝ) ^ (-(cb * (((max l₁ 0 - 1 : ℕ)) : ℝ)))
        = (2 : ℝ) ^ cb * (2 : ℝ) ^ (-(cb * ((max l₁ 0 : ℕ) : ℝ))) := by
      rw [Nat.cast_sub hmax1, Nat.cast_one,
        show -(cb * (((max l₁ 0 : ℕ) : ℝ) - 1))
            = -(cb * ((max l₁ 0 : ℕ) : ℝ)) + cb by ring,
        Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      ring
    have hfac : M = (Cb * (2 : ℝ) ^ cb) * (2 : ℝ) ^ (-(cb * ((max l₁ 0 : ℕ) : ℝ))) := by
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
  -- ## the `f`-side data bound (regime family)
  have hband₁4 : ∀ (n : ℕ) (α : Circ),
      HasRealFreqSupport (W₁ n α) (Set.Icc (-(1 / 4 : ℝ)) (1 / 4)) := by
    intro n α
    by_cases hc : Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ 0 k₁ k₂ n
    · have hquarter : (2 : ℝ) ^ ((k₁ : ℝ) - ((logN (Nat.floor (a n)) : ℤ) : ℝ)) ≤ 1 / 4 :=
        two_pow_k_sub_logN_le_quarter ρ hρ C₀ a l₁ 0 k₁ k₂ n hc
      refine hasRealFreqSupport_mono (fun x hx => ?_) (hW₁band n α)
      simp only [Set.mem_Icc] at hx ⊢
      exact ⟨by linarith [hx.1, hquarter], by linarith [hx.2, hquarter]⟩
    · rw [hW₁zeroCore n hc]
      exact hasRealFreqSupport_zero _
  have hFint : ∫⁻ X : ℝ, (VrLiftDataP (R : ℝ) (arithQ ρ (max l₁ 0))
        (fun n : ℕ => packetFamF ρ a l₁ 0 k₁ k₂ W₁ n X)) ^ (2 : ℕ)
      ≤ (KF Λ : ENNReal) ^ (2 : ℕ)
        * (ENNReal.ofReal (lossWeight (max AF AG) ρ l₁ 0 k₁ k₂)) ^ (2 : ℕ)
        * (MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count) ^ (2 : ℕ) := by
    refine le_trans (hKF' a Λ l₁ 0 k₁ k₂ t f W₁ hΛ ha ha1 hf ht hk₁ hband₁4
      (fun n α hα x => hW₁samp n α (mem_iwArithFreqsNew_le hα) x)
      (fun n α hα => hW₁zero n α hα)) ?_
    exact mul_le_mul' (mul_le_mul_right hpowF ((KF Λ : ENNReal) ^ (2 : ℕ))) le_rfl
  let F₂ : ℝ := (MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count).toReal
  have hF₂ : ENNReal.ofReal F₂ = MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
    simp only [F₂, ENNReal.ofReal_toReal (MeasureTheory.MemLp.eLpNorm_lt_top hf).ne]
  let Ku : ℝ := ((KF Λ : NNReal) : ℝ) * lossWeight (max AF AG) ρ l₁ 0 k₁ k₂ * F₂
  have hKu_nn : 0 ≤ Ku := by
    simp only [Ku]
    exact mul_nonneg (mul_nonneg (NNReal.coe_nonneg _) hlwA) (ENNReal.toReal_nonneg)
  have hKu_eq : ENNReal.ofReal Ku = (KF Λ : ENNReal)
      * ENNReal.ofReal (lossWeight (max AF AG) ρ l₁ 0 k₁ k₂)
      * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
    rw [show Ku = ((KF Λ : NNReal) : ℝ) * lossWeight (max AF AG) ρ l₁ 0 k₁ k₂ * F₂ from rfl,
      ENNReal.ofReal_mul (mul_nonneg (NNReal.coe_nonneg _) hlwA),
      ENNReal.ofReal_mul (NNReal.coe_nonneg _), hF₂, ENNReal.ofReal_coe_nnreal]
  have hKu_bound : ENNReal.ofReal Ku ≤ (Cin Λ : ENNReal)
      * ENNReal.ofReal (lossWeight (max AF AG) ρ l₁ 0 k₁ k₂)
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
      (mul_le_mul_left hstep (ENNReal.ofReal (lossWeight (max AF AG) ρ l₁ 0 k₁ k₂))) le_rfl
  have hKu_int : ∫⁻ X : ℝ, (VrLiftDataP (R : ℝ) (arithQ ρ (max l₁ 0))
        (fun n : ℕ => packetFamF ρ a l₁ 0 k₁ k₂ W₁ n X)) ^ (2 : ℕ)
      ≤ ENNReal.ofReal (Ku ^ 2) := by
    rw [ENNReal.ofReal_pow hKu_nn, hKu_eq, mul_pow, mul_pow]
    exact hFint
  -- ## the `g`-side data bound (height `0`, no vanishing hypothesis)
  have hband₂4 : ∀ (n : ℕ) (α : Circ),
      HasRealFreqSupport (W₂ n α) (Set.Icc (-(1 / 4 : ℝ)) (1 / 4)) := by
    intro n α
    by_cases hc : Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ 0 k₁ k₂ n
    · have hquarter : (2 : ℝ) ^ ((P.natDegree : ℝ) *
          ((k₂ : ℝ) - ((logN (Nat.floor (a n)) : ℤ) : ℝ))) ≤ 1 / 4 :=
        two_pow_d_mul_k_sub_logN_le_quarter ρ hρ P hd C₀ a l₁ 0 k₁ k₂ n hc
      refine hasRealFreqSupport_mono (fun x hx => ?_) (hW₂band n α)
      simp only [Set.mem_Icc] at hx ⊢
      exact ⟨by linarith [hx.1, hquarter], by linarith [hx.2, hquarter]⟩
    · rw [hW₂zeroCore n hc]
      exact hasRealFreqSupport_zero _
  have hGint : ∫⁻ X : ℝ, (VrLiftDataP (R : ℝ) (arithQ ρ (max l₁ 0))
        (fun n : ℕ => packetFamG ρ a l₁ 0 k₁ k₂ W₂ n X)) ^ (2 : ℕ)
      ≤ (KG Λ : ENNReal) ^ (2 : ℕ)
        * (ENNReal.ofReal (lossWeight (max AF AG) ρ l₁ 0 k₁ k₂)) ^ (2 : ℕ)
        * (MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count) ^ (2 : ℕ) := by
    refine le_trans (hKG' a Λ l₁ k₁ k₂ t g W₂ hΛ ha ha1 hg ht hk₂ hband₂4
      (fun n α hα x => hW₂samp n α hα x)) ?_
    exact mul_le_mul' (mul_le_mul_right hpowG ((KG Λ : ENNReal) ^ (2 : ℕ))) le_rfl
  let G₂ : ℝ := (MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count).toReal
  have hG₂ : ENNReal.ofReal G₂ = MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
    simp only [G₂, ENNReal.ofReal_toReal (MeasureTheory.MemLp.eLpNorm_lt_top hg).ne]
  let Kv : ℝ := ((KG Λ : NNReal) : ℝ) * lossWeight (max AF AG) ρ l₁ 0 k₁ k₂ * G₂
  have hKv_nn : 0 ≤ Kv := by
    simp only [Kv]
    exact mul_nonneg (mul_nonneg (NNReal.coe_nonneg _) hlwA) (ENNReal.toReal_nonneg)
  have hKv_eq : ENNReal.ofReal Kv = (KG Λ : ENNReal)
      * ENNReal.ofReal (lossWeight (max AF AG) ρ l₁ 0 k₁ k₂)
      * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
    rw [show Kv = ((KG Λ : NNReal) : ℝ) * lossWeight (max AF AG) ρ l₁ 0 k₁ k₂ * G₂ from rfl,
      ENNReal.ofReal_mul (mul_nonneg (NNReal.coe_nonneg _) hlwA),
      ENNReal.ofReal_mul (NNReal.coe_nonneg _), hG₂, ENNReal.ofReal_coe_nnreal]
  have hKv_bound : ENNReal.ofReal Kv ≤ (Cin Λ : ENNReal)
      * ENNReal.ofReal (lossWeight (max AF AG) ρ l₁ 0 k₁ k₂)
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
      (mul_le_mul_left hstep (ENNReal.ofReal (lossWeight (max AF AG) ρ l₁ 0 k₁ k₂))) le_rfl
  have hKv_int : ∫⁻ X : ℝ, (VrLiftDataP (R : ℝ) (arithQ ρ (max l₁ 0))
        (fun n : ℕ => packetFamG ρ a l₁ 0 k₁ k₂ W₂ n X)) ^ (2 : ℕ)
      ≤ ENNReal.ofReal (Kv ^ 2) := by
    rw [ENNReal.ofReal_pow hKv_nn, hKv_eq, mul_pow, mul_pow]
    exact hGint
  -- ## the assembly (the structural clauses are proved directly for the packet families)
  refine ⟨(fun (n : ℕ) (X : ℝ) (ρ' : ℤ) =>
      zmodAvg (negReflect P) (arithQ ρ (max l₁ 0))
        (packetFamF ρ a l₁ 0 k₁ k₂ W₁ n X) (packetFamG ρ a l₁ 0 k₁ k₂ W₂ n X)
        (((ρ' : ℤ)) : ZMod (arithQ ρ (max l₁ 0)))),
    packetFamF ρ a l₁ 0 k₁ k₂ W₁, packetFamG ρ a l₁ 0 k₁ k₂ W₂,
    M, Ku, Kv, ?_, ?_, ?_, ⟨hMnn, hMbound⟩, ⟨hKu_nn, hKu_bound⟩, ⟨hKv_nn, hKv_bound⟩,
    hKu_int, hKv_int, ?_, ?_, hbase, hB1, hB2⟩
  · -- clause (1): the band of the `zmodAvg` of the two packet families
    intro n ρ'
    by_cases hg : goodScale (arithQ ρ (max l₁ 0)) (lcL l₁ 0 k₁ k₂) (Nat.floor (a n))
    · have hb₁ : ∀ θ : ZMod (arithQ ρ (max l₁ 0)),
          HasRealFreqSupport (fun X : ℝ => packetFamF ρ a l₁ 0 k₁ k₂ W₁ n X θ)
            (Set.Icc (-(δ₁ n)) (δ₁ n)) := by
        intro θ
        simpa only [packetFamF] using
          hasRealFreqSupport_gatedProfile_nd ρ C₀ a l₁ 0 k₁ k₂ l₁ W₁ hW₁band n θ
      have hb₂ : ∀ θ : ZMod (arithQ ρ (max l₁ 0)),
          HasRealFreqSupport (fun X : ℝ => packetFamG ρ a l₁ 0 k₁ k₂ W₂ n X θ)
            (Set.Icc (-(δ₂ n)) (δ₂ n)) := by
        intro θ
        simpa only [packetFamG] using
          hasRealFreqSupport_gatedProfile_nd ρ C₀ a l₁ 0 k₁ k₂ 0 W₂ hW₂band n θ
      exact hasRealFreqSupport_zmodAvg_packets P (arithQ ρ (max l₁ 0))
        (fun θ X => packetFamF ρ a l₁ 0 k₁ k₂ W₁ n X θ)
        (fun θ X => packetFamG ρ a l₁ 0 k₁ k₂ W₂ n X θ) hb₁ hb₂ (hβ n hg)
        (((ρ' : ℤ)) : ZMod (arithQ ρ (max l₁ 0)))
    · have hzero : (fun X : ℝ => zmodAvg (negReflect P) (arithQ ρ (max l₁ 0))
          (packetFamF ρ a l₁ 0 k₁ k₂ W₁ n X) (packetFamG ρ a l₁ 0 k₁ k₂ W₂ n X)
          (((ρ' : ℤ)) : ZMod (arithQ ρ (max l₁ 0)))) = fun _ : ℝ => (0 : ℂ) := by
        funext X
        simp only [packetFamF, packetFamG, hg, if_false, zmodAvg, mul_zero,
          Finset.sum_const_zero]
      rw [hzero]
      exact hasRealFreqSupport_zero _
  · -- clause (2): the diagonal identity
    intro n x
    by_cases hg : goodScale (arithQ ρ (max l₁ 0)) (lcL l₁ 0 k₁ k₂) (Nat.floor (a n))
    · show zmodAvg (negReflect P) (arithQ ρ (max l₁ 0))
          (packetFamF ρ a l₁ 0 k₁ k₂ W₁ n (x : ℝ)) (packetFamG ρ a l₁ 0 k₁ k₂ W₂ n (x : ℝ))
          (((x % ((arithQ ρ (max l₁ 0) : ℕ) : ℤ) : ℤ)) : ZMod (arithQ ρ (max l₁ 0)))
        = (if goodScale (arithQ ρ (max l₁ 0)) (lcL l₁ 0 k₁ k₂) (Nat.floor (a n)) then
            mdlSliceJ ρ P C₀ a f g l₁ 0 k₁ k₂ j₁ j₂ t n x else 0)
      rw [intCast_emod_eq (arithQ ρ (max l₁ 0)) x]
      exact zmodAvg_gated_packets_eq_slice ρ hρ hρ1 P C₀ a f g l₁ 0 k₁ k₂ j₁ j₂ t n x
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
      aemeasurable_packetProfile_nd ρ C₀ a l₁ 0 k₁ k₂ l₁ W₁ hW₁meas n θ
  · -- clause (10): the a.e.-measurability of the `g`-side packet profile
    intro n θ
    simpa only [packetFamG] using
      aemeasurable_packetProfile_nd ρ C₀ a l₁ 0 k₁ k₂ 0 W₂ hW₂meas n θ

end

end Work.KMTPlan.A6Lead
