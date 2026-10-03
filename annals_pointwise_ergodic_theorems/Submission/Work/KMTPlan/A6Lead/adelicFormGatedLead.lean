/-
# The gated §8 adelic form: the producer, with the degenerate (`l₁ = 0 ∨ l₂ = 0`) branch split
across its three sub-cases

`Work.KMTPlan.A6Clean.AdelicFormPropRangePosB` demands the clause list
`Work.KMTPlan.A6Clean.AdelicClausesAt` on the data with `B ρ ≤ lcL l₁ l₂ k₁ k₂` (a `ρ`-only gate).

The producer `Work.KMTPlan.A6Clean.adelicFormPropRangePosB` splits its data into the *packet*
branch (`l₁ ≠ 0 ∧ l₂ ≠ 0`), where `adelicClausesCaseA` applies with the two per-scale regime
predicates `MdlLiftRegimeF`/`MdlLiftRegimeG` discharged from the gate by the PROVED
`Work.A6Clean.MdlWindowLiftRegimeNoGSB`/`MdlWindowLiftRegimeGNoGSB`, and the *degenerate* branch
(`l₁ = 0 ∨ l₂ = 0`), where the old producer called `adelicClausesCaseZero` — a lemma asking for the
clauses on **all** the degenerate data, with no gate and no regime.  That statement is **false**:
at the bounded-`lcL` data the window does not separate the arithmetic frequencies and the window
pieces cannot be lifted (verified counterexample in `A6Clean/windowPieceLiftG.lean`), which is
exactly what the clause list's presentation clause and the arithmetic-gain clauses force.  So the
degenerate branch has to be split further, each sub-case carrying the regime hypothesis that the
gate supplies:

* `l₁ = 0 ∧ l₂ = 0`: `Work.KMTPlan.A6Clean.adelicClausesCaseZeroCorner` — regime-free (at height
  `0` the frequency set is the singleton `{0}` and the separation is vacuous);
* `l₁ = 0 ∧ l₂ ≠ 0`: `Work.KMTPlan.A6Clean.adelicClausesCaseZeroFZero`, with the `g`-side regime
  `MdlLiftRegimeG` supplied by the gate;
* `l₂ = 0 ∧ l₁ ≠ 0`: `Work.KMTPlan.A6Lead.adelicClausesCaseZeroGZero` (this lane), with the
  `f`-side regime `MdlLiftRegimeF` supplied by the gate.

The four branches are glued by `Work.KMTPlan.A6Clean.adelicClausesAt_mono` (smaller `c`, larger
`A` and larger `Cin` are easier), with the combined constants
`c = min (min (min cA cC) cF) cG / 2`, `A = max (max (max AA AC) AF) AG`, `ρ₀` the minimum of the
four thresholds and of `1`, and `Cin Λ` the maximum of the four.

## Why we do not simply use `adelicClausesCaseZero`

`adelicClausesCaseZero` is stated with the *unconditional* hypothesis `l₁ = 0 ∨ l₂ = 0`; per the
counterexample above it is not provable, and in the producer the gate is exactly the extra
information that makes the degenerate data tractable.  This module is therefore the *corrected*
producer; it is a drop-in replacement (same conclusion, same name-free statement) for
`Work.KMTPlan.A6Clean.adelicFormPropRangePosB`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6Clean.adelicFormGated
import Submission.Work.KMTPlan.A6Lead.adelicClausesCaseZeroFZeroFresh
-- NOTE: the file `KMTPlan/A6Clean/adelicClausesCaseZeroFZero.lean` holds the statement of this
-- branch but its proof is broken (it relies on the impossible definitional equality
-- `u = packetFamF …` for the existential witness `u` of `packetsStructuralClausesGatedBeta`); the
-- branch is therefore taken from the fresh file below, which proves the structural clauses for the
-- *explicit* packet families, as the PROVED `adelicClausesCaseZeroCorner` does.

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6Lead

open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators
open Work.KMTAreas.A7
open Work.KMTPlan.A6
open Work.KMTPlan.A6Clean

noncomputable section

/-- **The producer of the gated adelic form, with the degenerate branch split.**

The constants are chosen before the datum (as the definition
`Work.KMTPlan.A6Clean.AdelicFormPropRangePosB` requires); the threshold is
`B = max BF BG`, where `BF`/`BG` are the two `ρ`-only regime thresholds — this is what allows the
gate `B ρ ≤ lcL l₁ l₂ k₁ k₂` to discharge the per-scale regime predicates inside the proof. -/
theorem adelicFormPropRangePosBLead (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (hA1 : Work.KMTContract.AreaA1) (hI : Work.KMTContract.ImprovKMT P) :
    ∃ B : ℝ → ℕ, Work.KMTPlan.A6Clean.AdelicFormPropRangePosB P hd hA1 hI B := by
  classical
  -- the two `ρ`-only thresholds of the regime lemmas
  let BF : ℝ → ℕ := fun ρ =>
    if h : 0 < ρ ∧ ρ ≤ 1 then
      Classical.choose (Work.A6Clean.MdlWindowLiftRegimeNoGSB ρ h.1 h.2 P hd)
    else 0
  let BG : ℝ → ℕ := fun ρ =>
    if h : 0 < ρ ∧ ρ ≤ 1 then
      Classical.choose (Work.A6Clean.MdlWindowLiftRegimeGNoGSB ρ h.1 h.2 P hd)
    else 0
  have hBF : ∀ ρ (h : 0 < ρ ∧ ρ ≤ 1), BF ρ
      = Classical.choose (Work.A6Clean.MdlWindowLiftRegimeNoGSB ρ h.1 h.2 P hd) := by
    intro ρ h
    dsimp only [BF]
    exact dif_pos h
  have hBG : ∀ ρ (h : 0 < ρ ∧ ρ ≤ 1), BG ρ
      = Classical.choose (Work.A6Clean.MdlWindowLiftRegimeGNoGSB ρ h.1 h.2 P hd) := by
    intro ρ h
    dsimp only [BG]
    exact dif_pos h
  refine ⟨fun ρ => max (BF ρ) (BG ρ), ?_⟩
  intro r hr hrT R hR hRr C₀ hC₀ j₁ j₂ hj₁ hj₂
  have hRnn : (0 : ℝ) ≤ R := le_of_lt (lt_trans (by norm_num) hR)
  have hRe : ((Real.toNNReal R : NNReal) : ℝ) = R := Real.coe_toNNReal R hRnn
  have hR' : (2 : NNReal) < Real.toNNReal R := by
    rw [← NNReal.coe_lt_coe, hRe]
    exact_mod_cast hR
  -- the four branch lemmas, at the fixed parameters
  obtain ⟨cA, hcA, AA, hAA, ρA, hρA, hA'⟩ :=
    Work.KMTPlan.A6Clean.adelicClausesCaseA P hd hI C₀ hC₀ (Real.toNNReal R) hR' r hr hrT
      j₁ j₂ hj₁ hj₂
  obtain ⟨cC, hcC, AC, hAC, ρC, hρC, hC'⟩ :=
    Work.KMTPlan.A6Clean.adelicClausesCaseZeroCorner P hd hI C₀ hC₀ (Real.toNNReal R) hR'
      r hr hrT j₁ j₂ hj₁ hj₂
  obtain ⟨cF, hcF, AF, hAF, ρF, hρF, hF'⟩ :=
    adelicClausesCaseZeroFZeroFresh P hd hI C₀ hC₀ (Real.toNNReal R) hR'
      r hr hrT j₁ j₂ hj₁ hj₂
  obtain ⟨cG, hcG, AG, hAG, ρG, hρG, hG'⟩ :=
    adelicClausesCaseZeroGZero P hd hI C₀ hC₀ (Real.toNNReal R) hR' r hr hrT j₁ j₂ hj₁ hj₂
  -- the combined constants
  refine ⟨min (min (min cA cC) cF) cG / 2, by positivity,
    max (max (max AA AC) AF) AG, ?_,
    min (min (min (min ρA ρC) ρF) ρG) 1, ?_, ?_⟩
  · exact le_trans hAA (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _)))
  · refine lt_min (lt_min (lt_min (lt_min hρA hρC) hρF) hρG) one_pos
  intro ρ hρ hρle
  have hρ1 : ρ ≤ 1 := le_trans hρle (min_le_right _ _)
  have hρA' : ρ ≤ ρA := le_trans hρle (le_trans (min_le_left _ _)
    (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _))))
  have hρC' : ρ ≤ ρC := le_trans hρle (le_trans (min_le_left _ _)
    (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))))
  have hρF' : ρ ≤ ρF := le_trans hρle (le_trans (min_le_left _ _)
    (le_trans (min_le_left _ _) (min_le_right _ _)))
  have hρG' : ρ ≤ ρG := le_trans hρle (le_trans (min_le_left _ _) (min_le_right _ _))
  obtain ⟨CinA, hCinA⟩ := hA' ρ hρ hρA'
  obtain ⟨CinC, hCinC⟩ := hC' ρ hρ hρC'
  obtain ⟨CinF, hCinF⟩ := hF' ρ hρ hρF'
  obtain ⟨CinG, hCinG⟩ := hG' ρ hρ hρG'
  refine ⟨fun Λ => max (max (max (CinA Λ) (CinC Λ)) (CinF Λ)) (CinG Λ), ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ t f g hΛ ha ha1 ht hk₁ hk₂ hf hg hLv
  have hBFle : BF ρ ≤ lcL l₁ l₂ k₁ k₂ := le_trans (le_max_left _ _) hLv
  have hBGle : BG ρ ≤ lcL l₁ l₂ k₁ k₂ := le_trans (le_max_right _ _) hLv
  -- the combined constants dominate each branch's constants
  have hc_le_A : min (min (min cA cC) cF) cG / 2 ≤ cA := by
    have h1 : min (min (min cA cC) cF) cG ≤ cA :=
      le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
    linarith [le_of_lt hcA]
  have hc_le_C : min (min (min cA cC) cF) cG / 2 ≤ cC := by
    have h1 : min (min (min cA cC) cF) cG ≤ cC :=
      le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
    linarith [le_of_lt hcC]
  have hc_le_F : min (min (min cA cC) cF) cG / 2 ≤ cF := by
    have h1 : min (min (min cA cC) cF) cG ≤ cF :=
      le_trans (min_le_left _ _) (min_le_right _ _)
    linarith [le_of_lt hcF]
  have hc_le_G : min (min (min cA cC) cF) cG / 2 ≤ cG := by
    have h1 : min (min (min cA cC) cF) cG ≤ cG := min_le_right _ _
    linarith [le_of_lt hcG]
  have hAA' : AA ≤ max (max (max AA AC) AF) AG :=
    le_trans (le_trans (le_max_left AA AC) (le_max_left (max AA AC) AF))
      (le_max_left (max (max AA AC) AF) AG)
  have hAC' : AC ≤ max (max (max AA AC) AF) AG :=
    le_trans (le_trans (le_max_right AA AC) (le_max_left (max AA AC) AF))
      (le_max_left (max (max AA AC) AF) AG)
  have hAF' : AF ≤ max (max (max AA AC) AF) AG :=
    le_trans (le_max_right (max AA AC) AF) (le_max_left (max (max AA AC) AF) AG)
  have hAG' : AG ≤ max (max (max AA AC) AF) AG := le_max_right _ _
  have hcinA' : ∀ L : NNReal, CinA L ≤ max (max (max (CinA L) (CinC L)) (CinF L)) (CinG L) :=
    fun L => le_trans (le_trans (le_max_left (CinA L) (CinC L))
      (le_max_left (max (CinA L) (CinC L)) (CinF L)))
      (le_max_left (max (max (CinA L) (CinC L)) (CinF L)) (CinG L))
  have hcinC' : ∀ L : NNReal, CinC L ≤ max (max (max (CinA L) (CinC L)) (CinF L)) (CinG L) :=
    fun L => le_trans (le_trans (le_max_right (CinA L) (CinC L))
      (le_max_left (max (CinA L) (CinC L)) (CinF L)))
      (le_max_left (max (max (CinA L) (CinC L)) (CinF L)) (CinG L))
  have hcinF' : ∀ L : NNReal, CinF L ≤ max (max (max (CinA L) (CinC L)) (CinF L)) (CinG L) :=
    fun L => le_trans (le_max_right (max (CinA L) (CinC L)) (CinF L))
      (le_max_left (max (max (CinA L) (CinC L)) (CinF L)) (CinG L))
  have hcinG' : ∀ L : NNReal, CinG L ≤ max (max (max (CinA L) (CinC L)) (CinF L)) (CinG L) :=
    fun _ => le_max_right _ _
  by_cases h1 : l₁ = 0
  · subst h1
    by_cases h2 : l₂ = 0
    · -- the corner: `l₁ = l₂ = 0`, regime-free
      subst h2
      have hcl := hCinC a Λ k₁ k₂ t f g hΛ ha ha1 ht hk₁ hk₂ hf hg
      rw [hRe] at hcl
      exact Work.KMTPlan.A6Clean.adelicClausesAt_mono P ρ R hρ.le r a Λ 0 0 k₁ k₂ t j₁ j₂
        f g C₀ hcl hc_le_C hAC' hcinC'
    · -- `l₁ = 0 < l₂`: the `g`-side regime comes from the gate
      have hregG : ∀ n, mdlCore ρ C₀ a 0 l₂ k₁ k₂ n → MdlLiftRegimeG ρ P a 0 l₂ k₁ k₂ j₂ t n := by
        intro n hn
        have hle : Classical.choose (Work.A6Clean.MdlWindowLiftRegimeGNoGSB ρ hρ hρ1 P hd)
            ≤ lcL 0 l₂ k₁ k₂ := by
          rw [← hBG ρ ⟨hρ, hρ1⟩]; exact hBGle
        exact Classical.choose_spec (Work.A6Clean.MdlWindowLiftRegimeGNoGSB ρ hρ hρ1 P hd)
          C₀ a Λ hΛ ha ha1 0 l₂ k₁ k₂ j₂ hj₂ hk₂ t ht n hn h2 hle
      have hcl := hCinF a Λ l₂ k₁ k₂ t f g hΛ ha ha1 ht hk₁ hk₂ hf hg h2 hregG
      rw [hRe] at hcl
      exact Work.KMTPlan.A6Clean.adelicClausesAt_mono P ρ R hρ.le r a Λ 0 l₂ k₁ k₂ t j₁ j₂
        f g C₀ hcl hc_le_F hAF' hcinF'
  · by_cases h2 : l₂ = 0
    · -- `l₂ = 0 < l₁`: the `f`-side regime comes from the gate
      subst h2
      have hregF : ∀ n, mdlCore ρ C₀ a l₁ 0 k₁ k₂ n → MdlLiftRegimeF ρ a l₁ 0 k₁ k₂ j₁ t n := by
        intro n hn
        have hle : Classical.choose (Work.A6Clean.MdlWindowLiftRegimeNoGSB ρ hρ hρ1 P hd)
            ≤ lcL l₁ 0 k₁ k₂ := by
          rw [← hBF ρ ⟨hρ, hρ1⟩]; exact hBFle
        exact Classical.choose_spec (Work.A6Clean.MdlWindowLiftRegimeNoGSB ρ hρ hρ1 P hd)
          C₀ a Λ hΛ ha ha1 l₁ 0 k₁ k₂ j₁ hj₁ hk₁ t ht n hn h1 hle
      have hcl := hCinG a Λ l₁ k₁ k₂ t f g hΛ ha ha1 ht hk₁ hk₂ hf hg h1 hregF
      rw [hRe] at hcl
      exact Work.KMTPlan.A6Clean.adelicClausesAt_mono P ρ R hρ.le r a Λ l₁ 0 k₁ k₂ t j₁ j₂
        f g C₀ hcl hc_le_G hAG' hcinG'
    · -- the packet branch: both regimes come from the gate
      have hregF : ∀ n, mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n → MdlLiftRegimeF ρ a l₁ l₂ k₁ k₂ j₁ t n := by
        intro n hn
        have hle : Classical.choose (Work.A6Clean.MdlWindowLiftRegimeNoGSB ρ hρ hρ1 P hd)
            ≤ lcL l₁ l₂ k₁ k₂ := by
          rw [← hBF ρ ⟨hρ, hρ1⟩]; exact hBFle
        exact Classical.choose_spec (Work.A6Clean.MdlWindowLiftRegimeNoGSB ρ hρ hρ1 P hd)
          C₀ a Λ hΛ ha ha1 l₁ l₂ k₁ k₂ j₁ hj₁ hk₁ t ht n hn h1 hle
      have hregG : ∀ n, mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n → MdlLiftRegimeG ρ P a l₁ l₂ k₁ k₂ j₂ t n := by
        intro n hn
        have hle : Classical.choose (Work.A6Clean.MdlWindowLiftRegimeGNoGSB ρ hρ hρ1 P hd)
            ≤ lcL l₁ l₂ k₁ k₂ := by
          rw [← hBG ρ ⟨hρ, hρ1⟩]; exact hBGle
        exact Classical.choose_spec (Work.A6Clean.MdlWindowLiftRegimeGNoGSB ρ hρ hρ1 P hd)
          C₀ a Λ hΛ ha ha1 l₁ l₂ k₁ k₂ j₂ hj₂ hk₂ t ht n hn h2 hle
      have hcl := hCinA a Λ l₁ l₂ k₁ k₂ t f g hΛ ha ha1 ht hk₁ hk₂ hf hg h1 h2 hregF hregG
      rw [hRe] at hcl
      exact Work.KMTPlan.A6Clean.adelicClausesAt_mono P ρ R hρ.le r a Λ l₁ l₂ k₁ k₂ t j₁ j₂
        f g C₀ hcl hc_le_A hAA' hcinA'

end

end Work.KMTPlan.A6Lead
