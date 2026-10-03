/-
# The uniform `ℓ²` bound for the exact-height model input `Π_{l,≤-du} g`

The §6/§8 model input of the `(2,2,1)` paraproduct estimate is the exact-height Ionescu--Wainger
projection

  `mdlG ρ P u l g = piExact (kmtPj ρ) l (-(d·u)) g`,  `d = P.natDegree`, `u = uScale ρ L`,

i.e. the paper's `G = Π_{l₂,≤-du} g`: arithmetic height *exactly* `l` and continuous height
`-d·u`, very negative.  The paraproduct estimate consumes it only through the `ℓ²` bound

  `‖Π_{l,≤-du} g‖_{ℓ²(ℤ)} ≤ C (1 + l) ‖g‖_{ℓ²(ℤ)}`

with a constant `C` independent of the scale `L` and of the height `l ≤ L`.

## The proof

The operator is the Fourier multiplier with symbol

  `piSym ρ l c = iwSymbolSet (diffFreqs ρ l) (etSym c)`,  `c = -(d·u)`,
  `diffFreqs ρ l = (ℚ/ℤ)_{≤l} \ (ℚ/ℤ)_{≤l-1}`,  `etSym c = periodize (η_{≤c})`,

so Plancherel gives `‖Π_{l,≤c} g‖₂ ≤ M ‖g‖₂` for any pointwise bound `M` on the symbol
(`piExact_two_le_of_symbol_bound`).  Two regimes give such a bound uniformly in `(L,l)`:

* **good scales** `L ≥ B`: the arithmetic frequencies `diffFreqs ρ l` are non-aliasing at the arc
  radius `2^c` (`nonAliasingDiffFreqsR`, whose level is `-(r · uScale ρ L)` with `r = d ≥ 2`, so
  the window `c = -(d·uScale ρ L)` is narrower), hence at each frequency at most one summand of
  the symbol is nonzero and the sup norm is at most `sup‖etSym c‖ ≤ 4`
  (`etSym_norm_le_four_uniform`), because `c ≤ 0 ≤ 1` and a bump of radius `2^c ≤ 2` has at most
  four overlapping integer translates;
* **bad scales** `L < B`: there are only finitely many of them, and on them `l ≤ L < B`, so the
  crude cardinality bound `sup‖symbol‖ ≤ 4·#(diffFreqs ρ l) ≤ 4·#(ℚ/ℤ)_{≤B}` applies.

Taking `C = max 4 (4·#(ℚ/ℤ)_{≤B} + 4)` finishes, the factor `(1 + l)` being harmless since
`1 + l ≥ 1`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.MdlDefs
import Submission.Work.KMTAreas.A7.LargeInterface
import Submission.Work.KMTPlan.A6.besselG
import Submission.Work.KMTPlan.A6.eLpNorm_iwConv_two_le_of_symbol_bound
import Submission.Work.KMTPlan.A6.nonAliasingDiffFreqsR

set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

open MeasureTheory
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger

noncomputable section

/-! ## The two component estimates -/

/-- **For `c ≤ 1` the periodised cutoff `η_{≤c}` is bounded by `4`.**  The support of
`etaCut kmtEta c` has radius `2^c ≤ 2`, so at the representative `u ∈ [0,1)` only the four
periods `k ∈ [-2,1]` can contribute, each by at most `1`. -/
theorem etSym_norm_le_four_uniform (c : ℤ) (hc : c ≤ 1) (ξ : Circ_bG) : ‖etSym c ξ‖ ≤ 4 := by
  rw [etSym, periodize]
  set u : ℝ := (AddCircle.equivIco (1 : ℝ) 0 ξ).val with hu
  have huI : u ∈ Set.Ico (0 : ℝ) 1 := by
    rw [hu]; simpa using (AddCircle.equivIco (1 : ℝ) 0 ξ).2
  rw [Set.mem_Ico] at huI
  have h2c : (2 : ℝ) ^ c ≤ 2 := by
    have h2 : (2 : ℝ) ^ c ≤ (2 : ℝ) ^ (1 : ℤ) := zpow_le_zpow_right₀ (by norm_num) hc
    simpa using h2
  have hsupp : ∀ k : ℤ, k ∉ Finset.Icc (-2 : ℤ) 1 →
      etaCut Work.KMTContract.kmtEta c (u + k) = 0 := by
    intro k hk
    rw [Finset.mem_Icc, not_and, not_le] at hk
    refine etaCut_eq_zero_of_le c ?_
    rcases lt_or_ge k (-2) with h | h
    · have hk3 : (k : ℝ) ≤ -3 := by exact_mod_cast (by omega : k ≤ -3)
      have hneg : u + (k : ℝ) < 0 := by linarith [huI.2]
      rw [abs_of_neg hneg]
      linarith
    · have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 2 ≤ k)
      have hpos : 0 < u + (k : ℝ) := by linarith [huI.1]
      rw [abs_of_pos hpos]
      linarith
  rw [tsum_eq_sum hsupp]
  calc ‖∑ k ∈ Finset.Icc (-2 : ℤ) 1,
        etaCut Work.KMTContract.kmtEta c (u + k)‖
      ≤ ∑ k ∈ Finset.Icc (-2 : ℤ) 1,
          ‖etaCut Work.KMTContract.kmtEta c (u + k)‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.Icc (-2 : ℤ) 1, (1 : ℝ) :=
        Finset.sum_le_sum fun k _ => norm_etaCut_le_one c (u + k)
    _ = 4 := by
        rw [Finset.sum_const]
        have hcard : (Finset.Icc (-2 : ℤ) 1).card = 4 := by decide
        rw [hcard]; norm_num

/-- **The `ℓ²` bound for the exact-height projection from a pointwise bound on its symbol.**
If `‖iwSymbolSet (diffFreqs ρ l) (etSym c) ξ‖ ≤ M` at every frequency `ξ`, then
`‖Π_{l,≤c} g‖_{ℓ²} ≤ M ‖g‖_{ℓ²}` for every `g : ℤ → ℂ`.

For `g ∈ ℓ²` this is Plancherel: `piExact_eq_multiplier` identifies `Π_{l,≤c}` with the Fourier
multiplier of that symbol, and `eLpNorm_iwConv_two_le_of_symbol_bound` converts a symbol bound into
an operator bound.  For `g ∉ ℓ²` the right-hand side is `⊤` (because `0 < M`), so no integrability
of `g` is needed. -/
theorem piExact_two_le_of_symbol_bound (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (l : ℕ) (c : ℤ)
    {M : ℝ} (hM : 0 < M)
    (hsup : ∀ ξ : Circ_bG,
      ‖iwSymbolSet (Work.KMTAreas.A7.diffFreqs ρ l) (etSym c) ξ‖ ≤ M)
    (g : ℤ → ℂ) :
    MeasureTheory.eLpNorm
        (Work.Analysis.EndVar.piExact (Work.KMTContract.kmtPj ρ) l c g) 2
        MeasureTheory.Measure.count
      ≤ ENNReal.ofReal M * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
  classical
  by_cases hg : MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count = ⊤
  · rw [hg, ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr hM))]
    exact le_top
  · have hgmem : MeasureTheory.MemLp g 2 MeasureTheory.Measure.count :=
      MeasureTheory.memLp_iff.mpr (lt_top_iff_ne_top.mpr hg)
    have hmem : MeasureTheory.MemLp
        (iwSymbolSet (Work.KMTAreas.A7.diffFreqs ρ l) (etSym c)) ⊤ circleMeasure :=
      memLp_iwSym (Work.KMTAreas.A7.diffFreqs ρ l) c
    have hbound := eLpNorm_iwConv_two_le_of_symbol_bound
      (Work.KMTAreas.A7.diffFreqs ρ l) (etSym c) M hM.le hsup hmem g hgmem
    have hconv : Work.Analysis.EndVar.piExact (Work.KMTContract.kmtPj ρ) l c g
        = Work.Analysis.IWMultiplier.iwConv (Work.KMTAreas.A7.diffFreqs ρ l) (etSym c) g := by
      have h1 : Work.Analysis.EndVar.piExact (Work.KMTContract.kmtPj ρ) l c
            (⇑(toL2Z hgmem))
          = ⇑(multiplierOf (piSym ρ l c) (memLp_piSym ρ l c) (toL2Z hgmem)) :=
        piExact_eq_multiplier ρ hρ hρ1 l c (toL2Z hgmem)
      rw [multiplierOf_congr_bG' (memLp_piSym ρ l c) hmem (by rfl)] at h1
      rw [toL2Z_coe hgmem] at h1
      calc Work.Analysis.EndVar.piExact (Work.KMTContract.kmtPj ρ) l c g
          = ⇑(multiplierOf (iwSymbolSet (Work.KMTAreas.A7.diffFreqs ρ l) (etSym c))
              hmem (toL2Z hgmem)) := h1
        _ = ⇑(iwOpSet (Work.KMTAreas.A7.diffFreqs ρ l) (etSym c) hmem (toL2Z hgmem)) := rfl
        _ = Work.Analysis.IWMultiplier.iwConv (Work.KMTAreas.A7.diffFreqs ρ l) (etSym c)
              (⇑(toL2Z hgmem)) := (iwConvEqIwOpSetMemlp hmem (toL2Z hgmem)).symm
        _ = Work.Analysis.IWMultiplier.iwConv (Work.KMTAreas.A7.diffFreqs ρ l) (etSym c) g := by
              rw [toL2Z_coe hgmem]
    rw [hconv]
    exact hbound

/-! ## The requested uniform bound -/

/-- **The model input `G = Π_{l,≤-du} g` obeys the `ℓ²` bound with a height-linear loss.**  The
constant is `max 4 (4·#(ℚ/ℤ)_{≤B} + 4)`, where `B` is the good-major-arcs threshold of
`nonAliasingDiffFreqsR`: for `L ≥ B` the symbol of `Π_{l,≤-du}` has at most one nonzero summand
(non-aliasing) and sup norm `≤ 4`, while for the finitely many scales `L < B` the crude bound
`sup ≤ 4·#(diffFreqs ρ l) ≤ 4·#(iwArithFreqs ρ B)` applies, since `l ≤ L < B`. -/
theorem mdlG_two_le_uniform (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) : ∃ C : ℝ, 0 < C ∧ ∀ (L l : ℕ), l ≤ L → ∀ g : ℤ → ℂ, MeasureTheory.eLpNorm (Work.KMTPlan.A6.mdlG ρ P (Work.KMTAreas.A7.uScale ρ L) l g) 2 MeasureTheory.Measure.count ≤ ENNReal.ofReal (C * (1 + (l : ℝ))) * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
  classical
  obtain ⟨B, hB⟩ := nonAliasingDiffFreqsR ρ hρ hρ1
  set C : ℝ := max 4 (4 * ((iwArithFreqs ρ B).card : ℝ) + 4) with hC
  have hCpos : 0 < C := by rw [hC]; exact lt_max_of_lt_left (by norm_num)
  refine ⟨C, hCpos, ?_⟩
  intro L l hl g
  set u : ℕ := Work.KMTAreas.A7.uScale ρ L with hu
  set c : ℤ := -((P.natDegree : ℤ) * (u : ℤ)) with hcu
  have hc1 : c ≤ 1 := by
    rw [hcu]
    have h0 : (0 : ℤ) ≤ (P.natDegree : ℤ) * (u : ℤ) := by positivity
    linarith
  have hmdl : Work.KMTPlan.A6.mdlG ρ P (Work.KMTAreas.A7.uScale ρ L) l g
      = Work.Analysis.EndVar.piExact (Work.KMTContract.kmtPj ρ) l c g := by
    rw [hcu, hu]
    rfl
  -- The sup norm of the symbol, in the two regimes.
  have hsup : ∀ ξ : Circ_bG,
      ‖iwSymbolSet (Work.KMTAreas.A7.diffFreqs ρ l) (etSym c) ξ‖ ≤ C := by
    intro ξ
    by_cases hBL : B ≤ L
    · have hNA : NonAliasing c (Work.KMTAreas.A7.diffFreqs ρ l) := by
        rw [hcu, hu]
        exact hB L l P.natDegree hBL hl (by omega)
      have hSupp : SupportedInArc c (etSym c) :=
        supportedInArc_periodize (k := c) (φ := etaCut Work.KMTContract.kmtEta c)
          (fun x hx => Work.KMTAreas.A7.etaCut_ne_zero_mem_realArc c hx)
          (fun x => Work.KMTAreas.A7.summable_etaCut_shift c x)
      exact (norm_iwSymbolSet_le_of_nonAliasing hNA hSupp (by norm_num)
        (fun ξ => etSym_norm_le_four_uniform c hc1 ξ) ξ).trans (le_max_left _ _)
    · have hlB : l ≤ B := le_trans hl (le_of_lt (lt_of_not_ge hBL))
      have hsub : Work.KMTAreas.A7.diffFreqs ρ l ⊆ iwArithFreqs ρ B := by
        have h1 : Work.KMTAreas.A7.diffFreqs ρ l ⊆ iwArithFreqs ρ l := by
          by_cases h0 : l = 0
          · rw [Work.KMTAreas.A7.diffFreqs, if_pos h0, h0]
          · rw [Work.KMTAreas.A7.diffFreqs, if_neg h0]
            exact Finset.sdiff_subset
        exact h1.trans (iwArithFreqs_mono hρ hρ1 hlB)
      have hcard : (Work.KMTAreas.A7.diffFreqs ρ l).card ≤ (iwArithFreqs ρ B).card :=
        Finset.card_le_card hsub
      have hbound : ‖iwSymbolSet (Work.KMTAreas.A7.diffFreqs ρ l) (etSym c) ξ‖
          ≤ ((Work.KMTAreas.A7.diffFreqs ρ l).card : ℝ) * 4 :=
        norm_iwSymbolSet_le (Work.KMTAreas.A7.diffFreqs ρ l)
          (fun ξ => etSym_norm_le_four_uniform c hc1 ξ) ξ
      have hcardR : ((Work.KMTAreas.A7.diffFreqs ρ l).card : ℝ)
          ≤ ((iwArithFreqs ρ B).card : ℝ) := by exact_mod_cast hcard
      calc ‖iwSymbolSet (Work.KMTAreas.A7.diffFreqs ρ l) (etSym c) ξ‖
          ≤ ((Work.KMTAreas.A7.diffFreqs ρ l).card : ℝ) * 4 := hbound
        _ ≤ 4 * ((iwArithFreqs ρ B).card : ℝ) := by linarith
        _ ≤ 4 * ((iwArithFreqs ρ B).card : ℝ) + 4 := by linarith
        _ ≤ C := by rw [hC]; exact le_max_right _ _
  have hmain := piExact_two_le_of_symbol_bound ρ hρ hρ1 l c hCpos hsup g
  rw [hmdl]
  refine hmain.trans ?_
  have h1 : (1 : ℝ) ≤ 1 + (l : ℝ) := by
    have hl0 : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
    linarith
  have h2 : C ≤ C * (1 + (l : ℝ)) := by
    calc C = C * 1 := by ring
      _ ≤ C * (1 + (l : ℝ)) := mul_le_mul_of_nonneg_left h1 hCpos.le
  exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal h2) zero_le

end

end Work.KMTPlan.A6
