/-
# The per-residue fibre estimate of the mixed range (KMT §8) — the reduction

Target: `Work.KMTAreas.A7MixedG.FiberLargeResidueCore` (the per-residue, uniform-in-`n₀`
large-scale fibre estimate of the mixed `g`-side; it is the body of
`Work.KMTAreas.A7MixedG.FiberLargeResidue`).

## The shape of the proof (see the file `NOTES_A7MixedG_FiberLargeResidueCore.md`)

Fix `P`, `p₂ ∈ (1,∞)`.  Choose `A := 8`, `ρ₀ := 1`, `B := 0`; for fixed `ρ ∈ (0,1]` the constant
`C : NNReal → NNReal` is chosen after `ρ`.

For each instance the proof splits on the size of `L := max l₂ (max k₁ k₂)`:

* **Case 1 (`l₂ ≤ B₁ ρ`, the "small-scale" regime).**  The crude variational Young bound
  (`Work.KMTAreas.A7.fiberOpVarYoungExact`) has constant `#(ℚ/ℤ)_{l₂} · ∑_j ‖cw m_* j‖`; both
  factors are uniformly bounded on the bounded box `l₂ ≤ B₁ ρ` (the first because `#(ℚ/ℤ)_{l₂}` is
  monotone over a finite range, the second by `Work.A7.exists_cw_mStargF_tsum_le`).  This gives the
  estimate for *all* families, in particular for `GmixedFam`.  Proved here
  (`fiberOpP_young_bound`).

* **Case 2 (`L > B₁ ρ`, the "large-scale" regime).**  The guard of `GmixedFam` supplies
  `splitCut ρ L < ⌊a n⌋`, and the arithmetic of `Work.KMTAreas.A7.farey_and_strict_of_large_L`
  (`lmax_le_of_not_farey`) turns `L > B₁ ρ` into the quantitative hypotheses of the paper's
  sampling/aliasing analysis: the Farey gap condition, the strict main regime (the packet band
  `2^{k₂}/N` inside the plateau of the cut `mStargF d U`), and the non-aliasing of the
  exact-height frequency set.  Under those, the composite
  `fiberOpP ρ P l₂ (GmixedKer …) n₀ ∘ Tm ρ l₂ (varphitildeNt …)` is — via the *aliasing product
  identity* (`Work.KMTAreas.A7.aliasingSymbolProduct`) and the plateau of `mStargF` — the
  *twisted* Ionescu–Wainger projection `n ↦ iwConv (iwArithFreqsNew ρ l₂) (ψ̃_n e(-P(n₀)·))`, and
  the comparison with the physical shift is the deep input
  `Work.KMTAreas.A7MixedG.FiberLargeResidueLargeScalesProp` (delegated).

## Status

**The finish.**  The large-scale branch is the `Prop` `FiberLargeResidueLargeScalesProp` below, and
the reduction `FiberLargeResidueCore_of_largeScales` derives the target from it.  That `Prop` is
proved in this very file, inside the auxiliary namespace `CruxAux` (as
`CruxAux.fiberLargeResidueLargeScalesProp_holds`): a self-contained copy of the proof of the
colleague's theorem `Work.A7MixedG.fiberLargeResidueLargeScalesProp_holds`, which lives in the
module `Submission/Work/A7MixedG/FiberLargeResidueHolds.lean`.  The copy is necessary because that
module *imports this one*, so importing it back is an import cycle.

The Case-1 bound is proved below, together with the three arithmetic/dispatching lemmas that turn
the guard into the hypotheses of the large-scale branch (`nonAliasing_Gmixed`,
`gside_farey_of_large_L`, `plateau_of_large_L`).  The large-scale branch itself is named as the
`Prop` `FiberLargeResidueLargeScalesProp`, and `FiberLargeResidueCore_of_largeScales` proves the target
from it; so the target is reduced to that single Prop (the paper's §8).

The Case-1 bound is proved below.  The Case-2 comparison (the paper's §8 quantitative
Shannon/decimation transfer with the twist-vs-shift error, cf. the session notes of the
`A7Hi/fiberOpRephasingUniformBound` family) is isolated as the named input
`FiberLargeResidueLargeScalesProp`; the target is derived from it in
`FiberLargeResidueCore_of_largeScales`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7Hi.FiberVarSamplingGLarge
import Submission.Work.KMTAreas.A7Hi.FiberOpTexFixNarrow
import Submission.Work.KMTAreas.A7Hi.residueLp_fiberOpP_le_of_range
import Submission.Work.A7MixedG.eLpNorm_le_of_tsum_rpow_le
import Submission.Work.KMTAreas.A7.MixedGSideNonAlias
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7MixedG

open MeasureTheory Polynomial Finset
open Filter Topology
open scoped ENNReal NNReal BigOperators FourierTransform
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger

/-! ## §0.  Basic facts about the cut `GmixedKer` -/

/-- The cut of the mixed range is the second tensor factor of the window:
`Work.KMTAreas.A7.GmixedKer ρ P l₂ k₁ k₂ = mStargF P.natDegree (loMixedU ρ P.natDegree l₂ k₁ k₂)`. -/
theorem GmixedKer_eq (ρ : ℝ) (P : Polynomial ℤ) (l₂ k₁ k₂ : ℕ) :
    Work.KMTAreas.A7.GmixedKer ρ P l₂ k₁ k₂
      = Work.KMTAreas.A7.mStargF P.natDegree (Work.KMTAreas.A7.loMixedU ρ P.natDegree l₂ k₁ k₂) :=
  rfl

/-- The Fourier coefficients of the cut are absolutely summable. -/
theorem summable_cw_GmixedKer (P : Polynomial ℤ) (ρ : ℝ) (l₂ k₁ k₂ : ℕ) :
    Summable (fun j : ℤ => ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.GmixedKer ρ P l₂ k₁ k₂) j‖) := by
  obtain ⟨Cd, hdec⟩ := Work.KMTAreas.A7.cw_mStargF_decay P.natDegree
    (Work.KMTAreas.A7.loMixedU ρ P.natDegree l₂ k₁ k₂)
  rw [GmixedKer_eq]
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
    (Work.KMTAreas.A7.summable_kmtKernWeight.mul_left Cd)
  rw [Work.KMTAreas.A7.norm_kmtKernWeight, mul_one_div]
  exact hdec j

/-- The uniform `ℓ¹`-mass bound for the coefficients of the cut, uniform in every scale. -/
theorem exists_cw_GmixedKer_tsum_le (P : Polynomial ℤ) (hd : 1 ≤ P.natDegree) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : ℝ) (l₂ k₁ k₂ : ℕ),
      ∑' j : ℤ, ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.GmixedKer ρ P l₂ k₁ k₂) j‖ ≤ C := by
  obtain ⟨C, hCpos, hC⟩ := Work.A7.exists_cw_mStargF_tsum_le P.natDegree hd
  refine ⟨C, hCpos, fun ρ l₂ k₁ k₂ => ?_⟩
  rw [GmixedKer_eq]
  exact hC _

/-- Value of the `ℓ¹`-mass bound of the cut, in `ℝ≥0∞` form. -/
theorem tsum_enorm_cw_GmixedKer_eq (P : Polynomial ℤ) (ρ : ℝ) (l₂ k₁ k₂ : ℕ) :
    (∑' j : ℤ, ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.GmixedKer ρ P l₂ k₁ k₂) j‖ₑ)
      = ENNReal.ofReal (∑' j : ℤ, ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.GmixedKer ρ P l₂ k₁ k₂) j‖) := by
  rw [tsum_congr (fun j => (ofReal_norm _).symm)]
  exact (ENNReal.ofReal_tsum_of_nonneg (fun j => norm_nonneg _)
    (summable_cw_GmixedKer P ρ l₂ k₁ k₂)).symm

/-! ## §1.  The small-scale (`Young`) branch of the fibre estimate -/

/-- The bookkeeping constant of the bounded-scale box: the maximal cardinality of the
exact-height frequency set `(ℚ/ℤ)_{l}` over `l ≤ B`. -/
noncomputable def cardUpper (ρ : ℝ) (B : ℕ) : ℕ :=
  (Finset.range (B + 1)).sup fun l => (iwArithFreqsNew ρ l).card

/-- Membership form of the cardinality bound. -/
theorem card_iwArithFreqsNew_le_cardUpper {ρ : ℝ} {B l : ℕ} (h : l ≤ B) :
    (iwArithFreqsNew ρ l).card ≤ cardUpper ρ B := by
  unfold cardUpper
  exact Finset.le_sup (f := fun l => (iwArithFreqsNew ρ l).card)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le h))

/-- **Young's/convolution inequality for the counting measure of `ℤ`, in `ℝ≥0∞` form.** -/
theorem eLpNorm_tsum_enorm_mul_sub_le' {q : ℝ} (hq : 1 ≤ q) (K : ℤ → ℂ) (W : ℤ → ℝ≥0∞) :
    eLpNorm (fun x : ℤ => ∑' j : ℤ, ‖K j‖ₑ * W (x - j)) (ENNReal.ofReal q) Measure.count
      ≤ (∑' j : ℤ, ‖K j‖ₑ) * eLpNorm W (ENNReal.ofReal q) Measure.count := by
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq
  have hmink := Commons.MeasureTheory.Lp.eLpNorm_tsum_le_tsum_eLpNorm
    (μ := Measure.count) (p := ENNReal.ofReal q)
    (ENNReal.one_le_ofReal.mpr hq) (f := fun j : ℤ => fun x : ℤ => ‖K j‖ₑ * W (x - j))
    (fun j => (measurable_of_countable _).aemeasurable)
  have hconst : ∀ j : ℤ,
      eLpNorm (fun x : ℤ => ‖K j‖ₑ * W (x - j)) (ENNReal.ofReal q) Measure.count
        = ‖K j‖ₑ * eLpNorm W (ENNReal.ofReal q) Measure.count := by
    intro j
    rw [show eLpNorm (fun x : ℤ => ‖K j‖ₑ * W (x - j)) (ENNReal.ofReal q) Measure.count
        = eLpNorm (fun x : ℤ => ‖K j‖ₑ * W x) (ENNReal.ofReal q) Measure.count from
        Commons.Analysis.Convolution.eLpNorm_sub_right_ennreal (fun y : ℤ => ‖K j‖ₑ * W y) j hq0]
    exact Commons.Analysis.Convolution.eLpNorm_const_mul_ennreal_of_pos (f := W)
      (measurable_of_countable W).aemeasurable (‖K j‖ₑ) hq0
  refine hmink.trans_eq ?_
  rw [tsum_congr hconst, ENNReal.tsum_mul_right]

/-- The kernel `ℓ¹`-mass of the fibre with the cut `GmixedKer`, with the cardinality factor
separated out. -/
theorem tsum_enorm_GmixedKernel_le (ρ : ℝ) (P : Polynomial ℤ) (l₂ k₁ k₂ : ℕ) (n₀ : ℤ) :
    (∑' j : ℤ, ‖(∑ α ∈ iwArithFreqsNew ρ l₂, fourier (T := 1) (P.eval n₀ - j) α)
        * Work.KMTAreas.A7.cw (Work.KMTAreas.A7.GmixedKer ρ P l₂ k₁ k₂) j‖ₑ)
      ≤ ((iwArithFreqsNew ρ l₂).card : ℝ≥0∞)
          * (∑' j : ℤ, ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.GmixedKer ρ P l₂ k₁ k₂) j‖ₑ) := by
  have hterm : ∀ j : ℤ,
      ‖(∑ α ∈ iwArithFreqsNew ρ l₂, fourier (T := 1) (P.eval n₀ - j) α)
        * Work.KMTAreas.A7.cw (Work.KMTAreas.A7.GmixedKer ρ P l₂ k₁ k₂) j‖ₑ
        ≤ ((iwArithFreqsNew ρ l₂).card : ℝ≥0∞)
            * ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.GmixedKer ρ P l₂ k₁ k₂) j‖ₑ := by
    intro j
    have h1 : ‖(∑ α ∈ iwArithFreqsNew ρ l₂, fourier (T := 1) (P.eval n₀ - j) α)‖ₑ
        ≤ ((iwArithFreqsNew ρ l₂).card : ℝ≥0∞) := by
      rw [← ofReal_norm, ← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal
        (Work.KMTAreas.A7.norm_arithCharSet_le_card (iwArithFreqsNew ρ l₂) (P.eval n₀ - j))
    rw [enorm_mul]
    exact mul_le_mul_left h1 _
  calc (∑' j : ℤ, ‖(∑ α ∈ iwArithFreqsNew ρ l₂, fourier (T := 1) (P.eval n₀ - j) α)
          * Work.KMTAreas.A7.cw (Work.KMTAreas.A7.GmixedKer ρ P l₂ k₁ k₂) j‖ₑ)
      ≤ ∑' j : ℤ, ((iwArithFreqsNew ρ l₂).card : ℝ≥0∞)
          * ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.GmixedKer ρ P l₂ k₁ k₂) j‖ₑ := ENNReal.tsum_le_tsum hterm
    _ = ((iwArithFreqsNew ρ l₂).card : ℝ≥0∞)
          * (∑' j : ℤ, ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.GmixedKer ρ P l₂ k₁ k₂) j‖ₑ) :=
        ENNReal.tsum_mul_left

/-- **The per-instance Young bound for the mixed fibre.**  For every instance of the scales and
every input family, the `ℓ^q`-norm of the variational norm of the fibre family is bounded by the
explicit constant `#(ℚ/ℤ)_{l₂} · ∑_j ‖cw (GmixedKer …) j‖` times the `ℓ^q`-norm of the variational
norm of the input family.  No hypothesis on the scales is needed. -/
theorem eLpNorm_GmixedFib_le (ρ : ℝ) (P : Polynomial ℤ) (r : NNReal) (hr : 1 ≤ r)
    (l₂ k₁ k₂ : ℕ) (n₀ : ℤ) (u : ℕ → ℤ → ℂ) {q : ℝ} (hq : 1 ≤ q) :
    eLpNorm (fun x : ℤ => variationalNorm r
        (fun n : ℕ => Work.KMTAreas.A7.fiberOpP ρ P l₂ (Work.KMTAreas.A7.GmixedKer ρ P l₂ k₁ k₂) n₀ (u n) x))
      (ENNReal.ofReal q) Measure.count
      ≤ ENNReal.ofReal (((iwArithFreqsNew ρ l₂).card : ℝ)
          * (∑' j : ℤ, ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.GmixedKer ρ P l₂ k₁ k₂) j‖))
        * eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => u n x))
            (ENNReal.ofReal q) Measure.count := by
  set W : ℤ → ℝ≥0∞ := fun x => variationalNorm r (fun n : ℕ => u n x) with hW
  set K : ℤ → ℂ := fun j => (∑ α ∈ iwArithFreqsNew ρ l₂, fourier (T := 1) (P.eval n₀ - j) α)
    * Work.KMTAreas.A7.cw (Work.KMTAreas.A7.GmixedKer ρ P l₂ k₁ k₂) j with hK
  have hpt : ∀ x : ℤ,
      variationalNorm r (fun n : ℕ => Work.KMTAreas.A7.fiberOpP ρ P l₂
          (Work.KMTAreas.A7.GmixedKer ρ P l₂ k₁ k₂) n₀ (u n) x)
        ≤ ∑' j : ℤ, ‖K j‖ₑ * W (x - j) := by
    intro x
    have h := Work.KMTAreas.A7.fiberOpVarYoungExact ρ l₂ (Work.KMTAreas.A7.GmixedKer ρ P l₂ k₁ k₂)
      (P.eval n₀) u r hr x
    rw [Work.KMTAreas.A7.fiberOpP_eq_fiberOp]
    simpa only [hK, hW] using h
  have hmass : (∑' j : ℤ, ‖K j‖ₑ)
      ≤ ENNReal.ofReal (((iwArithFreqsNew ρ l₂).card : ℝ)
          * (∑' j : ℤ, ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.GmixedKer ρ P l₂ k₁ k₂) j‖)) := by
    have h := tsum_enorm_GmixedKernel_le ρ P l₂ k₁ k₂ n₀
    have hT : (∑' j : ℤ, ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.GmixedKer ρ P l₂ k₁ k₂) j‖ₑ)
        = ENNReal.ofReal (∑' j : ℤ,
            ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.GmixedKer ρ P l₂ k₁ k₂) j‖) :=
      tsum_enorm_cw_GmixedKer_eq P ρ l₂ k₁ k₂
    have hofReal : ENNReal.ofReal (((iwArithFreqsNew ρ l₂).card : ℝ)
          * (∑' j : ℤ, ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.GmixedKer ρ P l₂ k₁ k₂) j‖))
        = ((iwArithFreqsNew ρ l₂).card : ℝ≥0∞)
            * (∑' j : ℤ, ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.GmixedKer ρ P l₂ k₁ k₂) j‖ₑ) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, ← hT]
    rw [hK]
    exact h.trans (le_of_eq hofReal.symm)
  calc eLpNorm (fun x : ℤ => variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7.fiberOpP ρ P l₂
            (Work.KMTAreas.A7.GmixedKer ρ P l₂ k₁ k₂) n₀ (u n) x))
        (ENNReal.ofReal q) Measure.count
      ≤ eLpNorm (fun x : ℤ => ∑' j : ℤ, ‖K j‖ₑ * W (x - j))
          (ENNReal.ofReal q) Measure.count :=
        eLpNorm_mono_enorm (hf := by pw_aesm) fun x => by simpa only [enorm_eq_self] using hpt x
    _ ≤ (∑' j : ℤ, ‖K j‖ₑ) * eLpNorm W (ENNReal.ofReal q) Measure.count :=
        eLpNorm_tsum_enorm_mul_sub_le' hq K W
    _ ≤ ENNReal.ofReal (((iwArithFreqsNew ρ l₂).card : ℝ)
          * (∑' j : ℤ, ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.GmixedKer ρ P l₂ k₁ k₂) j‖))
        * eLpNorm W (ENNReal.ofReal q) Measure.count := mul_le_mul_left hmass _
    _ = ENNReal.ofReal (((iwArithFreqsNew ρ l₂).card : ℝ)
          * (∑' j : ℤ, ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.GmixedKer ρ P l₂ k₁ k₂) j‖))
        * eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => u n x))
            (ENNReal.ofReal q) Measure.count := by rw [hW]

/-- **The small-scale (`Young`) branch of the mixed fibre estimate.**  For every bound function
`Bfun` on the scale `l₂` there is a constant `C ρ` such that, for `l₂ ≤ Bfun ρ` and *every* input
family, the variational norm of the fibre family is bounded by `C ρ` times the variational norm of
the input family. -/
theorem fiberOpP_young_bound (P : Polynomial ℤ) (hd : 1 ≤ P.natDegree) (r : NNReal) (hr : 1 ≤ r)
    (p : ENNReal) (hp : 1 < p) (hpt : p < ⊤) (Bfun : ℝ → ℕ) :
    ∃ C : ℝ → ℝ, (∀ ρ : ℝ, 0 < ρ → 0 < C ρ) ∧
      ∀ (ρ : ℝ), 0 < ρ → ∀ (l₂ k₁ k₂ : ℕ), l₂ ≤ Bfun ρ → ∀ (n₀ : ℤ) (u : ℕ → ℤ → ℂ),
        eLpNorm (fun x : ℤ => variationalNorm r
            (fun n : ℕ => Work.KMTAreas.A7.fiberOpP ρ P l₂ (Work.KMTAreas.A7.GmixedKer ρ P l₂ k₁ k₂) n₀
              (u n) x)) p Measure.count
          ≤ ENNReal.ofReal (C ρ) *
              eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => u n x)) p
                Measure.count := by
  obtain ⟨MM, hMMpos, hMM⟩ := exists_cw_GmixedKer_tsum_le P hd
  refine ⟨fun ρ => ((cardUpper ρ (Bfun ρ) : ℝ) * MM + 1), fun ρ _ => by positivity, ?_⟩
  intro ρ hρ l₂ k₁ k₂ hl₂ n₀ u
  have hq : (1 : ℝ) ≤ p.toReal := by
    have h1 : ((1 : ENNReal).toReal) ≤ p.toReal := ENNReal.toReal_mono (ne_of_lt hpt) (le_of_lt hp)
    simpa using h1
  have hp_eq : ENNReal.ofReal p.toReal = p := ENNReal.ofReal_toReal (ne_of_lt hpt)
  have hper := eLpNorm_GmixedFib_le ρ P r hr l₂ k₁ k₂ n₀ u hq
  rw [hp_eq] at hper
  have hcard : (((iwArithFreqsNew ρ l₂).card : ℝ)) ≤ ((cardUpper ρ (Bfun ρ) : ℕ) : ℝ) := by
    exact_mod_cast card_iwArithFreqsNew_le_cardUpper hl₂
  have hmass : (∑' j : ℤ, ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.GmixedKer ρ P l₂ k₁ k₂) j‖) ≤ MM :=
    hMM ρ l₂ k₁ k₂
  have hmassnn : 0 ≤ ∑' j : ℤ, ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.GmixedKer ρ P l₂ k₁ k₂) j‖ :=
    tsum_nonneg (fun j => norm_nonneg _)
  refine hper.trans ?_
  refine mul_le_mul_of_nonneg_right ?_ bot_le
  refine ENNReal.ofReal_le_ofReal ?_
  have hcarden : (0 : ℝ) ≤ ((cardUpper ρ (Bfun ρ) : ℕ) : ℝ) := Nat.cast_nonneg _
  have h1 : ((iwArithFreqsNew ρ l₂).card : ℝ)
      * (∑' j : ℤ, ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.GmixedKer ρ P l₂ k₁ k₂) j‖)
      ≤ ((cardUpper ρ (Bfun ρ) : ℕ) : ℝ) * MM :=
    mul_le_mul hcard hmass hmassnn hcarden
  linarith [h1, hMMpos]


/-! ## §1b.  The `g`-side arithmetic of the large-scale regime

The two estimates that turn the guard `splitCut ρ L < \u230aL` (`L = max l₂ (max k₁ k₂)`) plus
`L` large into the quantitative hypotheses of the paper's §8 analysis: the auxiliary window
`loMixedU ρ d l₂ k₁ k₂` is the pinned `uScale ρ L` (so the cut has width `2^{-2dU}`), and the
strict main regime holds (`k₂ + 2U + 1 ≤ logN N`). -/

/-- A linear function with slope `d` is eventually dominated by `uScale ρ L = ⌊2^{2ρL}⌋`. -/
theorem exists_uScale_ge_linear (ρ : ℝ) (hρ : 0 < ρ) (d : ℕ) :
    ∃ B : ℕ, ∀ L : ℕ, B ≤ L → d * L + 3 ≤ Work.KMTAreas.A7.uScale ρ L := by
  set b : ℝ := (2 : ℝ) ^ (2 * ρ) with hbdef
  have hb1 : 1 < b := Real.one_lt_rpow (by norm_num) (by linarith)
  have hb0 : 0 < b := lt_trans zero_lt_one hb1
  have hbL_eq : ∀ L : ℕ, b ^ L = (2 : ℝ) ^ (2 * ρ * (L : ℝ)) := by
    intro L
    rw [hbdef, ← Real.rpow_natCast ((2 : ℝ) ^ (2 * ρ)) L,
      ← Real.rpow_mul (show (0 : ℝ) ≤ 2 by norm_num)]
  have hbpow : Tendsto (fun L : ℕ => b ^ L) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hb1
  have h3 : Tendsto (fun L : ℕ => (3 : ℝ) / b ^ L) atTop (𝓝 0) := hbpow.const_div_atTop 3
  have hL1 : Tendsto (fun L : ℕ => (L : ℝ) / b ^ L) atTop (𝓝 0) := by
    have h := tendsto_pow_const_div_const_pow_of_one_lt 1 hb1
    simpa using h
  have hdL : Tendsto (fun L : ℕ => ((d : ℝ) * (L : ℝ)) / b ^ L) atTop (𝓝 0) := by
    have h := hL1.const_mul (d : ℝ)
    have heq : (fun L : ℕ => (d : ℝ) * ((L : ℝ) / b ^ L))
        =ᶠ[atTop] (fun L : ℕ => ((d : ℝ) * (L : ℝ)) / b ^ L) := by
      filter_upwards with L
      rw [mul_div_assoc]
    have h2 := Filter.Tendsto.congr' heq h
    simpa only [mul_zero] using h2
  have hsum : Tendsto (fun L : ℕ => ((d : ℝ) * (L : ℝ) + 3) / b ^ L) atTop (𝓝 0) := by
    have h := hdL.add h3
    have heq : (fun L : ℕ => ((d : ℝ) * (L : ℝ)) / b ^ L + 3 / b ^ L)
        =ᶠ[atTop] (fun L : ℕ => ((d : ℝ) * (L : ℝ) + 3) / b ^ L) := by
      filter_upwards with L
      rw [add_div]
    have h2 := Filter.Tendsto.congr' heq h
    simpa only [zero_add] using h2
  have hev : ∀ᶠ L : ℕ in atTop, ((d : ℝ) * (L : ℝ) + 3) / b ^ L < 1 :=
    (tendsto_order.1 hsum).2 1 (by norm_num)
  obtain ⟨L₁, hL₁⟩ := eventually_atTop.1 hev
  refine ⟨L₁, fun L hL => ?_⟩
  have hLt : ((d : ℝ) * (L : ℝ) + 3) < b ^ L := by
    have h := hL₁ L hL
    have hbpos : 0 < b ^ L := pow_pos hb0 L
    rw [div_lt_one hbpos] at h
    exact h
  have hu : Work.KMTAreas.A7.uScale ρ L = ⌊(2 : ℝ) ^ (2 * ρ * (L : ℝ))⌋₊ := by
    simp only [Work.KMTAreas.A7.uScale, Work.Analysis.EndVar.scaleCount, Int.floor_toNat,
      Nat.cast_one, one_mul]
  rw [hu]
  refine Nat.le_floor ?_
  rw [← hbL_eq L]
  have hcast : ((d * L + 3 : ℕ) : ℝ) = (d : ℝ) * (L : ℝ) + 3 := by push_cast; ring
  rw [hcast]
  linarith [hLt]

/-- In the large-scale regime the auxiliary window `loMixedU ρ d l₂ k₁ k₂` is the pinned
`uScale ρ L`. -/
theorem loMixedU_eq_uScale_of_large (ρ : ℝ) (hρ : 0 < ρ) (d : ℕ) :
    ∃ B : ℕ, ∀ (l₂ k₁ k₂ : ℕ), B ≤ max l₂ (max k₁ k₂) →
      Work.KMTAreas.A7.loMixedU ρ d l₂ k₁ k₂
        = Work.KMTAreas.A7.uScale ρ (max l₂ (max k₁ k₂)) := by
  obtain ⟨B, hB⟩ := exists_uScale_ge_linear ρ hρ d
  refine ⟨B, ?_⟩
  intro l₂ k₁ k₂ hL
  have hL' : max (max 0 l₂) (max k₁ k₂) = max l₂ (max k₁ k₂) := by omega
  rw [Work.KMTAreas.A7.loMixedU, hL']
  refine max_eq_left ?_
  have hl₂ : l₂ ≤ max l₂ (max k₁ k₂) := le_max_left _ _
  have h1 : d * l₂ + 3 ≤ d * max l₂ (max k₁ k₂) + 3 :=
    Nat.add_le_add_right (Nat.mul_le_mul_left d hl₂) 3
  exact le_trans h1 (hB _ hL)

/-- In the large-scale regime the guard's `splitCut ρ L < N` gives the strict main-regime
inequality `k₂ + 2·U + 1 ≤ logN N` with `U = loMixedU ρ d l₂ k₁ k₂`. -/
theorem plateau_of_large_L (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (d : ℕ) :
    ∃ B : ℕ, ∀ (l₂ k₁ k₂ N : ℕ),
      B < max l₂ (max k₁ k₂) →
      Work.KMTAreas.A7.splitCut ρ (max l₂ (max k₁ k₂)) < N →
      k₂ + 2 * Work.KMTAreas.A7.loMixedU ρ d l₂ k₁ k₂ + 1
        ≤ (Work.Analysis.EndVar.logN N).toNat := by
  obtain ⟨B₁, hB₁⟩ := loMixedU_eq_uScale_of_large ρ hρ d
  obtain ⟨B₂, hB₂⟩ := exists_uScale_ge_linear ρ hρ 1
  refine ⟨max B₁ (max B₂ 2), ?_⟩
  intro l₂ k₁ k₂ N hB hsplit
  set L : ℕ := max l₂ (max k₁ k₂) with hL
  have hB₁L : B₁ ≤ L := by omega
  have hB₂L : B₂ ≤ L := by omega
  have h2L : 2 ≤ L := by omega
  have hu : L + 3 ≤ Work.KMTAreas.A7.uScale ρ L := by simpa using hB₂ L hB₂L
  have hu1 : L ≤ Work.KMTAreas.A7.uScale ρ L := by omega
  have hu2 : 5 ≤ Work.KMTAreas.A7.uScale ρ L := by omega
  rw [hB₁ l₂ k₁ k₂ hB₁L]
  have hk₂L : k₂ ≤ L := by
    rw [hL]
    exact le_trans (le_max_right k₁ k₂) (le_max_right _ _)
  exact Work.KMTAreas.A7.strict_of_splitCut_lt hρ hk₂L hu1 hu2 (by rw [← hL]; exact hsplit)


/-- **The `g`-side Farey condition in the large-scale regime.**  For the cut scale `d = P.natDegree`
there is a threshold `B` such that, whenever `B < L` (`L = max l₂ (max k₁ k₂)`) and
`splitCut ρ L < N`, the packet band of the `g`-side bump sits below the Farey gap of the
exact-height frequency set:
`8 · 2^{d·k₂} · arithQ ρ l₂ ≤ N^d`. -/
theorem gside_farey_of_large_L (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (d : ℕ) (hd : 1 ≤ d) :
    ∃ B : ℕ, ∀ (l₂ k₁ k₂ N : ℕ),
      B < max l₂ (max k₁ k₂) →
      Work.KMTAreas.A7.splitCut ρ (max l₂ (max k₁ k₂)) < N →
      (8 : ℝ) * (2 : ℝ) ^ (d * k₂) * (Work.KMTAreas.A7.arithQ ρ l₂ : ℝ)
        ≤ (N : ℝ) ^ d := by
  obtain ⟨C, hCpos, hC⟩ := Work.KMTAreas.A7.arithQ_le_rpow ρ hρ hρ1
  have hC'd : 0 < C * (d : ℝ) + (d : ℝ) := by
    have : (0 : ℝ) ≤ C * (d : ℝ) := mul_nonneg hCpos.le (Nat.cast_nonneg d)
    have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    linarith
  obtain ⟨L₀, hL₀⟩ := Work.KMTAreas.A7.splitCut_dominates ρ hρ (C * (d : ℝ) + (d : ℝ)) hC'd
  refine ⟨L₀ + 1, ?_⟩
  intro l₂ k₁ k₂ N hB hsplit
  set L : ℕ := max l₂ (max k₁ k₂) with hL
  have hL₀L : L₀ ≤ L := by omega
  have hk₂L : k₂ ≤ L := by
    rw [hL]; exact le_trans (le_max_right k₁ k₂) (le_max_right _ _)
  have hl₂L : l₂ ≤ L := by rw [hL]; exact le_max_left _ _
  -- `N ≥ 1`
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    have hsc : 1 ≤ Work.KMTAreas.A7.splitCut ρ L := by
      rw [Work.KMTAreas.A7.splitCut]
      exact one_le_pow₀ (by norm_num)
    have hN : 1 ≤ N := le_trans hsc (le_of_lt hsplit)
    exact_mod_cast hN
  have hNd : (N : ℝ) ≤ (N : ℝ) ^ d := by
    simpa using pow_le_pow_right₀ hN1 hd
  by_contra hnot
  have hNlt : (N : ℝ) ^ d < 8 * (2 : ℝ) ^ (d * k₂) * (Work.KMTAreas.A7.arithQ ρ l₂ : ℝ) :=
    not_le.mp hnot
  -- the two power comparisons, and the Farey bound on the modulus
  have hL2 : ((L : ℕ) : ℝ) ≤ (2 : ℝ) ^ L := by
    exact_mod_cast (Nat.lt_two_pow_self (n := L)).le
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hpow_a : (2 : ℝ) ^ (d * L) ≤ (2 : ℝ) ^ ((d : ℝ) * (2 : ℝ) ^ L) := by
    rw [← Real.rpow_natCast (2 : ℝ) (d * L), Nat.cast_mul]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_left hL2 hd0)
  have hpow_b : (2 : ℝ) ^ (C * (2 : ℝ) ^ L)
      ≤ (2 : ℝ) ^ ((C * (d : ℝ)) * (2 : ℝ) ^ L) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have h2L : (0 : ℝ) < (2 : ℝ) ^ L := pow_pos (by norm_num) L
    have hCd : C ≤ C * (d : ℝ) := by nlinarith [hCpos, hd1]
    exact mul_le_mul_of_nonneg_right hCd h2L.le
  have hq : (Work.KMTAreas.A7.arithQ ρ l₂ : ℝ) ≤ (2 : ℝ) ^ (C * (2 : ℝ) ^ L) := by
    refine (hC l₂).trans ?_
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have hl₂2 : (2 : ℝ) ^ l₂ ≤ (2 : ℝ) ^ L := pow_le_pow_right₀ (by norm_num) hl₂L
    exact mul_le_mul_of_nonneg_left hl₂2 hCpos.le
  have hk₂ : (2 : ℝ) ^ (d * k₂) ≤ (2 : ℝ) ^ (d * L) :=
    pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left d hk₂L)
  have hcomb : (2 : ℝ) ^ ((d : ℝ) * (2 : ℝ) ^ L) * (2 : ℝ) ^ ((C * (d : ℝ)) * (2 : ℝ) ^ L)
      = (2 : ℝ) ^ ((C * (d : ℝ) + (d : ℝ)) * (2 : ℝ) ^ L) := by
    rw [← Real.rpow_add (by norm_num)]
    congr 1
    ring
  have hstep1 : 8 * (2 : ℝ) ^ (d * k₂) * (Work.KMTAreas.A7.arithQ ρ l₂ : ℝ)
      ≤ 8 * (2 : ℝ) ^ (d * L) * (2 : ℝ) ^ (C * (2 : ℝ) ^ L) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hk₂ (by norm_num)) hq (by positivity) (by positivity)
  have hstep2 : 8 * (2 : ℝ) ^ (d * L) * (2 : ℝ) ^ (C * (2 : ℝ) ^ L)
      ≤ 8 * ((2 : ℝ) ^ L * (2 : ℝ) ^ ((C * (d : ℝ) + (d : ℝ)) * (2 : ℝ) ^ L)) := by
    have h8 : (0 : ℝ) ≤ 8 := by norm_num
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ L := one_le_pow₀ (by norm_num)
    have hmul : (2 : ℝ) ^ (d * L) * (2 : ℝ) ^ (C * (2 : ℝ) ^ L)
        ≤ (2 : ℝ) ^ ((d : ℝ) * (2 : ℝ) ^ L) * (2 : ℝ) ^ ((C * (d : ℝ)) * (2 : ℝ) ^ L) :=
      mul_le_mul hpow_a hpow_b (by positivity) (by positivity)
    calc 8 * (2 : ℝ) ^ (d * L) * (2 : ℝ) ^ (C * (2 : ℝ) ^ L)
        = 8 * ((2 : ℝ) ^ (d * L) * (2 : ℝ) ^ (C * (2 : ℝ) ^ L)) := by ring
      _ ≤ 8 * ((2 : ℝ) ^ ((d : ℝ) * (2 : ℝ) ^ L)
            * (2 : ℝ) ^ ((C * (d : ℝ)) * (2 : ℝ) ^ L)) := mul_le_mul_of_nonneg_left hmul h8
      _ = 8 * (2 : ℝ) ^ ((C * (d : ℝ) + (d : ℝ)) * (2 : ℝ) ^ L) := by rw [hcomb]
      _ ≤ 8 * ((2 : ℝ) ^ L * (2 : ℝ) ^ ((C * (d : ℝ) + (d : ℝ)) * (2 : ℝ) ^ L)) := by
          refine mul_le_mul_of_nonneg_left ?_ h8
          exact le_mul_of_one_le_left (by positivity) h1
  have hstep3 : 8 * (2 : ℝ) ^ L * (2 : ℝ) ^ ((C * (d : ℝ) + (d : ℝ)) * (2 : ℝ) ^ L)
      < (Work.KMTAreas.A7.splitCut ρ L : ℝ) := hL₀ L hL₀L
  have hstep4 : (Work.KMTAreas.A7.splitCut ρ L : ℝ) < (N : ℝ) := by
    exact_mod_cast hsplit
  linarith [hNlt, hstep1, hstep2, hstep3, hstep4, hNd]


/-- Non-aliasing at a coarser frequency set. -/
theorem NonAliasing_subset {k : ℤ} {A B : Finset Work.Analysis.IonescuWainger.Circle}
    (h : Work.Analysis.IonescuWainger.NonAliasing k A) (hBA : B ⊆ A) :
    Work.Analysis.IonescuWainger.NonAliasing k B := by
  intro α hα β hβ
  exact h α (hBA hα) β (hBA hβ)

/-- **Non-aliasing of the exact-height frequency set at the cut scale.**  Above a `ρ`-dependent
threshold for `L = max l₂ (max k₁ k₂)`, the cut windows `α + ℝ_{≤ -2dU}`
(`U = loMixedU ρ d l₂ k₁ k₂`) are pairwise disjoint. -/
theorem nonAliasing_Gmixed (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (d : ℕ) (hd : 1 ≤ d) :
    ∃ B : ℕ, ∀ (l₂ k₁ k₂ : ℕ), B ≤ max l₂ (max k₁ k₂) →
      Work.Analysis.IonescuWainger.NonAliasing
        (-(2 * (d * (Work.KMTAreas.A7.loMixedU ρ d l₂ k₁ k₂ : ℤ))))
        (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂) := by
  obtain ⟨B, hB⟩ := Work.KMTAreas.A7.NonAliasing_loMixedU ρ hρ hρ1 d
  refine ⟨B, fun l₂ k₁ k₂ hL => ?_⟩
  have hLL : B ≤ Work.KMTAreas.A7.Lnat 0 l₂ k₁ k₂ := by
    show B ≤ max (max 0 l₂) (max k₁ k₂)
    omega
  have h1 := hB l₂ k₁ k₂ hLL
  have h2 : (-(2 * (d * (Work.KMTAreas.A7.loMixedU ρ d l₂ k₁ k₂ : ℤ))))
      ≤ (-(2 * (Work.KMTAreas.A7.loMixedU ρ d l₂ k₁ k₂ : ℤ))) := by
    have hd1 : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    have h0 : (0 : ℤ) ≤ (Work.KMTAreas.A7.loMixedU ρ d l₂ k₁ k₂ : ℤ) := Int.natCast_nonneg _
    have hmul : (1 : ℤ) * (Work.KMTAreas.A7.loMixedU ρ d l₂ k₁ k₂ : ℤ)
        ≤ (d : ℤ) * (Work.KMTAreas.A7.loMixedU ρ d l₂ k₁ k₂ : ℤ) :=
      mul_le_mul_of_nonneg_right hd1 h0
    simp only [one_mul] at hmul
    omega
  refine NonAliasing_subset (Work.KMTAreas.A7.NonAliasing_mono_scale h2 h1) ?_
  intro α hα
  exact (Finset.mem_sdiff.mp hα).1

/-! ## §2.  The large-scale branch (the delegated deep input) and the target -/



open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger

/-- **The large-scale branch of the mixed per-residue fibre estimate.**  The target's inequality,
under the three extra hypotheses that the guard supplies in the regime
`max l₂ (max k₁ k₂) > B`:

* the cut windows `α + ℝ_{≤ -2dU}` are pairwise disjoint (`NonAliasing`);
* the Farey gap condition `8 · 2^{d k₂} · arithQ ρ l₂ ≤ ⌊a n⌋^d` on the guard;
* the strict main regime / plateau `k₂ + 2U + 1 ≤ logN ⌊a n⌋`, `U = loMixedU ρ d l₂ k₁ k₂`, on the
  guard.

It is the paper's §8 (the quantitative Shannon/decimation transfer with the twist-vs-shift error);
it is *strictly weaker* than the target. -/
def FiberLargeResidueLargeScalesProp (P : Polynomial ℤ) (p₂ : ENNReal) (hdeg : 2 ≤ P.natDegree)
    (hp₂ : 1 < p₂) (htp₂ : p₂ < ⊤) : Prop :=
  ∀ (C₀ : ℕ) (r : NNReal), 1 ≤ C₀ → (2 : NNReal) < r →
    ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∃ B : ℕ,
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ C : NNReal → NNReal,
        ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₂ k₁ k₂ : ℕ) (t : ℝ) (g : ℤ → ℂ) (n₀ : ℤ),
          1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) → 1 ≤ l₂ →
          t ∈ Set.Icc (1/2 : ℝ) 1 → BddAbove (Set.range fun y : ℤ => ‖g y‖) →
          B < max l₂ (max k₁ k₂) →
          Work.Analysis.IonescuWainger.NonAliasing
            (-(2 * (P.natDegree * Work.KMTAreas.A7.loMixedU ρ P.natDegree l₂ k₁ k₂)))
            (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂) →
          (∀ n, Work.KMTAreas.A7.loGuard ρ C₀ a 0 l₂ k₁ k₂ n →
            (8 : ℝ) * (2 : ℝ) ^ (P.natDegree * k₂)
                * (Work.KMTAreas.A7.arithQ ρ l₂ : ℝ)
              ≤ (((Nat.floor (a n) : ℕ) : ℝ)) ^ P.natDegree ∧
              k₂ + 2 * Work.KMTAreas.A7.loMixedU ρ P.natDegree l₂ k₁ k₂ + 1
                ≤ (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat) →
          MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => Work.KMTAreas.A7.fiberOpP ρ P l₂
                (Work.KMTAreas.A7.GmixedKer ρ P l₂ k₁ k₂) n₀
                (Work.KMTAreas.A7.GmixedFam ρ P C₀ a l₂ k₁ k₂ t g n) x))
            p₂ MeasureTheory.Measure.count
          ≤ (↑(max 1 (C Λ)) : ENNReal) * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A ρ 0 l₂ k₁ k₂) *
              MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
                (fun n : ℕ => Work.KMTAreas.A7.GmixedFam ρ P C₀ a l₂ k₁ k₂ t g n x))
                p₂ MeasureTheory.Measure.count

/-- The guard supplies the `splitCut` hypothesis of
`Work.KMTAreas.A7.gside_farey_of_large_L` / `Work.KMTAreas.A7.plateau_of_large_L`. -/
theorem splitCut_of_loGuard {ρ : ℝ} {C₀ : ℕ} {a : ℕ → NNReal} {l₂ k₁ k₂ n : ℕ}
    (h : Work.KMTAreas.A7.loGuard ρ C₀ a 0 l₂ k₁ k₂ n) :
    Work.KMTAreas.A7.splitCut ρ (max l₂ (max k₁ k₂)) < Nat.floor (a n) := by
  have h' := h.2.1
  have harg : max (max 0 l₂) (max k₁ k₂) = max l₂ (max k₁ k₂) := by omega
  rwa [harg] at h'

/-- **The target, from its large-scale branch.** -/
theorem FiberLargeResidueCore_of_largeScales (P : Polynomial ℤ) (p₂ : ENNReal)
    (hdeg : 2 ≤ P.natDegree) (hp₂ : 1 < p₂) (htp₂ : p₂ < ⊤)
    (hcrux : FiberLargeResidueLargeScalesProp P p₂ hdeg hp₂ htp₂) :
  ∀ (C₀ : ℕ) (r : NNReal), 1 ≤ C₀ → (2 : NNReal) < r →
    ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∃ B : ℕ,
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ C : NNReal → NNReal,
        ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₂ k₁ k₂ : ℕ) (t : ℝ) (g : ℤ → ℂ) (n₀ : ℤ),
          1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) → 1 ≤ l₂ →
          t ∈ Set.Icc (1/2 : ℝ) 1 → BddAbove (Set.range fun y : ℤ => ‖g y‖) →
          B < max l₂ (max k₁ k₂) →
          MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => Work.KMTAreas.A7.fiberOpP ρ P l₂
                (Work.KMTAreas.A7.GmixedKer ρ P l₂ k₁ k₂) n₀
                (Work.KMTAreas.A7.GmixedFam ρ P C₀ a l₂ k₁ k₂ t g n) x))
            p₂ MeasureTheory.Measure.count
          ≤ (↑(max 1 (C Λ)) : ENNReal) * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A ρ 0 l₂ k₁ k₂) *
              MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
                (fun n : ℕ => Work.KMTAreas.A7.GmixedFam ρ P C₀ a l₂ k₁ k₂ t g n x))
                p₂ MeasureTheory.Measure.count := by
  intro C₀ r hC₀ hr
  obtain ⟨Ac, hAc, ρc, hρc, Bc, hcrux'⟩ := hcrux C₀ r hC₀ hr
  have hdeg1 : 1 ≤ P.natDegree := by omega
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num) (le_of_lt hr)
  refine ⟨max 8 Ac, le_trans (by norm_num) (le_max_left _ _), min 1 ρc,
    lt_min one_pos hρc, 0, ?_⟩
  intro ρ hρ hρle
  have hρ1 : ρ ≤ 1 := le_trans hρle (min_le_left _ _)
  have hρc' : ρ ≤ ρc := le_trans hρle (min_le_right _ _)
  obtain ⟨C2, hC2⟩ := hcrux' ρ hρ hρc'
  obtain ⟨Bna, hna⟩ := nonAliasing_Gmixed ρ hρ hρ1 P.natDegree hdeg1
  obtain ⟨Bfa, hfa⟩ := gside_farey_of_large_L ρ hρ hρ1 P.natDegree hdeg1
  obtain ⟨Bpl, hpl⟩ := plateau_of_large_L ρ hρ hρ1 P.natDegree
  obtain ⟨C1, hC1pos, hC1⟩ :=
    fiberOpP_young_bound P hdeg1 r hr1 p₂ hp₂ htp₂ (fun _ => max (max Bna Bfa) (max Bpl Bc))
  refine ⟨fun Λ => max (C2 Λ) ((⌈C1 ρ⌉₊ : ℕ) : NNReal), ?_⟩
  intro a Λ l₂ k₁ k₂ t g n₀ hΛ hLac ha hl₂ ht hgb hBL
  by_cases hcase : max l₂ (max k₁ k₂) ≤ max (max Bna Bfa) (max Bpl Bc)
  · -- ### Case 1: the small-scale (Young) branch
    have hl₂B : l₂ ≤ max (max Bna Bfa) (max Bpl Bc) :=
      le_trans (le_max_left l₂ (max k₁ k₂)) hcase
    have h1 := hC1 ρ hρ l₂ k₁ k₂ hl₂B n₀
      (fun n => Work.KMTAreas.A7.GmixedFam ρ P C₀ a l₂ k₁ k₂ t g n)
    have hle2 : ENNReal.ofReal (C1 ρ) ≤
        (↑(max 1 (max (C2 Λ) ((⌈C1 ρ⌉₊ : ℕ) : NNReal))) : ENNReal) := by
      refine (ENNReal.ofReal_le_ofReal (Nat.le_ceil (C1 ρ))).trans ?_
      rw [ENNReal.ofReal_natCast]
      refine ENNReal.coe_le_coe.mpr ?_
      exact le_trans (le_max_right (C2 Λ) ((⌈C1 ρ⌉₊ : ℕ) : NNReal))
        (le_max_right 1 (max (C2 Λ) ((⌈C1 ρ⌉₊ : ℕ) : NNReal)))
    have hone : (1 : ENNReal) ≤
        ENNReal.ofReal (Work.KMTAreas.A7.lossWeight (max 8 Ac) ρ 0 l₂ k₁ k₂) :=
      ENNReal.one_le_ofReal.mpr
        (Work.KMTAreas.A7.one_le_lossWeight'
          (le_trans (by norm_num) (le_max_left 8 Ac)) hρ.le 0 l₂ k₁ k₂)
    refine h1.trans ?_
    calc ENNReal.ofReal (C1 ρ) * MeasureTheory.eLpNorm (fun x : ℤ =>
            PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
              Work.KMTAreas.A7.GmixedFam ρ P C₀ a l₂ k₁ k₂ t g n x))
          p₂ MeasureTheory.Measure.count
        ≤ (↑(max 1 (max (C2 Λ) ((⌈C1 ρ⌉₊ : ℕ) : NNReal))) : ENNReal) *
            MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => Work.KMTAreas.A7.GmixedFam ρ P C₀ a l₂ k₁ k₂ t g n x))
              p₂ MeasureTheory.Measure.count := mul_le_mul_left hle2 _
      _ ≤ (↑(max 1 (max (C2 Λ) ((⌈C1 ρ⌉₊ : ℕ) : NNReal))) : ENNReal) *
            ENNReal.ofReal (Work.KMTAreas.A7.lossWeight (max 8 Ac) ρ 0 l₂ k₁ k₂) *
            MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => Work.KMTAreas.A7.GmixedFam ρ P C₀ a l₂ k₁ k₂ t g n x))
              p₂ MeasureTheory.Measure.count := by
          refine mul_le_mul ?_ le_rfl bot_le ?_
          · exact le_mul_of_one_le_right bot_le hone
          · positivity
  · -- ### Case 2: the large-scale branch (the deep input)
    have hlt : max (max Bna Bfa) (max Bpl Bc) < max l₂ (max k₁ k₂) := not_le.mp hcase
    have hBna₁ : Bna ≤ max (max Bna Bfa) (max Bpl Bc) :=
      le_trans (le_max_left Bna Bfa) (le_max_left (max Bna Bfa) (max Bpl Bc))
    have hBfa₁ : Bfa ≤ max (max Bna Bfa) (max Bpl Bc) :=
      le_trans (le_max_right Bna Bfa) (le_max_left (max Bna Bfa) (max Bpl Bc))
    have hBpl₁ : Bpl ≤ max (max Bna Bfa) (max Bpl Bc) :=
      le_trans (le_max_left Bpl Bc) (le_max_right (max Bna Bfa) (max Bpl Bc))
    have hBc₁ : Bc ≤ max (max Bna Bfa) (max Bpl Bc) :=
      le_trans (le_max_right Bpl Bc) (le_max_right (max Bna Bfa) (max Bpl Bc))
    have h2 := hC2 a Λ l₂ k₁ k₂ t g n₀ hΛ hLac ha hl₂ ht hgb (lt_of_le_of_lt hBc₁ hlt)
      (hna l₂ k₁ k₂ (le_of_lt (lt_of_le_of_lt hBna₁ hlt)))
      (fun n hn => ⟨hfa l₂ k₁ k₂ (Nat.floor (a n)) (lt_of_le_of_lt hBfa₁ hlt)
          (splitCut_of_loGuard hn),
        hpl l₂ k₁ k₂ (Nat.floor (a n)) (lt_of_le_of_lt hBpl₁ hlt) (splitCut_of_loGuard hn)⟩)
    refine h2.trans ?_
    have hconst : (↑(max 1 (C2 Λ)) : ENNReal) ≤
        (↑(max 1 (max (C2 Λ) ((⌈C1 ρ⌉₊ : ℕ) : NNReal))) : ENNReal) :=
      ENNReal.coe_le_coe.mpr (max_le (le_max_left _ _)
        (le_trans (le_max_left (C2 Λ) ((⌈C1 ρ⌉₊ : ℕ) : NNReal))
          (le_max_right 1 (max (C2 Λ) ((⌈C1 ρ⌉₊ : ℕ) : NNReal)))))
    have hlw : ENNReal.ofReal (Work.KMTAreas.A7.lossWeight Ac ρ 0 l₂ k₁ k₂)
        ≤ ENNReal.ofReal (Work.KMTAreas.A7.lossWeight (max 8 Ac) ρ 0 l₂ k₁ k₂) :=
      ENNReal.ofReal_le_ofReal
        (Work.KMTAreas.A7.lossWeight_mono_A hAc (le_max_right _ _) ρ hρ.le 0 l₂ k₁ k₂)
    calc (↑(max 1 (C2 Λ)) : ENNReal) *
          ENNReal.ofReal (Work.KMTAreas.A7.lossWeight Ac ρ 0 l₂ k₁ k₂) *
          MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => Work.KMTAreas.A7.GmixedFam ρ P C₀ a l₂ k₁ k₂ t g n x))
            p₂ MeasureTheory.Measure.count
        ≤ (↑(max 1 (max (C2 Λ) ((⌈C1 ρ⌉₊ : ℕ) : NNReal))) : ENNReal) *
            ENNReal.ofReal (Work.KMTAreas.A7.lossWeight (max 8 Ac) ρ 0 l₂ k₁ k₂) *
            MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => Work.KMTAreas.A7.GmixedFam ρ P C₀ a l₂ k₁ k₂ t g n x))
              p₂ MeasureTheory.Measure.count := by
          refine mul_le_mul (mul_le_mul hconst hlw bot_le (by positivity)) le_rfl bot_le ?_
          positivity

/-! ## §3.  The per-shift fibre sampling estimate and the large-scale crux

This block is the proof of the remaining input `FiberLargeResidueLargeScalesProp`.  It is the
content of `Submission/Work/A7MixedG/FiberLargeResidueHolds.lean` (proved by the colleague
agent that answered the delegation of this statement), **rebased** into this file: that file
imports *this* one (for the `Prop` and for the small-scale/Young branch below), so importing
it back would be an import cycle.  The declarations therefore live in the fresh namespace
`Work.KMTAreas.A7MixedG.CruxAux`; all references to this file's lemmas are fully qualified
and unchanged, and the only edited name is the cross-reference to the per-shift estimate. -/
namespace CruxAux

open Work.A7MixedG
open Work.KMTAreas.A7

open PointwiseErgodicTheorems

noncomputable section

/-! ## §1.  The per-shift fibre sampling estimate -/

/-- **The per-shift (per-residue) fibre sampling estimate of the `g`-side** (KMT §8, the
per-residue form of `fiberVarSamplingG_large_bdd`).

For `ρ ∈ (0,1]`, `p ∈ (1,∞)`, `r > 2` there is a constant `C` such that for every exact-height
`l₂`, every cut scale `U ≥ 1`, every `t`, every bounded `g`, every family of scales `N` and
clipping predicate `S` satisfying the quantitative Shannon hypotheses

* (Farey) `8·2^{k₂}·arithQ ρ l₂ ≤ N n` for all `n`,
* (strict main regime) `k₂ + 2U + 1 ≤ Log (N n)` for all `n`,
* (non-aliasing) `NonAliasing (-(2U)) (iwArithFreqs ρ l₂)`,

and every shift `M : ℤ`, the twisted fibre of the family
`(if S n then Tex ρ l₂ (φ̃_{N n, k₂, t}) g else 0)` is controlled by the family itself. -/
theorem fiberOp_var_shift_largeScales
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (P : Polynomial ℤ) (hd : 1 ≤ P.natDegree)
    (p : ENNReal) (hp : 1 < p) (hpt : p < ⊤) (r : NNReal) (hr : 2 < r) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (l₂ k₂ U : ℕ), 1 ≤ U → ∀ (t : ℝ) (g : ℤ → ℂ) (Bg : ℝ),
        (∀ x : ℤ, ‖g x‖ ≤ Bg) →
        ∀ (N : ℕ → ℕ) (S : ℕ → Prop) [DecidablePred S],
          (∀ n : ℕ, 8 * (2 : ℝ) ^ k₂ * (Work.KMTAreas.A7.arithQ ρ l₂ : ℝ) ≤ (N n : ℝ)) →
          (∀ n : ℕ, k₂ + 2 * U + 1 ≤ (Work.Analysis.EndVar.logN (N n)).toNat) →
          Work.Analysis.IonescuWainger.NonAliasing (-(2 * (U : ℤ)))
            (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂) →
          ∀ M : ℤ,
            MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => Work.KMTAreas.A7.fiberOp ρ l₂
                (Work.KMTAreas.A7.mStargF P.natDegree U) M
                (if S n then Work.KMTAreas.A7.Tex ρ l₂
                  (Work.KMTAreas.A7.varphitildeNt P P.natDegree (N n) k₂ t) g else 0) x))
              p MeasureTheory.Measure.count
            ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm (fun x : ℤ =>
                PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
                  (if S n then Work.KMTAreas.A7.Tex ρ l₂
                    (Work.KMTAreas.A7.varphitildeNt P P.natDegree (N n) k₂ t) g else 0) x))
              p MeasureTheory.Measure.count := by
  classical
  set pR : ℝ := p.toReal with hpR
  have hpR1 : 1 < pR := by
    rw [hpR, ← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top (ne_of_lt hpt)).mpr hp
  have hpR0 : 0 < pR := lt_trans zero_lt_one hpR1
  have hpof : ENNReal.ofReal pR = p := by
    rw [hpR]
    exact ENNReal.ofReal_toReal (ne_of_lt hpt)
  have h1pR : (0 : ℝ) ≤ 1 / pR := by positivity
  obtain ⟨Ceng, hCengpos, heng⟩ :=
    Work.KMTAreas.A7.convSublatticeCosetCompareBdd pR hpR1 r (le_of_lt (lt_trans (by norm_num) hr))
  refine ⟨Ceng ^ (1 / pR), Real.rpow_pos_of_pos hCengpos _, ?_⟩
  intro l₂ k₂ U hU t g Bg hBg N S _ hfarey hstrict hna M
  set q : ℕ := Work.KMTAreas.A7.arithQ ρ l₂ with hq
  set A : Finset Work.Analysis.IonescuWainger.Circle :=
    Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂ with hA
  set φ : ℕ → ℝ → ℂ := fun n => Work.KMTAreas.A7.varphitildeNt P P.natDegree (N n) k₂ t with hφ
  set κ : ℕ → ℤ → ℂ := fun n j => Work.KMTAreas.A7.cw (φ n) j with hκ
  set Hf : ℕ → ℤ → ℤ → ℂ :=
    fun n y z => if S n then Work.KMTAreas.A7.sliceInput A g y z else 0 with hHf
  set F : ℤ → ENNReal := fun y => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
    Work.KMTAreas.A7.fiberOp ρ l₂ (Work.KMTAreas.A7.mStargF P.natDegree U) M
      (if S n then Work.KMTAreas.A7.Tex ρ l₂ (φ n) g else 0) y) with hF
  set W : ℤ → ENNReal := fun x => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
    (if S n then Work.KMTAreas.A7.Tex ρ l₂ (φ n) g else 0) x) with hW
  have hqpos : 0 < q := by
    rw [hq]
    exact Work.KMTAreas.A7.arithQ_pos ρ l₂
  have hq1 : 1 ≤ q := hqpos
  have hnaNew : Work.Analysis.IonescuWainger.NonAliasing (-(2 * (U : ℤ)))
      (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂) :=
    Work.KMTAreas.A7MixedG.NonAliasing_subset hna
      (fun α hα => Work.KMTAreas.A7.mem_iwArithFreqsNew_le hα)
  have hqnsmul : ∀ α ∈ A, q • α = 0 := by
    intro α hα
    have hα' : α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂ := hA ▸ hα
    have h1 : Work.KMTAreas.A7.arithQ ρ l₂ • α = 0 :=
      Work.KMTAreas.A7.arithQ_nsmul_eq_zero (Work.KMTAreas.A7.mem_iwArithFreqsNew_le hα')
    rw [hq]
    exact h1
  have hφint : ∀ n : ℕ, Integrable (φ n) := by
    intro n
    rw [hφ]
    exact Work.KMTAreas.A7.integrable_varphitildeNt_aux P P.natDegree (N n) k₂ t
  have hφsum : ∀ n : ℕ, Summable (fun j : ℤ => ‖Work.KMTAreas.A7.cw (φ n) j‖) := by
    intro n
    rw [hφ]
    exact Work.KMTAreas.A7.summable_cw_varphitildeNt P P.natDegree (N n) k₂ t
  have hφsupp : ∀ n : ℕ, ∀ ξ : ℝ, φ n ξ ≠ 0 →
      |ξ| ≤ (2 : ℝ) ^ (-(2 * (((P.natDegree * U : ℕ) : ℤ))) - 1) := by
    intro n ξ hξ
    rw [hφ] at hξ
    exact Work.KMTAreas.A7Hi.varphitildeNt_support_strict_g P hd (N n) k₂ U t (hstrict n) ξ hξ
  have hfareyU : ∀ n : ℕ, 8 * (2 : ℝ) ^ k₂ * (q : ℝ) ≤ (N n : ℝ) := by
    intro n
    rw [hq]
    exact hfarey n
  have hβ : 0 < 1 / (4 * (q : ℝ)) := by positivity
  have hβq : (1 / (4 * (q : ℝ))) * (q : ℝ) ≤ 1 / 4 := by
    have h : (1 / (4 * (q : ℝ))) * (q : ℝ) = 1 / 4 := by
      have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqpos
      field_simp
    rw [h]
  have hφsuppq : ∀ n : ℕ, ∀ ξ : ℝ, φ n ξ ≠ 0 → |ξ| ≤ 1 / (4 * (q : ℝ)) := by
    intro n ξ hξ
    rw [hφ] at hξ
    exact Work.KMTAreas.A7Hi.varphitildeNt_support_le_quarter_g P hd q hq1 (N n) k₂ t
      (hfareyU n) ξ hξ
  have hκsum : ∀ n : ℕ, Summable (fun j : ℤ => ‖κ n j‖) := by
    intro n
    rw [hκ]
    exact hφsum n
  have hB0 : 0 ≤ Bg := le_trans (norm_nonneg (g 0)) (hBg 0)
  have hHfb : ∀ n : ℕ, ∀ y z : ℤ, ‖Hf n y z‖ ≤ Bg * (A.card : ℝ) := by
    intro n y z
    rw [hHf]
    by_cases hSn : S n
    · simp only [hSn, if_true]
      exact Work.KMTAreas.A7Hi.norm_sliceInput_le A g Bg hBg y z
    · simp only [hSn, if_false, norm_zero]
      exact mul_nonneg hB0 (Nat.cast_nonneg _)
  -- ### the band-`1/(4q)` continuous extension of the kernel `κ`
  set kext : ℕ → ℝ → ℂ := fun n s => ∫ θ, φ n θ * Work.KMTAreas.A7.ee (-(s * θ)) with hkext
  have hkextdata : ∀ n : ℕ,
      Integrable (kext n) ∧ Continuous (kext n) ∧
        (∀ m : ℤ, kext n (m : ℝ) = κ n m) ∧
        (∀ ξ : ℝ, ξ ∉ Set.Icc (-(1 / (4 * (q : ℝ)))) (1 / (4 * (q : ℝ))) →
          FourierTransform.fourier (kext n) ξ = 0) := by
    intro n
    have hfun : kext n = fun s : ℝ =>
        ∫ θ, (Work.KMTAreas.A7Hi.varphitildeNtSch_g P P.natDegree (N n) k₂ t : ℝ → ℂ) θ
          * Work.KMTAreas.A7.ee (-(s * θ)) := by
      funext s
      rw [hkext, hφ]
      simp only [Work.KMTAreas.A7Hi.varphitildeNtSch_g_coe]
    have hfun2 : kext n
        = ⇑(𝓕 (Work.KMTAreas.A7Hi.varphitildeNtSch_g P P.natDegree (N n) k₂ t) :
            SchwartzMap ℝ ℂ) := by
      rw [hfun]
      funext s
      exact Work.KMTAreas.A7.cwR_eq_fourier _ s
    have hsupp : ∀ ξ : ℝ,
        (Work.KMTAreas.A7Hi.varphitildeNtSch_g P P.natDegree (N n) k₂ t : ℝ → ℂ) ξ ≠ 0 →
        |ξ| ≤ 1 / (4 * (q : ℝ)) := by
      intro ξ hξ
      refine hφsuppq n ξ ?_
      simp only [hφ]
      rwa [← Work.KMTAreas.A7Hi.varphitildeNtSch_g_apply]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hfun2]
      exact (𝓕 (Work.KMTAreas.A7Hi.varphitildeNtSch_g P P.natDegree (N n) k₂ t)).integrable
    · rw [hfun2]
      exact (𝓕 (Work.KMTAreas.A7Hi.varphitildeNtSch_g P P.natDegree (N n) k₂ t)).continuous
    · intro m
      rw [hfun]
      have h1 : (∫ θ, (Work.KMTAreas.A7Hi.varphitildeNtSch_g P P.natDegree (N n) k₂ t :
              ℝ → ℂ) θ * Work.KMTAreas.A7.ee (-(((m : ℤ) : ℝ) * θ)))
          = Work.KMTAreas.A7.cw
              (Work.KMTAreas.A7.varphitildeNt P P.natDegree (N n) k₂ t) m := by
        simp only [Work.KMTAreas.A7.cw, Work.KMTAreas.A7Hi.varphitildeNtSch_g_apply, neg_mul]
      simpa only [hκ, hφ] using h1
    · intro ξ hξ
      rw [hfun]
      exact Work.KMTAreas.A7.fourier_cwR_band (1 / (4 * (q : ℝ))) hβ
        (Work.KMTAreas.A7Hi.varphitildeNtSch_g P P.natDegree (N n) k₂ t) hsupp ξ hξ
  -- ### the per-coset comparison
  have hpair : ∀ r₀ : ℤ,
      (∑' z : ℤ, (F ((q : ℤ) * z + r₀)) ^ pR)
        ≤ ENNReal.ofReal Ceng *
          (∑' z : ℤ, (W ((q : ℤ) * z + (r₀ - M))) ^ pR) := by
    intro r₀
    have hL : ∀ z : ℤ, F ((q : ℤ) * z + r₀)
        = PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => ∑' j : ℤ,
            κ n j * Hf n (M - r₀) ((q : ℤ) * z + r₀ - j)) := by
      intro z
      have hfun : (fun n : ℕ => Work.KMTAreas.A7.fiberOp ρ l₂
            (Work.KMTAreas.A7.mStargF P.natDegree U) M
            (if S n then Work.KMTAreas.A7.Tex ρ l₂ (φ n) g else 0)
            ((q : ℤ) * z + r₀))
          = fun n : ℕ => ∑' j : ℤ, κ n j * Hf n (M - r₀) ((q : ℤ) * z + r₀ - j) := by
        funext n
        rw [hκ, hHf]
        rw [Work.KMTAreas.A7Hi.fiberOp_mStargF_Sclip ρ hρ hρ1 P l₂ U hU hd hnaNew (φ n)
          (hφint n) (hφsum n) (hφsupp n) g Bg hBg (S n) M]
        simp only [ite_apply, Pi.zero_apply]
        rw [Work.KMTAreas.A7.fiberOp_residue_eq_slice ρ l₂ (φ n) q (hφsum n) g Bg hBg hqnsmul
          M r₀ z]
        exact (Work.KMTAreas.A7.sliceSumm_eq_tsum_cw_sliceInput A (φ n) (hφsum n) g Bg hBg
          (M - r₀) ((q : ℤ) * z + r₀) (S n)).symm
      simp only [hF]
      rw [hfun]
    have hR : ∀ z : ℤ, PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => ∑' j : ℤ,
          κ n j * Hf n (M - r₀) ((q : ℤ) * z + (r₀ - M) - j))
        = W ((q : ℤ) * z + (r₀ - M)) := by
      intro z
      have hfun : (fun n : ℕ => ∑' j : ℤ, κ n j * Hf n (M - r₀)
              ((q : ℤ) * z + (r₀ - M) - j))
          = fun n : ℕ => (if S n then Work.KMTAreas.A7.Tex ρ l₂ (φ n) g else 0)
              ((q : ℤ) * z + (r₀ - M)) := by
        funext n
        rw [hκ, hHf]
        rw [Work.KMTAreas.A7.sliceSumm_eq_tsum_cw_sliceInput A (φ n) (hφsum n) g Bg hBg
          (M - r₀) ((q : ℤ) * z + (r₀ - M)) (S n)]
        simp only [ite_apply, Pi.zero_apply]
        by_cases hSn : S n
        · simp only [hSn, if_true]
          rw [← Work.KMTAreas.A7Hi.fiberOp_zero_eq_Tex ρ l₂ (φ n) (hφint n) g]
          have hy : (M - r₀) = 0 - ((r₀ - M)) := by ring
          rw [hy]
          rw [← Work.KMTAreas.A7.fiberOp_residue_eq_slice ρ l₂ (φ n) q (hφsum n) g Bg hBg
            hqnsmul 0 (r₀ - M) z]
        · simp only [hSn, if_false]
      simp only [hW]
      rw [hfun]
    calc (∑' z : ℤ, (F ((q : ℤ) * z + r₀)) ^ pR)
        = ∑' z : ℤ, (PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => ∑' j : ℤ,
            κ n j * Hf n (M - r₀) ((q : ℤ) * z + r₀ - j))) ^ pR :=
          tsum_congr (fun z => by rw [hL z])
      _ ≤ ENNReal.ofReal Ceng * ∑' z : ℤ, (PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => ∑' j : ℤ, κ n j * Hf n (M - r₀)
              ((q : ℤ) * z + (r₀ - M) - j))) ^ pR :=
          heng (1 / (4 * (q : ℝ))) hβ q hqpos hβq κ kext hkextdata hκsum Hf
            (Bg * (A.card : ℝ)) hHfb (M - r₀) r₀ (r₀ - M)
      _ = ENNReal.ofReal Ceng *
            (∑' z : ℤ, (W ((q : ℤ) * z + (r₀ - M))) ^ pR) := by
          rw [tsum_congr (fun z => by rw [hR z])]
  -- ### the total-sum bound
  have hkey : (∑' x : ℤ, (F x) ^ pR) ≤ ENNReal.ofReal Ceng * (∑' x : ℤ, (W x) ^ pR) := by
    rw [Work.KMTAreas.A7Hi.periodDecompLocal q hqpos (fun x : ℤ => (F x) ^ pR)]
    calc ∑ r ∈ Finset.range q, ∑' z : ℤ, (F ((q : ℤ) * z + (r : ℤ))) ^ pR
        ≤ ∑ r ∈ Finset.range q, ENNReal.ofReal Ceng *
            (∑' z : ℤ, (W ((q : ℤ) * z + ((r : ℤ) - M))) ^ pR) :=
          Finset.sum_le_sum (fun r _ => hpair (r : ℤ))
      _ = ENNReal.ofReal Ceng * (∑ r ∈ Finset.range q,
            ∑' z : ℤ, (W ((q : ℤ) * z + ((r : ℤ) - M))) ^ pR) := by
          rw [Finset.mul_sum]
      _ = ENNReal.ofReal Ceng * (∑' x : ℤ, (W x) ^ pR) := by
          rw [Work.KMTAreas.A7Hi.cosetShift_decomp q hqpos (fun x : ℤ => (W x) ^ pR) M]
  -- ### the norm comparison
  have hgoal : MeasureTheory.eLpNorm F (ENNReal.ofReal pR) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (Ceng ^ (1 / pR)) *
        MeasureTheory.eLpNorm W (ENNReal.ofReal pR) MeasureTheory.Measure.count :=
    Work.A7MixedG.eLpNorm_le_of_tsum_rpow_le hpR0 hCengpos hkey
  rwa [← hpof]

/-! ## §2.  The `uScale` instance (the per-shift fibre sampling estimate of the mixed range) -/

/-- **The per-shift form of the mixed `g`-side fibre sampling estimate** — the statement of
`Work.KMTAreas.A7Hi.fiberVarSamplingGShift`, proved from `fiberOp_var_shift_largeScales` at the
cut scale `U := uScale ρ (max l₂ (max k₁ k₂))`. -/
theorem fiberVarSamplingGShift_holds (P : Polynomial ℤ) (hdeg : 2 ≤ P.natDegree) (r : NNReal)
    (hr : 2 < r) :
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∀ (p : ENNReal), 1 < p → p < ⊤ →
      ∃ C : ℝ, 0 < C ∧
        ∀ (l₂ k₁ k₂ : ℕ) (t : ℝ) (g : ℤ → ℂ) (Bg : ℝ), (∀ x : ℤ, ‖g x‖ ≤ Bg) →
          ∀ (N : ℕ → ℕ) (S : ℕ → Prop) [DecidablePred S] (M : ℤ),
          t ∈ Set.Icc (1 / 2 : ℝ) 1 →
          (∀ n : ℕ, 8 * (2 : ℝ) ^ k₂ * (Work.KMTAreas.A7.arithQ ρ l₂ : ℝ) ≤ (N n : ℝ)) →
          (∀ n : ℕ, k₂ + 2 * (Work.KMTAreas.A7.uScale ρ (max l₂ (max k₁ k₂)) : ℕ) + 1
              ≤ (Work.Analysis.EndVar.logN (N n)).toNat) →
          Work.Analysis.IonescuWainger.NonAliasing
            (-(2 * (Work.KMTAreas.A7.uScale ρ (max l₂ (max k₁ k₂)) : ℤ)))
            (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂) →
          MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => Work.KMTAreas.A7.fiberOp ρ l₂
                (Work.KMTAreas.A7.mStargF P.natDegree
                  (Work.KMTAreas.A7.uScale ρ (max l₂ (max k₁ k₂)))) M
                (if S n then Work.KMTAreas.A7.Tex ρ l₂
                  (Work.KMTAreas.A7.varphitildeNt P P.natDegree (N n) k₂ t) g else 0) x))
            p MeasureTheory.Measure.count
          ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm (fun x : ℤ =>
              PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
                (if S n then Work.KMTAreas.A7.Tex ρ l₂
                  (Work.KMTAreas.A7.varphitildeNt P P.natDegree (N n) k₂ t) g else 0) x))
            p MeasureTheory.Measure.count := by
  intro ρ hρ hρ1 p hp hpt
  obtain ⟨C, hC, hmain⟩ :=
    fiberOp_var_shift_largeScales ρ hρ hρ1 P (by omega) p hp hpt r hr
  refine ⟨C, hC, ?_⟩
  intro l₂ k₁ k₂ t g Bg hBg N S _ M ht hfarey hstrict hna
  exact hmain l₂ k₂ (Work.KMTAreas.A7.uScale ρ (max l₂ (max k₁ k₂)))
    (Work.KMTAreas.A7.one_le_uScale_bdd hρ.le _) t g Bg hBg N S hfarey hstrict hna M

end

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators FourierTransform
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier

noncomputable section

/-! ## §3.  The large-scale crux `FiberLargeResidueLargeScalesProp`

This is the assembly of `Submission/Work/KMTAreas/A7/mixedGFibreLargeScalesCrux.lean` with its
per-shift input `Work.KMTAreas.A7Hi.fiberVarSamplingGShift` replaced by the proved
`Work.KMTAreas.A7MixedG.CruxAux.fiberVarSamplingGShift_holds`. -/

/-- The loss weight at `c = 0` is `1`. -/
theorem lossWeight_zero_local (ρ : ℝ) (l₁ l₂ k₁ k₂ : ℕ) :
    lossWeight 0 ρ l₁ l₂ k₁ k₂ = 1 := by
  rw [lossWeight]
  have h1 : (0 : ℝ) * ρ * lmaxR l₁ l₂ k₁ k₂ = 0 := by ring
  rw [h1, Real.rpow_zero, Real.rpow_zero, mul_one]

/-- **The guarded `g`-side family of the mixed range is the `l₁ = 0` instance of `Gcl`.** -/
theorem GmixedFam_eq_Gcl_local (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → NNReal)
    (l₂ k₁ k₂ : ℕ) (t : ℝ) (g : ℤ → ℂ) (hl₂ : l₂ ≠ 0) :
    GmixedFam ρ P C₀ a l₂ k₁ k₂ t g = Gcl ρ P C₀ a 0 l₂ k₁ k₂ t g := by
  funext n x
  simp only [GmixedFam, Gcl, loGuard, core, Tm, Tex, diffFreqs_eq_iwArithFreqsNew hl₂]

theorem fiberLargeResidueLargeScalesProp_holds (P : Polynomial ℤ) (p₂ : ENNReal) (hdeg : 2 ≤ P.natDegree)
    (hp₂ : 1 < p₂) (htp₂ : p₂ < ⊤) :
    Work.KMTAreas.A7MixedG.FiberLargeResidueLargeScalesProp P p₂ hdeg hp₂ htp₂ := by
  intro C₀ r hC₀ hr
  -- ### the `ρ`-dependent threshold packaging the three arithmetic inputs of the fibre estimate
  have h_ex : ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∃ B : ℕ,
      (∀ (l₂ k₁ k₂ N : ℕ),
        splitCut ρ (max l₂ (max k₁ k₂)) < N → B < max l₂ (max k₁ k₂) →
          (8 * (2 : ℝ) ^ k₂ * (arithQ ρ l₂ : ℝ) ≤ (N : ℝ)) ∧
          (k₂ + 2 * (uScale ρ (max l₂ (max k₁ k₂)) : ℕ) + 1
            ≤ (Work.Analysis.EndVar.logN N).toNat)) ∧
      (∀ (l L : ℕ), l ≤ L → B ≤ L →
        Work.Analysis.IonescuWainger.NonAliasing (-(2 * (uScale ρ L : ℤ)))
          (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)) ∧
      (∀ (l₂ k₁ k₂ : ℕ), B ≤ max l₂ (max k₁ k₂) →
        loMixedU ρ P.natDegree l₂ k₁ k₂ = uScale ρ (max l₂ (max k₁ k₂))) := by
    intro ρ hρ hρ1
    obtain ⟨B₁, hB₁⟩ := Work.KMTAreas.A7Hi.farey_and_strict_of_large_L_g ρ hρ hρ1
    obtain ⟨B₂, hB₂⟩ := Work.KMTAreas.A7.exists_nonAliasing_uScale ρ hρ hρ1
    obtain ⟨B₃, hB₃⟩ := Work.KMTAreas.A7MixedG.loMixedU_eq_uScale_of_large ρ hρ P.natDegree
    refine ⟨max (B₁ + 1) (max B₂ B₃), ?_, ?_, ?_⟩
    · intro l₂ k₁ k₂ N hsplit hlt
      have hmax : max (max 0 l₂) (max k₁ k₂) = max l₂ (max k₁ k₂) := by omega
      have hB₁lt : B₁ < max l₂ (max k₁ k₂) := by
        have hle : B₁ + 1 ≤ max (B₁ + 1) (max B₂ B₃) := le_max_left _ _
        omega
      have hsplit' : splitCut ρ (max (max 0 l₂) (max k₁ k₂)) < N := by rw [hmax]; exact hsplit
      have h := hB₁ 0 l₂ k₁ k₂ N hsplit' (by rw [hmax]; exact hB₁lt)
      rw [hmax] at h
      refine ⟨?_, h.2⟩
      simpa only [max_eq_right (Nat.zero_le l₂)] using h.1
    · intro l L hl hL
      have h2 : B₂ ≤ L :=
        le_trans (le_trans (le_max_left B₂ B₃) (le_max_right (B₁ + 1) (max B₂ B₃))) hL
      exact hB₂ l L hl h2
    · intro l₂ k₁ k₂ hL
      have h3 : B₃ ≤ max l₂ (max k₁ k₂) :=
        le_trans (le_trans (le_max_right B₂ B₃) (le_max_right (B₁ + 1) (max B₂ B₃))) hL
      exact hB₃ l₂ k₁ k₂ h3
  classical
  -- ### the threshold as a *function* of `ρ`
  let T : ℝ → ℕ := fun ρ => if h : 0 < ρ ∧ ρ ≤ 1 then Classical.choose (h_ex ρ h.1 h.2) else 0
  have hTspec : ∀ ρ (hρ : 0 < ρ) (hρ1 : ρ ≤ 1),
      (∀ (l₂ k₁ k₂ N : ℕ),
        splitCut ρ (max l₂ (max k₁ k₂)) < N → T ρ < max l₂ (max k₁ k₂) →
          (8 * (2 : ℝ) ^ k₂ * (arithQ ρ l₂ : ℝ) ≤ (N : ℝ)) ∧
          (k₂ + 2 * (uScale ρ (max l₂ (max k₁ k₂)) : ℕ) + 1
            ≤ (Work.Analysis.EndVar.logN N).toNat)) ∧
      (∀ (l L : ℕ), l ≤ L → T ρ ≤ L →
        Work.Analysis.IonescuWainger.NonAliasing (-(2 * (uScale ρ L : ℤ)))
          (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)) ∧
      (∀ (l₂ k₁ k₂ : ℕ), T ρ ≤ max l₂ (max k₁ k₂) →
        loMixedU ρ P.natDegree l₂ k₁ k₂ = uScale ρ (max l₂ (max k₁ k₂))) := by
    intro ρ hρ hρ1
    have hchoose : T ρ = Classical.choose (h_ex ρ hρ hρ1) := by
      simp only [T]
      rw [dif_pos (show 0 < ρ ∧ ρ ≤ 1 from ⟨hρ, hρ1⟩)]
    rw [hchoose]
    exact Classical.choose_spec (h_ex ρ hρ hρ1)
  -- ### the Young constant of the small-scale branch
  have hr1 : (1 : NNReal) ≤ r := le_of_lt (lt_of_le_of_lt (by norm_num : (1 : NNReal) ≤ 2) hr)
  obtain ⟨Cyoung, hCyoungpos, hYoung⟩ :=
    Work.KMTAreas.A7MixedG.fiberOpP_young_bound P (by omega) r hr1 p₂ hp₂ htp₂ (Bfun := T)
  -- ### the fibre-sampling constant of the large-scale branch
  have hfib := Work.KMTAreas.A7MixedG.CruxAux.fiberVarSamplingGShift_holds P hdeg r hr
  -- ### the existential constants of the target
  refine ⟨0, le_refl 0, 1, one_pos, 0, ?_⟩
  intro ρ hρ hρ1
  obtain ⟨hTharf, hTna, hTu⟩ := hTspec ρ hρ hρ1
  obtain ⟨Cfib', hCfib'pos, hfib'⟩ := hfib ρ hρ hρ1 p₂ hp₂ htp₂
  set Cbig : NNReal := max (⌈Cyoung ρ⌉₊ : NNReal) (⌈Cfib'⌉₊ : NNReal) with hCbigdef
  have hCfle : ENNReal.ofReal (Cyoung ρ) ≤ ((max 1 (max 1 Cbig) : NNReal) : ENNReal) :=
    calc ENNReal.ofReal (Cyoung ρ) ≤ ((⌈Cyoung ρ⌉₊ : NNReal) : ENNReal) := by
          rw [← ENNReal.ofReal_coe_nnreal]
          exact ENNReal.ofReal_le_ofReal (Nat.le_ceil _)
      _ ≤ ((max 1 (max 1 Cbig) : NNReal) : ENNReal) := by
          rw [ENNReal.coe_le_coe]
          exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hCffle : ENNReal.ofReal Cfib' ≤ ((max 1 (max 1 Cbig) : NNReal) : ENNReal) :=
    calc ENNReal.ofReal Cfib' ≤ ((⌈Cfib'⌉₊ : NNReal) : ENNReal) := by
          rw [← ENNReal.ofReal_coe_nnreal]
          exact ENNReal.ofReal_le_ofReal (Nat.le_ceil _)
      _ ≤ ((max 1 (max 1 Cbig) : NNReal) : ENNReal) := by
          rw [ENNReal.coe_le_coe]
          exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  refine ⟨fun _ : NNReal => (max 1 Cbig : NNReal), ?_⟩
  intro a Λ l₂ k₁ k₂ t g n₀ hΛ hlac ha hl₂ ht hgb hBL hna hguard
  have hl₂0 : l₂ ≠ 0 := by omega
  obtain ⟨Bg, hBg⟩ := hgb
  have hgB : ∀ y : ℤ, ‖g y‖ ≤ Bg := fun y => hBg ⟨y, rfl⟩
  set L : ℕ := max l₂ (max k₁ k₂) with hLdef
  set q : ℕ := arithQ ρ l₂ with hqdef
  set U : ℕ := uScale ρ (max l₂ (max k₁ k₂)) with hUdef
  have hlossW : lossWeight 0 ρ 0 l₂ k₁ k₂ = 1 := lossWeight_zero_local ρ 0 l₂ k₁ k₂
  have hlw1 : (1 : ENNReal) ≤ ENNReal.ofReal (lossWeight 0 ρ 0 l₂ k₁ k₂) := by
    rw [hlossW, ENNReal.ofReal_one]
  have hE : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => GmixedFam ρ P C₀ a l₂ k₁ k₂ t g n x)) p₂ MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (lossWeight 0 ρ 0 l₂ k₁ k₂)
        * MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => GmixedFam ρ P C₀ a l₂ k₁ k₂ t g n x)) p₂ MeasureTheory.Measure.count := by
    calc MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => GmixedFam ρ P C₀ a l₂ k₁ k₂ t g n x)) p₂ MeasureTheory.Measure.count
        = MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => GmixedFam ρ P C₀ a l₂ k₁ k₂ t g n x)) p₂ MeasureTheory.Measure.count
            * 1 := (mul_one _).symm
      _ ≤ MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => GmixedFam ρ P C₀ a l₂ k₁ k₂ t g n x)) p₂ MeasureTheory.Measure.count
            * ENNReal.ofReal (lossWeight 0 ρ 0 l₂ k₁ k₂) := mul_le_mul_of_nonneg_left hlw1 bot_le
      _ = ENNReal.ofReal (lossWeight 0 ρ 0 l₂ k₁ k₂)
            * MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => GmixedFam ρ P C₀ a l₂ k₁ k₂ t g n x)) p₂
              MeasureTheory.Measure.count := mul_comm _ _
  by_cases hcase : L ≤ T ρ
  · -- ### Case 1: the small-scale (Young) branch
    have hl₂T : l₂ ≤ T ρ := by
      have h1 : l₂ ≤ L := by rw [hLdef]; exact le_max_left l₂ (max k₁ k₂)
      exact le_trans h1 hcase
    have hY := hYoung ρ hρ l₂ k₁ k₂ hl₂T n₀ (GmixedFam ρ P C₀ a l₂ k₁ k₂ t g)
    refine hY.trans ?_
    calc ENNReal.ofReal (Cyoung ρ) * MeasureTheory.eLpNorm (fun x : ℤ =>
            PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => GmixedFam ρ P C₀ a l₂ k₁ k₂ t g n x)) p₂ MeasureTheory.Measure.count
        ≤ ((max 1 (max 1 Cbig) : NNReal) : ENNReal)
            * MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
                (fun n : ℕ => GmixedFam ρ P C₀ a l₂ k₁ k₂ t g n x)) p₂
              MeasureTheory.Measure.count :=
          mul_le_mul_of_nonneg_right hCfle bot_le
      _ ≤ ((max 1 (max 1 Cbig) : NNReal) : ENNReal)
            * (ENNReal.ofReal (lossWeight 0 ρ 0 l₂ k₁ k₂)
              * MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
                  (fun n : ℕ => GmixedFam ρ P C₀ a l₂ k₁ k₂ t g n x)) p₂
                MeasureTheory.Measure.count) :=
          mul_le_mul_of_nonneg_left hE bot_le
      _ = ((max 1 (max 1 Cbig) : NNReal) : ENNReal)
            * ENNReal.ofReal (lossWeight 0 ρ 0 l₂ k₁ k₂)
            * MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
                (fun n : ℕ => GmixedFam ρ P C₀ a l₂ k₁ k₂ t g n x)) p₂
              MeasureTheory.Measure.count := by
          rw [mul_assoc]
  · -- ### Case 2: the large-scale fibre estimate
    have hTlt : T ρ < L := lt_of_not_ge hcase
    have hTL : T ρ ≤ L := le_of_lt hTlt
    have hsplit : ∀ n : ℕ, loGuard ρ C₀ a 0 l₂ k₁ k₂ n → splitCut ρ L < Nat.floor (a n) := by
      intro n hn
      rw [hLdef]
      exact Work.KMTAreas.A7MixedG.splitCut_of_loGuard hn
    set S : ℕ → Prop := fun n => loGuard ρ C₀ a 0 l₂ k₁ k₂ n with hSdef
    haveI : DecidablePred S := by intro n; rw [hSdef]; infer_instance
    set K : ℕ := 2 ^ (k₂ + 2 * U + 4) * (q + 1) with hKdef
    set N' : ℕ → ℕ := fun n => if S n then Nat.floor (a n) else K with hNdef
    have hfareyN' : ∀ n : ℕ, 8 * (2 : ℝ) ^ k₂ * (q : ℝ) ≤ (N' n : ℝ) := by
      intro n
      by_cases hSn : S n
      · have hsplit' : splitCut ρ L < Nat.floor (a n) := hsplit n (by simpa only [hSdef] using hSn)
        have h := (hTharf l₂ k₁ k₂ (Nat.floor (a n))
          (by rw [← hLdef]; exact hsplit') hTlt).1
        rw [hNdef]
        simp only [hSn, if_true]
        simpa only [hqdef] using h
      · rw [hNdef]
        simp only [hSn, if_false]
        have hKge : 8 * (2 : ℝ) ^ k₂ * (q : ℝ) ≤ (K : ℝ) := by
          rw [hKdef]
          push_cast
          have hpow : (2 : ℝ) ^ (k₂ + 2 * U + 4)
              = (2 : ℝ) ^ k₂ * (2 : ℝ) ^ (2 * U + 4) := by
            rw [show k₂ + 2 * U + 4 = k₂ + (2 * U + 4) from by ring, pow_add]
          rw [hpow]
          have h3 : (3 : ℕ) ≤ 2 * U + 4 :=
            le_trans (by norm_num : (3 : ℕ) ≤ 4) (Nat.le_add_left 4 (2 * U))
          have h8 : (8 : ℝ) ≤ (2 : ℝ) ^ (2 * U + 4) := by
            rw [show (8 : ℝ) = (2 : ℝ) ^ (3 : ℕ) by norm_num]
            exact pow_le_pow_right₀ (by norm_num) h3
          have hk : (0 : ℝ) < (2 : ℝ) ^ k₂ := by positivity
          have hqnn : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
          nlinarith [h8, hqnn, hk, mul_nonneg hk.le hqnn]
        exact hKge
    have hstrictN' : ∀ n : ℕ, k₂ + 2 * U + 1 ≤ (Work.Analysis.EndVar.logN (N' n)).toNat := by
      intro n
      by_cases hSn : S n
      · have hsplit' : splitCut ρ L < Nat.floor (a n) := hsplit n (by simpa only [hSdef] using hSn)
        have h := (hTharf l₂ k₁ k₂ (Nat.floor (a n))
          (by rw [← hLdef]; exact hsplit') hTlt).2
        rw [hNdef]
        simp only [hSn, if_true]
        simpa only [hUdef] using h
      · rw [hNdef]
        simp only [hSn, if_false]
        have hle : 2 ^ (k₂ + 2 * U + 4) ≤ max K 2 := by
          rw [hKdef]
          refine le_trans ?_ (le_max_left _ _)
          exact Nat.le_mul_of_pos_right _ (by omega : 0 < q + 1)
        have hlog := Nat.le_log_of_pow_le (by norm_num : 1 < 2) hle
        have hlogN : (Work.Analysis.EndVar.logN K).toNat = Nat.log 2 (max K 2) := by
          rw [Work.Analysis.EndVar.logN, Int.toNat_natCast]
        rw [hlogN]
        omega
    have hnaU : Work.Analysis.IonescuWainger.NonAliasing (-(2 * (U : ℤ)))
        (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂) := by
      have h := hTna l₂ L (by rw [hLdef]; exact le_max_left l₂ (max k₁ k₂)) hTL
      rw [hLdef] at h
      rw [hUdef]
      exact h
    have hcut : mStargF P.natDegree U = GmixedKer ρ P l₂ k₁ k₂ := by
      rw [Work.KMTAreas.A7MixedG.GmixedKer_eq,
        hTu l₂ k₁ k₂ (by rw [← hLdef]; exact hTL), ← hUdef]
    have hfam : ∀ n : ℕ, (if S n then Tex ρ l₂
          (varphitildeNt P P.natDegree (N' n) k₂ t) g else 0)
        = GmixedFam ρ P C₀ a l₂ k₁ k₂ t g n := by
      intro n
      rw [GmixedFam_eq_Gcl_local ρ P C₀ a l₂ k₁ k₂ t g hl₂0]
      by_cases hn : S n
      · have hc : core ρ C₀ 0 l₂ k₁ k₂ a n := by
          simpa only [hSdef, loGuard, core] using hn
        have hNn : N' n = Nat.floor (a n) := by
          rw [hNdef]; simp only [hn, if_true]
        simp only [Gcl, hn, hc, if_true, hNn]
      · have hc : ¬ core ρ C₀ 0 l₂ k₁ k₂ a n := by
          simpa only [hSdef, loGuard, core] using hn
        simp only [Gcl, hn, hc, if_false]
    have hbdd := hfib' l₂ k₁ k₂ t g Bg hgB N' S (P.eval n₀) ht hfareyN' hstrictN' hnaU
    simp only [hfam] at hbdd
    have hfiber : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => fiberOp ρ l₂ (mStargF P.natDegree U) (P.eval n₀)
            (GmixedFam ρ P C₀ a l₂ k₁ k₂ t g n) x))
        = (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => fiberOpP ρ P l₂ (GmixedKer ρ P l₂ k₁ k₂) n₀
            (GmixedFam ρ P C₀ a l₂ k₁ k₂ t g n) x)) := by
      funext x
      refine congrArg (fun v => PointwiseErgodicTheorems.variationalNorm r v) (funext fun n => ?_)
      show fiberOp ρ l₂ (mStargF P.natDegree U) (P.eval n₀)
          (GmixedFam ρ P C₀ a l₂ k₁ k₂ t g n) x
        = fiberOp ρ l₂ (GmixedKer ρ P l₂ k₁ k₂) (P.eval n₀)
          (GmixedFam ρ P C₀ a l₂ k₁ k₂ t g n) x
      rw [hcut]
    rw [hfiber] at hbdd
    refine hbdd.trans ?_
    calc ENNReal.ofReal Cfib' * MeasureTheory.eLpNorm (fun x : ℤ =>
            PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => GmixedFam ρ P C₀ a l₂ k₁ k₂ t g n x)) p₂ MeasureTheory.Measure.count
        ≤ ((max 1 (max 1 Cbig) : NNReal) : ENNReal)
            * MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
                (fun n : ℕ => GmixedFam ρ P C₀ a l₂ k₁ k₂ t g n x)) p₂
              MeasureTheory.Measure.count :=
          mul_le_mul_of_nonneg_right hCffle bot_le
      _ ≤ ((max 1 (max 1 Cbig) : NNReal) : ENNReal)
            * (ENNReal.ofReal (lossWeight 0 ρ 0 l₂ k₁ k₂)
              * MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
                  (fun n : ℕ => GmixedFam ρ P C₀ a l₂ k₁ k₂ t g n x)) p₂
                MeasureTheory.Measure.count) :=
          mul_le_mul_of_nonneg_left hE bot_le
      _ = ((max 1 (max 1 Cbig) : NNReal) : ENNReal)
            * ENNReal.ofReal (lossWeight 0 ρ 0 l₂ k₁ k₂)
            * MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
                (fun n : ℕ => GmixedFam ρ P C₀ a l₂ k₁ k₂ t g n x)) p₂
              MeasureTheory.Measure.count := by
          rw [mul_assoc]

end

end CruxAux

/-- **The per-residue, uniform-in-`n₀` large-scale fibre estimate of the mixed range**, i.e. the
statement of `FiberLargeResidueCore` in the regime in which the quantitative
Shannon/aliasing hypotheses of KMT §8 hold (Farey gap of the exact-height frequency set, strict
main regime, non-aliasing).  It is the paper's §8 comparison of the *twisted* Ionescu--Wainger
projection with the *physical shift*; the exact statement consumed by the assembly is that of
`FiberLargeResidueLargeScalesProp` (delegated). -/
theorem FiberLargeResidueCore (P : Polynomial ℤ) (p₂ : ENNReal) (hdeg : 2 ≤ P.natDegree)
    (hp₂ : 1 < p₂) (htp₂ : p₂ < ⊤) :
  ∀ (C₀ : ℕ) (r : NNReal), 1 ≤ C₀ → (2 : NNReal) < r →
    ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∃ B : ℕ,
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ C : NNReal → NNReal,
        ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₂ k₁ k₂ : ℕ) (t : ℝ) (g : ℤ → ℂ) (n₀ : ℤ),
          1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) → 1 ≤ l₂ →
          t ∈ Set.Icc (1/2 : ℝ) 1 → BddAbove (Set.range fun y : ℤ => ‖g y‖) →
          B < max l₂ (max k₁ k₂) →
          MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => Work.KMTAreas.A7.fiberOpP ρ P l₂
                (Work.KMTAreas.A7.GmixedKer ρ P l₂ k₁ k₂) n₀
                (Work.KMTAreas.A7.GmixedFam ρ P C₀ a l₂ k₁ k₂ t g n) x))
            p₂ MeasureTheory.Measure.count
          ≤ (↑(max 1 (C Λ)) : ENNReal) * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A ρ 0 l₂ k₁ k₂) *
              MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
                (fun n : ℕ => Work.KMTAreas.A7.GmixedFam ρ P C₀ a l₂ k₁ k₂ t g n x))
                p₂ MeasureTheory.Measure.count :=
  FiberLargeResidueCore_of_largeScales P p₂ hdeg hp₂ htp₂
    (CruxAux.fiberLargeResidueLargeScalesProp_holds P p₂ hdeg hp₂ htp₂)

end Work.KMTAreas.A7MixedG
