/-
# The bounded-height `§8` model bound for the repaired model `modelTupleRep`

`Work.KMTPlan.A6.ModelPieceBound P r C₀ ρ B` is the bounded-height (`lcL l₁ l₂ k₁ k₂ ≤ B`),
low-case (`k₁ = 0 ∨ k₂ = 0`) `ℓ¹(ℤ;V^r)` bound

  `‖ V^r_n (modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n ·) ‖_{ℓ¹(ℤ)} ≤ K(Λ) ‖f‖₂ ‖g‖₂`

for the *repaired* `§6` model `Work.KMTAreas.A7.modelTupleRep`, for every `ρ ∈ (0,1]` and every
`B`, **without** the deep unproved input `AreaA1`.

## The route

Everything here is at bounded height, so every loss is an absolute constant:

1. `modelTupleRep_eq_intervalIntegral` writes the model tuple as the `t`-integral of the frozen
   slice `t ↦ BtwistExact ρ P l₁ l₂ (mStarF u) (mStargF d u) (HclRep ρ C₀ a … t f) (GclRep … t g)`
   with `u = uRep ρ l₁ l₂ k₁ k₂`.
2. `BtwistExact` is *by definition* the slice kernel `∑'_{i,j} c i j · h(·-i) · k(·-j)` with
   `c i j = arithKernelExact ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ i j · cw m₁ i · cw m₂ j`, so
   `Work.Analysis.Variational.SliceKernelL1` gives, for every frozen `t`,
   `‖V^r (slice)‖_{ℓ¹} ≤ 2 ‖c‖_{ℓ¹(ℤ²)} ‖V^r (HclRep … t f)‖_{ℓ²} ‖V^r (GclRep … t g)‖_{ℓ²}`.
3. The kernel mass `‖c‖_{ℓ¹(ℤ²)}` is bounded at bounded height by
   `max_{l ≤ B} #(ℚ/ℤ)_{≤l}² · Cw²`: the arithmetic part by the two cardinalities
   (`norm_arithKernelSet_le`) and the two continuous parts by the *`u`-uniform* bound
   `vpc_exists_cw_mStarF_tsum_le`.
4. The two linear inputs are the `(2,2)`-instances of the paper's linear lacunary variational
   estimates `(lin-1)`, `(lin-2)` at *arithmetic height* `0`:
   * the `f`-side is `Work.KMTAreas.A7.LoFLinVarClipped` (proved for every `ρ ≤ 1`);
   * the `g`-side is the level-`0` predicate `LowModApproxBoundedH.Lvl0`, obtained for every
     `ρ > 0` from `lvl0DegTwo` (small `ρ`) by the `ρ`-transfer `lvl0Transfer`.
   The passage from height `0` to height `l` is the *lift*
   `LowModApproxBoundedH.Lift.Tle_eq_sum_modulation` (reproduced here in its `eLpNorm` form):
   `Tle ρ l φ` is a finite sum of at most `#(ℚ/ℤ)_{≤l} ≤ #(ℚ/ℤ)_{≤B}` modulated height-`0`
   operators.  The exact-height multiplier is a difference of two cumulative ones
   (`Tex_eq_Tle_sub_of_bounded`), and the extra clipping at `bandCond` is a tail condition in `n`
   (`variationalNorm_clip_of_tail`), costing a factor `2`.
5. The `t`-integration is the pointwise Minkowski inequality `varNorm_integral_le` followed by
   `eLpNorm_lintegral_le` (the interval `(1/2,1]` has measure `≤ 1`).

The degree hypothesis `2 ≤ P.natDegree` and the low-case hypothesis `k₁ = 0 ∨ k₂ = 0` are not
used: at bounded height the slice-kernel/lacunary-variational route applies to all quadruples and
all polynomials.  The statement is proved as given, with those hypotheses present but unused.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.BoundedHMain.Defs
import Submission.Work.KMTAreas.A7.RepAux
import Submission.Work.KMTPlan.A6.LowModApproxBoundedH.allRhoBase
import Submission.Work.KMTPlan.A6.LowModApproxBoundedH.sliceFBound
import Submission.Work.KMTPlan.A6.LowModApproxBoundedH.iwArithFreqs_mono_all
import Submission.Work.Analysis.Variational.SliceKernelL1
import Submission.Work.KMTPlan.A6.MdlSliceCoreGainBig
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 32000000
set_option linter.unusedVariables false

namespace Work.KMTPlan.A6.LowModApproxBoundedH

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.KMTAreas.A7
open Work.Analysis.IonescuWainger Work.Analysis.EndVar

/-! ## Bounded-height cardinality of the arithmetic frequency sets -/

/-- A constant dominating `#(ℚ/ℤ)_{≤ l}` for every `l ≤ B`. -/
private def cardMax (ρ : ℝ) (B : ℕ) : ℕ :=
  (Finset.range (B + 1)).sup (fun l => (iwArithFreqs ρ l).card)

private theorem cardMax_le (ρ : ℝ) (B : ℕ) {l : ℕ} (hl : l ≤ B) :
    (iwArithFreqs ρ l).card ≤ cardMax ρ B :=
  Finset.le_sup (f := fun l => (iwArithFreqs ρ l).card)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hl))

private theorem cardNew_le (ρ : ℝ) (B : ℕ) {l : ℕ} (hl : l ≤ B) :
    (iwArithFreqsNew ρ l).card ≤ cardMax ρ B := by
  refine le_trans (Finset.card_le_card ?_) (cardMax_le ρ B hl)
  rw [iwArithFreqsNew]
  exact Finset.sdiff_subset

/-! ## Monotonicity of the loss weight at bounded height -/

private theorem lmaxR_eq_lcL (l₁ l₂ k₁ k₂ : ℕ) :
    lmaxR l₁ l₂ k₁ k₂ = (lcL l₁ l₂ k₁ k₂ : ℝ) := by
  rw [lmaxR, ← Work.KMTPlan.A6.lcL_eq]
  push_cast
  ring

/-- The scale `lmaxR` is monotone in its four indices. -/
private theorem lmaxR_mono {l₁ l₂ k₁ k₂ B : ℕ} (h1 : l₁ ≤ B) (h2 : l₂ ≤ B) (h3 : k₁ ≤ B)
    (h4 : k₂ ≤ B) : lmaxR l₁ l₂ k₁ k₂ ≤ lmaxR B B B B := by
  rw [lmaxR_eq_lcL, lmaxR_eq_lcL, show lcL B B B B = B from by simp [lcL]]
  exact_mod_cast (max_le (max_le h1 h2) (max_le h3 h4))

/-- **The loss weight at bounded height is a constant.** -/
private theorem lossWeight_mono (ρ : ℝ) (hρ : 0 ≤ ρ) (B : ℕ) {l₁ l₂ k₁ k₂ : ℕ}
    (h1 : l₁ ≤ B) (h2 : l₂ ≤ B) (h3 : k₁ ≤ B) (h4 : k₂ ≤ B) :
    lossWeight 4 ρ l₁ l₂ k₁ k₂ ≤ lossWeight 4 ρ B B B B := by
  have hL := lmaxR_mono h1 h2 h3 h4
  have hL0 : (0 : ℝ) ≤ lmaxR l₁ l₂ k₁ k₂ := by
    rw [lmaxR_eq_lcL]
    exact_mod_cast Nat.zero_le _
  rw [lossWeight, lossWeight]
  refine mul_le_mul ?_ ?_ ?_ ?_
  · exact Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
  · refine Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ?_
    exact mul_le_mul_of_nonneg_left hL (mul_nonneg (by norm_num) hρ)
  · positivity
  · exact Real.rpow_nonneg (by linarith) _

/-! ## The `ℓ¹(ℤ²)` mass of the repaired model kernel at bounded height -/

private theorem exactKernelMass (ρ : ℝ) (P : Polynomial ℤ) (B : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (l₁ l₂ k₁ k₂ : ℕ), lcL l₁ l₂ k₁ k₂ ≤ B →
      (Summable fun p : ℤ × ℤ => ‖arithKernelExact ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ p.1 p.2
          * cw (mStarF (uRep ρ l₁ l₂ k₁ k₂)) p.1
          * cw (mStargF P.natDegree (uRep ρ l₁ l₂ k₁ k₂)) p.2‖)
      ∧ (∑' p : ℤ × ℤ, ‖arithKernelExact ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ p.1 p.2
          * cw (mStarF (uRep ρ l₁ l₂ k₁ k₂)) p.1
          * cw (mStargF P.natDegree (uRep ρ l₁ l₂ k₁ k₂)) p.2‖)
        ≤ C := by
  obtain ⟨Cs, hCs0, hCs⟩ := Work.KMTPlan.A6.vpc_exists_cw_mStarF_tsum_le
  refine ⟨max 1 (((cardMax ρ B : ℕ) : ℝ) ^ 2 * Cs * Cs),
    lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro l₁ l₂ k₁ k₂ hLB
  have hl₁ : l₁ ≤ B := le_trans (le_trans (le_max_left l₁ l₂) (le_max_left _ _)) hLB
  have hl₂ : l₂ ≤ B := le_trans (le_trans (le_max_right l₁ l₂) (le_max_left _ _)) hLB
  have hc₁ : (((iwArithFreqsNew ρ l₁).card : ℕ) : ℝ) ≤ ((cardMax ρ B : ℕ) : ℝ) := by
    exact_mod_cast cardNew_le ρ B hl₁
  have hc₂ : (((iwArithFreqsNew ρ l₂).card : ℕ) : ℝ) ≤ ((cardMax ρ B : ℕ) : ℝ) := by
    exact_mod_cast cardNew_le ρ B hl₂
  rw [mStargF_eq_mStarF P (uRep ρ l₁ l₂ k₁ k₂)]
  have hsum₁ : Summable (fun j : ℤ => ‖cw (mStarF (uRep ρ l₁ l₂ k₁ k₂)) j‖) :=
    (hCs (uRep ρ l₁ l₂ k₁ k₂)).1
  have hb₁ : (∑' j : ℤ, ‖cw (mStarF (uRep ρ l₁ l₂ k₁ k₂)) j‖) ≤ Cs :=
    (hCs (uRep ρ l₁ l₂ k₁ k₂)).2
  have hsum₂ : Summable
      (fun j : ℤ => ‖cw (mStarF (P.natDegree * uRep ρ l₁ l₂ k₁ k₂)) j‖) :=
    (hCs (P.natDegree * uRep ρ l₁ l₂ k₁ k₂)).1
  have hb₂ : (∑' j : ℤ, ‖cw (mStarF (P.natDegree * uRep ρ l₁ l₂ k₁ k₂)) j‖) ≤ Cs :=
    (hCs (P.natDegree * uRep ρ l₁ l₂ k₁ k₂)).2
  have hprod : Summable (fun p : ℤ × ℤ =>
      ‖cw (mStarF (uRep ρ l₁ l₂ k₁ k₂)) p.1‖
        * ‖cw (mStarF (P.natDegree * uRep ρ l₁ l₂ k₁ k₂)) p.2‖) :=
    hsum₁.mul_of_nonneg hsum₂ (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hle : ∀ p : ℤ × ℤ,
      ‖arithKernelExact ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ p.1 p.2
          * cw (mStarF (uRep ρ l₁ l₂ k₁ k₂)) p.1
          * cw (mStarF (P.natDegree * uRep ρ l₁ l₂ k₁ k₂)) p.2‖
        ≤ (((iwArithFreqsNew ρ l₁).card : ℝ) * ((iwArithFreqsNew ρ l₂).card : ℝ))
            * (‖cw (mStarF (uRep ρ l₁ l₂ k₁ k₂)) p.1‖
                * ‖cw (mStarF (P.natDegree * uRep ρ l₁ l₂ k₁ k₂)) p.2‖) := by
    intro p
    rw [norm_mul, norm_mul]
    have hk : ‖arithKernelExact ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ p.1 p.2‖
        ≤ ((iwArithFreqsNew ρ l₁).card : ℝ) * ((iwArithFreqsNew ρ l₂).card : ℝ) := by
      rw [← arithKernelSet_iwArithFreqsNew ρ P _ l₁ l₂]
      exact norm_arithKernelSet_le P _ _ _ p.1 p.2
    calc ‖arithKernelExact ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ p.1 p.2‖
          * ‖cw (mStarF (uRep ρ l₁ l₂ k₁ k₂)) p.1‖
          * ‖cw (mStarF (P.natDegree * uRep ρ l₁ l₂ k₁ k₂)) p.2‖
        ≤ (((iwArithFreqsNew ρ l₁).card : ℝ) * ((iwArithFreqsNew ρ l₂).card : ℝ))
            * ‖cw (mStarF (uRep ρ l₁ l₂ k₁ k₂)) p.1‖
            * ‖cw (mStarF (P.natDegree * uRep ρ l₁ l₂ k₁ k₂)) p.2‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hk (norm_nonneg _))
            (norm_nonneg _)
      _ = (((iwArithFreqsNew ρ l₁).card : ℝ) * ((iwArithFreqsNew ρ l₂).card : ℝ))
            * (‖cw (mStarF (uRep ρ l₁ l₂ k₁ k₂)) p.1‖
                * ‖cw (mStarF (P.natDegree * uRep ρ l₁ l₂ k₁ k₂)) p.2‖) := by ring
  have hsumm : Summable (fun p : ℤ × ℤ =>
      ‖arithKernelExact ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ p.1 p.2
        * cw (mStarF (uRep ρ l₁ l₂ k₁ k₂)) p.1
        * cw (mStarF (P.natDegree * uRep ρ l₁ l₂ k₁ k₂)) p.2‖) :=
    Summable.of_nonneg_of_le (fun p => norm_nonneg _) hle (hprod.mul_left _)
  have hmaj : Summable (fun p : ℤ × ℤ =>
      (((iwArithFreqsNew ρ l₁).card : ℝ) * ((iwArithFreqsNew ρ l₂).card : ℝ))
        * (‖cw (mStarF (uRep ρ l₁ l₂ k₁ k₂)) p.1‖
            * ‖cw (mStarF (P.natDegree * uRep ρ l₁ l₂ k₁ k₂)) p.2‖)) := hprod.mul_left _
  have hmain : (∑' p : ℤ × ℤ,
        ‖arithKernelExact ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ p.1 p.2
          * cw (mStarF (uRep ρ l₁ l₂ k₁ k₂)) p.1
          * cw (mStarF (P.natDegree * uRep ρ l₁ l₂ k₁ k₂)) p.2‖)
      ≤ (((iwArithFreqsNew ρ l₁).card : ℝ) * ((iwArithFreqsNew ρ l₂).card : ℝ))
          * ((∑' j : ℤ, ‖cw (mStarF (uRep ρ l₁ l₂ k₁ k₂)) j‖)
              * (∑' j : ℤ, ‖cw (mStarF (P.natDegree * uRep ρ l₁ l₂ k₁ k₂)) j‖)) := by
    have h := hsumm.tsum_le_tsum hle hmaj
    rw [tsum_mul_left, (Summable.tsum_mul_tsum hsum₁ hsum₂ hprod).symm] at h
    exact h
  refine ⟨?_, ?_⟩
  · exact hsumm
  · calc (∑' p : ℤ × ℤ,
          ‖arithKernelExact ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ p.1 p.2
            * cw (mStarF (uRep ρ l₁ l₂ k₁ k₂)) p.1
            * cw (mStarF (P.natDegree * uRep ρ l₁ l₂ k₁ k₂)) p.2‖)
        ≤ (((iwArithFreqsNew ρ l₁).card : ℝ) * ((iwArithFreqsNew ρ l₂).card : ℝ))
            * ((∑' j : ℤ, ‖cw (mStarF (uRep ρ l₁ l₂ k₁ k₂)) j‖)
                * (∑' j : ℤ, ‖cw (mStarF (P.natDegree * uRep ρ l₁ l₂ k₁ k₂)) j‖)) :=
          hmain
      _ ≤ (((iwArithFreqsNew ρ l₁).card : ℝ) * ((iwArithFreqsNew ρ l₂).card : ℝ))
            * (Cs * Cs) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul hb₁ hb₂ (tsum_nonneg (fun j => norm_nonneg _)) hCs0.le
      _ = (((iwArithFreqsNew ρ l₁).card : ℝ) * ((iwArithFreqsNew ρ l₂).card : ℝ))
            * Cs * Cs := by ring
      _ ≤ ((cardMax ρ B : ℕ) : ℝ) ^ 2 * Cs * Cs := by
          have h1 : (((iwArithFreqsNew ρ l₁).card : ℝ) * ((iwArithFreqsNew ρ l₂).card : ℝ))
              ≤ ((cardMax ρ B : ℕ) : ℝ) * ((cardMax ρ B : ℕ) : ℝ) :=
            mul_le_mul hc₁ hc₂ (Nat.cast_nonneg _) (le_trans (Nat.cast_nonneg _) hc₁)
          have h3 : (((iwArithFreqsNew ρ l₁).card : ℝ) * ((iwArithFreqsNew ρ l₂).card : ℝ))
                * Cs * Cs
              ≤ ((cardMax ρ B : ℕ) : ℝ) * ((cardMax ρ B : ℕ) : ℝ) * Cs * Cs :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hCs0.le) hCs0.le
          have h4 : ((cardMax ρ B : ℕ) : ℝ) * ((cardMax ρ B : ℕ) : ℝ) * Cs * Cs
              = ((cardMax ρ B : ℕ) : ℝ) ^ 2 * Cs * Cs := by ring
          exact h3.trans (le_of_eq h4)
      _ ≤ max 1 (((cardMax ρ B : ℕ) : ℝ) ^ 2 * Cs * Cs) := le_max_right _ _

/-! ## Toolbox: the slice-kernel bound and the height lift -/

/-- **The `ℓ¹(ℤ)`-slice-kernel bound for the variational norm** (the cleaned form of the bound of
`Work.Analysis.Variational.SliceKernelL1`, with the unused finiteness hypotheses removed). -/
private theorem sliceKernelL1 (r : NNReal) (hr : 1 ≤ r) (c : ℤ → ℤ → ℂ) (h k : ℕ → ℤ → ℂ) :
    MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => ∑' i : ℤ, ∑' j : ℤ, c i j * h n (x - i) * k n (x - j)))
      1 MeasureTheory.Measure.count
      ≤ 2 * (∑' p : ℤ × ℤ, ‖c p.1 p.2‖ₑ) *
          MeasureTheory.eLpNorm (fun y : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => h n y)) 2 MeasureTheory.Measure.count *
          MeasureTheory.eLpNorm (fun y : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => k n y)) 2 MeasureTheory.Measure.count := by
  set H : ℤ → ℝ≥0∞ := fun y => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => h n y)
    with hH
  set K : ℤ → ℝ≥0∞ := fun y => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => k n y)
    with hK
  have hpt : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => ∑' i : ℤ, ∑' j : ℤ, c i j * h n (x - i) * k n (x - j))
      ≤ ∑' p : ℤ × ℤ, ‖c p.1 p.2‖ₑ * (H (x - p.1) * K (x - p.2)) :=
    fun x => Work.Analysis.Variational.variationalNorm_bilinear_slice_le hr c h k x
  have h1 : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => ∑' i : ℤ, ∑' j : ℤ, c i j * h n (x - i) * k n (x - j)))
      1 MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (fun x : ℤ => ∑' p : ℤ × ℤ,
            ‖c p.1 p.2‖ₑ * (H (x - p.1) * K (x - p.2))) 1 MeasureTheory.Measure.count :=
    MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) fun x => by simpa only [enorm_eq_self] using hpt x
  have h2 : MeasureTheory.eLpNorm (fun x : ℤ => ∑' p : ℤ × ℤ,
          ‖c p.1 p.2‖ₑ * (H (x - p.1) * K (x - p.2))) 1 MeasureTheory.Measure.count
      ≤ (∑' p : ℤ × ℤ, ‖c p.1 p.2‖ₑ) * MeasureTheory.eLpNorm H 2 MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm K 2 MeasureTheory.Measure.count :=
    Work.Analysis.Variational.eLpNorm_slice_kernel_le (fun p : ℤ × ℤ => ‖c p.1 p.2‖ₑ) H K
  have h3 : (∑' p : ℤ × ℤ, ‖c p.1 p.2‖ₑ) * MeasureTheory.eLpNorm H 2 MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm K 2 MeasureTheory.Measure.count
      ≤ 2 * (∑' p : ℤ × ℤ, ‖c p.1 p.2‖ₑ)
          * MeasureTheory.eLpNorm H 2 MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm K 2 MeasureTheory.Measure.count := by
    have hS : (∑' p : ℤ × ℤ, ‖c p.1 p.2‖ₑ) ≤ 2 * (∑' p : ℤ × ℤ, ‖c p.1 p.2‖ₑ) := by
      simpa only [one_mul] using mul_le_mul' (show (1 : ℝ≥0∞) ≤ 2 by norm_num)
        (le_refl (∑' p : ℤ × ℤ, ‖c p.1 p.2‖ₑ))
    exact mul_le_mul' (mul_le_mul' hS le_rfl) le_rfl
  exact (h1.trans h2).trans (by simpa only [hH, hK] using h3)

/-- `‖z‖ₑ = ofReal ‖z‖` for a complex number. -/
private theorem enorm_ofReal_norm (z : ℂ) : ‖z‖ₑ = ENNReal.ofReal ‖z‖ := by
  rw [enorm_eq_nnnorm, ← ENNReal.ofReal_coe_nnreal]
  rfl

/-- Modulating a sequence by a character does not change its `ℓᵖ`-norm under counting measure. -/
private theorem eLpNorm_fourier_mul (α : Work.Analysis.IonescuWainger.Circle) (F : ℤ → ℂ)
    (p : ENNReal) :
    MeasureTheory.eLpNorm (fun y : ℤ => fourier (T := 1) y α * F y) p MeasureTheory.Measure.count
      = MeasureTheory.eLpNorm F p MeasureTheory.Measure.count := by
  have h1 : ∀ y : ℤ, ‖fourier (T := 1) y α‖ₑ = 1 := fun y => by
    rw [enorm_ofReal_norm, norm_fourier_apply_, ENNReal.ofReal_one]
  refine le_antisymm ?_ ?_
  · refine MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) (fun y => ?_)
    rw [enorm_mul, h1 y, one_mul]
  · refine MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) (fun y => ?_)
    rw [enorm_mul, h1 y, one_mul]

/-- **The `ℓᵖ` variational bound at height `≤ l` from the height-`0` bound** (the `eLpNorm` form of
the lift `Lift.variationalNorm_Tle_le_sum`: the cumulative multiplier `Tle ρ l` is a finite sum of
at most `#(ℚ/ℤ)_{≤l}` modulated height-`0` multipliers). -/
private theorem eLpNorm_Tle_le_sum (ρ : ℝ) (l : ℕ) {ψ : ℕ → ℝ → ℂ}
    (hψ : ∀ n, MeasureTheory.Integrable (ψ n))
    (hψcw : ∀ n, Summable fun j : ℤ => ‖Work.KMTAreas.A7.cw (ψ n) j‖)
    (c : ℕ → Prop) [DecidablePred c] (r : NNReal) (hr : 1 ≤ r)
    (p : ENNReal) (hp : 1 ≤ p) (hpt : p ≠ ⊤) {K : ENNReal}
    (h0 : ∀ F : ℤ → ℂ, MeasureTheory.eLpNorm (fun x : ℤ =>
        PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => if c n then Work.KMTAreas.A7.Tle ρ 0 (ψ n) F x else 0))
        p MeasureTheory.Measure.count
      ≤ K * MeasureTheory.eLpNorm F p MeasureTheory.Measure.count)
    (F : ℤ → ℂ) {CF : ℝ} (hbdd : ∀ y : ℤ, ‖F y‖ ≤ CF) :
    MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => if c n then Work.KMTAreas.A7.Tle ρ l (ψ n) F x else 0))
      p MeasureTheory.Measure.count
    ≤ (∑ _α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l, K)
        * MeasureTheory.eLpNorm F p MeasureTheory.Measure.count := by
  classical
  have hp0 : p ≠ 0 := by
    intro h
    rw [h] at hp
    exact absurd hp (by norm_num)
  have hpt_bound : ∀ x : ℤ,
      PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => if c n then Work.KMTAreas.A7.Tle ρ l (ψ n) F x else 0)
      ≤ ∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l,
          PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => if c n then
              Work.KMTAreas.A7.Tle ρ 0 (ψ n) (fun y : ℤ => fourier (T := 1) y α * F y) x
              else 0) :=
    fun x => Work.KMTPlan.A6.LowModApproxBoundedH.Lift.variationalNorm_Tle_le_sum ρ l hψ hψcw F
      CF hbdd c r hr x
  -- NOTE (2026-10-02): qualify the `A7` monotonicity lemma explicitly.  This file sits in the
  -- namespace `Work.KMTPlan.A6` (and imports an `A6` module), so the unqualified
  -- `eLpNorm_mono_ennreal` resolves to `Work.KMTPlan.A6.eLpNorm_mono_ennreal` (`A6/FkrAux.lean`),
  -- whose first explicit argument is `p ≠ ⊤`, instead of the `A7` one (`A7/lacDilTriVar.lean`)
  -- that the argument list below is written for.
  have hstep1 := Work.KMTAreas.A7.eLpNorm_mono_ennreal
    (μ := MeasureTheory.Measure.count) hpt_bound hp0 hpt
  have hstep2 := eLpNorm_finset_sum_le_ennreal
    (μ := MeasureTheory.Measure.count)
    (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
    (fun α x => PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => if c n then Work.KMTAreas.A7.Tle ρ 0 (ψ n)
        (fun y : ℤ => fourier (T := 1) y α * F y) x else 0)) hp hpt
  have hstep3 : (∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l,
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => if c n then Work.KMTAreas.A7.Tle ρ 0 (ψ n)
            (fun y : ℤ => fourier (T := 1) y α * F y) x else 0))
        p MeasureTheory.Measure.count)
      ≤ ∑ _α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l,
          K * MeasureTheory.eLpNorm F p MeasureTheory.Measure.count :=
    Finset.sum_le_sum (fun α _hα =>
      (h0 (fun y : ℤ => fourier (T := 1) y α * F y)).trans
        (le_of_eq (by rw [eLpNorm_fourier_mul])))
  exact hstep1.trans (hstep2.trans (hstep3.trans (Finset.sum_mul _ _ _).symm.le))

/-! ## The exact-height multiplier as a difference of two cumulative ones (all `ρ > 0`) -/

/-- **`Tex = Tle l - Tle (l-1)` for every `ρ > 0` with nested frequency sets.**  The proof is that
of `Work.KMTAreas.A7.Tex_eq_Tle_sub_of_bounded`, with the inclusion
`(ℚ/ℤ)_{≤l-1} ⊆ (ℚ/ℤ)_{≤l}` supplied by the hypothesis `hmono` (which holds for every `ρ > 0` by
`iwArithFreqs_mono_all`, unlike the paper's `ρ ≤ 1` version). -/
theorem Tex_eq_Tle_sub_all (ρ : ℝ)
    (hmono : ∀ l l' : ℕ, l ≤ l' → iwArithFreqs ρ l ⊆ iwArithFreqs ρ l')
    {l : ℕ} (_hl : 1 ≤ l)
    {φ : ℝ → ℂ} (hAdm : Adm (iwArithFreqs ρ l) φ) (hAdm' : Adm (iwArithFreqs ρ (l - 1)) φ)
    {f : ℤ → ℂ} {Bnd : ℝ} (hf : ∀ m : ℤ, ‖f m‖ ≤ Bnd) :
    Tex ρ l φ f = Tle ρ l φ f - Tle ρ (l - 1) φ f := by
  have hsub : iwArithFreqs ρ (l - 1) ⊆ iwArithFreqs ρ l := hmono (l - 1) l (Nat.pred_le l)
  have hmain := iwConv_sdiff_of_bounded hsub hAdm.2.1 hAdm'.2.1 hf hAdm.2.2 hAdm'.2.2
  simpa only [Tex, Tle, iwArithFreqsNew] using hmain

/-! ## The target -/

theorem modelPieceBoundAllRho_of_mono (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (r : NNReal)
    (hr : 2 < r) (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (ρ : ℝ) (hρ : 0 < ρ)
    (hmono : ∀ l l' : ℕ, l ≤ l' → iwArithFreqs ρ l ⊆ iwArithFreqs ρ l') (B : ℕ) :
    Work.KMTPlan.A6.ModelPieceBound P r C₀ ρ B := by
  classical
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num) (le_of_lt hr)
  have hhalf : ((1 : ℝ) / 2) ≤ 1 := by norm_num
  obtain ⟨Ck, hCkpos, hCk⟩ := exactKernelMass ρ P B
  -- the level-`0` `g`-side estimate, for every `ρ > 0` (bounded height)
  obtain ⟨Klv0, hKlv0⟩ := Lvl0_all P hd r hr C₀ hC₀ B ρ hρ
  -- the level-`0` `f`-side estimate, for every `ρ > 0` (bounded height)
  obtain ⟨Klev0F, hKlev0F⟩ := lev0CoreClip_aux r hr C₀ hC₀ ρ hρ B
  -- the level-`0` `f`-side estimate, as a constant for every `Λ`
  have hCloAll : ∀ Λ : NNReal, ∃ c : ℝ, 0 < c ∧
      (1 < Λ → ∀ (a : ℕ → NNReal) (ha : PointwiseErgodicTheorems.Lacunary Λ a)
        (ha1 : ∀ n, 1 ≤ a n) (l₁ l₂ k₁ k₂ : ℕ) (hLB' : lcL l₁ l₂ k₁ k₂ ≤ B) (t : ℝ)
        (ht : t ∈ Set.Icc (1 / 2 : ℝ) 1) (f : ℤ → ℂ),
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => if core ρ C₀ l₁ l₂ k₁ k₂ a n
              then Tle ρ 0 (varphiNt (Nat.floor (a n)) k₁ t) f x else 0))
          2 MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (c * lossWeight 4 ρ l₁ l₂ k₁ k₂)
              * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count) := by
    intro Λ
    refine ⟨(Klev0F Λ : ℝ) + 1, by positivity, fun hΛ => ?_⟩
    intro a ha ha1 l₁ l₂ k₁ k₂ hLB' t ht f
    have hexp : (0 : ℝ) ≤ 4 * ρ * lmaxR l₁ l₂ k₁ k₂ :=
      mul_nonneg (mul_nonneg (by norm_num) hρ.le) (lmaxR_nonneg l₁ l₂ k₁ k₂)
    have hL1 : (1 : ℝ) ≤ lossWeight 4 ρ l₁ l₂ k₁ k₂ := by
      rw [lossWeight]
      refine one_le_mul_of_one_le_of_one_le ?_ ?_
      · exact Real.one_le_rpow (by linarith [lmaxR_nonneg l₁ l₂ k₁ k₂]) (by norm_num)
      · exact Real.one_le_rpow (by norm_num) hexp
    have hcf : (Klev0F Λ : ENNReal) ≤ ENNReal.ofReal ((Klev0F Λ : ℝ) + 1) := by
      rw [ENNReal.ofReal_add (by positivity) (by norm_num), ENNReal.ofReal_coe_nnreal]
      exact le_add_right le_rfl
    have hmul : ENNReal.ofReal ((Klev0F Λ : ℝ) + 1)
        ≤ ENNReal.ofReal (((Klev0F Λ : ℝ) + 1) * lossWeight 4 ρ l₁ l₂ k₁ k₂) := by
      rw [ENNReal.ofReal_mul (by positivity)]
      exact le_mul_of_one_le_right (by positivity)
        (ENNReal.ofReal_one ▸ ENNReal.ofReal_le_ofReal hL1)
    exact (hKlev0F a Λ l₁ l₂ k₁ k₂ t f hΛ ha ha1 hLB' ht).trans
      (le_trans (mul_le_mul' (hcf.trans hmul) le_rfl) le_rfl)
  choose Clo hClopos hClo using hCloAll
  -- the constants of the estimate
  let Qc : ENNReal := ((cardMax ρ B : ℕ) : ENNReal)
  let K0 : NNReal → ENNReal := fun Λ => ENNReal.ofReal (Clo Λ * lossWeight 4 ρ B B B B)
  let Kf : NNReal → ENNReal := fun Λ => 4 * Qc * K0 Λ
  let Kg : NNReal → ENNReal := fun Λ => 4 * Qc * (Klv0 Λ : ENNReal)
  let Kc : NNReal → ENNReal := fun Λ => 2 * ENNReal.ofReal Ck * Kf Λ * Kg Λ
  have hQcv : Qc = ((cardMax ρ B : ℕ) : ENNReal) := rfl
  have hK0v : ∀ Λ : NNReal, K0 Λ = ENNReal.ofReal (Clo Λ * lossWeight 4 ρ B B B B) :=
    fun _ => rfl
  have hKfv : ∀ Λ : NNReal, Kf Λ = 4 * Qc * K0 Λ := fun _ => rfl
  have hKgv : ∀ Λ : NNReal, Kg Λ = 4 * Qc * (Klv0 Λ : ENNReal) := fun _ => rfl
  have hKcv : ∀ Λ : NNReal, Kc Λ = 2 * ENNReal.ofReal Ck * Kf Λ * Kg Λ := fun _ => rfl
  have hQcne : Qc ≠ ⊤ := by rw [hQcv]; exact ENNReal.coe_ne_top
  have hK0ne : ∀ Λ : NNReal, K0 Λ ≠ ⊤ := fun Λ => by
    rw [hK0v Λ]
    exact ENNReal.ofReal_ne_top
  have hKfne : ∀ Λ : NNReal, Kf Λ ≠ ⊤ := fun Λ => by
    rw [hKfv Λ]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.coe_ne_top (r := 4)) hQcne)
      (hK0ne Λ)
  have hKgne : ∀ Λ : NNReal, Kg Λ ≠ ⊤ := fun Λ => by
    rw [hKgv Λ]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.coe_ne_top (r := 4)) hQcne)
      ENNReal.coe_ne_top
  have hKcne : ∀ Λ : NNReal, Kc Λ ≠ ⊤ := fun Λ => by
    rw [hKcv Λ]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.coe_ne_top (r := 2)) ENNReal.ofReal_ne_top) (hKfne Λ)) (hKgne Λ)
  refine ⟨fun Λ => ENNReal.toNNReal (Kc Λ) + 1, ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hLB hQlow
  have hKcle : Kc Λ ≤ ((ENNReal.toNNReal (Kc Λ) + 1 : NNReal) : ENNReal) := by
    rw [ENNReal.coe_add, ENNReal.coe_one, ← ENNReal.coe_toNNReal (hKcne Λ)]
    exact le_add_right le_rfl
  have hKne : ((ENNReal.toNNReal (Kc Λ) + 1 : NNReal) : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr (by positivity)
  by_cases hf0 : MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count = 0
  · rw [Work.KMTPlan.A6.eq_zero_of_eLpNorm_two_eq_zero hf0]
    have hzero : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Work.KMTAreas.A7.modelTupleRep ρ P C₀ a 0 g l₁ l₂ k₁ k₂ n x)) = 0 := by
      funext x
      have hfun : (fun n : ℕ => Work.KMTAreas.A7.modelTupleRep ρ P C₀ a 0 g l₁ l₂ k₁ k₂ n x)
          = 0 := by
        funext n
        exact repModelTupleRep_zero_left ρ P C₀ a g l₁ l₂ k₁ k₂ n x
      rw [hfun]
      simp only [Work.KMTAreas.A7.variationalNorm_zero r hr1, Pi.zero_apply]
    rw [hzero, MeasureTheory.eLpNorm_zero]
    exact bot_le
  by_cases hg0 : MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count = 0
  · rw [Work.KMTPlan.A6.eq_zero_of_eLpNorm_two_eq_zero hg0]
    have hzero : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Work.KMTAreas.A7.modelTupleRep ρ P C₀ a f 0 l₁ l₂ k₁ k₂ n x)) = 0 := by
      funext x
      have hfun : (fun n : ℕ => Work.KMTAreas.A7.modelTupleRep ρ P C₀ a f 0 l₁ l₂ k₁ k₂ n x)
          = 0 := by
        funext n
        exact repModelTupleRep_zero_right ρ P C₀ a f l₁ l₂ k₁ k₂ n x
      rw [hfun]
      simp only [Work.KMTAreas.A7.variationalNorm_zero r hr1, Pi.zero_apply]
    rw [hzero, MeasureTheory.eLpNorm_zero]
    exact bot_le
  by_cases hfT : MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count = ⊤
  · rw [hfT, ENNReal.mul_top hKne, ENNReal.top_mul hg0]
    exact le_top
  by_cases hgT : MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count = ⊤
  · rw [hgT, ENNReal.mul_top (mul_ne_zero hKne hf0)]
    exact le_top
  obtain ⟨Cf, hfbd⟩ := eLpNorm_finite_bounded 2 (by norm_num) f (lt_top_iff_ne_top.mpr hfT)
  obtain ⟨Cg, hgbd⟩ := eLpNorm_finite_bounded 2 (by norm_num) g (lt_top_iff_ne_top.mpr hgT)
  -- the four indices are bounded by `B`
  have hl₁B : l₁ ≤ B := by
    simp only [Work.KMTPlan.A6.lcL] at hLB; omega
  have hl₂B : l₂ ≤ B := by
    simp only [Work.KMTPlan.A6.lcL] at hLB; omega
  have hk₁B : k₁ ≤ B := by
    simp only [Work.KMTPlan.A6.lcL] at hLB; omega
  have hk₂B : k₂ ≤ B := by
    simp only [Work.KMTPlan.A6.lcL] at hLB; omega
  have hcard₁ : ((iwArithFreqs ρ l₁).card : ENNReal) ≤ Qc := by
    rw [hQcv]; exact_mod_cast cardMax_le ρ B hl₁B
  have hcard₂ : ((iwArithFreqs ρ l₂).card : ENNReal) ≤ Qc := by
    rw [hQcv]; exact_mod_cast cardMax_le ρ B hl₂B
  have hcard₁' : ((iwArithFreqs ρ (l₁ - 1)).card : ENNReal) ≤ Qc := by
    rw [hQcv]; exact_mod_cast cardMax_le ρ B (le_trans (Nat.sub_le _ _) hl₁B)
  have hcard₂' : ((iwArithFreqs ρ (l₂ - 1)).card : ENNReal) ≤ Qc := by
    rw [hQcv]; exact_mod_cast cardMax_le ρ B (le_trans (Nat.sub_le _ _) hl₂B)
  -- the band condition is a tail in `n`
  have hbandtail : ∀ n m : ℕ, n ≤ m → bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n)) →
      bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a m)) := by
    intro n m hnm hn
    have hmono : Monotone (fun n : ℕ => Nat.floor (a n)) := by
      refine monotone_nat_of_le_succ (fun n => ?_)
      have hdiv := ha n
      have ha0 : (0 : NNReal) < a n := lt_of_lt_of_le one_pos (ha1 n)
      have hlt : a n < a (n + 1) := by
        have hmul : Λ * a n < a (n + 1) := by
          have h := mul_lt_mul_of_pos_right hdiv ha0
          rwa [div_mul_cancel₀ _ (ne_of_gt ha0)] at h
        have hle' : a n ≤ Λ * a n := by
          nth_rewrite 1 [← one_mul (a n)]
          exact mul_le_mul_of_nonneg_right (le_of_lt hΛ) (zero_le : (0 : NNReal) ≤ a n)
        exact lt_of_le_of_lt hle' hmul
      exact Nat.floor_mono (le_of_lt hlt)
    have hlog := Work.Analysis.EndVar.logN_mono (hmono hnm)
    exact ⟨le_trans hn.1 (Int.toNat_le_toNat hlog), le_trans hn.2 (Int.toNat_le_toNat hlog)⟩
  -- boundedness and measurability in `t`
  have hboundF : ∀ n : ℕ, ∃ C : ℝ, ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ y : ℤ,
      ‖HclRep ρ C₀ a l₁ l₂ k₁ k₂ t f n y‖ ≤ C := by
    intro n
    obtain ⟨⟨hbn, hbn'⟩, _⟩ := iwConv_varphiNt_bounded_measurable (iwArithFreqsNew ρ l₁)
      (Nat.floor (a n)) k₁ f Cf hfbd
    refine ⟨max hbn 0, fun t ht y => ?_⟩
    by_cases hc : core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n))
    · rw [HclRep_apply_of hc]
      exact le_trans (hbn' t ht y) (le_max_left _ _)
    · simp only [HclRep, if_neg hc, Pi.zero_apply, norm_zero]
      exact le_max_right _ _
  have hboundG : ∀ n : ℕ, ∃ C : ℝ, ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ y : ℤ,
      ‖GclRep ρ P C₀ a l₁ l₂ k₁ k₂ t g n y‖ ≤ C := by
    intro n
    obtain ⟨⟨hbn, hbn'⟩, _⟩ := iwConv_varphitildeNt_bounded_measurable P (iwArithFreqsNew ρ l₂)
      (Nat.floor (a n)) k₂ g Cg hgbd
    refine ⟨max hbn 0, fun t ht y => ?_⟩
    by_cases hc : core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n))
    · rw [GclRep_apply_of hc]
      exact le_trans (hbn' t ht y) (le_max_left _ _)
    · simp only [GclRep, if_neg hc, Pi.zero_apply, norm_zero]
      exact le_max_right _ _
  have hmeasF : ∀ n : ℕ, ∀ y : ℤ,
      Measurable (fun t : ℝ => HclRep ρ C₀ a l₁ l₂ k₁ k₂ t f n y) := by
    intro n y
    by_cases hc : core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n))
    · have hfun : (fun t : ℝ => HclRep ρ C₀ a l₁ l₂ k₁ k₂ t f n y)
          = fun t : ℝ => Tex ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t) f y := by
        funext t; exact congrFun (HclRep_apply_of hc) y
      rw [hfun]
      exact (iwConv_varphiNt_bounded_measurable (iwArithFreqsNew ρ l₁)
        (Nat.floor (a n)) k₁ f Cf hfbd).2 y
    · have hfun : (fun t : ℝ => HclRep ρ C₀ a l₁ l₂ k₁ k₂ t f n y) = fun _ : ℝ => 0 := by
        funext t
        simp only [HclRep, hc, if_false, Pi.zero_apply]
      rw [hfun]; exact measurable_const
  have hmeasG : ∀ n : ℕ, ∀ y : ℤ,
      Measurable (fun t : ℝ => GclRep ρ P C₀ a l₁ l₂ k₁ k₂ t g n y) := by
    intro n y
    by_cases hc : core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n))
    · have hfun : (fun t : ℝ => GclRep ρ P C₀ a l₁ l₂ k₁ k₂ t g n y)
          = fun t : ℝ => Tex ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g y := by
        funext t; exact congrFun (GclRep_apply_of hc) y
      rw [hfun]
      exact (iwConv_varphitildeNt_bounded_measurable P (iwArithFreqsNew ρ l₂)
        (Nat.floor (a n)) k₂ g Cg hgbd).2 y
    · have hfun : (fun t : ℝ => GclRep ρ P C₀ a l₁ l₂ k₁ k₂ t g n y) = fun _ : ℝ => 0 := by
        funext t
        simp only [GclRep, hc, if_false, Pi.zero_apply]
      rw [hfun]; exact measurable_const
  -- the two continuous kernels of the slice
  have hdec₁ : ∃ Cd : ℝ, ∀ j : ℤ,
      ‖cw (mStarF (uRep ρ l₁ l₂ k₁ k₂)) j‖ ≤ Cd / (1 + |(j : ℝ)|) ^ 2 := by
    obtain ⟨hw, _, hw'⟩ := cw_etaCut_decay (-(2 * (uRep ρ l₁ l₂ k₁ k₂ : ℤ)))
    exact ⟨hw, fun j => by simpa only [mStarF] using hw' j⟩
  have hdec₂ : ∃ Cd : ℝ, ∀ j : ℤ,
      ‖cw (mStargF P.natDegree (uRep ρ l₁ l₂ k₁ k₂)) j‖ ≤ Cd / (1 + |(j : ℝ)|) ^ 2 := by
    obtain ⟨hw, _, hw'⟩ :=
      cw_etaCut_decay (-((P.natDegree : ℤ) * 2 * (uRep ρ l₁ l₂ k₁ k₂ : ℤ)))
    exact ⟨hw, fun j => by simpa only [mStargF] using hw' j⟩
  have hKern : ∃ K : ℝ, ∀ j₁ j₂ : ℤ, ‖arithKernelSet P (arithQ ρ (max l₁ l₂))
      (iwArithFreqsNew ρ l₁) (iwArithFreqsNew ρ l₂) j₁ j₂‖ ≤ K :=
    ⟨_, fun j₁ j₂ => norm_arithKernelSet_le P _ _ _ j₁ j₂⟩
  -- the level-`0` `f`-side bound (at the clip `core ρ C₀ l₁ l₂ k₁ k₂`)
  have hh0F : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ F : ℤ → ℂ, MeasureTheory.eLpNorm (fun x : ℤ =>
        PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => if core ρ C₀ l₁ l₂ k₁ k₂ a n
            then Tle ρ 0 (varphiNt (Nat.floor (a n)) k₁ t) F x else 0))
        2 MeasureTheory.Measure.count ≤ K0 Λ * MeasureTheory.eLpNorm F 2 MeasureTheory.Measure.count :=
    fun t ht F => (hClo Λ hΛ a ha ha1 l₁ l₂ k₁ k₂ hLB t ht F).trans
      (mul_le_mul' (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
        (lossWeight_mono ρ hρ.le B hl₁B hl₂B hk₁B hk₂B) (hClopos Λ).le)) le_rfl)
  -- the `f`-side linear estimate
  have hlinF : ∀ t ∈ Set.Icc (1/2 : ℝ) 1,
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => HclRep ρ C₀ a l₁ l₂ k₁ k₂ t f n x)) 2 MeasureTheory.Measure.count
        ≤ Kf Λ * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
    intro t ht
    have hclF : ∀ y : ℤ, ‖PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => HclRep ρ C₀ a l₁ l₂ k₁ k₂ t f n y)‖ₑ
        ≤ (2 : ENNReal) * ‖PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => Hcl ρ C₀ a l₁ l₂ k₁ k₂ t f n y)‖ₑ := by
      intro y
      rw [enorm_eq_self, enorm_eq_self]
      have hfun : (fun n : ℕ => HclRep ρ C₀ a l₁ l₂ k₁ k₂ t f n y)
          = fun n : ℕ => if bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n)) then
              Hcl ρ C₀ a l₁ l₂ k₁ k₂ t f n y else 0 := by
        funext n
        rw [HclRep_eq_ite]
        by_cases hb : bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n))
        · simp only [hb, if_true]
        · simp only [hb, if_false, Pi.zero_apply]
      rw [hfun]
      exact variationalNorm_clip_of_tail r hr1 hbandtail
        (fun n : ℕ => Hcl ρ C₀ a l₁ l₂ k₁ k₂ t f n y)
    have hclip : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => HclRep ρ C₀ a l₁ l₂ k₁ k₂ t f n x)) 2 MeasureTheory.Measure.count
        ≤ (2 : ENNReal) * MeasureTheory.eLpNorm (fun x : ℤ =>
            PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => Hcl ρ C₀ a l₁ l₂ k₁ k₂ t f n x)) 2 MeasureTheory.Measure.count := by
      have hsm := MeasureTheory.eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul' (hf := by pw_aesm)
        (μ := MeasureTheory.Measure.count) (Eventually.of_forall hclF) 2
      rw [ENNReal.smul_def, smul_eq_mul] at hsm
      norm_num at hsm
      exact hsm
    rw [hKfv Λ]
    refine hclip.trans ?_
    rcases Nat.eq_zero_or_pos l₁ with h0 | hpos
    · -- `l₁ = 0`: the clipped family vanishes
      subst h0
      have hz : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Hcl ρ C₀ a 0 l₂ k₁ k₂ t f n x)) = 0 := by
        funext x
        have hfun : (fun n : ℕ => Hcl ρ C₀ a 0 l₂ k₁ k₂ t f n x) = 0 := by
          funext n
          by_cases hc : core ρ C₀ 0 l₂ k₁ k₂ a n
          · rw [show Hcl ρ C₀ a 0 l₂ k₁ k₂ t f n
                = (if core ρ C₀ 0 l₂ k₁ k₂ a n then
                    Tex ρ 0 (varphiNt (Nat.floor (a n)) k₁ t) f else 0) from rfl, if_pos hc]
            simp only [Tex_zero_level, Pi.zero_apply]
          · rw [show Hcl ρ C₀ a 0 l₂ k₁ k₂ t f n
                = (if core ρ C₀ 0 l₂ k₁ k₂ a n then
                    Tex ρ 0 (varphiNt (Nat.floor (a n)) k₁ t) f else 0) from rfl, if_neg hc]
            simp only [Pi.zero_apply]
        rw [hfun]
        simp only [Work.KMTAreas.A7.variationalNorm_zero r hr1, Pi.zero_apply]
      rw [hz, MeasureTheory.eLpNorm_zero]
      simp
    · -- the level splitting
      have hψ : ∀ n : ℕ, MeasureTheory.Integrable (varphiNt (Nat.floor (a n)) k₁ t) := fun n =>
        (contDiff_varphiNt (Nat.floor (a n)) k₁ t).continuous.integrable_of_hasCompactSupport
          (hasCompactSupport_varphiNt (Nat.floor (a n)) k₁ t)
      have hψcw : ∀ n : ℕ, Summable fun j : ℤ =>
          ‖cw (varphiNt (Nat.floor (a n)) k₁ t) j‖ := fun n =>
        summable_cw_varphiNt (Nat.floor (a n)) k₁ t
      have hbridge : ∀ n : ℕ, Hcl ρ C₀ a l₁ l₂ k₁ k₂ t f n
          = (fun x : ℤ => if core ρ C₀ l₁ l₂ k₁ k₂ a n
                then Tle ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t) f x else 0)
            - (fun x : ℤ => if core ρ C₀ l₁ l₂ k₁ k₂ a n
                then Tle ρ (l₁ - 1) (varphiNt (Nat.floor (a n)) k₁ t) f x else 0) := by
        intro n
        by_cases hc : core ρ C₀ l₁ l₂ k₁ k₂ a n
        · rw [show Hcl ρ C₀ a l₁ l₂ k₁ k₂ t f n
              = (if core ρ C₀ l₁ l₂ k₁ k₂ a n then
                  Tex ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t) f else 0) from rfl, if_pos hc]
          have hadm1 : Adm (iwArithFreqs ρ l₁) (varphiNt (Nat.floor (a n)) k₁ t) :=
            adm_of_bump (contDiff_varphiNt (Nat.floor (a n)) k₁ t)
              (hasCompactSupport_varphiNt (Nat.floor (a n)) k₁ t)
          have hadm2 : Adm (iwArithFreqs ρ (l₁ - 1)) (varphiNt (Nat.floor (a n)) k₁ t) :=
            adm_of_bump (contDiff_varphiNt (Nat.floor (a n)) k₁ t)
              (hasCompactSupport_varphiNt (Nat.floor (a n)) k₁ t)
          rw [Tex_eq_Tle_sub_all ρ hmono hpos hadm1 hadm2 hfbd]
          ext x
          simp only [Pi.sub_apply, if_pos hc]
        · rw [show Hcl ρ C₀ a l₁ l₂ k₁ k₂ t f n
              = (if core ρ C₀ l₁ l₂ k₁ k₂ a n then
                  Tex ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t) f else 0) from rfl, if_neg hc]
          ext x
          simp only [Pi.sub_apply, if_neg hc, sub_zero, Pi.zero_apply]
      have hE : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => Hcl ρ C₀ a l₁ l₂ k₁ k₂ t f n x)) 2 MeasureTheory.Measure.count
          ≤ MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
                (fun n : ℕ => if core ρ C₀ l₁ l₂ k₁ k₂ a n
                  then Tle ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t) f x else 0))
                2 MeasureTheory.Measure.count
            + MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
                (fun n : ℕ => if core ρ C₀ l₁ l₂ k₁ k₂ a n
                  then Tle ρ (l₁ - 1) (varphiNt (Nat.floor (a n)) k₁ t) f x else 0))
                2 MeasureTheory.Measure.count := by
        have hsplit : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => Hcl ρ C₀ a l₁ l₂ k₁ k₂ t f n x)
            ≤ PointwiseErgodicTheorems.variationalNorm r
                (fun n : ℕ => if core ρ C₀ l₁ l₂ k₁ k₂ a n
                  then Tle ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t) f x else 0)
              + PointwiseErgodicTheorems.variationalNorm r
                (fun n : ℕ => if core ρ C₀ l₁ l₂ k₁ k₂ a n
                  then Tle ρ (l₁ - 1) (varphiNt (Nat.floor (a n)) k₁ t) f x else 0) := by
          intro x
          have hfun : (fun n : ℕ => Hcl ρ C₀ a l₁ l₂ k₁ k₂ t f n x)
              = (fun n : ℕ => if core ρ C₀ l₁ l₂ k₁ k₂ a n
                    then Tle ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t) f x else 0)
                + (-(fun n : ℕ => if core ρ C₀ l₁ l₂ k₁ k₂ a n
                    then Tle ρ (l₁ - 1) (varphiNt (Nat.floor (a n)) k₁ t) f x else 0)) := by
            funext n
            rw [hbridge n]
            simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply]
            ring
          rw [hfun]
          refine (Submission.PointwiseErgodicTheorems.variationalNorm_add_le hr1 _ _).trans
            (add_le_add le_rfl ?_)
          refine le_of_eq ?_
          have hfam : (-(fun n : ℕ => if core ρ C₀ l₁ l₂ k₁ k₂ a n
                then Tle ρ (l₁ - 1) (varphiNt (Nat.floor (a n)) k₁ t) f x else 0))
              = (-1 : ℂ) • (fun n : ℕ => if core ρ C₀ l₁ l₂ k₁ k₂ a n
                then Tle ρ (l₁ - 1) (varphiNt (Nat.floor (a n)) k₁ t) f x else 0) := by
            funext n
            by_cases h : core ρ C₀ l₁ l₂ k₁ k₂ a n <;> simp [h]
          rw [hfam, Submission.PointwiseErgodicTheorems.variationalNorm_smul hr1]
          have h2 : ‖(-1 : ℂ)‖ₑ = 1 := by
            rw [← ofReal_norm, norm_neg, norm_one, ENNReal.ofReal_one]
          rw [h2, one_mul]
        refine (MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) (f := fun x : ℤ =>
            PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => Hcl ρ C₀ a l₁ l₂ k₁ k₂ t f n x))
          (g := fun x : ℤ =>
            PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => if core ρ C₀ l₁ l₂ k₁ k₂ a n
                then Tle ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t) f x else 0)
            + PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => if core ρ C₀ l₁ l₂ k₁ k₂ a n
                then Tle ρ (l₁ - 1) (varphiNt (Nat.floor (a n)) k₁ t) f x else 0))
          (fun x => by rw [enorm_eq_self, enorm_eq_self]; exact hsplit x)).trans
          (eLpNorm_add_le_ennreal (by norm_num) (by norm_num) (μ := MeasureTheory.Measure.count))
      have hb1 : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => if core ρ C₀ l₁ l₂ k₁ k₂ a n
                then Tle ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t) f x else 0))
              2 MeasureTheory.Measure.count
          ≤ Qc * K0 Λ * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
        refine (eLpNorm_Tle_le_sum ρ l₁ hψ hψcw (core ρ C₀ l₁ l₂ k₁ k₂ a) r hr1 2
          (by norm_num) (by norm_num) (K := K0 Λ) (hh0F t ht) f hfbd).trans ?_
        refine mul_le_mul' ?_ le_rfl
        rw [Finset.sum_const, nsmul_eq_mul]
        exact mul_le_mul' hcard₁ le_rfl
      have hb2 : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => if core ρ C₀ l₁ l₂ k₁ k₂ a n
                then Tle ρ (l₁ - 1) (varphiNt (Nat.floor (a n)) k₁ t) f x else 0))
              2 MeasureTheory.Measure.count
          ≤ Qc * K0 Λ * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
        refine (eLpNorm_Tle_le_sum ρ (l₁ - 1) hψ hψcw (core ρ C₀ l₁ l₂ k₁ k₂ a) r hr1 2
          (by norm_num) (by norm_num) (K := K0 Λ) (hh0F t ht) f hfbd).trans ?_
        refine mul_le_mul' ?_ le_rfl
        rw [Finset.sum_const, nsmul_eq_mul]
        exact mul_le_mul' hcard₁' le_rfl
      calc (2 : ENNReal) * MeasureTheory.eLpNorm (fun x : ℤ =>
              PointwiseErgodicTheorems.variationalNorm r
                (fun n : ℕ => Hcl ρ C₀ a l₁ l₂ k₁ k₂ t f n x)) 2 MeasureTheory.Measure.count
          ≤ (2 : ENNReal) * (MeasureTheory.eLpNorm (fun x : ℤ =>
                PointwiseErgodicTheorems.variationalNorm r
                  (fun n : ℕ => if core ρ C₀ l₁ l₂ k₁ k₂ a n
                    then Tle ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t) f x else 0))
                2 MeasureTheory.Measure.count
              + MeasureTheory.eLpNorm (fun x : ℤ =>
                PointwiseErgodicTheorems.variationalNorm r
                  (fun n : ℕ => if core ρ C₀ l₁ l₂ k₁ k₂ a n
                    then Tle ρ (l₁ - 1) (varphiNt (Nat.floor (a n)) k₁ t) f x else 0))
                2 MeasureTheory.Measure.count) := mul_le_mul' le_rfl hE
        _ ≤ (2 : ENNReal) * (Qc * K0 Λ * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
              + Qc * K0 Λ * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count) :=
            mul_le_mul' le_rfl (add_le_add hb1 hb2)
        _ = 4 * Qc * K0 Λ * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by ring
  -- the level-`0` `g`-side bound
  have hh0G : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ F : ℤ → ℂ, MeasureTheory.eLpNorm (fun x : ℤ =>
        PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => if core ρ C₀ l₁ l₂ k₁ k₂ a n
            then Tle ρ 0 (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) F x else 0))
        2 MeasureTheory.Measure.count ≤ (Klv0 Λ : ENNReal)
          * MeasureTheory.eLpNorm F 2 MeasureTheory.Measure.count :=
    fun t ht F => hKlv0 a Λ l₁ l₂ k₁ k₂ t F hΛ ha ha1 hLB ht
  -- the `g`-side linear estimate
  have hlinG : ∀ t ∈ Set.Icc (1/2 : ℝ) 1,
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => GclRep ρ P C₀ a l₁ l₂ k₁ k₂ t g n x)) 2 MeasureTheory.Measure.count
        ≤ Kg Λ * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
    intro t ht
    have hclG : ∀ y : ℤ, ‖PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => GclRep ρ P C₀ a l₁ l₂ k₁ k₂ t g n y)‖ₑ
        ≤ (2 : ENNReal) * ‖PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => Gcl ρ P C₀ a l₁ l₂ k₁ k₂ t g n y)‖ₑ := by
      intro y
      rw [enorm_eq_self, enorm_eq_self]
      have hfun : (fun n : ℕ => GclRep ρ P C₀ a l₁ l₂ k₁ k₂ t g n y)
          = fun n : ℕ => if bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n)) then
              Gcl ρ P C₀ a l₁ l₂ k₁ k₂ t g n y else 0 := by
        funext n
        rw [GclRep_eq_ite]
        by_cases hb : bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n))
        · simp only [hb, if_true]
        · simp only [hb, if_false, Pi.zero_apply]
      rw [hfun]
      exact variationalNorm_clip_of_tail r hr1 hbandtail
        (fun n : ℕ => Gcl ρ P C₀ a l₁ l₂ k₁ k₂ t g n y)
    have hclip : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => GclRep ρ P C₀ a l₁ l₂ k₁ k₂ t g n x)) 2 MeasureTheory.Measure.count
        ≤ (2 : ENNReal) * MeasureTheory.eLpNorm (fun x : ℤ =>
            PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => Gcl ρ P C₀ a l₁ l₂ k₁ k₂ t g n x)) 2 MeasureTheory.Measure.count := by
      have hsm := MeasureTheory.eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul' (hf := by pw_aesm)
        (μ := MeasureTheory.Measure.count) (Eventually.of_forall hclG) 2
      rw [ENNReal.smul_def, smul_eq_mul] at hsm
      norm_num at hsm
      exact hsm
    rw [hKgv Λ]
    refine hclip.trans ?_
    rcases Nat.eq_zero_or_pos l₂ with h0 | hpos
    · -- `l₂ = 0`: the clipped family vanishes
      subst h0
      have hz : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Gcl ρ P C₀ a l₁ 0 k₁ k₂ t g n x)) = 0 := by
        funext x
        have hfun : (fun n : ℕ => Gcl ρ P C₀ a l₁ 0 k₁ k₂ t g n x) = 0 := by
          funext n
          by_cases hc : core ρ C₀ l₁ 0 k₁ k₂ a n
          · rw [show Gcl ρ P C₀ a l₁ 0 k₁ k₂ t g n
                = (if core ρ C₀ l₁ 0 k₁ k₂ a n then
                    Tex ρ 0 (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g else 0)
                from rfl, if_pos hc]
            simp only [Tex_zero_level, Pi.zero_apply]
          · rw [show Gcl ρ P C₀ a l₁ 0 k₁ k₂ t g n
                = (if core ρ C₀ l₁ 0 k₁ k₂ a n then
                    Tex ρ 0 (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g else 0)
                from rfl, if_neg hc]
            simp only [Pi.zero_apply]
        rw [hfun]
        simp only [Work.KMTAreas.A7.variationalNorm_zero r hr1, Pi.zero_apply]
      rw [hz, MeasureTheory.eLpNorm_zero]
      simp
    · have hψ : ∀ n : ℕ,
          MeasureTheory.Integrable (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) :=
        fun n =>
          (contDiff_varphitildeNt_aux P P.natDegree (Nat.floor (a n)) k₂ t).continuous
            |>.integrable_of_hasCompactSupport
              (hasCompactSupport_varphitildeNt_aux P P.natDegree (Nat.floor (a n)) k₂ t)
      have hψcw : ∀ n : ℕ, Summable fun j : ℤ =>
          ‖cw (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) j‖ := fun n =>
        summable_cw_varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t
      have hbridge : ∀ n : ℕ, Gcl ρ P C₀ a l₁ l₂ k₁ k₂ t g n
          = (fun x : ℤ => if core ρ C₀ l₁ l₂ k₁ k₂ a n
                then Tle ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g x else 0)
            - (fun x : ℤ => if core ρ C₀ l₁ l₂ k₁ k₂ a n
                then Tle ρ (l₂ - 1) (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g x
                else 0) := by
        intro n
        by_cases hc : core ρ C₀ l₁ l₂ k₁ k₂ a n
        · rw [show Gcl ρ P C₀ a l₁ l₂ k₁ k₂ t g n
              = (if core ρ C₀ l₁ l₂ k₁ k₂ a n then
                  Tex ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g else 0)
              from rfl, if_pos hc]
          have hadm1 : Adm (iwArithFreqs ρ l₂)
              (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) :=
            adm_of_bump (contDiff_varphitildeNt_aux P P.natDegree (Nat.floor (a n)) k₂ t)
              (hasCompactSupport_varphitildeNt_aux P P.natDegree (Nat.floor (a n)) k₂ t)
          have hadm2 : Adm (iwArithFreqs ρ (l₂ - 1))
              (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) :=
            adm_of_bump (contDiff_varphitildeNt_aux P P.natDegree (Nat.floor (a n)) k₂ t)
              (hasCompactSupport_varphitildeNt_aux P P.natDegree (Nat.floor (a n)) k₂ t)
          rw [Tex_eq_Tle_sub_all ρ hmono hpos hadm1 hadm2 hgbd]
          ext x
          simp only [Pi.sub_apply, if_pos hc]
        · rw [show Gcl ρ P C₀ a l₁ l₂ k₁ k₂ t g n
              = (if core ρ C₀ l₁ l₂ k₁ k₂ a n then
                  Tex ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g else 0)
              from rfl, if_neg hc]
          ext x
          simp only [Pi.sub_apply, if_neg hc, sub_zero, Pi.zero_apply]
      have hE : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => Gcl ρ P C₀ a l₁ l₂ k₁ k₂ t g n x)) 2 MeasureTheory.Measure.count
          ≤ MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
                (fun n : ℕ => if core ρ C₀ l₁ l₂ k₁ k₂ a n
                  then Tle ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g x
                  else 0)) 2 MeasureTheory.Measure.count
            + MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
                (fun n : ℕ => if core ρ C₀ l₁ l₂ k₁ k₂ a n
                  then Tle ρ (l₂ - 1) (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g x
                  else 0)) 2 MeasureTheory.Measure.count := by
        have hsplit : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => Gcl ρ P C₀ a l₁ l₂ k₁ k₂ t g n x)
            ≤ PointwiseErgodicTheorems.variationalNorm r
                (fun n : ℕ => if core ρ C₀ l₁ l₂ k₁ k₂ a n
                  then Tle ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g x
                  else 0)
              + PointwiseErgodicTheorems.variationalNorm r
                (fun n : ℕ => if core ρ C₀ l₁ l₂ k₁ k₂ a n
                  then Tle ρ (l₂ - 1) (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g x
                  else 0) := by
          intro x
          have hfun : (fun n : ℕ => Gcl ρ P C₀ a l₁ l₂ k₁ k₂ t g n x)
              = (fun n : ℕ => if core ρ C₀ l₁ l₂ k₁ k₂ a n
                    then Tle ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g x
                    else 0)
                + (-(fun n : ℕ => if core ρ C₀ l₁ l₂ k₁ k₂ a n
                    then Tle ρ (l₂ - 1) (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g x
                    else 0)) := by
            funext n
            rw [hbridge n]
            simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply]
            ring
          rw [hfun]
          refine (Submission.PointwiseErgodicTheorems.variationalNorm_add_le hr1 _ _).trans
            (add_le_add le_rfl ?_)
          refine le_of_eq ?_
          have hfam : (-(fun n : ℕ => if core ρ C₀ l₁ l₂ k₁ k₂ a n
                then Tle ρ (l₂ - 1) (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g x
                else 0))
              = (-1 : ℂ) • (fun n : ℕ => if core ρ C₀ l₁ l₂ k₁ k₂ a n
                then Tle ρ (l₂ - 1) (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g x
                else 0) := by
            funext n
            by_cases h : core ρ C₀ l₁ l₂ k₁ k₂ a n <;> simp [h]
          rw [hfam, Submission.PointwiseErgodicTheorems.variationalNorm_smul hr1]
          have h2 : ‖(-1 : ℂ)‖ₑ = 1 := by
            rw [← ofReal_norm, norm_neg, norm_one, ENNReal.ofReal_one]
          rw [h2, one_mul]
        refine (MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) (f := fun x : ℤ =>
            PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => Gcl ρ P C₀ a l₁ l₂ k₁ k₂ t g n x))
          (g := fun x : ℤ =>
            PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => if core ρ C₀ l₁ l₂ k₁ k₂ a n
                then Tle ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g x
                else 0)
            + PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => if core ρ C₀ l₁ l₂ k₁ k₂ a n
                then Tle ρ (l₂ - 1) (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g x
                else 0))
          (fun x => by rw [enorm_eq_self, enorm_eq_self]; exact hsplit x)).trans
          (eLpNorm_add_le_ennreal (by norm_num) (by norm_num) (μ := MeasureTheory.Measure.count))
      have hb1 : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => if core ρ C₀ l₁ l₂ k₁ k₂ a n
                then Tle ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g x
                else 0)) 2 MeasureTheory.Measure.count
          ≤ Qc * (Klv0 Λ : ENNReal) * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
        refine (eLpNorm_Tle_le_sum ρ l₂ hψ hψcw (core ρ C₀ l₁ l₂ k₁ k₂ a) r hr1 2
          (by norm_num) (by norm_num) (K := (Klv0 Λ : ENNReal)) (hh0G t ht) g hgbd).trans ?_
        refine mul_le_mul' ?_ le_rfl
        rw [Finset.sum_const, nsmul_eq_mul]
        exact mul_le_mul' hcard₂ le_rfl
      have hb2 : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => if core ρ C₀ l₁ l₂ k₁ k₂ a n
                then Tle ρ (l₂ - 1) (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g x
                else 0)) 2 MeasureTheory.Measure.count
          ≤ Qc * (Klv0 Λ : ENNReal) * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
        refine (eLpNorm_Tle_le_sum ρ (l₂ - 1) hψ hψcw (core ρ C₀ l₁ l₂ k₁ k₂ a) r hr1 2
          (by norm_num) (by norm_num) (K := (Klv0 Λ : ENNReal)) (hh0G t ht) g hgbd).trans ?_
        refine mul_le_mul' ?_ le_rfl
        rw [Finset.sum_const, nsmul_eq_mul]
        exact mul_le_mul' hcard₂' le_rfl
      calc (2 : ENNReal) * MeasureTheory.eLpNorm (fun x : ℤ =>
              PointwiseErgodicTheorems.variationalNorm r
                (fun n : ℕ => Gcl ρ P C₀ a l₁ l₂ k₁ k₂ t g n x)) 2 MeasureTheory.Measure.count
          ≤ (2 : ENNReal) * (MeasureTheory.eLpNorm (fun x : ℤ =>
                PointwiseErgodicTheorems.variationalNorm r
                  (fun n : ℕ => if core ρ C₀ l₁ l₂ k₁ k₂ a n
                    then Tle ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g x
                    else 0)) 2 MeasureTheory.Measure.count
              + MeasureTheory.eLpNorm (fun x : ℤ =>
                PointwiseErgodicTheorems.variationalNorm r
                  (fun n : ℕ => if core ρ C₀ l₁ l₂ k₁ k₂ a n
                    then Tle ρ (l₂ - 1) (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g x
                    else 0)) 2 MeasureTheory.Measure.count) := mul_le_mul' le_rfl hE
        _ ≤ (2 : ENNReal) * (Qc * (Klv0 Λ : ENNReal)
              * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count
              + Qc * (Klv0 Λ : ENNReal)
              * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count) :=
            mul_le_mul' le_rfl (add_le_add hb1 hb2)
        _ = 4 * Qc * (Klv0 Λ : ENNReal) * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count :=
            by ring
  -- the kernel mass and its `ℝ≥0∞` form
  let cc : ℤ → ℤ → ℂ := fun i j => arithKernelExact ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ i j
      * cw (mStarF (uRep ρ l₁ l₂ k₁ k₂)) i * cw (mStargF P.natDegree (uRep ρ l₁ l₂ k₁ k₂)) j
  have hcc_summable : Summable (fun p : ℤ × ℤ => ‖cc p.1 p.2‖) := by
    show Summable (fun p : ℤ × ℤ =>
      ‖arithKernelExact ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ p.1 p.2
        * cw (mStarF (uRep ρ l₁ l₂ k₁ k₂)) p.1
        * cw (mStargF P.natDegree (uRep ρ l₁ l₂ k₁ k₂)) p.2‖)
    exact (hCk l₁ l₂ k₁ k₂ hLB).1
  have hcc_sum : (∑' p : ℤ × ℤ, ‖cc p.1 p.2‖) ≤ Ck := by
    show (∑' p : ℤ × ℤ,
      ‖arithKernelExact ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ p.1 p.2
        * cw (mStarF (uRep ρ l₁ l₂ k₁ k₂)) p.1
        * cw (mStargF P.natDegree (uRep ρ l₁ l₂ k₁ k₂)) p.2‖) ≤ Ck
    exact (hCk l₁ l₂ k₁ k₂ hLB).2
  have hccE : (∑' p : ℤ × ℤ, ‖cc p.1 p.2‖ₑ) ≤ ENNReal.ofReal Ck := by
    calc (∑' p : ℤ × ℤ, ‖cc p.1 p.2‖ₑ)
        = ∑' p : ℤ × ℤ, ENNReal.ofReal ‖cc p.1 p.2‖ := by
          refine tsum_congr (fun p => ?_)
          rw [enorm_eq_nnnorm, ← ENNReal.ofReal_coe_nnreal]
          rfl
      _ = ENNReal.ofReal (∑' p : ℤ × ℤ, ‖cc p.1 p.2‖) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun p => norm_nonneg _) hcc_summable).symm
      _ ≤ ENNReal.ofReal Ck := ENNReal.ofReal_le_ofReal hcc_sum
  -- the frozen slice and its bound
  have hslice : ∀ t ∈ Set.Ioc (1/2 : ℝ) 1,
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => BtwistExact ρ P l₁ l₂ (mStarF (uRep ρ l₁ l₂ k₁ k₂))
            (mStargF P.natDegree (uRep ρ l₁ l₂ k₁ k₂))
            (HclRep ρ C₀ a l₁ l₂ k₁ k₂ t f n) (GclRep ρ P C₀ a l₁ l₂ k₁ k₂ t g n) x))
        1 MeasureTheory.Measure.count
      ≤ Kc Λ * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
    intro t ht
    have htI : t ∈ Set.Icc (1/2 : ℝ) 1 := Set.Ioc_subset_Icc_self ht
    have hsliceK := sliceKernelL1 r hr1 cc (fun n : ℕ => HclRep ρ C₀ a l₁ l₂ k₁ k₂ t f n)
      (fun n : ℕ => GclRep ρ P C₀ a l₁ l₂ k₁ k₂ t g n)
    rw [show (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => ∑' i : ℤ, ∑' j : ℤ, cc i j * HclRep ρ C₀ a l₁ l₂ k₁ k₂ t f n (x - i)
            * GclRep ρ P C₀ a l₁ l₂ k₁ k₂ t g n (x - j)))
        = (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => BtwistExact ρ P l₁ l₂ (mStarF (uRep ρ l₁ l₂ k₁ k₂))
              (mStargF P.natDegree (uRep ρ l₁ l₂ k₁ k₂))
              (HclRep ρ C₀ a l₁ l₂ k₁ k₂ t f n) (GclRep ρ P C₀ a l₁ l₂ k₁ k₂ t g n) x)) from by
      funext x
      simp only [BtwistExact, cc]] at hsliceK
    rw [hKcv Λ]
    refine hsliceK.trans ?_
    calc (2 * (∑' p : ℤ × ℤ, ‖cc p.1 p.2‖ₑ))
          * MeasureTheory.eLpNorm (fun y : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => HclRep ρ C₀ a l₁ l₂ k₁ k₂ t f n y)) 2 MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm (fun y : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => GclRep ρ P C₀ a l₁ l₂ k₁ k₂ t g n y)) 2 MeasureTheory.Measure.count
        ≤ (2 * ENNReal.ofReal Ck) * (Kf Λ * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count)
            * (Kg Λ * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count) :=
          mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl hccE) (hlinF t htI)) (hlinG t htI)
      _ = (2 * ENNReal.ofReal Ck * Kf Λ * Kg Λ)
            * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
            * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by ring
  -- the `t`-integration
  have hpt : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Work.KMTAreas.A7.modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
      ≤ ∫⁻ t in Set.Ioc (1/2 : ℝ) 1, PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => BtwistExact ρ P l₁ l₂ (mStarF (uRep ρ l₁ l₂ k₁ k₂))
            (mStargF P.natDegree (uRep ρ l₁ l₂ k₁ k₂))
            (HclRep ρ C₀ a l₁ l₂ k₁ k₂ t f n) (GclRep ρ P C₀ a l₁ l₂ k₁ k₂ t g n) x) := by
    intro x
    have key := varNorm_integral_le r hr1 (fun t n y =>
      BtwistExact ρ P l₁ l₂ (mStarF (uRep ρ l₁ l₂ k₁ k₂))
        (mStargF P.natDegree (uRep ρ l₁ l₂ k₁ k₂))
        (HclRep ρ C₀ a l₁ l₂ k₁ k₂ t f n) (GclRep ρ P C₀ a l₁ l₂ k₁ k₂ t g n) y) x
      (fun n => ?_) (fun n => ?_)
    · rw [Set.uIoc_of_le hhalf] at key
      rw [modelTupleRep_eq_intervalIntegral]
      exact key
    · -- interval integrability of the `n`-th slice
      obtain ⟨C, hC⟩ := exists_bound_BtwistSet_uniform ρ P l₁ l₂ (iwArithFreqsNew ρ l₁)
        (iwArithFreqsNew ρ l₂) (mStarF (uRep ρ l₁ l₂ k₁ k₂))
        (mStargF P.natDegree (uRep ρ l₁ l₂ k₁ k₂))
        (fun t : ℝ => HclRep ρ C₀ a l₁ l₂ k₁ k₂ t f n)
        (fun t : ℝ => GclRep ρ P C₀ a l₁ l₂ k₁ k₂ t g n)
        x hKern hdec₁ hdec₂ (hboundF n) (hboundG n)
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hhalf]
      refine Integrable.of_bound ?_ C ?_
      · exact (Measurable.tsum (fun j₁ : ℤ => Measurable.tsum (fun j₂ : ℤ =>
          (measurable_const.mul (hmeasF n (x - j₁))).mul (hmeasG n (x - j₂))))).aestronglyMeasurable
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
        simpa only [BtwistSet_iwArithFreqsNew] using hC t (Set.Ioc_subset_Icc_self ht)
    · -- measurability in `t` of the `n`-th slice
      simp only [BtwistExact]
      exact Measurable.tsum (fun j₁ : ℤ => Measurable.tsum (fun j₂ : ℤ =>
        (measurable_const.mul (hmeasF n (x - j₁))).mul (hmeasG n (x - j₂))))
  have hmono : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Work.KMTAreas.A7.modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
      1 MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (fun x : ℤ => ∫⁻ t in Set.Ioc (1/2 : ℝ) 1,
          PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => BtwistExact ρ P l₁ l₂ (mStarF (uRep ρ l₁ l₂ k₁ k₂))
              (mStargF P.natDegree (uRep ρ l₁ l₂ k₁ k₂))
              (HclRep ρ C₀ a l₁ l₂ k₁ k₂ t f n) (GclRep ρ P C₀ a l₁ l₂ k₁ k₂ t g n) x))
      1 MeasureTheory.Measure.count :=
    MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) (fun x => by simpa only [enorm_eq_self] using hpt x)
  have hlin : MeasureTheory.eLpNorm (fun x : ℤ => ∫⁻ t in Set.Ioc (1/2 : ℝ) 1,
        PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => BtwistExact ρ P l₁ l₂ (mStarF (uRep ρ l₁ l₂ k₁ k₂))
            (mStargF P.natDegree (uRep ρ l₁ l₂ k₁ k₂))
            (HclRep ρ C₀ a l₁ l₂ k₁ k₂ t f n) (GclRep ρ P C₀ a l₁ l₂ k₁ k₂ t g n) x))
      1 MeasureTheory.Measure.count
      ≤ Kc Λ * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count :=
    eLpNorm_lintegral_le 1 le_rfl
      (fun t x => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => BtwistExact ρ P l₁ l₂ (mStarF (uRep ρ l₁ l₂ k₁ k₂))
          (mStargF P.natDegree (uRep ρ l₁ l₂ k₁ k₂))
          (HclRep ρ C₀ a l₁ l₂ k₁ k₂ t f n) (GclRep ρ P C₀ a l₁ l₂ k₁ k₂ t g n) x)) _
      hslice
  exact (hmono.trans hlin).trans (mul_le_mul' (mul_le_mul' hKcle le_rfl) le_rfl)

/-- **The `§8` model bound for the repaired model `modelTupleRep`, at every `ρ > 0`.**

This is `modelPieceBoundAllRho_of_mono` with the monotonicity of the Ionescu--Wainger frequency
sets supplied by `iwArithFreqs_mono_all`, which holds for every `ρ > 0` (the paper's
`iwArithFreqs_mono` requires `ρ ≤ 1`). -/
theorem modelPieceBoundAllRho (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (r : NNReal) (hr : 2 < r)
    (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (ρ : ℝ) (hρ : 0 < ρ) (B : ℕ) :
    Work.KMTPlan.A6.ModelPieceBound P r C₀ ρ B :=
  modelPieceBoundAllRho_of_mono P hd r hr C₀ hC₀ ρ hρ
    (fun _ _ h => iwArithFreqs_mono_all hρ h) B

end

end Work.KMTPlan.A6.LowModApproxBoundedH
