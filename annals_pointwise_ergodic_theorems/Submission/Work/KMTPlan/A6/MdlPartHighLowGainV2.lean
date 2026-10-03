/-
# The high-low (`k₂ = 0 < k₁`) branch of the large-scale model estimate (area A6, §6)

Statement: `Work.KMTPlan.A6.MdlPartHighLowGainV2` — the `k₂ = 0 ∧ max l₁ l₂ < k₁` branch of the
model tuple `mdlPart` of Krause--Mirek--Tao (§6-§8), i.e. the case in which the *only* decay
available comes from the integration-by-parts identity (i) (`MdlDecayHighLowB`, i.e.
`mdlDecayHighLow_core`), applied to the `t`-integral of the tensor `φ_{N,t} ⊗ φ̃_{N,t}`: it produces
the factor `2^{-k₁}` = `mdlScaleF k₁` (and the same factor `mdlScaleFG P k₁ 0 = 2^{-k₁}` on the
middle term).

## Why this file exists (duplication note)

`Submission/Work/KMTPlan/A6/MdlPartHighLowGain.lean` carries the same statement with a complete
855-line proof *on paper*, but that proof does not elaborate (its own header records the outstanding
elaboration/heartbeat problems and the "NEXT PEEL" plan).  `LowModelGainEstimate.lean` — the
consumer, which needs the pair `(HighLow, LowHigh)` of branch estimates — imports *this* module
(`MdlPartHighLowGainV2`) while the draft does not compile.  This file is written as the mirror
image of the *proved* sibling `MdlPartLowHighGain.lean` (identity (ii) + weights `mdlW1`,`mdlW2`),
whose auxiliary lemmas are reused here.

## The proof

* the three frozen-`t` slice instances in their **loss (no-gain) form**
  `Work.KMTPlan.A6Clean.MdlSliceNoGainAt P hd hA1 C₀ r j₁ j₂` — supplied unconditionally by the
  PROVED and axiom-clean `Work.KMTPlan.A6LH.MdlSliceNoGainAtProved` — used at
  `(j₁,j₂) = (-1,0)` (the two boundary terms `t = 1`, `t = 1/2`), `(-1,1)` (the middle term) and
  `(0,0)` (the small-`k₁` case, through the `t`-integrated form `mdlWIntF_norm_le`);
* `MdlWeightVarBound`: the uniform `V^r`-bound of the clipped weight `mdlW3` on the core (threshold
  `Bb ≤ ⌊a n⌋`, which on the core follows from `splitCut ρ k₁ < ⌊a n⌋`);
* `MdlDecayHighLowB`: identity (i) for the model tuple with the modified bumps, giving
  `mdlPart = 2^{-k₁}(2πi)^{-1}(W₁ - W₂) - 2^{-k₁}·Z`, where `W₁,W₂` are the boundary slices and `Z`
  the `mdlW3`-weighted `t`-integral of the `(-1,1)` slice;
* `eLpNorm_varNorm_four_le`, `eLpNorm_varNorm_mul_le`, `mdlWIntF_norm_le` (`MdlPartLowHighGain`)
  and the elementary absorption of the loss `lossWeight A ρ l₁ l₂ k₁ 0` into the gain `2^{-k₁}`
  (`lossWeight_absorb_large_nogain`, `lossWeight_absorb_small_nogain`);
* the two cases `k₁ > K₀` (`K₀` a threshold with `Bb ≤ 2^{K₀}`) and `k₁ ≤ K₀`.

## No dependence on the area's deep input (2026-10-03 rewrite)

An earlier version of this file consumed the three slice instances in the *gain* form
`Work.KMTPlan.A6.MdlSliceCoreGain` (i.e. `MdlSliceCoreGainBig`, the paper's Theorem `model-est-2`
at `(2,2,1)`) and was therefore conditional on that (still open) deep input.  That is **not
necessary** for this branch: here the gain in `max l₁ l₂` is useless (`lcL l₁ l₂ k₁ 0 = k₁` because
`max l₁ l₂ < k₁`) and the whole decay in `k₁` is produced by the integration-by-parts factor
`2^{-k₁}` of `MdlDecayHighLowB` and then absorbed as the gain `2^{-cF·k₁}` with `cF = 1/4`
(`lossWeight_absorb_large_nogain`, `lossWeight_absorb_small_nogain`).  The present proof consumes
only the loss-form inputs — the same upstream statement that the proved sibling branch
`MdlPartLowHighGain` consumes — so it is **axiom-clean**:
`#print axioms Work.KMTPlan.A6.MdlPartHighLowGainV2 = [propext, Classical.choice, Quot.sound]`.

## Session 2 (state of the reduction of the *other* branch, and the route that is dead)

* The assembly `Work.KMTPlan.A6.MdlSliceCoreGain_of_inputs` **cannot** be used to prove
  `MdlSliceCoreGain`: its hypotheses `hF`/`hG` (the *square sums of the values* of the packet
  families) are **false** in the low-pass case `(k,j) = (0,0)` — see
  `Submission/Work/KMTPlan/A6/NOTES_SQSUM_REFUTED_READ_ME.md` and `NOTES_A6_sqSum_REFUTATION.md`
  (a nested family whose values are all `≍ ‖f‖₂` on the infinitely many plateau scales).  So
  `MdlSliceSqSumF`, `MdlSliceSqSumG` and every `hF`/`hG`-shaped packet *square sum* must not be
  attacked again.
* The corrected route to `MdlSliceCoreGain` keeps the variation in the scale index and uses:
  the single-scale gain `Work.KMTPlan.A6.MdlSliceSsuGain` (**proved**), Corollary `bilinear-fkr`
  `Work.KMTPlan.A6.MdlSliceFkrPacketsV2` (**proved**), the band-limited transfer
  `Work.KMTPlan.A6.diagonalVrSampling_le_of_modQ`/`…_of_arcAmplitude` (proved, conditional on an
  amplitude presentation), and the two *linear* lacunary variational estimates for the packet
  families (`(lin-1)`/`(lin-2)`); the `g`-side one is the low-pass family at `k₂ = 0`, i.e. the
  workspace's Lépingle/JSW crux.
* Delivered this session on that path: `Submission/Work/KMTPlan/A6/LowpassVarClean.lean`
  (`Work.KMTPlan.A6.LowpassVar_of_maximal_chain`, **axiom-clean**), the *compilable* form of the
  low-pass variational estimate `‖V^r_m (Π_{≤l₁,≤-(m₀+m)} f)‖_{ℓᵖ} ≤ C(1+l₁)²‖f‖_{ℓᵖ}` from the
  values supremum + the chain estimate (the tree's own module `A7Hi/LowpassVar.lean` does not
  compile).  The full analysis and the ordered remaining chain are in
  `NOTES_A6_MdlPartHighLowGainV2_SESSION2.md`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.MdlDecayHighLowB
import Submission.Work.KMTPlan.A6.MdlPartLowHighGain
-- The three frozen-`t` slice inputs are taken in the *loss form* (no arithmetic gain), from the
-- PROVED and axiom-clean `Work.KMTPlan.A6LH.MdlSliceNoGainAtProved` — the same upstream statement
-- that the proved sibling branch `MdlPartLowHighGain` consumes.  In the present (high-low) branch
-- the whole decay in `k₁` comes from the integration-by-parts identity (i) (`MdlDecayHighLowB`,
-- factor `2^{-k₁}`), so no gain in `max l₁ l₂` is needed and the deep gain-form input
-- `MdlSliceCoreGain` (`MdlSliceCoreGainBig`) is *not* used.

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators Interval
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.EndVar Work.KMTContract Work.KMTAreas.A7

/-! ## Elementary helpers -/

/-- The constant weight `1` makes `mdlSliceW` the frozen slice `mdlSliceJ`. -/
@[simp] lemma mdlSliceW_one_eq_mdlSliceJ' (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0)
    (f g : ℤ → ℂ) (l₁ l₂ k₁ k₂ : ℕ) (j₁ j₂ : ℤ) (t : ℝ) :
    mdlSliceW ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ (fun _ _ => (1 : ℂ)) t
      = mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t := by
  funext n x
  rw [mdlSliceW, mdlSliceJ]
  by_cases h : mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
  · rw [if_pos h, if_pos h, one_mul]
  · rw [if_neg h, if_neg h]

/-- `lmaxR` is insensitive to the order of its two `k`-arguments. -/
lemma lmaxR_zero_swap (l₁ l₂ k : ℕ) : lmaxR l₁ l₂ k 0 = lmaxR l₁ l₂ 0 k := by
  rw [lmaxR, lmaxR, lmax, lmax, max_comm (k : ℤ) (((0 : ℕ)) : ℤ)]

/-- `lossWeight` is insensitive to the order of its two `k`-arguments. -/
lemma lossWeight_zero_swap (A ρ : ℝ) (l₁ l₂ k : ℕ) :
    lossWeight A ρ l₁ l₂ k 0 = lossWeight A ρ l₁ l₂ 0 k := by
  simp only [lossWeight, lmaxR_zero_swap]

/-- `lcWeight` is insensitive to the order of its two `k`-arguments. -/
lemma lcWeight_zero_swap (c : ℝ) (l₁ l₂ k : ℕ) :
    lcWeight c l₁ l₂ k 0 = lcWeight c l₁ l₂ 0 k := by
  simp only [lcWeight, lmax]
  rw [max_comm (k : ℤ) (((0 : ℕ)) : ℤ)]

/-! ## The target -/

/-- **The high-low branch, conditional on the three frozen-`t` slice estimates in their loss
(no-gain) form** (`Work.KMTPlan.A6Clean.MdlSliceNoGainAt`, supplied unconditionally by the proved
and axiom-clean `Work.KMTPlan.A6LH.MdlSliceNoGainAtProved`).  This is the stub-free form of the
target: it becomes an unconditional proof of `MdlPartHighLowGainV2` as soon as those three
instances are provided, and every declaration in its proof is axiom-clean. -/
theorem MdlPartHighLowGainV2_of_sliceGain (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (r : NNReal) (hr : 2 < r) (C₀ : ℕ) (hC₀ : 1 ≤ C₀)
    (hA1 : Work.KMTContract.AreaA1)
    (hS : Work.KMTPlan.A6Clean.MdlSliceNoGainAt P hd hA1 C₀ r (-1) 0)
    (hT : Work.KMTPlan.A6Clean.MdlSliceNoGainAt P hd hA1 C₀ r (-1) 1)
    (hZ : Work.KMTPlan.A6Clean.MdlSliceNoGainAt P hd hA1 C₀ r 0 0) :
    ∃ c : ℝ, 0 < c ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
      ∃ K : NNReal → NNReal,
        ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ : ℕ) (f g : ℤ → ℂ),
          1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n : ℕ, 1 ≤ a n) →
          max l₁ l₂ < k₁ →
          MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => Work.KMTPlan.A6.mdlPart ρ P C₀ a f g l₁ l₂ k₁ 0 n x))
            1 MeasureTheory.Measure.count
            ≤ ((K Λ : NNReal) : ENNReal) *
                ENNReal.ofReal (Work.KMTPlan.A6.lcWeight c l₁ l₂ k₁ 0) *
                MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count *
                MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
  classical
  have hr1 : (1 : ℝ≥0) ≤ r := le_trans (by norm_num : (1 : ℝ≥0) ≤ 2) (le_of_lt hr)
  -- the three frozen-`t` slice instances, in their loss (no-gain) form: their first component is
  -- the *coefficient* of `lossWeight` (the old `A`), and there is no arithmetic gain in
  -- `max l₁ l₂` — the whole decay in `k₁` is supplied below by the integration-by-parts identity.
  obtain ⟨Am1, hAm1, ρm1, hρm1, Hm1⟩ := hS
  obtain ⟨A1p, hA1p, ρ1p, hρ1p, H1p⟩ := hT
  obtain ⟨A00, hA00, ρ00, hρ00, H00⟩ := hZ
  obtain ⟨Bb, hBbpos, Cw, hCwpos, hWb⟩ := MdlWeightVarBound P (by omega) r hr1
  obtain ⟨K₀, hK₀⟩ := exists_pow_ge Bb
  -- the combined constants
  let A : ℝ := max (max Am1 A1p) A00
  have hAm1A : Am1 ≤ A := le_trans (le_max_left _ _) (le_max_left _ _)
  have hA1pA : A1p ≤ A := le_trans (le_max_right Am1 A1p) (le_max_left _ _)
  have hA00A : A00 ≤ A := le_max_right _ _
  have hA0 : 0 ≤ A := le_trans hA00 hA00A
  -- The gain rate is *chosen*, not inherited from the slice estimates (which carry none): the
  -- identity (i) of `MdlDecayHighLowB` produces the factor `2^{-1·k₁}`, and the loss weight is
  -- absorbed into the gain `2^{-cF·k₁}` with any `cF ≤ 1/2` (`lossWeight_absorb_large_nogain`).
  let cF : ℝ := 1 / 4
  have hcFpos : 0 < cF := by norm_num [cF]
  have hcF_le_half : cF ≤ 1 / 2 := by norm_num [cF]
  let ρ₀ : ℝ := min (min (min ρm1 ρ1p) ρ00) (min (1 / (4 * (A + 1))) 1)
  have hρ0pos : 0 < ρ₀ := by
    dsimp only [ρ₀]
    exact lt_min (lt_min (lt_min hρm1 hρ1p) hρ00)
      (lt_min (div_pos zero_lt_one (by positivity)) zero_lt_one)
  refine ⟨cF, hcFpos, ρ₀, hρ0pos, fun ρ hρ hρle => ?_⟩
  have hρS : ρ ≤ min (min ρm1 ρ1p) ρ00 := le_trans hρle (min_le_left _ _)
  have hρm1' : ρ ≤ ρm1 := le_trans hρS (le_trans (min_le_left _ _) (min_le_left _ _))
  have hρ1p' : ρ ≤ ρ1p := le_trans hρS (le_trans (min_le_left _ _) (min_le_right _ _))
  have hρ00' : ρ ≤ ρ00 := le_trans hρS (min_le_right _ _)
  have hρd : ρ ≤ 1 / (4 * (A + 1)) :=
    le_trans hρle (le_trans (min_le_right _ _) (min_le_left _ _))
  have hρA : 4 * ρ * (A + 1) ≤ 1 := by
    have h4 : (0 : ℝ) < 4 * (A + 1) := by positivity
    rw [le_div_iff₀ h4] at hρd
    linarith
  obtain ⟨Km1, hKm1⟩ := Hm1 ρ hρ hρm1'
  obtain ⟨K1p, hK1p⟩ := H1p ρ hρ hρ1p'
  obtain ⟨K00, hK00⟩ := H00 ρ hρ hρ00'
  obtain ⟨Ca, hCapos, hCa⟩ :=
    lossWeight_absorb_large_nogain A 1 ρ hA0 (by norm_num) hρ hρA
  have hK₀nn : (0 : ℝ) ≤ (K₀ : ℝ) := by positivity
  obtain ⟨Cs, hCspos, hCs⟩ :=
    lossWeight_absorb_small_nogain A cF ρ (K₀ : ℝ) hA0 hρ.le hK₀nn
  let ιb : ℝ := max 1 ‖mdlIota‖
  have hιb1 : 1 ≤ ιb := le_max_left 1 ‖mdlIota‖
  let Kfac : ℝ := 4 * ιb * (2 * Cw + 1) + 2
  have hKfacpos : 0 < Kfac := by dsimp only [Kfac]; positivity
  let Ks : NNReal → NNReal := fun Λ => max (Km1 Λ) (K1p Λ)
  have hKs1 : ∀ Λ, Km1 Λ ≤ Ks Λ := fun Λ => le_max_left _ _
  have hKs2 : ∀ Λ, K1p Λ ≤ Ks Λ := fun Λ => le_max_right _ _
  let Kfun : NNReal → NNReal := fun Λ =>
    ⟨(Ks Λ : ℝ) * Kfac * Ca + (K00 Λ : ℝ) * Cs + 1, by positivity⟩
  have hKval : ∀ Λ, ((Kfun Λ : NNReal) : ENNReal)
      = ENNReal.ofReal ((Ks Λ : ℝ) * Kfac * Ca + (K00 Λ : ℝ) * Cs + 1) :=
    fun Λ => ENNReal.ofReal_coe_nnreal.symm
  refine ⟨Kfun, ?_⟩
  intro a Λ l₁ l₂ k₁ f g hΛ hlac ha1 hklt
  have hk1 : 1 ≤ k₁ := by omega
  have hk1ne : k₁ ≠ 0 := by omega
  have hN : ∀ n : ℕ, 1 ≤ Nat.floor (a n) := fun n => Nat.le_floor (by exact_mod_cast ha1 n)
  -- the right-hand side factors are non-zero
  have hKne : ((Kfun Λ : NNReal) : ENNReal) ≠ 0 := by
    rw [hKval Λ, ENNReal.ofReal_ne_zero_iff]
    have h1 : (0 : ℝ) ≤ (Ks Λ : ℝ) * Kfac * Ca :=
      mul_nonneg (mul_nonneg (by positivity) hKfacpos.le) hCapos.le
    have h2 : (0 : ℝ) ≤ (K00 Λ : ℝ) * Cs := mul_nonneg (by positivity) hCspos.le
    linarith
  have hlwne : ENNReal.ofReal (lcWeight cF l₁ l₂ k₁ 0) ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff, lcWeight]
    exact Real.rpow_pos_of_pos (by norm_num) _
  -- degenerate cases
  rcases eq_or_ne (eLpNorm f 2 Measure.count) ⊤ with hfT | hfT
  · rcases eq_or_ne (eLpNorm g 2 Measure.count) 0 with hg0 | hg0
    · have hgz : g = 0 := eq_zero_of_eLpNorm_two_eq_zero hg0
      have hpart0 : mdlPart ρ P C₀ a f g l₁ l₂ k₁ 0 = 0 := by
        rw [hgz, ← mdlPartJ_zero_zero]
        exact mdlPartJ_eq_zero_of_right_zero ρ P C₀ a f l₁ l₂ k₁ 0 0 0
      have hlhs : eLpNorm (fun x : ℤ => variationalNorm r
          (fun n : ℕ => mdlPart ρ P C₀ a f g l₁ l₂ k₁ 0 n x)) 1 Measure.count = 0 := by
        rw [hpart0]
        simpa using eLpNorm_variationalNorm_zero hr1
      rw [hlhs]
      exact bot_le
    · have htop : ((Kfun Λ : NNReal) : ENNReal) * ENNReal.ofReal (lcWeight cF l₁ l₂ k₁ 0)
          * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count = ⊤ := by
        rw [hfT, ENNReal.mul_top (mul_ne_zero hKne hlwne), ENNReal.top_mul hg0]
      rw [htop]
      exact le_top
  rcases eq_or_ne (eLpNorm g 2 Measure.count) ⊤ with hgT | hgT
  · rcases eq_or_ne (eLpNorm f 2 Measure.count) 0 with hf0 | hf0
    · have hfz : f = 0 := eq_zero_of_eLpNorm_two_eq_zero hf0
      have hpart0 : mdlPart ρ P C₀ a f g l₁ l₂ k₁ 0 = 0 := by
        rw [hfz, ← mdlPartJ_zero_zero]
        exact mdlPartJ_eq_zero_of_left_zero ρ P C₀ a g l₁ l₂ k₁ 0 0 0
      have hlhs : eLpNorm (fun x : ℤ => variationalNorm r
          (fun n : ℕ => mdlPart ρ P C₀ a f g l₁ l₂ k₁ 0 n x)) 1 Measure.count = 0 := by
        rw [hpart0]
        simpa using eLpNorm_variationalNorm_zero hr1
      rw [hlhs]
      exact bot_le
    · have htop : ((Kfun Λ : NNReal) : ENNReal) * ENNReal.ofReal (lcWeight cF l₁ l₂ k₁ 0)
          * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count = ⊤ := by
        rw [hgT, ENNReal.mul_top (mul_ne_zero (mul_ne_zero hKne hlwne) hf0)]
      rw [htop]
      exact le_top
  -- main case: f, g ∈ ℓ²
  have hf2 : MemLp f 2 Measure.count := memLp_two_count_of_ne_top hfT
  have hg2 : MemLp g 2 Measure.count := memLp_two_count_of_ne_top hgT
  have hsumf : Summable (fun y : ℤ => ‖f y‖ ^ 2) := summable_norm_sq_of_memLp hf2
  have hsumg : Summable (fun y : ℤ => ‖g y‖ ^ 2) := summable_norm_sq_of_memLp hg2
  rcases lt_or_ge K₀ k₁ with hbig | hsmall
  · -- ################ LARGE CASE ################
    have hcore_pow : ∀ n : ℕ, mdlCore ρ C₀ a l₁ l₂ k₁ 0 n → 2 ^ k₁ ≤ Nat.floor (a n) := by
      intro n hn
      have hmain := ((mdlCore_iff ρ C₀ a l₁ l₂ k₁ 0 n).mp hn).2.2
      have hlog : k₁ ≤ (logN (Nat.floor (a n))).toNat := by
        unfold Work.KMTAreas.A7.mainRegime at hmain
        exact le_trans (Nat.le_add_right k₁ (2 * uScale ρ (max k₁ 0))) hmain.1
      have hlog2 : k₁ ≤ Nat.log 2 (max (Nat.floor (a n)) 2) := by
        simpa [Work.Analysis.EndVar.logN] using hlog
      have hp := Nat.pow_le_of_le_log (b := 2) (x := k₁)
        (y := max (Nat.floor (a n)) 2) (by positivity) hlog2
      have h2le : 2 ≤ Work.KMTAreas.A7.splitCut ρ k₁ := by
        rw [Work.KMTAreas.A7.splitCut]
        have h1 : 1 ≤ 2 ^ Work.Analysis.EndVar.scaleCount 1 ρ k₁ := by
          have hpos := Nat.pow_pos (n := Work.Analysis.EndVar.scaleCount 1 ρ k₁)
            (by norm_num : (0 : ℕ) < 2)
          omega
        calc (2 : ℕ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (2 ^ Work.Analysis.EndVar.scaleCount 1 ρ k₁) :=
              Nat.pow_le_pow_right (by norm_num) h1
      have hcut := ((mdlCore_iff ρ C₀ a l₁ l₂ k₁ 0 n).mp hn).2.1
      have hlc : lcL l₁ l₂ k₁ 0 = k₁ := by
        rw [lcL, max_eq_left (Nat.zero_le k₁), max_eq_right (le_of_lt hklt)]
      rw [hlc] at hcut
      have hN2 : 2 ≤ Nat.floor (a n) := le_of_lt (lt_of_le_of_lt h2le hcut)
      rwa [max_eq_left hN2] at hp
    have hNbound : ∀ n : ℕ, mdlCore ρ C₀ a l₁ l₂ k₁ 0 n →
        Bb ≤ ((Nat.floor (a n) : ℕ) : ℝ) := by
      intro n hn
      have h2 : Bb ≤ (2 : ℝ) ^ k₁ :=
        le_trans hK₀ (pow_le_pow_right₀ (by norm_num) (le_of_lt hbig))
      have h3 : (2 : ℝ) ^ k₁ ≤ ((Nat.floor (a n) : ℕ) : ℝ) := by
        have hp := hcore_pow n hn
        push_cast
        exact_mod_cast hp
      linarith
    have hthr : ∀ n : ℕ, mdlCore ρ C₀ a l₁ l₂ k₁ 0 n →
        Bb ≤ ((Nat.floor (a n) : ℕ) : ℝ) := hNbound
    -- the three families and the two scalars of the identity
    obtain ⟨F1, hF1⟩ : ∃ Y : ℕ → ℤ → ℂ, Y = (fun n x =>
        mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ 0 (-1) 0 1 n x) := ⟨_, rfl⟩
    obtain ⟨F2, hF2⟩ : ∃ Y : ℕ → ℤ → ℂ, Y = (fun n x =>
        mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ 0 (-1) 0 (1 / 2) n x) := ⟨_, rfl⟩
    obtain ⟨F3, hF3⟩ : ∃ Y : ℕ → ℤ → ℂ, Y = (fun n x =>
        mdlWInt ρ P C₀ a f g l₁ l₂ k₁ 0 (-1) 1
          (fun n t => mdlW3 P (Nat.floor (a n)) t) n x) := ⟨_, rfl⟩
    obtain ⟨Z0, hZ0⟩ : ∃ Y : ℕ → ℤ → ℂ, Y = (fun (_ : ℕ) (_ : ℤ) => (0 : ℂ)) := ⟨_, rfl⟩
    obtain ⟨cs, hcs⟩ : ∃ Y : ℂ, Y = ((mdlScaleF k₁ : ℝ) : ℂ) * mdlIota := ⟨_, rfl⟩
    obtain ⟨cg, hcg⟩ : ∃ Y : ℂ, Y = ((mdlScaleFG P k₁ 0 : ℝ) : ℂ) := ⟨_, rfl⟩
    have hid : mdlPart ρ P C₀ a f g l₁ l₂ k₁ 0 = fun n x =>
        cs * (F1 n x - F2 n x) - cg * F3 n x + cs * Z0 n x := by
      rw [hcs, hcg, hF1, hF2, hF3, hZ0]
      rw [← mdlPartJ_zero_zero]
      have h := MdlDecayHighLowB ρ P C₀ a f g l₁ l₂ k₁ hk1 (∑' y : ℤ, ‖f y‖ ^ 2)
        (∑' y : ℤ, ‖g y‖ ^ 2) (normSq_le_tsum_norm_sq hsumf)
        (normSq_le_tsum_norm_sq hsumg) hN
      rw [h]
      simp only [mdlSliceW_one_eq_mdlSliceJ']
      funext n x
      ring
    -- the coefficient bounds
    have hcs_norm : ‖cs‖ ≤ (2 : ℝ) ^ (-(k₁ : ℝ)) * ιb := by
      have h1 : ‖(((mdlScaleF k₁ : ℝ)) : ℂ)‖ = (2 : ℝ) ^ (-(k₁ : ℝ)) := by
        rw [norm_ofReal_complex', mdlScaleF,
          abs_of_nonneg (Real.rpow_pos_of_pos (by norm_num) _).le]
      calc ‖cs‖ = ‖(((mdlScaleF k₁ : ℝ)) : ℂ) * mdlIota‖ := by rw [hcs]
        _ ≤ ‖(((mdlScaleF k₁ : ℝ)) : ℂ)‖ * ‖mdlIota‖ := norm_mul_le _ _
        _ = (2 : ℝ) ^ (-(k₁ : ℝ)) * ‖mdlIota‖ := by rw [h1]
        _ ≤ (2 : ℝ) ^ (-(k₁ : ℝ)) * ιb :=
            mul_le_mul_of_nonneg_left (le_max_right 1 ‖mdlIota‖)
              (Real.rpow_pos_of_pos (by norm_num) _).le
    have hcg_norm : ‖cg‖ ≤ (2 : ℝ) ^ (-(k₁ : ℝ)) * ιb := by
      have hge : mdlScaleFG P k₁ 0 = (2 : ℝ) ^ (-(k₁ : ℝ)) := by
        rw [mdlScaleFG]
        congr 1
        ring
      have h1 : ‖(((mdlScaleFG P k₁ 0 : ℝ)) : ℂ)‖ = (2 : ℝ) ^ (-(k₁ : ℝ)) := by
        rw [norm_ofReal_complex', hge,
          abs_of_nonneg (Real.rpow_pos_of_pos (by norm_num) _).le]
      calc ‖cg‖ = ‖(((mdlScaleFG P k₁ 0 : ℝ)) : ℂ)‖ := by rw [hcg]
        _ = (2 : ℝ) ^ (-(k₁ : ℝ)) := h1
        _ ≤ (2 : ℝ) ^ (-(k₁ : ℝ)) * ιb :=
            le_mul_of_one_le_right (Real.rpow_pos_of_pos (by norm_num) _).le hιb1
    -- the bookkeeping constants: `L0` is the *loss weight alone* (the slice bounds carry no
    -- arithmetic gain in `max l₁ l₂`; the decay in `k₁` is produced by `D` below)
    obtain ⟨L0, hL0⟩ : ∃ Y : ℝ, Y = lossWeight A ρ l₁ l₂ k₁ 0 := ⟨_, rfl⟩
    obtain ⟨D, hD0⟩ : ∃ Y : ENNReal, Y = ENNReal.ofReal ((2 : ℝ) ^ (-(k₁ : ℝ))) := ⟨_, rfl⟩
    obtain ⟨Ccoef, hCC⟩ : ∃ Y : ENNReal, Y = D * ENNReal.ofReal ιb := ⟨_, rfl⟩
    obtain ⟨Nw, hNw0⟩ : ∃ Y : ENNReal, Y = ENNReal.ofReal (2 * Cw + 1) := ⟨_, rfl⟩
    obtain ⟨Bslice, hBs⟩ : ∃ Y : ENNReal, Y = (Ks Λ : ENNReal) * ENNReal.ofReal L0
      * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count := ⟨_, rfl⟩
    have hNw1 : 1 ≤ Nw := by
      rw [hNw0]
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (by linarith [hCwpos])
    have hιb0 : 0 ≤ ιb := le_trans zero_le_one hιb1
    have hCtop : Ccoef ≠ ⊤ := by
      rw [hCC, hD0]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    have hcs_bd : ‖cs‖ₑ ≤ Ccoef := by
      rw [enorm_eq_ofReal_norm']
      refine (ENNReal.ofReal_le_ofReal hcs_norm).trans ?_
      rw [hCC, hD0]
      rw [ENNReal.ofReal_mul (Real.rpow_pos_of_pos (by norm_num) _).le]
    have hcg_bd : ‖cg‖ₑ ≤ Ccoef := by
      rw [enorm_eq_ofReal_norm']
      refine (ENNReal.ofReal_le_ofReal hcg_norm).trans ?_
      rw [hCC, hD0]
      rw [ENNReal.ofReal_mul (Real.rpow_pos_of_pos (by norm_num) _).le]
    have h2Cw : (2 : ENNReal) * ENNReal.ofReal Cw ≤ Nw := by
      have h2w : (2 : ENNReal) * ENNReal.ofReal Cw = ENNReal.ofReal (Cw + Cw) := by
        rw [two_mul, ← ENNReal.ofReal_add hCwpos.le hCwpos.le]
      rw [h2w]
      rw [hNw0]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    -- comparison of a slice bound with `Bslice`
    have hcmp : ∀ (K' : NNReal) (_ : K' ≤ Ks Λ) (A' : ℝ) (_ : A' ≤ A),
        (K' : ENNReal) * ENNReal.ofReal (lossWeight A' ρ l₁ l₂ k₁ 0)
          * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count ≤ Bslice := by
      intro K' hK' A' hA'
      have hof : ENNReal.ofReal (lossWeight A' ρ l₁ l₂ k₁ 0) ≤ ENNReal.ofReal L0 := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hL0]
        exact lossWeight_le_of_le_A hA' hρ.le l₁ l₂ k₁ 0
      have hK'' : (K' : ENNReal) ≤ ((Ks Λ : NNReal) : ENNReal) := by exact_mod_cast hK'
      have hmid : (K' : ENNReal) * ENNReal.ofReal (lossWeight A' ρ l₁ l₂ k₁ 0)
          ≤ ((Ks Λ : NNReal) : ENNReal) * ENNReal.ofReal L0 :=
        mul_le_mul hK'' hof (by positivity) (by positivity)
      calc (K' : ENNReal) * ENNReal.ofReal (lossWeight A' ρ l₁ l₂ k₁ 0)
            * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count
          ≤ (((Ks Λ : NNReal) : ENNReal) * ENNReal.ofReal L0)
              * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count :=
            mul_le_mul (mul_le_mul hmid le_rfl (by positivity) (by positivity)) le_rfl
              (by positivity) (by positivity)
        _ = Bslice := by rw [hBs]
    -- the three slice bounds
    have hslice1 : eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => F1 n x))
        1 Measure.count ≤ Nw * Bslice := by
      have h1 := hKm1 a Λ l₁ l₂ k₁ 0 1 f g hΛ hlac ha1 (by norm_num)
        (fun h => absurd h hk1ne) (fun _ => by norm_num) hf2 hg2
      have hEq : (fun x : ℤ => variationalNorm r (fun n : ℕ => F1 n x))
          = (fun x : ℤ => variationalNorm r (fun n : ℕ =>
              mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ 0 (-1) 0 1 n x)) := by
        rw [hF1]
      rw [hEq]
      exact (h1.trans (hcmp (Km1 Λ) (hKs1 Λ) Am1 hAm1A)).trans
        (le_mul_of_one_le_left (show (0 : ENNReal) ≤ Bslice from bot_le) hNw1)
    have hslice2 : eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => F2 n x))
        1 Measure.count ≤ Nw * Bslice := by
      have h1 := hKm1 a Λ l₁ l₂ k₁ 0 (1 / 2) f g hΛ hlac ha1 (by norm_num)
        (fun h => absurd h hk1ne) (fun _ => by norm_num) hf2 hg2
      have hEq : (fun x : ℤ => variationalNorm r (fun n : ℕ => F2 n x))
          = (fun x : ℤ => variationalNorm r (fun n : ℕ =>
              mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ 0 (-1) 0 (1 / 2) n x)) := by
        rw [hF2]
      rw [hEq]
      exact (h1.trans (hcmp (Km1 Λ) (hKs1 Λ) Am1 hAm1A)).trans
        (le_mul_of_one_le_left (show (0 : ENNReal) ≤ Bslice from bot_le) hNw1)
    have hslice3 : eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => F3 n x))
        1 Measure.count ≤ Nw * Bslice := by
      have hEqF : F3 = mdlWIntF (fun n t => mdlW3 P (Nat.floor (a n)) t)
          (fun t n x => mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ 0 (-1) 1 t n x) := by
        rw [hF3]
        exact mdlWInt_eq_mdlWIntF ρ P C₀ a f g l₁ l₂ k₁ 0 (-1) 1
          (fun n t => mdlW3 P (Nat.floor (a n)) t)
      rw [hEqF]
      refine mdlWIntF_norm_le (r := r) hr1 _ _ ?_ ?_ ?_
      · intro n x
        exact ((mdl_W3_continuous P (Nat.floor (a n))).measurable).mul
          (MdlSliceMeasurable ρ P C₀ a f g l₁ l₂ k₁ 0 (-1) 1 n x)
      · intro n x
        by_cases hn : mdlCore ρ C₀ a l₁ l₂ k₁ 0 n
        · obtain ⟨Cw₃, _hCw₃, hwb⟩ := mdl_W3_bound P (Nat.floor (a n))
          have hYint : Integrable (fun t : ℝ =>
              mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ 0 (-1) 1 t n x)
              (volume.restrict (Set.uIoc (1 / 2 : ℝ) 1)) := by
            have h := MdlSliceIntervalIntegrable ρ P C₀ a f g l₁ l₂ k₁ 0 (-1) 1 n x hf2 hg2
              (fun h => absurd h hk1ne) (fun _ => by norm_num)
            rwa [intervalIntegrable_iff] at h
          rw [intervalIntegrable_iff]
          refine Integrable.bdd_mul (c := Cw₃) hYint
            ((mdl_W3_continuous P (Nat.floor (a n))).measurable.aestronglyMeasurable) ?_
          filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
          exact hwb t (by
            rw [← Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)]
            exact Set.uIoc_subset_uIcc ht)
        · have hzero : (fun t : ℝ => mdlW3 P (Nat.floor (a n)) t
              * mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ 0 (-1) 1 t n x) = fun _ => (0 : ℂ) := by
            funext t
            rw [mdlSliceJ_apply, if_neg hn, mul_zero]
          rw [hzero]
          exact intervalIntegrable_const (μ := volume) (a := (1 / 2 : ℝ)) (b := 1) (c := (0 : ℂ))
      · intro t ht
        have h1 := hK1p a Λ l₁ l₂ k₁ 0 t f g hΛ hlac ha1 ht
          (fun h => absurd h hk1ne) (fun _ => by norm_num) hf2 hg2
        have hw3 : variationalNorm r (fun n : ℕ =>
            if mdlCore ρ C₀ a l₁ l₂ k₁ 0 n then mdlW3 P (Nat.floor (a n)) t else 0)
            ≤ ENNReal.ofReal Cw := (hWb ρ C₀ a Λ l₁ l₂ k₁ 0 t hΛ hlac hthr ht).2.2
        have hmul := eLpNorm_varNorm_mul_le (r := r) hr1 hw3
          (fun n x => mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ 0 (-1) 1 t n x)
        have hEq2 : (fun x : ℤ => variationalNorm r (fun n : ℕ =>
              mdlW3 P (Nat.floor (a n)) t * mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ 0 (-1) 1 t n x))
            = (fun x : ℤ => variationalNorm r (fun n : ℕ =>
              (if mdlCore ρ C₀ a l₁ l₂ k₁ 0 n then mdlW3 P (Nat.floor (a n)) t else 0)
                * mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ 0 (-1) 1 t n x)) := by
          funext x
          congr 1
          funext n
          by_cases hn : mdlCore ρ C₀ a l₁ l₂ k₁ 0 n
          · simp only [if_pos hn]
          · rw [if_neg hn, zero_mul, mdlSliceJ_apply, if_neg hn, mul_zero]
        rw [hEq2]
        have h4 : eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ =>
            mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ 0 (-1) 1 t n x)) 1 Measure.count ≤ Bslice :=
          h1.trans (hcmp (K1p Λ) (hKs2 Λ) A1p hA1pA)
        calc eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ =>
                (if mdlCore ρ C₀ a l₁ l₂ k₁ 0 n then mdlW3 P (Nat.floor (a n)) t else 0)
                  * mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ 0 (-1) 1 t n x)) 1 Measure.count
            ≤ (2 * ENNReal.ofReal Cw) * eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ =>
                mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ 0 (-1) 1 t n x)) 1 Measure.count := hmul
          _ ≤ (2 * ENNReal.ofReal Cw) * Bslice :=
              mul_le_mul_of_nonneg_left h4 (by positivity)
          _ ≤ Nw * Bslice := mul_le_mul_of_nonneg_right h2Cw (by positivity)
    -- the four-term bound
    have hE0 : eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => Z0 n x))
        1 Measure.count ≤ Nw * Bslice := by
      have hz : (fun x : ℤ => variationalNorm r (fun n : ℕ => Z0 n x))
          = (fun _ : ℤ => variationalNorm r (fun _ : ℕ => (0 : ℂ))) := by
        rw [hZ0]
      rw [hz, eLpNorm_variationalNorm_zero hr1]
      exact bot_le
    have hfour := eLpNorm_varNorm_four_le (r := r) hr1 cs cg hCtop hcs_bd hcg_bd F1 F2 F3 Z0
    have hsum : (((eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => F1 n x)) 1 Measure.count
          + eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => F2 n x)) 1 Measure.count)
          + eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => F3 n x)) 1 Measure.count)
          + eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => Z0 n x)) 1 Measure.count)
        ≤ (Nw + Nw + Nw + Nw) * Bslice := by
      have hN' : (Nw + Nw + Nw + Nw) * Bslice
          = ((Nw * Bslice + Nw * Bslice) + Nw * Bslice) + Nw * Bslice := by ring
      rw [hN']
      exact add_le_add (add_le_add (add_le_add hslice1 hslice2) hslice3) hE0
    have hmain_le : eLpNorm (fun x : ℤ => variationalNorm r
          (fun n : ℕ => mdlPart ρ P C₀ a f g l₁ l₂ k₁ 0 n x)) 1 Measure.count
        ≤ Ccoef * ((Nw + Nw + Nw + Nw) * Bslice) := by
      have hid2 : (fun x : ℤ => variationalNorm r
            (fun n : ℕ => mdlPart ρ P C₀ a f g l₁ l₂ k₁ 0 n x))
          = (fun x : ℤ => variationalNorm r (fun n : ℕ =>
              cs * (F1 n x - F2 n x) - cg * F3 n x + cs * Z0 n x)) := by
        funext x
        congr 1
        funext n
        exact congrFun (congrFun hid n) x
      rw [hid2]
      exact hfour.trans (mul_le_mul_of_nonneg_left hsum (by positivity))
    -- the absorption
    have hD : D * ENNReal.ofReal L0
        ≤ ENNReal.ofReal Ca * ENNReal.ofReal (lcWeight cF l₁ l₂ k₁ 0) := by
      have h0 : (2 : ℝ) ^ (-(k₁ : ℝ)) * L0 ≤ Ca * lcWeight cF l₁ l₂ k₁ 0 := by
        have h := hCa l₁ l₂ k₁ hklt
        rw [← lossWeight_zero_swap A ρ l₁ l₂ k₁,
          ← lcWeight_zero_swap (1 / 2) l₁ l₂ k₁] at h
        refine (le_of_eq ?_).trans (h.trans
          (mul_le_mul_of_nonneg_left (lcWeight_le_of_le hcF_le_half l₁ l₂ k₁ 0) hCapos.le))
        rw [hL0]
        ring
      have hDL : D * ENNReal.ofReal L0
          = ENNReal.ofReal ((2 : ℝ) ^ (-(k₁ : ℝ)) * L0) := by
        rw [hD0, ← ENNReal.ofReal_mul (Real.rpow_pos_of_pos (by norm_num) _).le]
      rw [hDL]
      refine (ENNReal.ofReal_le_ofReal h0).trans ?_
      rw [ENNReal.ofReal_mul hCapos.le]
    have habs : ENNReal.ofReal ιb * (Nw + Nw + Nw + Nw) ≤ ENNReal.ofReal Kfac := by
      have hsumNw : Nw + Nw + Nw + Nw = ENNReal.ofReal (4 * (2 * Cw + 1)) := by
        rw [hNw0]
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
      rw [hsumNw, ← ENNReal.ofReal_mul hιb0]
      refine ENNReal.ofReal_le_ofReal ?_
      have he : ιb * (4 * (2 * Cw + 1)) = 4 * ιb * (2 * Cw + 1) := by ring
      rw [he]
      dsimp only [Kfac]
      linarith
    -- the final assembly
    have hfinal : eLpNorm (fun x : ℤ => variationalNorm r
          (fun n : ℕ => mdlPart ρ P C₀ a f g l₁ l₂ k₁ 0 n x)) 1 Measure.count
        ≤ ((Kfun Λ : NNReal) : ENNReal) * ENNReal.ofReal (lcWeight cF l₁ l₂ k₁ 0)
          * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count := by
      have hcoef : ENNReal.ofReal Kfac * (Ks Λ : ENNReal) * ENNReal.ofReal Ca
          ≤ ((Kfun Λ : NNReal) : ENNReal) := by
        have h1 : ENNReal.ofReal Kfac * (Ks Λ : ENNReal) * ENNReal.ofReal Ca
            = ENNReal.ofReal (Kfac * (Ks Λ : ℝ) * Ca) := by
          rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ Kfac * (Ks Λ : ℝ))]
          rw [ENNReal.ofReal_mul hKfacpos.le]
          rw [ENNReal.ofReal_coe_nnreal]
        rw [h1, hKval Λ]
        refine ENNReal.ofReal_le_ofReal ?_
        have h2 : (0 : ℝ) ≤ (K00 Λ : ℝ) * Cs := mul_nonneg (by positivity) hCspos.le
        have h3 : Kfac * (Ks Λ : ℝ) * Ca = (Ks Λ : ℝ) * Kfac * Ca := by ring
        rw [h3]
        linarith
      have hE1 : Ccoef * ((Nw + Nw + Nw + Nw) * Bslice)
          = (((ENNReal.ofReal ιb * (Nw + Nw + Nw + Nw))
              * ((Ks Λ : ENNReal) * (D * ENNReal.ofReal L0)))
              * eLpNorm f 2 Measure.count) * eLpNorm g 2 Measure.count := by
        rw [hCC, hBs]
        ring
      have hA : ((ENNReal.ofReal ιb * (Nw + Nw + Nw + Nw))
              * ((Ks Λ : ENNReal) * (D * ENNReal.ofReal L0)))
            ≤ (ENNReal.ofReal Kfac) * ((Ks Λ : ENNReal) * (D * ENNReal.ofReal L0)) :=
        mul_le_mul_of_nonneg_right habs
          (show (0 : ENNReal) ≤ (Ks Λ : ENNReal) * (D * ENNReal.ofReal L0) from bot_le)
      have hB : (ENNReal.ofReal Kfac) * ((Ks Λ : ENNReal) * (D * ENNReal.ofReal L0))
            ≤ (ENNReal.ofReal Kfac) * ((Ks Λ : ENNReal)
              * (ENNReal.ofReal Ca * ENNReal.ofReal (lcWeight cF l₁ l₂ k₁ 0))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hD (show (0 : ENNReal) ≤ (Ks Λ : ENNReal) from bot_le))
          (show (0 : ENNReal) ≤ ENNReal.ofReal Kfac from bot_le)
      have hC : (ENNReal.ofReal Kfac) * ((Ks Λ : ENNReal)
              * (ENNReal.ofReal Ca * ENNReal.ofReal (lcWeight cF l₁ l₂ k₁ 0)))
            = ((ENNReal.ofReal Kfac * (Ks Λ : ENNReal) * ENNReal.ofReal Ca)
              * ENNReal.ofReal (lcWeight cF l₁ l₂ k₁ 0)) := by ring
      have hDc : ((ENNReal.ofReal Kfac * (Ks Λ : ENNReal) * ENNReal.ofReal Ca)
              * ENNReal.ofReal (lcWeight cF l₁ l₂ k₁ 0))
            ≤ (((Kfun Λ : NNReal) : ENNReal)
              * ENNReal.ofReal (lcWeight cF l₁ l₂ k₁ 0)) :=
        mul_le_mul_of_nonneg_right hcoef
          (show (0 : ENNReal) ≤ ENNReal.ofReal (lcWeight cF l₁ l₂ k₁ 0) from bot_le)
      have hmain : ((ENNReal.ofReal ιb * (Nw + Nw + Nw + Nw))
              * ((Ks Λ : ENNReal) * (D * ENNReal.ofReal L0)))
            ≤ (((Kfun Λ : NNReal) : ENNReal)
              * ENNReal.ofReal (lcWeight cF l₁ l₂ k₁ 0)) :=
        hA.trans (hB.trans ((le_of_eq hC).trans hDc))
      have hchain : ((ENNReal.ofReal ιb * (Nw + Nw + Nw + Nw))
              * ((Ks Λ : ENNReal) * (D * ENNReal.ofReal L0)))
              * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count
            ≤ ((((Kfun Λ : NNReal) : ENNReal)
              * ENNReal.ofReal (lcWeight cF l₁ l₂ k₁ 0))
              * eLpNorm f 2 Measure.count) * eLpNorm g 2 Measure.count :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmain
          (show (0 : ENNReal) ≤ eLpNorm f 2 Measure.count from bot_le))
          (show (0 : ENNReal) ≤ eLpNorm g 2 Measure.count from bot_le)
      refine hmain_le.trans ?_
      rw [hE1]
      exact hchain
    exact hfinal
  · -- ################ SMALL CASE ################
    have hkK : (k₁ : ℝ) ≤ (K₀ : ℝ) := by exact_mod_cast hsmall
    -- the `t`-integration of the loss-form frozen-slice bound (the interval has length `1/2`)
    have hEqPart : mdlWIntF (fun _ _ => (1 : ℂ))
          (fun t n x => mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ 0 0 0 t n x)
        = mdlPart ρ P C₀ a f g l₁ l₂ k₁ 0 := by
      rw [← mdlWInt_eq_mdlWIntF ρ P C₀ a f g l₁ l₂ k₁ 0 0 0 (fun _ _ => (1 : ℂ)),
        mdlWInt_one_eq_mdlPartJ, ← mdlPartJ_zero_zero]
    have h00 : eLpNorm (fun x : ℤ => variationalNorm r
          (fun n : ℕ => mdlPart ρ P C₀ a f g l₁ l₂ k₁ 0 n x)) 1 Measure.count
        ≤ (K00 Λ : ENNReal) * ENNReal.ofReal (lossWeight A00 ρ l₁ l₂ k₁ 0)
          * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count := by
      rw [← hEqPart]
      refine mdlWIntF_norm_le (r := r) hr1 (fun _ _ => (1 : ℂ))
        (fun t n x => mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ 0 0 0 t n x) ?_ ?_ ?_
      · intro n x
        simpa only [one_mul] using MdlSliceMeasurable ρ P C₀ a f g l₁ l₂ k₁ 0 0 0 n x
      · intro n x
        simpa only [one_mul] using
          MdlSliceIntervalIntegrable ρ P C₀ a f g l₁ l₂ k₁ 0 0 0 n x hf2 hg2
            (fun _ => by norm_num) (fun _ => by norm_num)
      · intro t ht
        have h := hK00 a Λ l₁ l₂ k₁ 0 t f g hΛ hlac ha1 ht (fun _ => by norm_num)
          (fun _ => by norm_num) hf2 hg2
        simpa only [one_mul] using h
    refine h00.trans ?_
    have hW1 : ENNReal.ofReal (lossWeight A00 ρ l₁ l₂ k₁ 0)
        ≤ ENNReal.ofReal (lossWeight A ρ l₁ l₂ k₁ 0) :=
      ENNReal.ofReal_le_ofReal (lossWeight_le_of_le_A hA00A hρ.le l₁ l₂ k₁ 0)
    have hW2 : ENNReal.ofReal (lossWeight A ρ l₁ l₂ k₁ 0)
        ≤ ENNReal.ofReal (Cs * lcWeight cF l₁ l₂ k₁ 0) := by
      refine ENNReal.ofReal_le_ofReal ?_
      rw [lossWeight_zero_swap A ρ l₁ l₂ k₁, lcWeight_zero_swap cF l₁ l₂ k₁]
      exact hCs l₁ l₂ k₁ hklt hkK
    have hfac : ENNReal.ofReal Cs * ENNReal.ofReal (lcWeight cF l₁ l₂ k₁ 0)
        = ENNReal.ofReal (Cs * lcWeight cF l₁ l₂ k₁ 0) := (ENNReal.ofReal_mul hCspos.le).symm
    have hE2 : ENNReal.ofReal ((K00 Λ : ℝ) * Cs) * ENNReal.ofReal (lcWeight cF l₁ l₂ k₁ 0)
        = (K00 Λ : ENNReal) * ENNReal.ofReal (Cs * lcWeight cF l₁ l₂ k₁ 0) := by
      rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (K00 Λ : ℝ))]
      rw [ENNReal.ofReal_coe_nnreal]
      rw [← hfac]
      ring
    have hcoef2 : ENNReal.ofReal ((K00 Λ : ℝ) * Cs) ≤ ((Kfun Λ : NNReal) : ENNReal) := by
      rw [hKval Λ]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : (0 : ℝ) ≤ (Ks Λ : ℝ) * Kfac * Ca :=
        mul_nonneg (mul_nonneg (by positivity) hKfacpos.le) hCapos.le
      linarith
    calc (K00 Λ : ENNReal) * ENNReal.ofReal (lossWeight A00 ρ l₁ l₂ k₁ 0)
            * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count
        ≤ (K00 Λ : ENNReal) * ENNReal.ofReal (lossWeight A ρ l₁ l₂ k₁ 0)
            * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hW1
              (show (0 : ENNReal) ≤ (K00 Λ : ENNReal) from bot_le))
            (show (0 : ENNReal) ≤ eLpNorm f 2 Measure.count from bot_le))
            (show (0 : ENNReal) ≤ eLpNorm g 2 Measure.count from bot_le)
      _ ≤ (K00 Λ : ENNReal) * ENNReal.ofReal (Cs * lcWeight cF l₁ l₂ k₁ 0)
            * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hW2
              (show (0 : ENNReal) ≤ (K00 Λ : ENNReal) from bot_le))
            (show (0 : ENNReal) ≤ eLpNorm f 2 Measure.count from bot_le))
            (show (0 : ENNReal) ≤ eLpNorm g 2 Measure.count from bot_le)
      _ = ENNReal.ofReal ((K00 Λ : ℝ) * Cs) * ENNReal.ofReal (lcWeight cF l₁ l₂ k₁ 0)
            * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count := by
          rw [hE2]
      _ ≤ ((Kfun Λ : NNReal) : ENNReal) * ENNReal.ofReal (lcWeight cF l₁ l₂ k₁ 0)
            * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hcoef2
              (show (0 : ENNReal) ≤ ENNReal.ofReal (lcWeight cF l₁ l₂ k₁ 0) from bot_le))
            (show (0 : ENNReal) ≤ eLpNorm f 2 Measure.count from bot_le))
            (show (0 : ENNReal) ≤ eLpNorm g 2 Measure.count from bot_le)

/-- **The target of this file**: the high-low (`k₂ = 0 < k₁`) branch of the large-scale model
estimate, obtained from the conditional form `MdlPartHighLowGainV2_of_sliceGain` and the three
*loss-form* (no-gain) instances of the frozen-`t` slice estimate supplied by the PROVED and
axiom-clean `Work.KMTPlan.A6LH.MdlSliceNoGainAtProved`.

The whole decay in `k₁` comes from the integration-by-parts identity (i) (`MdlDecayHighLowB`) and
the loss absorption `lossWeight_absorb_{large,small}_nogain`; the deep gain-form input
`MdlSliceCoreGainBig` (the paper's Theorem `model-est-2` at `(2,2,1)`) is **not** used, so this
theorem is axiom-clean. -/
theorem MdlPartHighLowGainV2 (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (r : NNReal) (hr : 2 < r)
    (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (hA1 : Work.KMTContract.AreaA1)
    (hI : Work.KMTContract.ImprovKMT P) :
    ∃ c : ℝ, 0 < c ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
      ∃ K : NNReal → NNReal,
        ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ : ℕ) (f g : ℤ → ℂ),
          1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n : ℕ, 1 ≤ a n) →
          max l₁ l₂ < k₁ →
          MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => Work.KMTPlan.A6.mdlPart ρ P C₀ a f g l₁ l₂ k₁ 0 n x))
            1 MeasureTheory.Measure.count
            ≤ ((K Λ : NNReal) : ENNReal) *
                ENNReal.ofReal (Work.KMTPlan.A6.lcWeight c l₁ l₂ k₁ 0) *
                MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count *
                MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count :=
  MdlPartHighLowGainV2_of_sliceGain P hd r hr C₀ hC₀ hA1
    (Work.KMTPlan.A6LH.MdlSliceNoGainAtProved P hd hA1 C₀ hC₀ r hr (-1) 0 (by decide) (by decide))
    (Work.KMTPlan.A6LH.MdlSliceNoGainAtProved P hd hA1 C₀ hC₀ r hr (-1) 1 (by decide) (by decide))
    (Work.KMTPlan.A6LH.MdlSliceNoGainAtProved P hd hA1 C₀ hC₀ r hr 0 0 (by decide) (by decide))

end

end Work.KMTPlan.A6
