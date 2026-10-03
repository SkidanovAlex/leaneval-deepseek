import Mathlib
import Submission.Work.KMTPlan.A6.MdlWeightVarBound
import Submission.Work.KMTPlan.A6.MdlDecayLowHighB
import Submission.Work.KMTPlan.A6LH.MdlSliceNoGainAtProved
import Submission.Work.KMTPlan.A6.PderivThreshold
import Submission.Work.KMTPlan.A6.MdlWIntNormDefs
import Submission.Work.KMTPlan.A6.variationalNorm_prod_le
import Submission.Port.Aesm
-- The frozen-`t` slice estimate is taken from the *loss-form* (no arithmetic gain) bound
-- `Work.KMTPlan.A6LH.MdlSliceNoGainAtProved`; the gain-form crux `MdlSliceCoreGainBig` is no longer
-- needed, because the `k₂`-decay of `MdlDecayLowHighB` already supplies the loss of the target.
-- `MdlCoreGainEstimate` was imported until 2026-10-03 but is *not used* by the proof below: the
-- `(j₁,j₂) = (0,0)` instance is taken from `MdlCoreGain_of_sliceCoreGain` (`MdlCoreGainBook`,
-- which `MdlSliceCoreGainBig` already imports) applied to the same `MdlSliceCoreGainBig` instance.
-- Dropping the import removes the whole `MdlCoreGainEstimate` subtree (and with it the duplicate
-- declaration of `Work.KMTPlan.A6Clean.AdelicFormAtRangeP` in
-- `A6Clean/MdlSliceCoreGainMemLp_of_pieces_rangeP.lean`, which made this module unbuildable).

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators Interval
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.EndVar Work.KMTContract Work.KMTAreas.A7

/-! ## 1. Elementary facts about `eLpNorm` at `p = 1` -/

/-- `eLpNorm` at `p = 1` of a pointwise sum, given the a.e.-measurability of the first summand. -/
lemma eLpNorm_one_add_le' (f g : ℤ → ENNReal) (hf : AEMeasurable f Measure.count) :
    eLpNorm (fun x : ℤ => f x + g x) 1 Measure.count
      ≤ eLpNorm f 1 Measure.count + eLpNorm g 1 Measure.count := by
  rw [eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm), eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm),
    eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm)]
  simp only [enorm_eq_self]
  exact le_of_eq (lintegral_add_left' hf g)

/-- The `eLpNorm` at `p = 1` of an `ℝ≥0∞`-valued function is its integral against `count`. -/
lemma eLpNorm_eq_lintegral (f : ℤ → ENNReal) :
    eLpNorm f 1 Measure.count = ∫⁻ x : ℤ, f x ∂Measure.count := by
  rw [eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm)]
  simp only [enorm_eq_self]

/-- Subadditivity of the `count`-integral of `ℝ≥0∞`-valued functions (four terms). -/
lemma lintegral_add_four_le (f1 f2 f3 f4 : ℤ → ENNReal)
    (h1 : AEMeasurable f1 Measure.count) (h2 : AEMeasurable f2 Measure.count)
    (h3 : AEMeasurable f3 Measure.count) :
    ∫⁻ x : ℤ, (f1 x + f2 x) + (f3 x + f4 x) ∂Measure.count
      ≤ (∫⁻ x : ℤ, f1 x ∂Measure.count + ∫⁻ x : ℤ, f2 x ∂Measure.count)
          + (∫⁻ x : ℤ, f3 x ∂Measure.count + ∫⁻ x : ℤ, f4 x ∂Measure.count) := by
  have ha : AEMeasurable (fun x : ℤ => f1 x + f2 x) Measure.count := h1.add h2
  have e1 : ∫⁻ x : ℤ, (f1 x + f2 x) + (f3 x + f4 x) ∂Measure.count
      = (∫⁻ x : ℤ, (f1 x + f2 x) ∂Measure.count)
        + (∫⁻ x : ℤ, (f3 x + f4 x) ∂Measure.count) := lintegral_add_left' ha _
  have e2 : ∫⁻ x : ℤ, (f1 x + f2 x) ∂Measure.count
      = (∫⁻ x : ℤ, f1 x ∂Measure.count) + (∫⁻ x : ℤ, f2 x ∂Measure.count) :=
    lintegral_add_left' h1 f2
  have e3 : ∫⁻ x : ℤ, (f3 x + f4 x) ∂Measure.count
      = (∫⁻ x : ℤ, f3 x ∂Measure.count) + (∫⁻ x : ℤ, f4 x ∂Measure.count) :=
    lintegral_add_left' h3 f4
  rw [e1, e2, e3]

/-- Homogeneity of the `ℓ¹(ℤ)`-norm of the variational norm under a complex scalar. -/
lemma eLpNorm_varNorm_const_mul (r : ℝ≥0) (hr : 1 ≤ r) (c : ℂ) (Y : ℕ → ℤ → ℂ) :
    eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => c * Y n x)) 1 Measure.count
      = ‖c‖ₑ * eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => Y n x)) 1 Measure.count := by
  have hfun : (fun x : ℤ => variationalNorm r (fun n : ℕ => c * Y n x))
      = (fun x : ℤ => ‖c‖ₑ * variationalNorm r (fun n : ℕ => Y n x)) := by
    funext x
    have hsm : (fun n : ℕ => c * Y n x) = c • (fun n : ℕ => Y n x) := rfl
    rw [hsm]
    exact variationalNorm_smul hr c _
  rw [hfun, eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm), eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm)]
  simp only [enorm_eq_self]
  exact lintegral_const_mul' ‖c‖ₑ (fun x : ℤ => variationalNorm r (fun n : ℕ => Y n x))
    (show ‖c‖ₑ ≠ ∞ from enorm_ne_top)

/-- Subadditivity of the `ℓ¹(ℤ)`-norm of the variational norm. -/
lemma eLpNorm_varNorm_add_le (r : ℝ≥0) (hr : 1 ≤ r) (Y Z : ℕ → ℤ → ℂ) :
    eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => Y n x + Z n x)) 1 Measure.count
      ≤ eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => Y n x)) 1 Measure.count
        + eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => Z n x)) 1 Measure.count := by
  refine (eLpNorm_mono_enorm (hf := by pw_aesm) (f := fun x : ℤ => variationalNorm r (fun n : ℕ => Y n x + Z n x))
    (g := fun x : ℤ => variationalNorm r (fun n : ℕ => Y n x)
      + variationalNorm r (fun n : ℕ => Z n x)) (fun x => ?_)).trans ?_
  · have hfun : (fun n : ℕ => Y n x + Z n x) = (fun n : ℕ => Y n x) + (fun n : ℕ => Z n x) := rfl
    rw [hfun]
    simpa only [enorm_eq_self] using
      variationalNorm_add_le hr (fun n : ℕ => Y n x) (fun n : ℕ => Z n x)
  · rw [eLpNorm_eq_lintegral, eLpNorm_eq_lintegral, eLpNorm_eq_lintegral]
    exact le_of_eq (lintegral_add_left'
      ((measurable_of_countable
        (fun x : ℤ => variationalNorm r (fun n : ℕ => Y n x))).aemeasurable) _)

/-- The variational norm is subadditive for the difference. -/
lemma variationalNorm_sub_le {r : ℝ≥0} (hr : 1 ≤ r) (a b : ℕ → ℂ) :
    variationalNorm r (a - b) ≤ variationalNorm r a + variationalNorm r b := by
  have h : (a - b) = a + (-1 : ℂ) • b := by
    funext n
    simp [sub_eq_add_neg]
  rw [h]
  refine (variationalNorm_add_le hr a _).trans ?_
  rw [variationalNorm_smul hr (-1) b]
  simp

/-- The pointwise `V^r`-bound for the right-hand side of the integration-by-parts identity. -/
lemma variationalNorm_four_le {r : ℝ≥0} (hr : 1 ≤ r) (cs cg : ℂ) (C : ENNReal)
    (hcs : ‖cs‖ₑ ≤ C) (hcg : ‖cg‖ₑ ≤ C) (Y1 Y2 Y3 Y4 : ℕ → ℂ) :
    variationalNorm r (fun n : ℕ => cs * (Y1 n - Y2 n) - cg * Y3 n + cs * Y4 n)
      ≤ C * ((variationalNorm r Y1 + variationalNorm r Y2)
          + (variationalNorm r Y3 + variationalNorm r Y4)) := by
  have h3 : variationalNorm r (fun n : ℕ => cs * (Y1 n - Y2 n))
      ≤ C * (variationalNorm r Y1 + variationalNorm r Y2) := by
    have hsm : (fun n : ℕ => cs * (Y1 n - Y2 n)) = cs • (fun n : ℕ => Y1 n - Y2 n) := rfl
    rw [hsm, variationalNorm_smul hr cs]
    exact (mul_le_mul_of_nonneg_right hcs (by positivity)).trans
      (mul_le_mul_of_nonneg_left (variationalNorm_sub_le hr Y1 Y2) (by positivity))
  have h4 : variationalNorm r (fun n : ℕ => cg * Y3 n) ≤ C * variationalNorm r Y3 := by
    have hsm : (fun n : ℕ => cg * Y3 n) = cg • Y3 := rfl
    rw [hsm, variationalNorm_smul hr cg]
    exact mul_le_mul_of_nonneg_right hcg (by positivity)
  have h5 : variationalNorm r (fun n : ℕ => cs * Y4 n) ≤ C * variationalNorm r Y4 := by
    have hsm : (fun n : ℕ => cs * Y4 n) = cs • Y4 := rfl
    rw [hsm, variationalNorm_smul hr cs]
    exact mul_le_mul_of_nonneg_right hcs (by positivity)
  have h2 : variationalNorm r (fun n : ℕ => cs * (Y1 n - Y2 n) - cg * Y3 n)
      ≤ variationalNorm r (fun n : ℕ => cs * (Y1 n - Y2 n)) + variationalNorm r (fun n : ℕ => cg * Y3 n) :=
    variationalNorm_sub_le hr _ _
  have h1 : variationalNorm r (fun n : ℕ => cs * (Y1 n - Y2 n) - cg * Y3 n + cs * Y4 n)
      ≤ variationalNorm r (fun n : ℕ => cs * (Y1 n - Y2 n) - cg * Y3 n)
        + variationalNorm r (fun n : ℕ => cs * Y4 n) :=
    variationalNorm_add_le hr _ _
  have hEq : C * (variationalNorm r Y1 + variationalNorm r Y2) + C * variationalNorm r Y3
        + C * variationalNorm r Y4
      = C * ((variationalNorm r Y1 + variationalNorm r Y2)
          + (variationalNorm r Y3 + variationalNorm r Y4)) := by
    ring
  calc variationalNorm r (fun n : ℕ => cs * (Y1 n - Y2 n) - cg * Y3 n + cs * Y4 n)
      ≤ variationalNorm r (fun n : ℕ => cs * (Y1 n - Y2 n) - cg * Y3 n)
          + variationalNorm r (fun n : ℕ => cs * Y4 n) := h1
    _ ≤ (variationalNorm r (fun n : ℕ => cs * (Y1 n - Y2 n))
          + variationalNorm r (fun n : ℕ => cg * Y3 n))
          + variationalNorm r (fun n : ℕ => cs * Y4 n) := add_le_add h2 le_rfl
    _ ≤ (C * (variationalNorm r Y1 + variationalNorm r Y2) + C * variationalNorm r Y3)
          + C * variationalNorm r Y4 := add_le_add (add_le_add h3 h4) h5
    _ = C * ((variationalNorm r Y1 + variationalNorm r Y2)
          + (variationalNorm r Y3 + variationalNorm r Y4)) := hEq

/-- The same bound, at the level of the `ℓ¹(ℤ)`-norm of the variational norm. -/
lemma eLpNorm_varNorm_four_le {r : ℝ≥0} (hr : 1 ≤ r) (cs cg : ℂ) {C : ENNReal}
    (hCtop : C ≠ ⊤) (hcs : ‖cs‖ₑ ≤ C) (hcg : ‖cg‖ₑ ≤ C) (Y1 Y2 Y3 Y4 : ℕ → ℤ → ℂ) :
    eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ =>
        cs * (Y1 n x - Y2 n x) - cg * Y3 n x + cs * Y4 n x)) 1 Measure.count
      ≤ C * (((eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => Y1 n x)) 1 Measure.count
              + eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => Y2 n x)) 1 Measure.count)
              + eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => Y3 n x)) 1 Measure.count)
              + eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => Y4 n x)) 1 Measure.count) := by
  have hm1 : AEMeasurable (fun x : ℤ => variationalNorm r (fun n : ℕ => Y1 n x)) Measure.count :=
    (measurable_of_countable
      (fun x : ℤ => variationalNorm r (fun n : ℕ => Y1 n x))).aemeasurable
  have hm2 : AEMeasurable (fun x : ℤ => variationalNorm r (fun n : ℕ => Y2 n x)) Measure.count :=
    (measurable_of_countable
      (fun x : ℤ => variationalNorm r (fun n : ℕ => Y2 n x))).aemeasurable
  have hm3 : AEMeasurable (fun x : ℤ => variationalNorm r (fun n : ℕ => Y3 n x)) Measure.count :=
    (measurable_of_countable
      (fun x : ℤ => variationalNorm r (fun n : ℕ => Y3 n x))).aemeasurable
  refine (eLpNorm_mono_enorm (hf := by pw_aesm) (f := fun x : ℤ => variationalNorm r (fun n : ℕ =>
        cs * (Y1 n x - Y2 n x) - cg * Y3 n x + cs * Y4 n x))
    (g := fun x : ℤ => C * ((variationalNorm r (fun n : ℕ => Y1 n x)
          + variationalNorm r (fun n : ℕ => Y2 n x))
          + (variationalNorm r (fun n : ℕ => Y3 n x)
            + variationalNorm r (fun n : ℕ => Y4 n x)))) (fun x => ?_)).trans ?_
  · simpa only [enorm_eq_self] using
      variationalNorm_four_le hr cs cg C hcs hcg (fun n => Y1 n x) (fun n => Y2 n x)
        (fun n => Y3 n x) (fun n => Y4 n x)
  · rw [eLpNorm_eq_lintegral]
    rw [lintegral_const_mul' C _ hCtop]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hfour := lintegral_add_four_le
      (fun x : ℤ => variationalNorm r (fun n : ℕ => Y1 n x))
      (fun x : ℤ => variationalNorm r (fun n : ℕ => Y2 n x))
      (fun x : ℤ => variationalNorm r (fun n : ℕ => Y3 n x))
      (fun x : ℤ => variationalNorm r (fun n : ℕ => Y4 n x)) hm1 hm2 hm3
    refine hfour.trans ?_
    rw [eLpNorm_eq_lintegral, eLpNorm_eq_lintegral, eLpNorm_eq_lintegral, eLpNorm_eq_lintegral]
    try exact le_of_eq (by ring)

/-- **Weight pull-out for the variational norm**: multiplying a family by a scalar weight family
whose `V^r`-norm is at most `ofReal C` multiplies the `ℓ¹(ℤ;V^r)`-norm by at most `2C`. -/
lemma eLpNorm_varNorm_mul_le (r : ℝ≥0) (hr : 1 ≤ r) {w : ℕ → ℂ} {C : ℝ}
    (hw : variationalNorm r w ≤ ENNReal.ofReal C) (Y : ℕ → ℤ → ℂ) :
    eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => w n * Y n x)) 1 Measure.count
      ≤ ((2 : ENNReal) * ENNReal.ofReal C) *
          eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => Y n x)) 1 Measure.count := by
  have hstep : ∀ x : ℤ, variationalNorm r (fun n : ℕ => w n * Y n x)
      ≤ ((2 : ENNReal) * ENNReal.ofReal C) * variationalNorm r (fun n : ℕ => Y n x) := by
    intro x
    calc variationalNorm r (fun n : ℕ => w n * Y n x)
        ≤ 2 * (variationalNorm r w * variationalNorm r (fun n : ℕ => Y n x)) :=
          variationalNorm_prod_le hr w _
      _ ≤ 2 * (ENNReal.ofReal C * variationalNorm r (fun n : ℕ => Y n x)) := by gcongr
      _ = ((2 : ENNReal) * ENNReal.ofReal C) * variationalNorm r (fun n : ℕ => Y n x) := by
          ring
  refine (eLpNorm_mono_enorm (hf := by pw_aesm) (f := fun x : ℤ => variationalNorm r (fun n : ℕ => w n * Y n x))
    (g := fun x : ℤ => ((2 : ENNReal) * ENNReal.ofReal C) *
      variationalNorm r (fun n : ℕ => Y n x)) (fun x => ?_)).trans ?_
  · simpa only [enorm_eq_self] using hstep x
  · rw [eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm), eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm)]
    simp only [enorm_eq_self]
    exact le_of_eq (lintegral_const_mul' ((2 : ENNReal) * ENNReal.ofReal C)
      (fun x : ℤ => variationalNorm r (fun n : ℕ => Y n x))
      (show ((2 : ENNReal) * ENNReal.ofReal C) ≠ ∞ from
        ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top))

/-- **Minkowski in `t`** for the `t`-integral of a weighted family. -/
lemma mdlWIntF_norm_le (r : ℝ≥0) (hr : 1 ≤ r) (w : ℕ → ℝ → ℂ) (Y : ℝ → ℕ → ℤ → ℂ) {B : ENNReal}
    (hmeas : ∀ (n : ℕ) (x : ℤ), Measurable (fun t : ℝ => w n t * Y t n x))
    (hint : ∀ (n : ℕ) (x : ℤ), IntervalIntegrable (fun t : ℝ => w n t * Y t n x) volume (1 / 2) 1)
    (hbd : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1,
      eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => w n t * Y t n x)) 1 Measure.count
        ≤ B) :
    eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => mdlWIntF w Y n x)) 1 Measure.count
      ≤ B := by
  set s : Set ℝ := Set.uIoc (1 / 2 : ℝ) 1 with hs
  have hle : (1 / 2 : ℝ) ≤ 1 := by norm_num
  -- the pointwise Minkowski step
  have hpt : ∀ x : ℤ, variationalNorm r (fun n : ℕ => mdlWIntF w Y n x)
      ≤ ∫⁻ t in s, variationalNorm r (fun n : ℕ => w n t * Y t n x) := by
    intro x
    refine varNorm_integral_le r hr (fun t n x => w n t * Y t n x) x (fun n => ?_)
      (fun n => hmeas n x)
    simpa only [hs, intervalIntegral.integral_of_le hle, ← Set.uIoc_of_le hle] using hint n x
  have hsec : ∀ x : ℤ, AEMeasurable (fun t : ℝ =>
      variationalNorm r (fun n : ℕ => w n t * Y t n x)) (volume.restrict s) := fun x =>
    (measurable_variationalNorm (lt_of_lt_of_le zero_lt_one hr) (fun n => hmeas n x)).aemeasurable.restrict
  -- the three steps
  have hstep1 : eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => mdlWIntF w Y n x))
      1 Measure.count
      ≤ eLpNorm (fun x : ℤ => ∫⁻ t in s,
          variationalNorm r (fun n : ℕ => w n t * Y t n x)) 1 Measure.count :=
    eLpNorm_mono_enorm (hf := by pw_aesm) (fun x => by simpa only [enorm_eq_self] using hpt x)
  have hstep2 : eLpNorm (fun x : ℤ => ∫⁻ t in s,
        variationalNorm r (fun n : ℕ => w n t * Y t n x)) 1 Measure.count
      = ∫⁻ t in s, eLpNorm (fun x : ℤ => variationalNorm r
          (fun n : ℕ => w n t * Y t n x)) 1 Measure.count := by
    have hleft : eLpNorm (fun x : ℤ => ∫⁻ t in s,
          variationalNorm r (fun n : ℕ => w n t * Y t n x)) 1 Measure.count
        = ∑' x : ℤ, (∫⁻ t in s, variationalNorm r (fun n : ℕ => w n t * Y t n x)) := by
      rw [eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm)]
      simp only [enorm_eq_self]
      rw [lintegral_count]
    have hright : (∫⁻ t in s, eLpNorm (fun x : ℤ => variationalNorm r
          (fun n : ℕ => w n t * Y t n x)) 1 Measure.count)
        = ∫⁻ t in s, ∑' x : ℤ, variationalNorm r (fun n : ℕ => w n t * Y t n x) := by
      refine lintegral_congr_ae ?_
      filter_upwards with t
      rw [eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm)]
      simp only [enorm_eq_self]
      rw [lintegral_count]
    rw [hleft, hright]
    exact (MeasureTheory.lintegral_tsum (f := fun (x : ℤ) (t : ℝ) =>
      variationalNorm r (fun n : ℕ => w n t * Y t n x)) (fun x => hsec x)).symm
  have hstep3 : ∫⁻ t in s, eLpNorm (fun x : ℤ => variationalNorm r
        (fun n : ℕ => w n t * Y t n x)) 1 Measure.count ≤ B := by
    have h1 : ∫⁻ t in s, eLpNorm (fun x : ℤ => variationalNorm r
          (fun n : ℕ => w n t * Y t n x)) 1 Measure.count ≤ ∫⁻ _t in s, B := by
      refine lintegral_mono_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
      exact hbd t (by rw [← Set.uIcc_of_le hle]; exact Set.uIoc_subset_uIcc ht)
    refine h1.trans ?_
    calc ∫⁻ _t in s, B = B * volume s := by
          rw [MeasureTheory.lintegral_const, Measure.restrict_apply_univ]
      _ ≤ B := by
          rw [hs, Real.volume_uIoc]
          have hvv : ENNReal.ofReal |1 - (1 / 2 : ℝ)| ≤ (1 : ENNReal) := by
            rw [show |1 - (1 / 2 : ℝ)| = 1 / 2 by norm_num]
            exact ENNReal.ofReal_le_one.mpr (by norm_num)
          calc B * ENNReal.ofReal |1 - (1 / 2 : ℝ)| ≤ B * 1 :=
                mul_le_mul_of_nonneg_left hvv (by positivity)
            _ = B := mul_one B
  exact hstep1.trans (le_of_eq hstep2 |>.trans hstep3)

/-! ## 2. The weights on the region `max l₁ l₂ < k₂` -/

/-- On `k₁ ≤ k₂` and `max l₁ l₂ < k₂` the index `lmax l₁ l₂ k₁ k₂` is just `k₂`. -/
lemma lmax_eq_self_of_lt_max {l₁ l₂ k₁ k₂ : ℕ} (hk₁ : k₁ ≤ k₂) (hk : max l₁ l₂ < k₂) :
    lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) = (k₂ : ℤ) := by
  have h1 : max (l₁ : ℤ) (l₂ : ℤ) ≤ (k₂ : ℤ) := by
    rw [← Nat.cast_max]
    exact_mod_cast le_of_lt hk
  have hmain : max (max (l₁ : ℤ) (l₂ : ℤ)) (max (k₁ : ℤ) (k₂ : ℤ)) = (k₂ : ℤ) := by omega
  rw [Work.Analysis.EndVar.lmax]
  exact hmain

/-- The loss weight on the region `max l₁ l₂ < k₂`. -/
lemma lossWeight_eq_of_lt_max {A ρ : ℝ} {l₁ l₂ k₁ k₂ : ℕ} (hk₁ : k₁ ≤ k₂)
    (hk : max l₁ l₂ < k₂) :
    lossWeight A ρ l₁ l₂ k₁ k₂ = (1 + (k₂ : ℝ)) ^ A * (2 : ℝ) ^ (A * ρ * (k₂ : ℝ)) := by
  rw [lossWeight, lmaxR, lmax_eq_self_of_lt_max hk₁ hk, Int.cast_natCast]

/-- The gain weight on the region `max l₁ l₂ < k₂`. -/
lemma lcWeight_eq_of_lt_max {c : ℝ} {l₁ l₂ k₁ k₂ : ℕ} (hk₁ : k₁ ≤ k₂)
    (hk : max l₁ l₂ < k₂) :
    lcWeight c l₁ l₂ k₁ k₂ = (2 : ℝ) ^ (-(c * (k₂ : ℝ))) := by
  rw [lcWeight, lmax_eq_self_of_lt_max hk₁ hk, Int.cast_natCast]

-- (The lemma `lmaxR_nonneg` of this file was a duplicate of the one declared in
-- `Submission/Work/KMTPlan/A6/MdlSliceCoreGainAll.lean`, which this file imports, and the
-- duplicate made the module unbuildable; the imported copy is used below.  The original file is
-- backed up at `.scratch/mine/MdlPartLowHighGain.lean.bak`.)

/-- The loss weight is monotone in its first parameter. -/
lemma lossWeight_le_of_le_A {A A' ρ : ℝ} (hA : A ≤ A') (hρ : 0 ≤ ρ) (l₁ l₂ k₁ k₂ : ℕ) :
    lossWeight A ρ l₁ l₂ k₁ k₂ ≤ lossWeight A' ρ l₁ l₂ k₁ k₂ := by
  have h0 := lmaxR_nonneg l₁ l₂ k₁ k₂
  rw [lossWeight, lossWeight]
  refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
  · exact Real.rpow_le_rpow_of_exponent_le (by linarith) hA
  · have h1 : A * lmaxR l₁ l₂ k₁ k₂ ≤ A' * lmaxR l₁ l₂ k₁ k₂ :=
      mul_le_mul_of_nonneg_right hA h0
    have h2 : A * lmaxR l₁ l₂ k₁ k₂ * ρ ≤ A' * lmaxR l₁ l₂ k₁ k₂ * ρ :=
      mul_le_mul_of_nonneg_right h1 hρ
    have h3 : A * ρ * lmaxR l₁ l₂ k₁ k₂ = A * lmaxR l₁ l₂ k₁ k₂ * ρ := by ring
    have h4 : A' * ρ * lmaxR l₁ l₂ k₁ k₂ = A' * lmaxR l₁ l₂ k₁ k₂ * ρ := by ring
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

/-- **Absorption of the loss weight into the gain, on the large-`k₂` branch.** -/
lemma lossWeight_absorb_large (A c d ρ : ℝ) (hA : 0 ≤ A) (hc : 0 < c) (hd : 0 < d)
    (hρ : 0 < ρ) (hρA : 4 * ρ * (A + 1) ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (l₁ l₂ k₂ : ℕ), max l₁ l₂ < k₂ →
      lossWeight A ρ l₁ l₂ 0 k₂ * (2 : ℝ) ^ (-(c * max (l₁ : ℝ) (l₂ : ℝ)))
        * (2 : ℝ) ^ (-(d * (k₂ : ℝ)))
        ≤ C * lcWeight (min c d / 2) l₁ l₂ 0 k₂ := by
  obtain ⟨C₁, hC₁ge, hC₁⟩ := rpow_poly_le_const_exp A (d / 4) hA (by positivity)
  have hC₁pos : (0 : ℝ) < C₁ := lt_of_lt_of_le zero_lt_one hC₁ge
  refine ⟨C₁, hC₁pos, fun l₁ l₂ k₂ hk => ?_⟩
  have hmax0 : (0 : ℝ) ≤ max (l₁ : ℝ) (l₂ : ℝ) := by positivity
  have hk2 : (0 : ℝ) ≤ (k₂ : ℝ) := by positivity
  have h1 : (2 : ℝ) ^ (-(c * max (l₁ : ℝ) (l₂ : ℝ))) ≤ 1 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (show -(c * max (l₁ : ℝ) (l₂ : ℝ)) ≤ 0 by nlinarith [hc, hmax0])
    simpa using h
  have h3 : A * ρ ≤ d / 4 := by nlinarith [hA, hρ, hρA]
  have h2 : (1 + (k₂ : ℝ)) ^ A ≤ C₁ * (2 : ℝ) ^ ((d / 4) * (k₂ : ℝ)) := hC₁ k₂
  rw [lossWeight_eq_of_lt_max (Nat.zero_le k₂) hk, lcWeight_eq_of_lt_max (Nat.zero_le k₂) hk]
  have e1 : (2 : ℝ) ^ (A * ρ * (k₂ : ℝ)) * (2 : ℝ) ^ (-(d * (k₂ : ℝ)))
      = (2 : ℝ) ^ ((A * ρ - d) * (k₂ : ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have e2 : (2 : ℝ) ^ ((d / 4) * (k₂ : ℝ)) * (2 : ℝ) ^ ((A * ρ - d) * (k₂ : ℝ))
      = (2 : ℝ) ^ ((d / 4 + (A * ρ - d)) * (k₂ : ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have hX : (0 : ℝ) < (1 + (k₂ : ℝ)) ^ A * (2 : ℝ) ^ (A * ρ * (k₂ : ℝ)) := by positivity
  calc (1 + (k₂ : ℝ)) ^ A * (2 : ℝ) ^ (A * ρ * (k₂ : ℝ))
        * (2 : ℝ) ^ (-(c * max (l₁ : ℝ) (l₂ : ℝ))) * (2 : ℝ) ^ (-(d * (k₂ : ℝ)))
      ≤ ((1 + (k₂ : ℝ)) ^ A * (2 : ℝ) ^ (A * ρ * (k₂ : ℝ))) * (2 : ℝ) ^ (-(d * (k₂ : ℝ))) :=
        mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hX.le h1) (by positivity)
    _ = (1 + (k₂ : ℝ)) ^ A * ((2 : ℝ) ^ (A * ρ * (k₂ : ℝ)) * (2 : ℝ) ^ (-(d * (k₂ : ℝ)))) := by
        rw [mul_assoc]
    _ = (1 + (k₂ : ℝ)) ^ A * (2 : ℝ) ^ ((A * ρ - d) * (k₂ : ℝ)) := by rw [e1]
    _ ≤ (C₁ * (2 : ℝ) ^ ((d / 4) * (k₂ : ℝ))) * (2 : ℝ) ^ ((A * ρ - d) * (k₂ : ℝ)) :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = C₁ * ((2 : ℝ) ^ ((d / 4) * (k₂ : ℝ)) * (2 : ℝ) ^ ((A * ρ - d) * (k₂ : ℝ))) := by
        rw [mul_assoc]
    _ = C₁ * (2 : ℝ) ^ ((d / 4 + (A * ρ - d)) * (k₂ : ℝ)) := by rw [e2]
    _ ≤ C₁ * (2 : ℝ) ^ (-(d / 2 * (k₂ : ℝ))) := by
        refine mul_le_mul_of_nonneg_left ?_ hC₁pos.le
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ?_
        nlinarith [h3, hk2]
    _ ≤ C₁ * (2 : ℝ) ^ (-(min c d / 2 * (k₂ : ℝ))) := by
        refine mul_le_mul_of_nonneg_left ?_ hC₁pos.le
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ?_
        have h4 : min c d / 2 ≤ d / 2 := by
          have h5 : min c d ≤ d := min_le_right _ _
          linarith
        nlinarith [h4, hk2]

/-- **Absorption of the loss weight into the gain, on the small-`k₂` branch.** -/
lemma lossWeight_absorb_small (A c ρ K₀ : ℝ) (hA : 0 ≤ A) (hρ : 0 ≤ ρ)
    (hK₀ : 0 ≤ K₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (l₁ l₂ k₂ : ℕ), max l₁ l₂ < k₂ → (k₂ : ℝ) ≤ K₀ →
      lossWeight A ρ l₁ l₂ 0 k₂ * (2 : ℝ) ^ (-(c * max (l₁ : ℝ) (l₂ : ℝ)))
        ≤ C * lcWeight c l₁ l₂ 0 k₂ := by
  refine ⟨(1 + K₀) ^ A * (2 : ℝ) ^ (A * ρ * K₀) * (2 : ℝ) ^ (max (c * K₀) 0), by positivity,
    fun l₁ l₂ k₂ hk hkK => ?_⟩
  have hmlt : (max (l₁ : ℝ) (l₂ : ℝ)) < (k₂ : ℝ) := by
    rw [← Nat.cast_max]
    exact_mod_cast hk
  have hgap0 : (0 : ℝ) ≤ (k₂ : ℝ) - max (l₁ : ℝ) (l₂ : ℝ) := by linarith
  have hK2 : (0 : ℝ) ≤ max (l₁ : ℝ) (l₂ : ℝ) := by positivity
  have hgapK : (k₂ : ℝ) - max (l₁ : ℝ) (l₂ : ℝ) ≤ K₀ := by linarith
  have hAρ : 0 ≤ A * ρ := mul_nonneg hA hρ
  have h2 : (1 + (k₂ : ℝ)) ^ A ≤ (1 + K₀) ^ A :=
    Real.rpow_le_rpow (by positivity) (by linarith) hA
  have h3 : (2 : ℝ) ^ (A * ρ * (k₂ : ℝ)) ≤ (2 : ℝ) ^ (A * ρ * K₀) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by nlinarith [hAρ, hkK])
  have h4 : (2 : ℝ) ^ (c * ((k₂ : ℝ) - max (l₁ : ℝ) (l₂ : ℝ)))
      ≤ (2 : ℝ) ^ (max (c * K₀) 0) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ?_
    by_cases hc : 0 ≤ c
    · calc c * ((k₂ : ℝ) - max (l₁ : ℝ) (l₂ : ℝ)) ≤ c * K₀ :=
            mul_le_mul_of_nonneg_left hgapK hc
        _ ≤ max (c * K₀) 0 := le_max_left _ _
    · have hc' : c < 0 := not_le.mp hc
      calc c * ((k₂ : ℝ) - max (l₁ : ℝ) (l₂ : ℝ)) ≤ c * 0 :=
            mul_le_mul_of_nonpos_left hgap0 hc'.le
        _ = 0 := by ring
        _ ≤ max (c * K₀) 0 := le_max_right _ _
  have hfac : (2 : ℝ) ^ (-(c * max (l₁ : ℝ) (l₂ : ℝ)))
      = (2 : ℝ) ^ (c * ((k₂ : ℝ) - max (l₁ : ℝ) (l₂ : ℝ)))
        * (2 : ℝ) ^ (-(c * (k₂ : ℝ))) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  rw [lossWeight_eq_of_lt_max (Nat.zero_le k₂) hk, lcWeight_eq_of_lt_max (Nat.zero_le k₂) hk,
    hfac]
  have h5 : (1 + (k₂ : ℝ)) ^ A * (2 : ℝ) ^ (A * ρ * (k₂ : ℝ))
      ≤ (1 + K₀) ^ A * (2 : ℝ) ^ (A * ρ * K₀) :=
    mul_le_mul h2 h3 (by positivity) (by positivity)
  calc (1 + (k₂ : ℝ)) ^ A * (2 : ℝ) ^ (A * ρ * (k₂ : ℝ))
        * ((2 : ℝ) ^ (c * ((k₂ : ℝ) - max (l₁ : ℝ) (l₂ : ℝ)))
          * (2 : ℝ) ^ (-(c * (k₂ : ℝ))))
      = ((1 + (k₂ : ℝ)) ^ A * (2 : ℝ) ^ (A * ρ * (k₂ : ℝ))
          * (2 : ℝ) ^ (c * ((k₂ : ℝ) - max (l₁ : ℝ) (l₂ : ℝ))))
        * (2 : ℝ) ^ (-(c * (k₂ : ℝ))) := by ring
    _ ≤ ((1 + K₀) ^ A * (2 : ℝ) ^ (A * ρ * K₀) * (2 : ℝ) ^ (max (c * K₀) 0))
          * (2 : ℝ) ^ (-(c * (k₂ : ℝ))) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact mul_le_mul h5 h4 (by positivity) (by positivity)

/-- **Absorption of the loss weight, large-`k₂` branch, *without* an arithmetic gain factor.**
If the exact-height slice bound is used with no gain, the `2^{-d·k₂}` of `MdlDecayLowHighB` has to
absorb the whole loss weight `⟨k₂⟩^A 2^{Aρk₂}`, which it does as soon as `Aρ ≤ d/4`. -/
lemma lossWeight_absorb_large_nogain (A d ρ : ℝ) (hA : 0 ≤ A) (hd : 0 < d) (hρ : 0 < ρ)
    (hρA : 4 * ρ * (A + 1) ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (l₁ l₂ k₂ : ℕ), max l₁ l₂ < k₂ →
      lossWeight A ρ l₁ l₂ 0 k₂ * (2 : ℝ) ^ (-(d * (k₂ : ℝ)))
        ≤ C * lcWeight (d / 2) l₁ l₂ 0 k₂ := by
  obtain ⟨C₁, hC₁ge, hC₁⟩ := rpow_poly_le_const_exp A (d / 4) hA (by positivity)
  have hC₁pos : (0 : ℝ) < C₁ := lt_of_lt_of_le zero_lt_one hC₁ge
  refine ⟨C₁, hC₁pos, fun l₁ l₂ k₂ hk => ?_⟩
  have hk2 : (0 : ℝ) ≤ (k₂ : ℝ) := by positivity
  have h3 : A * ρ ≤ d / 4 := by nlinarith [hA, hρ, hρA]
  have h2 : (1 + (k₂ : ℝ)) ^ A ≤ C₁ * (2 : ℝ) ^ ((d / 4) * (k₂ : ℝ)) := hC₁ k₂
  rw [lossWeight_eq_of_lt_max (Nat.zero_le k₂) hk, lcWeight_eq_of_lt_max (Nat.zero_le k₂) hk]
  have e1 : (2 : ℝ) ^ (A * ρ * (k₂ : ℝ)) * (2 : ℝ) ^ (-(d * (k₂ : ℝ)))
      = (2 : ℝ) ^ ((A * ρ - d) * (k₂ : ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have e2 : (2 : ℝ) ^ ((d / 4) * (k₂ : ℝ)) * (2 : ℝ) ^ ((A * ρ - d) * (k₂ : ℝ))
      = (2 : ℝ) ^ ((d / 4 + (A * ρ - d)) * (k₂ : ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  calc (1 + (k₂ : ℝ)) ^ A * (2 : ℝ) ^ (A * ρ * (k₂ : ℝ))
        * (2 : ℝ) ^ (-(d * (k₂ : ℝ)))
      = (1 + (k₂ : ℝ)) ^ A
          * ((2 : ℝ) ^ (A * ρ * (k₂ : ℝ)) * (2 : ℝ) ^ (-(d * (k₂ : ℝ)))) := by ring
    _ = (1 + (k₂ : ℝ)) ^ A * (2 : ℝ) ^ ((A * ρ - d) * (k₂ : ℝ)) := by rw [e1]
    _ ≤ (C₁ * (2 : ℝ) ^ ((d / 4) * (k₂ : ℝ))) * (2 : ℝ) ^ ((A * ρ - d) * (k₂ : ℝ)) :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = C₁ * ((2 : ℝ) ^ ((d / 4) * (k₂ : ℝ)) * (2 : ℝ) ^ ((A * ρ - d) * (k₂ : ℝ))) := by ring
    _ = C₁ * (2 : ℝ) ^ ((d / 4 + (A * ρ - d)) * (k₂ : ℝ)) := by rw [e2]
    _ ≤ C₁ * (2 : ℝ) ^ (-(d / 2 * (k₂ : ℝ))) := by
        refine mul_le_mul_of_nonneg_left ?_ hC₁pos.le
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ?_
        nlinarith [h3, hk2]

/-- **Absorption of the loss weight, small-`k₂` branch, *without* an arithmetic gain factor**: on
`k₂ ≤ K₀` the loss weight is bounded by a constant and `2^{-c k₂} ≥ 2^{-c K₀}` for `c ≥ 0`. -/
lemma lossWeight_absorb_small_nogain (A c ρ K₀ : ℝ) (hA : 0 ≤ A) (hρ : 0 ≤ ρ) (hK₀ : 0 ≤ K₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (l₁ l₂ k₂ : ℕ), max l₁ l₂ < k₂ → (k₂ : ℝ) ≤ K₀ →
      lossWeight A ρ l₁ l₂ 0 k₂ ≤ C * lcWeight c l₁ l₂ 0 k₂ := by
  refine ⟨(1 + K₀) ^ A * (2 : ℝ) ^ (A * ρ * K₀) * (2 : ℝ) ^ (max (c * K₀) 0), by positivity,
    fun l₁ l₂ k₂ hk hkK => ?_⟩
  have hk2 : (0 : ℝ) ≤ (k₂ : ℝ) := by positivity
  have hAρ : 0 ≤ A * ρ := mul_nonneg hA hρ
  have h2 : (1 + (k₂ : ℝ)) ^ A ≤ (1 + K₀) ^ A :=
    Real.rpow_le_rpow (by positivity) (by linarith) hA
  have h3 : (2 : ℝ) ^ (A * ρ * (k₂ : ℝ)) ≤ (2 : ℝ) ^ (A * ρ * K₀) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by nlinarith [hAρ, hkK])
  rw [lossWeight_eq_of_lt_max (Nat.zero_le k₂) hk, lcWeight_eq_of_lt_max (Nat.zero_le k₂) hk]
  have h4 : (2 : ℝ) ^ (-(max (c * K₀) 0)) ≤ (2 : ℝ) ^ (-(c * (k₂ : ℝ))) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ?_
    by_cases hc : 0 ≤ c
    · have h5 : c * (k₂ : ℝ) ≤ c * K₀ := mul_le_mul_of_nonneg_left hkK hc
      have h6 : c * (k₂ : ℝ) ≤ max (c * K₀) 0 := le_trans h5 (le_max_left _ _)
      linarith
    · have hc' : c < 0 := not_le.mp hc
      have h5 : c * K₀ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc'.le hK₀
      have h6 : max (c * K₀) 0 = 0 := max_eq_right h5
      rw [h6]
      have h7 : c * (k₂ : ℝ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc'.le hk2
      linarith
  calc (1 + (k₂ : ℝ)) ^ A * (2 : ℝ) ^ (A * ρ * (k₂ : ℝ))
      ≤ (1 + K₀) ^ A * (2 : ℝ) ^ (A * ρ * K₀) :=
        mul_le_mul h2 h3 (by positivity) (by positivity)
    _ = (1 + K₀) ^ A * (2 : ℝ) ^ (A * ρ * K₀) * (2 : ℝ) ^ (max (c * K₀) 0)
          * (2 : ℝ) ^ (-(max (c * K₀) 0)) := by
        have h : (2 : ℝ) ^ (max (c * K₀) 0) * (2 : ℝ) ^ (-(max (c * K₀) 0)) = 1 := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), add_neg_cancel, Real.rpow_zero]
        calc (1 + K₀) ^ A * (2 : ℝ) ^ (A * ρ * K₀)
            = (1 + K₀) ^ A * (2 : ℝ) ^ (A * ρ * K₀) * 1 := by ring
          _ = ((1 + K₀) ^ A * (2 : ℝ) ^ (A * ρ * K₀))
                * ((2 : ℝ) ^ (max (c * K₀) 0) * (2 : ℝ) ^ (-(max (c * K₀) 0))) := by rw [h]
          _ = (1 + K₀) ^ A * (2 : ℝ) ^ (A * ρ * K₀) * (2 : ℝ) ^ (max (c * K₀) 0)
                * (2 : ℝ) ^ (-(max (c * K₀) 0)) := by ring
    _ ≤ (1 + K₀) ^ A * (2 : ℝ) ^ (A * ρ * K₀) * (2 : ℝ) ^ (max (c * K₀) 0)
          * (2 : ℝ) ^ (-(c * (k₂ : ℝ))) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)

/-- For every real `B` there is a natural `K` with `B ≤ 2^K`. -/
lemma exists_pow_ge (B : ℝ) : ∃ K : ℕ, B ≤ (2 : ℝ) ^ K := by
  have h : Tendsto (fun n : ℕ => (2 : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  exact (h.eventually_ge_atTop B).exists

/-- The norm of a real number, viewed as a complex number. -/
lemma norm_ofReal_complex' (z : ℝ) : ‖((z : ℝ) : ℂ)‖ = |z| := by simp

/-- The `ℝ≥0∞`-norm of a complex number is `ofReal` of its norm. -/
lemma enorm_eq_ofReal_norm' (z : ℂ) : ‖z‖ₑ = ENNReal.ofReal ‖z‖ :=
  ENNReal.coe_nnreal_eq ‖z‖₊

/-! ## 3. The weighted slices and integrals of the model tuple -/

/-- The weighted slice family is the product of the (clipped) weight with the frozen slice. -/
lemma mdlSliceW_eq_ite_mul (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ : ℕ) (j₁ j₂ : ℤ) (w : ℕ → ℝ → ℂ) (t : ℝ) :
    mdlSliceW ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ w t
      = fun n x => (if mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n then w n t else 0)
          * mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x := by
  funext n x
  by_cases h : mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
  · simp only [mdlSliceW, mdlSliceJ_apply, if_pos h]
  · simp only [mdlSliceW, mdlSliceJ_apply, if_neg h, mul_zero]

/-- The weighted `t`-integral is the `t`-integral of the weighted frozen slices (the weight need
not be clipped: the frozen slice vanishes off the core). -/
lemma mdlWInt_eq_mdlWIntF (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ : ℕ) (j₁ j₂ : ℤ) (w : ℕ → ℝ → ℂ) :
    mdlWInt ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ w
      = mdlWIntF w (fun t n x => mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x) := by
  funext n x
  by_cases h : mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
  · simp only [mdlWInt, mdlWIntF, mdlSliceJ_apply, if_pos h]
  · simp only [mdlWInt, mdlWIntF, mdlSliceJ_apply, if_neg h, mul_zero,
      intervalIntegral.integral_zero]

/-! ## 4. The `ℓ²`-inputs as bounded sequences -/

/-- For an `ℓ²`-sequence the squared moduli are summable. -/
lemma summable_norm_sq_of_memLp {f : ℤ → ℂ} (hf : MemLp f 2 Measure.count) :
    Summable (fun y : ℤ => ‖f y‖ ^ 2) := by
  have hmem : Memℓp f (2 : ℝ≥0∞) := memlpOfMemLpCount (by norm_num) (by norm_num) hf
  have h := (memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)).mp hmem
  simpa using h

/-- Every value of an `ℓ²`-sequence is bounded by the sum of the squared moduli, so that the
bounded-input hypotheses of the integration-by-parts identity are available for `ℓ²`-inputs. -/
lemma normSq_le_tsum_norm_sq {f : ℤ → ℂ} (hf : Summable (fun y : ℤ => ‖f y‖ ^ 2)) (x : ℤ) :
    Complex.normSq (f x) ≤ ∑' y : ℤ, ‖f y‖ ^ 2 := by
  rw [Complex.normSq_eq_norm_sq]
  exact hf.le_tsum x (fun y _ => by positivity)

/-! ## 5. The main theorem -/

theorem MdlPartLowHighGain (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (r : NNReal) (hr : 2 < r)
    (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (hA1 : Work.KMTContract.AreaA1)
    (hI : Work.KMTContract.ImprovKMT P) :
    ∃ c : ℝ, 0 < c ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
      ∃ K : NNReal → NNReal,
        ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₂ : ℕ) (f g : ℤ → ℂ),
          1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n : ℕ, 1 ≤ a n) →
          max l₁ l₂ < k₂ →
          MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => Work.KMTPlan.A6.mdlPart ρ P C₀ a f g l₁ l₂ 0 k₂ n x))
            1 MeasureTheory.Measure.count
            ≤ ((K Λ : NNReal) : ENNReal) *
                ENNReal.ofReal (Work.KMTPlan.A6.lcWeight c l₁ l₂ 0 k₂) *
                MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count *
                MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
  classical
  have hr1 : (1 : ℝ≥0) ≤ r := le_trans (by norm_num : (1 : ℝ≥0) ≤ 2) (le_of_lt hr)
  -- All three instances of the frozen-`t` slice estimate are taken from the *single* upstream
  -- statement `Work.KMTPlan.A6LH.MdlSliceNoGainAtProved`, the loss-form (no-gain) bound, so that
  -- this theorem's axiom closure contains no unproved upstream statement.
  obtain ⟨cm1, hcm1, ρm1, hρm1, Hm1⟩ :=
    Work.KMTPlan.A6LH.MdlSliceNoGainAtProved P hd hA1 C₀ hC₀ r hr 0 (-1) (by decide) (by decide)
  obtain ⟨c1m, hc1m, ρ1m, hρ1m, H1m⟩ :=
    Work.KMTPlan.A6LH.MdlSliceNoGainAtProved P hd hA1 C₀ hC₀ r hr 1 (-1) (by decide) (by decide)
  obtain ⟨c00, hc00, ρ00, hρ00, H00⟩ :=
    Work.KMTPlan.A6LH.MdlSliceNoGainAtProved P hd hA1 C₀ hC₀ r hr 0 0 (by decide) (by decide)
  obtain ⟨Bb, hBbpos, Cw, hCwpos, hWb⟩ := MdlWeightVarBound P (by omega) r hr1
  obtain ⟨BP, hBPpos, hBP⟩ := PderivThreshold P hd
  obtain ⟨K₀, hK₀⟩ := exists_pow_ge (max Bb BP)
  -- the combined constants
  let A : ℝ := max (max cm1 c1m) c00
  have hAm1A : cm1 ≤ A := le_trans (le_max_left _ _) (le_max_left _ _)
  have hA1mA : c1m ≤ A := le_trans (le_max_right cm1 c1m) (le_max_left _ _)
  have hA00A : c00 ≤ A := le_max_right _ _
  have hA0 : 0 ≤ A := le_trans hc00 hA00A
  have hd3 : (0 : ℝ) < (P.natDegree : ℝ) := by exact_mod_cast (by omega : 0 < P.natDegree)
  -- the gain rate is *chosen*, not inherited from the slice estimates: the loss-form (no-gain)
  -- slice bound gives no decay in `max l₁ l₂`, and the whole decay in the target comes from the
  -- `2^{-(deg P)·k₂}` of `MdlDecayLowHighB` (large `k₂`) and from the boundedness of `lcL` on
  -- `k₂ ≤ K₀` (small `k₂`).
  let cF : ℝ := min ((P.natDegree : ℝ) / 8) (1 / 2)
  have hcFpos : 0 < cF := by
    dsimp only [cF]
    exact lt_min (by linarith [hd3]) (by norm_num)
  have hcF_le_d : cF ≤ (P.natDegree : ℝ) / 2 := by
    dsimp only [cF]
    have h1 := min_le_left ((P.natDegree : ℝ) / 8) (1 / 2)
    linarith [hd3]
  let ρ₀ : ℝ := min (min (min ρm1 ρ1m) ρ00) (min ((P.natDegree : ℝ) / (4 * (A + 1))) 1)
  have hρ0pos : 0 < ρ₀ := by
    dsimp only [ρ₀]
    exact lt_min (lt_min (lt_min hρm1 hρ1m) hρ00)
      (lt_min (div_pos hd3 (by positivity)) zero_lt_one)
  refine ⟨cF, hcFpos, ρ₀, hρ0pos, fun ρ hρ hρle => ?_⟩
  have hρS : ρ ≤ min (min ρm1 ρ1m) ρ00 := le_trans hρle (min_le_left _ _)
  have hρm1' : ρ ≤ ρm1 := le_trans hρS (le_trans (min_le_left _ _) (min_le_left _ _))
  have hρ1m' : ρ ≤ ρ1m := le_trans hρS (le_trans (min_le_left _ _) (min_le_right _ _))
  have hρ00' : ρ ≤ ρ00 := le_trans hρS (min_le_right _ _)
  have hρd : ρ ≤ (P.natDegree : ℝ) / (4 * (A + 1)) :=
    le_trans hρle (le_trans (min_le_right _ _) (min_le_left _ _))
  have hρA : 4 * ρ * (A + 1) ≤ (P.natDegree : ℝ) := by
    have h4 : (0 : ℝ) < 4 * (A + 1) := by positivity
    rw [le_div_iff₀ h4] at hρd
    linarith
  obtain ⟨Km1, hKm1⟩ := Hm1 ρ hρ hρm1'
  obtain ⟨K1m, hK1m⟩ := H1m ρ hρ hρ1m'
  obtain ⟨K00, hK00⟩ := H00 ρ hρ hρ00'
  obtain ⟨Ca, hCapos, hCa⟩ :=
    lossWeight_absorb_large_nogain A (P.natDegree : ℝ) ρ hA0 hd3 hρ hρA
  obtain ⟨Cs, hCspos, hCs⟩ :=
    lossWeight_absorb_small_nogain A cF ρ (K₀ : ℝ) hA0 hρ.le (by positivity)
  let ιb : ℝ := max 1 ‖mdlIota‖
  have hιb1 : 1 ≤ ιb := le_max_left 1 ‖mdlIota‖
  let Kfac : ℝ := 4 * ιb * (2 * Cw + 1) + 2
  have hKfacpos : 0 < Kfac := by
    dsimp only [Kfac]; positivity
  let Ks : NNReal → NNReal := fun Λ => max (Km1 Λ) (K1m Λ)
  have hKs1 : ∀ Λ, Km1 Λ ≤ Ks Λ := fun Λ => le_max_left _ _
  have hKs2 : ∀ Λ, K1m Λ ≤ Ks Λ := fun Λ => le_max_right _ _
  let Kfun : NNReal → NNReal := fun Λ =>
    ⟨(Ks Λ : ℝ) * Kfac * Ca + (K00 Λ : ℝ) * Cs + 1, by positivity⟩
  have hKval : ∀ Λ, ((Kfun Λ : NNReal) : ENNReal)
      = ENNReal.ofReal ((Ks Λ : ℝ) * Kfac * Ca + (K00 Λ : ℝ) * Cs + 1) :=
    fun Λ => ENNReal.ofReal_coe_nnreal.symm
  have hKge : ∀ Λ, (Ks Λ : ℝ) * Kfac * Ca ≤ (Ks Λ : ℝ) * Kfac * Ca + (K00 Λ : ℝ) * Cs + 1 :=
    fun Λ => by
      have h1 : (0 : ℝ) ≤ (K00 Λ : ℝ) * Cs := by positivity
      linarith
  refine ⟨Kfun, ?_⟩
  intro a Λ l₁ l₂ k₂ f g hΛ hlac ha1 hklt
  have hk2 : 1 ≤ k₂ := by omega
  have hN : ∀ n : ℕ, 1 ≤ Nat.floor (a n) := fun n => Nat.le_floor (by exact_mod_cast ha1 n)
  -- the right-hand side factors
  have hKne : ((Kfun Λ : NNReal) : ENNReal) ≠ 0 := by
    rw [hKval Λ, ENNReal.ofReal_ne_zero_iff]
    have h1 : (0 : ℝ) ≤ (Ks Λ : ℝ) * Kfac * Ca :=
      mul_nonneg (mul_nonneg (by positivity) hKfacpos.le) hCapos.le
    have h2 : (0 : ℝ) ≤ (K00 Λ : ℝ) * Cs := mul_nonneg (by positivity) hCspos.le
    linarith
  have hlwne : ENNReal.ofReal (lcWeight cF l₁ l₂ 0 k₂) ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff, lcWeight]
    exact Real.rpow_pos_of_pos (by norm_num) _
  -- degenerate cases
  rcases eq_or_ne (eLpNorm f 2 Measure.count) ⊤ with hfT | hfT
  · rcases eq_or_ne (eLpNorm g 2 Measure.count) 0 with hg0 | hg0
    · have hgz : g = 0 := eq_zero_of_eLpNorm_two_eq_zero hg0
      have hpart0 : mdlPart ρ P C₀ a f g l₁ l₂ 0 k₂ = 0 := by
        rw [hgz, ← mdlPartJ_zero_zero]
        exact mdlPartJ_eq_zero_of_right_zero ρ P C₀ a f l₁ l₂ 0 k₂ 0 0
      have hlhs : eLpNorm (fun x : ℤ => variationalNorm r
          (fun n : ℕ => mdlPart ρ P C₀ a f g l₁ l₂ 0 k₂ n x)) 1 Measure.count = 0 := by
        rw [hpart0]
        simpa using eLpNorm_variationalNorm_zero hr1
      rw [hlhs]
      exact bot_le
    · have htop : ((Kfun Λ : NNReal) : ENNReal) * ENNReal.ofReal (lcWeight cF l₁ l₂ 0 k₂)
          * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count = ⊤ := by
        rw [hfT, ENNReal.mul_top (mul_ne_zero hKne hlwne), ENNReal.top_mul hg0]
      rw [htop]
      exact le_top
  rcases eq_or_ne (eLpNorm g 2 Measure.count) ⊤ with hgT | hgT
  · rcases eq_or_ne (eLpNorm f 2 Measure.count) 0 with hf0 | hf0
    · have hfz : f = 0 := eq_zero_of_eLpNorm_two_eq_zero hf0
      have hpart0 : mdlPart ρ P C₀ a f g l₁ l₂ 0 k₂ = 0 := by
        rw [hfz, ← mdlPartJ_zero_zero]
        exact mdlPartJ_eq_zero_of_left_zero ρ P C₀ a g l₁ l₂ 0 k₂ 0 0
      have hlhs : eLpNorm (fun x : ℤ => variationalNorm r
          (fun n : ℕ => mdlPart ρ P C₀ a f g l₁ l₂ 0 k₂ n x)) 1 Measure.count = 0 := by
        rw [hpart0]
        simpa using eLpNorm_variationalNorm_zero hr1
      rw [hlhs]
      exact bot_le
    · have htop : ((Kfun Λ : NNReal) : ENNReal) * ENNReal.ofReal (lcWeight cF l₁ l₂ 0 k₂)
          * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count = ⊤ := by
        rw [hgT, ENNReal.mul_top (mul_ne_zero (mul_ne_zero hKne hlwne) hf0)]
      rw [htop]
      exact le_top
  -- main case: f, g ∈ ℓ²
  have hf2 : MemLp f 2 Measure.count := memLp_two_count_of_ne_top hfT
  have hg2 : MemLp g 2 Measure.count := memLp_two_count_of_ne_top hgT
  have hsumf : Summable (fun y : ℤ => ‖f y‖ ^ 2) := summable_norm_sq_of_memLp hf2
  have hsumg : Summable (fun y : ℤ => ‖g y‖ ^ 2) := summable_norm_sq_of_memLp hg2
  have hkltR : max (l₁ : ℝ) (l₂ : ℝ) < (k₂ : ℝ) := by
    have h2 : ((max l₁ l₂ : ℕ) : ℝ) < (k₂ : ℝ) := by exact_mod_cast hklt
    rwa [Nat.cast_max] at h2
  rcases lt_or_ge K₀ k₂ with hbig | hsmall
  · -- ################ LARGE CASE ################
    have hcore_pow : ∀ n : ℕ, mdlCore ρ C₀ a l₁ l₂ 0 k₂ n → 2 ^ k₂ ≤ Nat.floor (a n) := by
      intro n hn
      have hmain := ((mdlCore_iff ρ C₀ a l₁ l₂ 0 k₂ n).mp hn).2.2
      have hlog : k₂ ≤ (logN (Nat.floor (a n))).toNat := by
        unfold Work.KMTAreas.A7.mainRegime at hmain
        exact le_trans (Nat.le_add_right k₂ (2 * uScale ρ (max 0 k₂))) hmain.2
      have hlog2 : k₂ ≤ Nat.log 2 (max (Nat.floor (a n)) 2) := by
        simpa [Work.Analysis.EndVar.logN] using hlog
      have hp := Nat.pow_le_of_le_log (b := 2) (x := k₂)
        (y := max (Nat.floor (a n)) 2) (by positivity) hlog2
      have h2le : 2 ≤ Work.KMTAreas.A7.splitCut ρ k₂ := by
        rw [Work.KMTAreas.A7.splitCut]
        have h1 : 1 ≤ 2 ^ Work.Analysis.EndVar.scaleCount 1 ρ k₂ := by
          have hpos := Nat.pow_pos (n := Work.Analysis.EndVar.scaleCount 1 ρ k₂)
            (by norm_num : (0 : ℕ) < 2)
          omega
        calc (2 : ℕ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (2 ^ Work.Analysis.EndVar.scaleCount 1 ρ k₂) :=
              Nat.pow_le_pow_right (by norm_num) h1
      have hcut := ((mdlCore_iff ρ C₀ a l₁ l₂ 0 k₂ n).mp hn).2.1
      have hlc : lcL l₁ l₂ 0 k₂ = k₂ := by
        have h1 : max (0 : ℕ) k₂ = k₂ := max_eq_right (Nat.zero_le k₂)
        rw [lcL, h1, max_eq_right (le_of_lt hklt)]
      rw [hlc] at hcut
      have hN2 : 2 ≤ Nat.floor (a n) := le_of_lt (lt_of_le_of_lt h2le hcut)
      rwa [max_eq_left hN2] at hp
    have hNbound : ∀ n : ℕ, mdlCore ρ C₀ a l₁ l₂ 0 k₂ n →
        max Bb BP ≤ ((Nat.floor (a n) : ℕ) : ℝ) := by
      intro n hn
      have h2 : max Bb BP ≤ (2 : ℝ) ^ k₂ :=
        le_trans hK₀ (pow_le_pow_right₀ (by norm_num) (le_of_lt hbig))
      have h3 : (2 : ℝ) ^ k₂ ≤ ((Nat.floor (a n) : ℕ) : ℝ) := by
        have hp := hcore_pow n hn
        push_cast
        exact_mod_cast hp
      linarith
    have hPne : ∀ n : ℕ, mdlCore ρ C₀ a l₁ l₂ 0 k₂ n →
        ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, PderivR P ((Nat.floor (a n) : ℝ) * t) ≠ 0 := by
      intro n hn t ht
      exact hBP (Nat.floor (a n)) t (le_trans (le_max_right Bb BP) (hNbound n hn)) ht
    have hthr : ∀ n : ℕ, mdlCore ρ C₀ a l₁ l₂ 0 k₂ n → Bb ≤ ((Nat.floor (a n) : ℕ) : ℝ) :=
      fun n hn => le_trans (le_max_left Bb BP) (hNbound n hn)
    have hk2ne : k₂ ≠ 0 := by omega
    -- the four families of the identity
    obtain ⟨F1, hF1⟩ : ∃ Y : ℕ → ℤ → ℂ, Y = (fun n x =>
      mdlSliceW ρ P C₀ a f g l₁ l₂ 0 k₂ 0 (-1) (fun n t => mdlW1 P (Nat.floor (a n)) t) 1 n x) :=
      ⟨_, rfl⟩
    obtain ⟨F2, hF2⟩ : ∃ Y : ℕ → ℤ → ℂ, Y = (fun n x =>
      mdlSliceW ρ P C₀ a f g l₁ l₂ 0 k₂ 0 (-1) (fun n t => mdlW1 P (Nat.floor (a n)) t) (1 / 2) n x) :=
      ⟨_, rfl⟩
    obtain ⟨F3, hF3⟩ : ∃ Y : ℕ → ℤ → ℂ, Y = (fun n x =>
      mdlWInt ρ P C₀ a f g l₁ l₂ 0 k₂ 1 (-1) (fun n t => mdlW1 P (Nat.floor (a n)) t) n x) :=
      ⟨_, rfl⟩
    obtain ⟨F4, hF4⟩ : ∃ Y : ℕ → ℤ → ℂ, Y = (fun n x =>
      mdlWInt ρ P C₀ a f g l₁ l₂ 0 k₂ 0 (-1) (fun n t => mdlW2 P (Nat.floor (a n)) t) n x) :=
      ⟨_, rfl⟩
    obtain ⟨cs, hcs⟩ : ∃ Y : ℂ, Y = ((mdlScale P k₂ : ℂ) * mdlIota) := ⟨_, rfl⟩
    obtain ⟨cg, hcg⟩ : ∃ Y : ℂ, Y = ((mdlScaleGe P 0 k₂ : ℂ)) := ⟨_, rfl⟩
    have hid : mdlPart ρ P C₀ a f g l₁ l₂ 0 k₂ = fun n x =>
        cs * (F1 n x - F2 n x) - cg * F3 n x + cs * F4 n x := by
      rw [hcs, hcg, hF1, hF2, hF3, hF4]
      rw [← mdlPartJ_zero_zero]
      exact MdlDecayLowHighB ρ P C₀ a f g l₁ l₂ k₂ hk2 (∑' y : ℤ, ‖f y‖ ^ 2)
        (∑' y : ℤ, ‖g y‖ ^ 2) (normSq_le_tsum_norm_sq hsumf) (normSq_le_tsum_norm_sq hsumg)
        hN hPne
    -- the coefficient bounds
    have hcs_norm : ‖cs‖ ≤ (2 : ℝ) ^ (-((P.natDegree : ℝ) * (k₂ : ℝ))) * ιb := by
      have h1 : ‖((mdlScale P k₂ : ℝ) : ℂ)‖ = (2 : ℝ) ^ (-((P.natDegree : ℝ) * (k₂ : ℝ))) := by
        rw [norm_ofReal_complex', mdlScale,
          abs_of_nonneg (Real.rpow_pos_of_pos (by norm_num) _).le]
      calc ‖cs‖ = ‖(mdlScale P k₂ : ℂ) * mdlIota‖ := by rw [hcs]
        _ ≤ ‖(mdlScale P k₂ : ℂ)‖ * ‖mdlIota‖ := norm_mul_le _ _
        _ = (2 : ℝ) ^ (-((P.natDegree : ℝ) * (k₂ : ℝ))) * ‖mdlIota‖ := by rw [h1]
        _ ≤ (2 : ℝ) ^ (-((P.natDegree : ℝ) * (k₂ : ℝ))) * ιb :=
            mul_le_mul_of_nonneg_left (le_max_right 1 ‖mdlIota‖)
              (Real.rpow_pos_of_pos (by norm_num) _).le
    have hcg_norm : ‖cg‖ ≤ (2 : ℝ) ^ (-((P.natDegree : ℝ) * (k₂ : ℝ))) * ιb := by
      have hge : mdlScaleGe P 0 k₂ = (2 : ℝ) ^ (-((P.natDegree : ℝ) * (k₂ : ℝ))) := by
        rw [mdlScaleGe]
        congr 1
        ring
      have h1 : ‖((mdlScaleGe P 0 k₂ : ℝ) : ℂ)‖ = (2 : ℝ) ^ (-((P.natDegree : ℝ) * (k₂ : ℝ))) := by
        rw [norm_ofReal_complex', hge,
          abs_of_nonneg (Real.rpow_pos_of_pos (by norm_num) _).le]
      calc ‖cg‖ = ‖((mdlScaleGe P 0 k₂ : ℝ) : ℂ)‖ := by rw [hcg]
        _ = (2 : ℝ) ^ (-((P.natDegree : ℝ) * (k₂ : ℝ))) := h1
        _ ≤ (2 : ℝ) ^ (-((P.natDegree : ℝ) * (k₂ : ℝ))) * ιb :=
            le_mul_of_one_le_right (Real.rpow_pos_of_pos (by norm_num) _).le hιb1
    obtain ⟨L0, hL0⟩ : ∃ Y : ℝ, Y = lossWeight A ρ l₁ l₂ 0 k₂ := ⟨_, rfl⟩
    obtain ⟨D, hD0⟩ : ∃ Y : ENNReal, Y = ENNReal.ofReal ((2 : ℝ) ^ (-((P.natDegree : ℝ) * (k₂ : ℝ)))) :=
      ⟨_, rfl⟩
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
        (K' : ENNReal) * ENNReal.ofReal (lossWeight A' ρ l₁ l₂ 0 k₂)
          * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count ≤ Bslice := by
      intro K' hK' A' hA'
      have hof : ENNReal.ofReal (lossWeight A' ρ l₁ l₂ 0 k₂) ≤ ENNReal.ofReal L0 := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hL0]
        exact lossWeight_le_of_le_A hA' hρ.le l₁ l₂ 0 k₂
      have hK'' : (K' : ENNReal) ≤ ((Ks Λ : NNReal) : ENNReal) := by exact_mod_cast hK'
      have hmid : (K' : ENNReal) * ENNReal.ofReal (lossWeight A' ρ l₁ l₂ 0 k₂)
          ≤ ((Ks Λ : NNReal) : ENNReal) * ENNReal.ofReal L0 :=
        mul_le_mul hK'' hof (by positivity) (by positivity)
      calc (K' : ENNReal) * ENNReal.ofReal (lossWeight A' ρ l₁ l₂ 0 k₂)
              * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count
          ≤ (((Ks Λ : NNReal) : ENNReal) * ENNReal.ofReal L0)
              * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count :=
            mul_le_mul (mul_le_mul hmid le_rfl (by positivity) (by positivity)) le_rfl
              (by positivity) (by positivity)
        _ = Bslice := by rw [hBs]
    -- the four slice bounds
    have hslice1 : eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => F1 n x))
        1 Measure.count ≤ Nw * Bslice := by
      have h1 := hKm1 a Λ l₁ l₂ 0 k₂ 1 f g hΛ hlac ha1 (by norm_num)
        (fun _ => by norm_num) (fun h => absurd h hk2ne) hf2 hg2
      have hw1 : variationalNorm r (fun n : ℕ =>
          if mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then mdlW1 P (Nat.floor (a n)) 1 else 0)
          ≤ ENNReal.ofReal Cw := (hWb ρ C₀ a Λ l₁ l₂ 0 k₂ 1 hΛ hlac hthr (by norm_num)).1
      have hmul := eLpNorm_varNorm_mul_le (r := r) hr1 hw1
        (fun n x => mdlSliceJ ρ P C₀ a f g l₁ l₂ 0 k₂ 0 (-1) 1 n x)
      have hEq : (fun x : ℤ => variationalNorm r (fun n : ℕ => F1 n x))
          = (fun x : ℤ => variationalNorm r (fun n : ℕ =>
              (if mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then mdlW1 P (Nat.floor (a n)) 1 else 0)
                * mdlSliceJ ρ P C₀ a f g l₁ l₂ 0 k₂ 0 (-1) 1 n x)) := by
        simp only [hF1]
        funext x
        congr 1
        funext n
        exact congrFun (congrFun (mdlSliceW_eq_ite_mul ρ P C₀ a f g l₁ l₂ 0 k₂ 0 (-1)
          (fun n t => mdlW1 P (Nat.floor (a n)) t) 1) n) x
      rw [hEq]
      have h4 : eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ =>
          mdlSliceJ ρ P C₀ a f g l₁ l₂ 0 k₂ 0 (-1) 1 n x)) 1 Measure.count ≤ Bslice :=
        h1.trans (hcmp (Km1 Λ) (hKs1 Λ) cm1 hAm1A)
      calc eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ =>
              (if mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then mdlW1 P (Nat.floor (a n)) 1 else 0)
                * mdlSliceJ ρ P C₀ a f g l₁ l₂ 0 k₂ 0 (-1) 1 n x)) 1 Measure.count
          ≤ (2 * ENNReal.ofReal Cw) * eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ =>
              mdlSliceJ ρ P C₀ a f g l₁ l₂ 0 k₂ 0 (-1) 1 n x)) 1 Measure.count := hmul
        _ ≤ (2 * ENNReal.ofReal Cw) * Bslice :=
            mul_le_mul_of_nonneg_left h4 (by positivity)
        _ ≤ Nw * Bslice := mul_le_mul_of_nonneg_right h2Cw (by positivity)
    have hslice2 : eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => F2 n x))
        1 Measure.count ≤ Nw * Bslice := by
      have h1 := hKm1 a Λ l₁ l₂ 0 k₂ (1 / 2) f g hΛ hlac ha1 (by norm_num)
        (fun _ => by norm_num) (fun h => absurd h hk2ne) hf2 hg2
      have hw1 : variationalNorm r (fun n : ℕ =>
          if mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then mdlW1 P (Nat.floor (a n)) (1 / 2) else 0)
          ≤ ENNReal.ofReal Cw := (hWb ρ C₀ a Λ l₁ l₂ 0 k₂ (1 / 2) hΛ hlac hthr (by norm_num)).1
      have hmul := eLpNorm_varNorm_mul_le (r := r) hr1 hw1
        (fun n x => mdlSliceJ ρ P C₀ a f g l₁ l₂ 0 k₂ 0 (-1) (1 / 2) n x)
      have hEq : (fun x : ℤ => variationalNorm r (fun n : ℕ => F2 n x))
          = (fun x : ℤ => variationalNorm r (fun n : ℕ =>
              (if mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then mdlW1 P (Nat.floor (a n)) (1 / 2) else 0)
                * mdlSliceJ ρ P C₀ a f g l₁ l₂ 0 k₂ 0 (-1) (1 / 2) n x)) := by
        simp only [hF2]
        funext x
        congr 1
        funext n
        exact congrFun (congrFun (mdlSliceW_eq_ite_mul ρ P C₀ a f g l₁ l₂ 0 k₂ 0 (-1)
          (fun n t => mdlW1 P (Nat.floor (a n)) t) (1 / 2)) n) x
      rw [hEq]
      have h4 : eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ =>
          mdlSliceJ ρ P C₀ a f g l₁ l₂ 0 k₂ 0 (-1) (1 / 2) n x)) 1 Measure.count ≤ Bslice :=
        h1.trans (hcmp (Km1 Λ) (hKs1 Λ) cm1 hAm1A)
      calc eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ =>
              (if mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then mdlW1 P (Nat.floor (a n)) (1 / 2) else 0)
                * mdlSliceJ ρ P C₀ a f g l₁ l₂ 0 k₂ 0 (-1) (1 / 2) n x)) 1 Measure.count
          ≤ (2 * ENNReal.ofReal Cw) * eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ =>
              mdlSliceJ ρ P C₀ a f g l₁ l₂ 0 k₂ 0 (-1) (1 / 2) n x)) 1 Measure.count := hmul
        _ ≤ (2 * ENNReal.ofReal Cw) * Bslice :=
            mul_le_mul_of_nonneg_left h4 (by positivity)
        _ ≤ Nw * Bslice := mul_le_mul_of_nonneg_right h2Cw (by positivity)
    have hslice3 : eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => F3 n x))
        1 Measure.count ≤ Nw * Bslice := by
      have hEqF : F3 = mdlWIntF (fun n t => mdlW1 P (Nat.floor (a n)) t)
          (fun t n x => mdlSliceJ ρ P C₀ a f g l₁ l₂ 0 k₂ 1 (-1) t n x) := by
        rw [hF3]
        exact mdlWInt_eq_mdlWIntF ρ P C₀ a f g l₁ l₂ 0 k₂ 1 (-1)
          (fun n t => mdlW1 P (Nat.floor (a n)) t)
      rw [hEqF]
      refine mdlWIntF_norm_le (r := r) hr1 _ _ ?_ ?_ ?_
      · intro n x
        exact (measurable_mdlW1 P (Nat.floor (a n))).mul
          (MdlSliceMeasurable ρ P C₀ a f g l₁ l₂ 0 k₂ 1 (-1) n x)
      · intro n x
        by_cases hn : mdlCore ρ C₀ a l₁ l₂ 0 k₂ n
        · obtain ⟨Cw₁, hCw₁, hwb⟩ := mdl_W1_bound P (Nat.floor (a n)) (hPne n hn)
          have hYint : Integrable (fun t : ℝ => mdlSliceJ ρ P C₀ a f g l₁ l₂ 0 k₂ 1 (-1) t n x)
              (volume.restrict (Set.uIoc (1 / 2 : ℝ) 1)) := by
            have h := MdlSliceIntervalIntegrable ρ P C₀ a f g l₁ l₂ 0 k₂ 1 (-1) n x hf2 hg2
              (fun _ => by norm_num) (fun h => absurd h hk2ne)
            rwa [intervalIntegrable_iff] at h
          rw [intervalIntegrable_iff]
          exact Integrable.bdd_mul hYint
            ((measurable_mdlW1 P (Nat.floor (a n))).aestronglyMeasurable)
            (by
              filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
              exact hwb t (by
                rw [← Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)]
                exact Set.uIoc_subset_uIcc ht))
        · have hzero : (fun t : ℝ => mdlW1 P (Nat.floor (a n)) t
              * mdlSliceJ ρ P C₀ a f g l₁ l₂ 0 k₂ 1 (-1) t n x) = fun _ => (0 : ℂ) := by
            funext t
            rw [mdlSliceJ_apply, if_neg hn, mul_zero]
          rw [hzero]
          exact intervalIntegrable_const (μ := volume) (a := (1 / 2 : ℝ)) (b := 1) (c := (0 : ℂ))
      · intro t ht
        have h1 := hK1m a Λ l₁ l₂ 0 k₂ t f g hΛ hlac ha1 ht
          (fun _ => by norm_num) (fun h => absurd h hk2ne) hf2 hg2
        have hw1 : variationalNorm r (fun n : ℕ =>
            if mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then mdlW1 P (Nat.floor (a n)) t else 0)
            ≤ ENNReal.ofReal Cw := (hWb ρ C₀ a Λ l₁ l₂ 0 k₂ t hΛ hlac hthr ht).1
        have hmul := eLpNorm_varNorm_mul_le (r := r) hr1 hw1
          (fun n x => mdlSliceJ ρ P C₀ a f g l₁ l₂ 0 k₂ 1 (-1) t n x)
        have hEq2 : (fun x : ℤ => variationalNorm r (fun n : ℕ =>
              mdlW1 P (Nat.floor (a n)) t * mdlSliceJ ρ P C₀ a f g l₁ l₂ 0 k₂ 1 (-1) t n x))
            = (fun x : ℤ => variationalNorm r (fun n : ℕ =>
              (if mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then mdlW1 P (Nat.floor (a n)) t else 0)
                * mdlSliceJ ρ P C₀ a f g l₁ l₂ 0 k₂ 1 (-1) t n x)) := by
          funext x
          congr 1
          funext n
          by_cases hn : mdlCore ρ C₀ a l₁ l₂ 0 k₂ n
          · simp only [if_pos hn]
          · rw [if_neg hn, zero_mul, mdlSliceJ_apply, if_neg hn, mul_zero]
        rw [hEq2]
        have h4 : eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ =>
            mdlSliceJ ρ P C₀ a f g l₁ l₂ 0 k₂ 1 (-1) t n x)) 1 Measure.count ≤ Bslice :=
          h1.trans (hcmp (K1m Λ) (hKs2 Λ) c1m hA1mA)
        calc eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ =>
                (if mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then mdlW1 P (Nat.floor (a n)) t else 0)
                  * mdlSliceJ ρ P C₀ a f g l₁ l₂ 0 k₂ 1 (-1) t n x)) 1 Measure.count
            ≤ (2 * ENNReal.ofReal Cw) * eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ =>
                mdlSliceJ ρ P C₀ a f g l₁ l₂ 0 k₂ 1 (-1) t n x)) 1 Measure.count := hmul
          _ ≤ (2 * ENNReal.ofReal Cw) * Bslice :=
              mul_le_mul_of_nonneg_left h4 (by positivity)
          _ ≤ Nw * Bslice := mul_le_mul_of_nonneg_right h2Cw (by positivity)
    have hslice4 : eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => F4 n x))
        1 Measure.count ≤ Nw * Bslice := by
      have hEqF : F4 = mdlWIntF (fun n t => mdlW2 P (Nat.floor (a n)) t)
          (fun t n x => mdlSliceJ ρ P C₀ a f g l₁ l₂ 0 k₂ 0 (-1) t n x) := by
        rw [hF4]
        exact mdlWInt_eq_mdlWIntF ρ P C₀ a f g l₁ l₂ 0 k₂ 0 (-1)
          (fun n t => mdlW2 P (Nat.floor (a n)) t)
      rw [hEqF]
      refine mdlWIntF_norm_le (r := r) hr1 _ _ ?_ ?_ ?_
      · intro n x
        exact (measurable_mdlW2 P (Nat.floor (a n))).mul
          (MdlSliceMeasurable ρ P C₀ a f g l₁ l₂ 0 k₂ 0 (-1) n x)
      · intro n x
        by_cases hn : mdlCore ρ C₀ a l₁ l₂ 0 k₂ n
        · obtain ⟨Cw₂, hCw₂, hwb⟩ := mdl_W2_bound P (Nat.floor (a n)) (hPne n hn)
          have hYint : Integrable (fun t : ℝ => mdlSliceJ ρ P C₀ a f g l₁ l₂ 0 k₂ 0 (-1) t n x)
              (volume.restrict (Set.uIoc (1 / 2 : ℝ) 1)) := by
            have h := MdlSliceIntervalIntegrable ρ P C₀ a f g l₁ l₂ 0 k₂ 0 (-1) n x hf2 hg2
              (fun _ => by norm_num) (fun h => absurd h hk2ne)
            rwa [intervalIntegrable_iff] at h
          rw [intervalIntegrable_iff]
          exact Integrable.bdd_mul hYint
            ((measurable_mdlW2 P (Nat.floor (a n))).aestronglyMeasurable)
            (by
              filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
              exact hwb t (by
                rw [← Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)]
                exact Set.uIoc_subset_uIcc ht))
        · have hzero : (fun t : ℝ => mdlW2 P (Nat.floor (a n)) t
              * mdlSliceJ ρ P C₀ a f g l₁ l₂ 0 k₂ 0 (-1) t n x) = fun _ => (0 : ℂ) := by
            funext t
            rw [mdlSliceJ_apply, if_neg hn, mul_zero]
          rw [hzero]
          exact intervalIntegrable_const (μ := volume) (a := (1 / 2 : ℝ)) (b := 1) (c := (0 : ℂ))
      · intro t ht
        have h1 := hKm1 a Λ l₁ l₂ 0 k₂ t f g hΛ hlac ha1 ht
          (fun _ => by norm_num) (fun h => absurd h hk2ne) hf2 hg2
        have hw2 : variationalNorm r (fun n : ℕ =>
            if mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then mdlW2 P (Nat.floor (a n)) t else 0)
            ≤ ENNReal.ofReal Cw := (hWb ρ C₀ a Λ l₁ l₂ 0 k₂ t hΛ hlac hthr ht).2.1
        have hmul := eLpNorm_varNorm_mul_le (r := r) hr1 hw2
          (fun n x => mdlSliceJ ρ P C₀ a f g l₁ l₂ 0 k₂ 0 (-1) t n x)
        have hEq2 : (fun x : ℤ => variationalNorm r (fun n : ℕ =>
              mdlW2 P (Nat.floor (a n)) t * mdlSliceJ ρ P C₀ a f g l₁ l₂ 0 k₂ 0 (-1) t n x))
            = (fun x : ℤ => variationalNorm r (fun n : ℕ =>
              (if mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then mdlW2 P (Nat.floor (a n)) t else 0)
                * mdlSliceJ ρ P C₀ a f g l₁ l₂ 0 k₂ 0 (-1) t n x)) := by
          funext x
          congr 1
          funext n
          by_cases hn : mdlCore ρ C₀ a l₁ l₂ 0 k₂ n
          · simp only [if_pos hn]
          · rw [if_neg hn, zero_mul, mdlSliceJ_apply, if_neg hn, mul_zero]
        rw [hEq2]
        have h4 : eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ =>
            mdlSliceJ ρ P C₀ a f g l₁ l₂ 0 k₂ 0 (-1) t n x)) 1 Measure.count ≤ Bslice :=
          h1.trans (hcmp (Km1 Λ) (hKs1 Λ) cm1 hAm1A)
        calc eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ =>
                (if mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then mdlW2 P (Nat.floor (a n)) t else 0)
                  * mdlSliceJ ρ P C₀ a f g l₁ l₂ 0 k₂ 0 (-1) t n x)) 1 Measure.count
            ≤ (2 * ENNReal.ofReal Cw) * eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ =>
                mdlSliceJ ρ P C₀ a f g l₁ l₂ 0 k₂ 0 (-1) t n x)) 1 Measure.count := hmul
          _ ≤ (2 * ENNReal.ofReal Cw) * Bslice :=
              mul_le_mul_of_nonneg_left h4 (by positivity)
          _ ≤ Nw * Bslice := mul_le_mul_of_nonneg_right h2Cw (by positivity)
    -- the four-term bound
    have hfour := eLpNorm_varNorm_four_le (r := r) hr1 cs cg hCtop hcs_bd hcg_bd F1 F2 F3 F4
    have hsum : (((eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => F1 n x)) 1 Measure.count + eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => F2 n x)) 1 Measure.count) + eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => F3 n x)) 1 Measure.count) + eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => F4 n x)) 1 Measure.count) ≤ (Nw + Nw + Nw + Nw) * Bslice := by
      have hN : (Nw + Nw + Nw + Nw) * Bslice
          = ((Nw * Bslice + Nw * Bslice) + Nw * Bslice) + Nw * Bslice := by ring
      rw [hN]
      exact add_le_add (add_le_add (add_le_add hslice1 hslice2) hslice3) hslice4
    have hmain_le : eLpNorm (fun x : ℤ => variationalNorm r
          (fun n : ℕ => mdlPart ρ P C₀ a f g l₁ l₂ 0 k₂ n x)) 1 Measure.count
        ≤ Ccoef * ((Nw + Nw + Nw + Nw) * Bslice) := by
      have hid2 : (fun x : ℤ => variationalNorm r
            (fun n : ℕ => mdlPart ρ P C₀ a f g l₁ l₂ 0 k₂ n x))
          = (fun x : ℤ => variationalNorm r (fun n : ℕ =>
              cs * (F1 n x - F2 n x) - cg * F3 n x + cs * F4 n x)) := by
        funext x
        congr 1
        funext n
        exact congrFun (congrFun hid n) x
      rw [hid2]
      exact hfour.trans (mul_le_mul_of_nonneg_left hsum (by positivity))
    -- the absorption
    have hD : D * ENNReal.ofReal L0
        ≤ ENNReal.ofReal Ca * ENNReal.ofReal (lcWeight cF l₁ l₂ 0 k₂) := by
      have h0 : (2 : ℝ) ^ (-((P.natDegree : ℝ) * (k₂ : ℝ))) * L0
          ≤ Ca * lcWeight cF l₁ l₂ 0 k₂ := by
        have h := hCa l₁ l₂ k₂ hklt
        rw [hL0]
        refine (le_of_eq ?_).trans (h.trans
          (mul_le_mul_of_nonneg_left (lcWeight_le_of_le hcF_le_d l₁ l₂ 0 k₂) hCapos.le))
        ring
      have hDL : D * ENNReal.ofReal L0
          = ENNReal.ofReal ((2 : ℝ) ^ (-((P.natDegree : ℝ) * (k₂ : ℝ))) * L0) := by
        rw [hD0]
        rw [ENNReal.ofReal_mul (Real.rpow_pos_of_pos (by norm_num) _).le]
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
          (fun n : ℕ => mdlPart ρ P C₀ a f g l₁ l₂ 0 k₂ n x)) 1 Measure.count
        ≤ ((Kfun Λ : NNReal) : ENNReal) * ENNReal.ofReal (lcWeight cF l₁ l₂ 0 k₂)
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
              * (ENNReal.ofReal Ca * ENNReal.ofReal (lcWeight cF l₁ l₂ 0 k₂))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hD (show (0 : ENNReal) ≤ (Ks Λ : ENNReal) from bot_le))
          (show (0 : ENNReal) ≤ ENNReal.ofReal Kfac from bot_le)
      have hC : (ENNReal.ofReal Kfac) * ((Ks Λ : ENNReal)
              * (ENNReal.ofReal Ca * ENNReal.ofReal (lcWeight cF l₁ l₂ 0 k₂)))
            = ((ENNReal.ofReal Kfac * (Ks Λ : ENNReal) * ENNReal.ofReal Ca)
              * ENNReal.ofReal (lcWeight cF l₁ l₂ 0 k₂)) := by ring
      have hDc : ((ENNReal.ofReal Kfac * (Ks Λ : ENNReal) * ENNReal.ofReal Ca)
              * ENNReal.ofReal (lcWeight cF l₁ l₂ 0 k₂))
            ≤ (((Kfun Λ : NNReal) : ENNReal)
              * ENNReal.ofReal (lcWeight cF l₁ l₂ 0 k₂)) :=
        mul_le_mul_of_nonneg_right hcoef
          (show (0 : ENNReal) ≤ ENNReal.ofReal (lcWeight cF l₁ l₂ 0 k₂) from bot_le)
      have hmain : ((ENNReal.ofReal ιb * (Nw + Nw + Nw + Nw))
              * ((Ks Λ : ENNReal) * (D * ENNReal.ofReal L0)))
            ≤ (((Kfun Λ : NNReal) : ENNReal)
              * ENNReal.ofReal (lcWeight cF l₁ l₂ 0 k₂)) :=
        hA.trans (hB.trans ((le_of_eq hC).trans hDc))
      have hchain : ((ENNReal.ofReal ιb * (Nw + Nw + Nw + Nw))
              * ((Ks Λ : ENNReal) * (D * ENNReal.ofReal L0)))
              * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count
            ≤ ((((Kfun Λ : NNReal) : ENNReal)
              * ENNReal.ofReal (lcWeight cF l₁ l₂ 0 k₂))
              * eLpNorm f 2 Measure.count) * eLpNorm g 2 Measure.count :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmain
          (show (0 : ENNReal) ≤ eLpNorm f 2 Measure.count from bot_le))
          (show (0 : ENNReal) ≤ eLpNorm g 2 Measure.count from bot_le)
      refine hmain_le.trans ?_
      rw [hE1]
      exact hchain
    exact hfinal
  · -- ################ SMALL CASE ################
    have hkK : (k₂ : ℝ) ≤ K₀ := by exact_mod_cast hsmall
    -- the `t`-integration of the loss-form frozen-slice bound (the interval has length `1/2`)
    have hEqPart : mdlWIntF (fun _ _ => (1 : ℂ))
          (fun t n x => mdlSliceJ ρ P C₀ a f g l₁ l₂ 0 k₂ 0 0 t n x)
        = mdlPart ρ P C₀ a f g l₁ l₂ 0 k₂ := by
      rw [← mdlWInt_eq_mdlWIntF ρ P C₀ a f g l₁ l₂ 0 k₂ 0 0 (fun _ _ => (1 : ℂ)),
        mdlWInt_one_eq_mdlPartJ, ← mdlPartJ_zero_zero]
    have h00 : eLpNorm (fun x : ℤ => variationalNorm r
          (fun n : ℕ => mdlPart ρ P C₀ a f g l₁ l₂ 0 k₂ n x)) 1 Measure.count
        ≤ (K00 Λ : ENNReal) * ENNReal.ofReal (lossWeight c00 ρ l₁ l₂ 0 k₂)
          * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count := by
      rw [← hEqPart]
      refine mdlWIntF_norm_le (r := r) hr1 (fun _ _ => (1 : ℂ))
        (fun t n x => mdlSliceJ ρ P C₀ a f g l₁ l₂ 0 k₂ 0 0 t n x) ?_ ?_ ?_
      · intro n x
        simpa only [one_mul] using MdlSliceMeasurable ρ P C₀ a f g l₁ l₂ 0 k₂ 0 0 n x
      · intro n x
        simpa only [one_mul] using
          MdlSliceIntervalIntegrable ρ P C₀ a f g l₁ l₂ 0 k₂ 0 0 n x hf2 hg2
            (fun _ => by norm_num) (fun _ => by norm_num)
      · intro t ht
        have h := hK00 a Λ l₁ l₂ 0 k₂ t f g hΛ hlac ha1 ht (fun _ => by norm_num)
          (fun _ => by norm_num) hf2 hg2
        simpa only [one_mul] using h
    refine h00.trans ?_
    have hW1 : ENNReal.ofReal (lossWeight c00 ρ l₁ l₂ 0 k₂)
        ≤ ENNReal.ofReal (lossWeight A ρ l₁ l₂ 0 k₂) :=
      ENNReal.ofReal_le_ofReal (lossWeight_le_of_le_A hA00A hρ.le l₁ l₂ 0 k₂)
    have hW2 : ENNReal.ofReal (lossWeight A ρ l₁ l₂ 0 k₂)
        ≤ ENNReal.ofReal (Cs * lcWeight cF l₁ l₂ 0 k₂) :=
      ENNReal.ofReal_le_ofReal (hCs l₁ l₂ k₂ hklt hkK)
    have hfac : ENNReal.ofReal Cs * ENNReal.ofReal (lcWeight cF l₁ l₂ 0 k₂)
        = ENNReal.ofReal (Cs * lcWeight cF l₁ l₂ 0 k₂) := (ENNReal.ofReal_mul hCspos.le).symm
    have hE2 : ENNReal.ofReal ((K00 Λ : ℝ) * Cs) * ENNReal.ofReal (lcWeight cF l₁ l₂ 0 k₂)
        = (K00 Λ : ENNReal) * ENNReal.ofReal (Cs * lcWeight cF l₁ l₂ 0 k₂) := by
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
    calc (K00 Λ : ENNReal) * ENNReal.ofReal (lossWeight c00 ρ l₁ l₂ 0 k₂)
            * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count
        ≤ (K00 Λ : ENNReal) * ENNReal.ofReal (lossWeight A ρ l₁ l₂ 0 k₂)
            * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hW1
              (show (0 : ENNReal) ≤ (K00 Λ : ENNReal) from bot_le))
            (show (0 : ENNReal) ≤ eLpNorm f 2 Measure.count from bot_le))
            (show (0 : ENNReal) ≤ eLpNorm g 2 Measure.count from bot_le)
      _ ≤ (K00 Λ : ENNReal) * ENNReal.ofReal (Cs * lcWeight cF l₁ l₂ 0 k₂)
            * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hW2
              (show (0 : ENNReal) ≤ (K00 Λ : ENNReal) from bot_le))
            (show (0 : ENNReal) ≤ eLpNorm f 2 Measure.count from bot_le))
            (show (0 : ENNReal) ≤ eLpNorm g 2 Measure.count from bot_le)
      _ = ENNReal.ofReal ((K00 Λ : ℝ) * Cs) * ENNReal.ofReal (lcWeight cF l₁ l₂ 0 k₂)
            * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count := by
          rw [hE2]
      _ ≤ ((Kfun Λ : NNReal) : ENNReal) * ENNReal.ofReal (lcWeight cF l₁ l₂ 0 k₂)
            * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hcoef2
              (show (0 : ENNReal) ≤ ENNReal.ofReal (lcWeight cF l₁ l₂ 0 k₂) from bot_le))
            (show (0 : ENNReal) ≤ eLpNorm f 2 Measure.count from bot_le))
            (show (0 : ENNReal) ≤ eLpNorm g 2 Measure.count from bot_le)

end

end Work.KMTPlan.A6
