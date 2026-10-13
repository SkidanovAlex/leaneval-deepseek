/-
Copyright: work module for the Elgindi finite-time singularity project.

# The pointwise radial bound `RadSupZ` (`L³` right-hand side, `Nfk` auxiliary)

This module proves `Work.FTS.StrongPersist.L3Rhs.NfkAux.RadSupZ`: there is a universal
constant `C > 0` such that for every `h : ℝ → ℝ` which is differentiable on `(0,∞)` and
whose weighted square (`h² w²`) and weighted radial-derivative square (`(z h')² w²`) are
integrable over `(0,∞)`, one has

  `(h z)² ≤ C · (∫_{(0,∞)} h² w² + ∫_{(0,∞)} (z h')² w²)`  for every `z > 0`,

where `w z = (1+z)²/z²` is Elgindi's radial weight.  This is the one-dimensional Agmon
(supremum) inequality in the form needed by the priced estimate of the nonlinear
right-hand side.

## Proof

For `z > 0` put `c = z/2`, so that `z ∈ [c, 2c]`.  On `[c,2c]` the classical local Agmon
inequality `Work.FTS.H2.CruxPair.ZAgmon` (average the identity `h z² ≤ 2 h t² + 2 (h z - h t)²`
over the window of length `c` around `z` and estimate the increment by Cauchy–Schwarz)
gives

  `(h z)² ≤ (2/c) ∫_c^{2c} h² + 2c ∫_c^{2c} (h')²`.

Both window integrals are dominated by the weighted global data: on `[c,2c]` one has
`t ≥ c` and, `w` being antitone on `(0,∞)`, `w t ≥ w (2c) = w z`, whence

  `∫_c^{2c} h² ≤ (1/w(2c)²) ∫_{(0,∞)} h² w²`,
  `∫_c^{2c} (h')² ≤ (1/(c w(2c))²) ∫_{(0,∞)} (z h')² w²`.

The two resulting coefficients are both `2/(c w(2c)²) = 2/((z/2) w z²) = 4z³/(1+z)^4 ≤ 1`
because `(1+z)^4 = 1 + 4z + 6z² + 4z³ + z⁴ ≥ 4z³`.  Hence `C = 1` works.  The only
requirement on `h` beyond integrability is that `h` be differentiable at every point of
`(0,∞)` (so that the increments of `h` over the window are integrals of `h'`); the
fundamental theorem of calculus applies because `[c,2c]` is a compact subinterval of
`(0,∞)`: there `(h')²` is integrable, hence `h'` is integrable (Cauchy–Schwarz against the
constant `1` on a set of finite measure).
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.H2.CruxPair.ZAgmon

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs.NfkAux

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Elementary facts about the radial weight `w z = (1+z)²/z²` -/

private lemma w_pos {z : ℝ} (hz : 0 < z) : 0 < Work.Spaces.w z := by
  rw [Work.Spaces.w]
  exact div_pos (pow_pos (by linarith) 2) (pow_pos hz 2)

private lemma one_le_w {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w, one_le_div (pow_pos hz 2)]
  nlinarith

/-- The pointwise square of an a.e. strongly measurable function is a.e. strongly
measurable (the `Pi`-power form of Mathlib's `AEStronglyMeasurable.pow` is not
definitionally the pointwise one, so this small rewriting step is recorded once). -/
private lemma aeSM_sq {f : ℝ → ℝ} {μ : Measure ℝ} (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun t => (f t) ^ 2) μ :=
  (hf.pow 2).congr (Filter.Eventually.of_forall fun t => by simp [Pi.pow_apply])

/-- `t ↦ t * f t` is a.e. strongly measurable when `f` is. -/
private lemma aeSM_id_mul {f : ℝ → ℝ} {μ : Measure ℝ} (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun t => t * f t) μ :=
  (aestronglyMeasurable_id.mul hf).congr
    (Filter.Eventually.of_forall fun t => by simp [Pi.mul_apply])

/-- `w` is antitone on `(0,∞)`; in the form needed here: `w t ≥ w (2c)` for `t ∈ [c,2c]`,
`c > 0`. -/
private lemma w_two_le_of_mem {c t : ℝ} (hc : 0 < c) (ht : t ∈ Set.Icc c (2 * c)) :
    Work.Spaces.w (2 * c) ≤ Work.Spaces.w t := by
  have h2c : 0 < 2 * c := by linarith
  have ht0 : 0 < t := lt_of_lt_of_le hc ht.1
  have hle : (1 + 2 * c) / (2 * c) ≤ (1 + t) / t := by
    have h1 : (1 + 2 * c) / (2 * c) = 1 / (2 * c) + 1 := by
      rw [add_div, div_self (ne_of_gt h2c)]
    have h2 : (1 + t) / t = 1 / t + 1 := by rw [add_div, div_self (ne_of_gt ht0)]
    rw [h1, h2]
    have h3 : 1 / (2 * c) ≤ 1 / t := one_div_le_one_div_of_le ht0 ht.2
    linarith
  rw [Work.Spaces.w, Work.Spaces.w, ← div_pow, ← div_pow]
  exact pow_le_pow_left₀ (by positivity) hle 2

/-! ## The main theorem -/

theorem RadSupZ : ∃ C : ℝ, 0 < C ∧ ∀ (h : ℝ → ℝ),
    (∀ z ∈ Set.Ioi (0 : ℝ), DifferentiableAt ℝ h z) →
    MeasureTheory.IntegrableOn (fun z : ℝ => (h z) ^ 2 * (Work.Spaces.w z) ^ 2) (Set.Ioi 0) →
    MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.Spaces.Dz (fun z _ => h z) z 0) ^ 2 * (Work.Spaces.w z) ^ 2)
      (Set.Ioi 0) →
    ∀ z ∈ Set.Ioi (0 : ℝ), (h z) ^ 2 ≤ C *
      ((∫ z in Set.Ioi (0 : ℝ), (h z) ^ 2 * (Work.Spaces.w z) ^ 2)
        + (∫ z in Set.Ioi (0 : ℝ),
            (Work.Spaces.Dz (fun z _ => h z) z 0) ^ 2 * (Work.Spaces.w z) ^ 2)) := by
  refine ⟨1, one_pos, ?_⟩
  intro h hdiff hA hB z hz
  have hz0 : (0 : ℝ) < z := hz
  -- the value of `D_z` on a `θ`-independent function
  have hDz : ∀ t : ℝ, Work.Spaces.Dz (fun z _ => h z) t 0 = t * deriv h t := by
    intro t
    simp [Work.Spaces.Dz, Work.Spaces.pz]
  -- the second hypothesis, in the `z * deriv h z` form
  have hB' : MeasureTheory.IntegrableOn
      (fun t : ℝ => (t * deriv h t) ^ 2 * (Work.Spaces.w t) ^ 2) (Set.Ioi 0) :=
    hB.congr_fun (fun t _ => by
      show Work.Spaces.Dz (fun z _ => h z) t 0 ^ 2 * (Work.Spaces.w t) ^ 2
        = (t * deriv h t) ^ 2 * (Work.Spaces.w t) ^ 2
      rw [hDz t]) measurableSet_Ioi
  -- the window `[c, 2c]` containing `z`
  set c : ℝ := z / 2 with hc_def
  have hc : 0 < c := by rw [hc_def]; linarith
  have hc2c : c ≤ 2 * c := by linarith
  have h2c : 2 * c = z := by rw [hc_def]; ring
  have hzIcc : z ∈ Set.Icc c (2 * c) := by
    constructor <;> rw [hc_def] <;> linarith
  have hIcc_sub : Set.Icc c (2 * c) ⊆ Set.Ioi (0 : ℝ) := fun t ht => lt_of_lt_of_le hc ht.1
  have hIoc_sub : Set.Ioc c (2 * c) ⊆ Set.Ioi (0 : ℝ) := fun t ht => lt_of_lt_of_le hc ht.1.le
  -- `h` is continuous on the window
  have hdiffOn : DifferentiableOn ℝ h (Set.Ioi (0 : ℝ)) :=
    fun x hx => (hdiff x hx).differentiableWithinAt
  have hcont : ContinuousOn h (Set.Icc c (2 * c)) := hdiffOn.continuousOn.mono hIcc_sub
  -- ### Step 1: `(∂_z h)²` and `∂_z h` are integrable on the window
  -- `(z h')²` is integrable on `(0,∞)` since `w ≥ 1`
  have hB1 : MeasureTheory.IntegrableOn (fun t : ℝ => (t * deriv h t) ^ 2) (Set.Ioi 0) := by
    refine Integrable.mono' hB' ?_ ?_
    · exact aeSM_sq (aeSM_id_mul (aestronglyMeasurable_deriv h (volume.restrict (Set.Ioi (0 : ℝ)))))
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      have h1 : (1 : ℝ) ≤ (Work.Spaces.w t) ^ 2 := by
        have hw := one_le_w ht
        nlinarith
      nlinarith [sq_nonneg (t * deriv h t)]
  -- hence `(h')²` is integrable on `[c,2c]`
  have hB2 : MeasureTheory.IntegrableOn (fun t : ℝ => (deriv h t) ^ 2) (Set.Icc c (2 * c)) := by
    have hc2 : 0 < c ^ 2 := pow_pos hc 2
    refine Integrable.mono' ((hB'.mono_set hIcc_sub).const_mul (1 / c ^ 2)) ?_ ?_
    · exact aeSM_sq (aestronglyMeasurable_deriv h (volume.restrict (Set.Icc c (2 * c))))
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      have ht0 : 0 < t := lt_of_lt_of_le hc ht.1
      have hct : c ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hc.le ht.1 2
      have hw1 : (1 : ℝ) ≤ (Work.Spaces.w t) ^ 2 := by
        have hw := one_le_w ht0
        nlinarith
      have h1 : (deriv h t) ^ 2 ≤ (t * deriv h t) ^ 2 / c ^ 2 := by
        rw [le_div_iff₀ hc2, show (t * deriv h t) ^ 2 = (deriv h t) ^ 2 * t ^ 2 by ring]
        exact mul_le_mul_of_nonneg_left hct (sq_nonneg _)
      have h2 : (t * deriv h t) ^ 2 / c ^ 2
          ≤ (1 / c ^ 2) * ((t * deriv h t) ^ 2 * (Work.Spaces.w t) ^ 2) := by
        rw [show (t * deriv h t) ^ 2 / c ^ 2 = (1 / c ^ 2) * (t * deriv h t) ^ 2 by ring]
        exact mul_le_mul_of_nonneg_left
          (by simpa using mul_le_mul_of_nonneg_left hw1 (sq_nonneg (t * deriv h t)))
          (by positivity)
      linarith
  -- `h'` itself is integrable on `[c,2c]` (Cauchy–Schwarz on a set of finite measure)
  have hderivInt : MeasureTheory.IntegrableOn (fun t : ℝ => deriv h t) (Set.Icc c (2 * c)) := by
    have hfin : IsFiniteMeasure (volume.restrict (Set.Icc c (2 * c))) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact measure_Icc_lt_top⟩
    haveI := hfin
    have hmem : MemLp (fun t : ℝ => deriv h t) 2 (volume.restrict (Set.Icc c (2 * c))) := by
      rw [memLp_two_iff_integrable_sq
        (aestronglyMeasurable_deriv h (volume.restrict (Set.Icc c (2 * c))))]
      exact hB2
    exact hmem.integrable (by norm_num)
  -- ### Step 2: the fundamental theorem of calculus on the window
  have hFTC : ∀ x ∈ Set.Icc c (2 * c), ∀ y ∈ Set.Icc c (2 * c),
      h x - h y = ∫ t in y..x, deriv h t := by
    intro x hx y hy
    have hsub₁ : Set.Ioc y x ⊆ Set.Icc c (2 * c) :=
      Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc hy.1 hx.2)
    have hsub₂ : Set.Ioc x y ⊆ Set.Icc c (2 * c) :=
      Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc hx.1 hy.2)
    have hint : IntervalIntegrable (fun t : ℝ => deriv h t) volume y x :=
      ⟨hderivInt.mono_set hsub₁, hderivInt.mono_set hsub₂⟩
    have hsub_uIcc : Set.uIcc y x ⊆ Set.Icc c (2 * c) := by
      rcases le_total y x with hle | hle
      · rw [Set.uIcc_of_le hle]; exact Set.Icc_subset_Icc hy.1 hx.2
      · rw [Set.uIcc_of_ge hle]; exact Set.Icc_subset_Icc hx.1 hy.2
    have hder : ∀ s ∈ Set.uIcc y x, HasDerivAt h (deriv h s) s := by
      intro s hs
      exact (hdiff s (lt_of_lt_of_le hc (hsub_uIcc hs).1)).hasDerivAt
    exact (intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint).symm
  -- ### Step 3: the two interval integrability hypotheses of Agmon
  have hint1 : IntervalIntegrable (fun t : ℝ => (h t) ^ 2) volume c (2 * c) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hc2c]
    refine Integrable.mono' (hA.mono_set hIcc_sub) ?_ ?_
    · exact aeSM_sq (hcont.aestronglyMeasurable measurableSet_Icc)
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      have hw1 : (1 : ℝ) ≤ (Work.Spaces.w t) ^ 2 := by
        have hw := one_le_w (lt_of_lt_of_le hc ht.1)
        nlinarith
      nlinarith [sq_nonneg (h t)]
  have hint2 : IntervalIntegrable (fun t : ℝ => (deriv h t) ^ 2) volume c (2 * c) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hc2c]
    exact hB2
  -- ### Step 4: the local Agmon inequality on the window
  have hZg := Work.FTS.H2.CruxPair.ZAgmon h hc hcont hFTC hint1 hint2 z hzIcc
  -- ### Step 5: dominating the window integrals by the weighted global data
  have hb1 : ∫ t in Set.Ioc c (2 * c), (h t) ^ 2
      ≤ (1 / (Work.Spaces.w (2 * c)) ^ 2) *
          ∫ t in Set.Ioi (0 : ℝ), (h t) ^ 2 * (Work.Spaces.w t) ^ 2 := by
    have hm0 : 0 < (Work.Spaces.w (2 * c)) ^ 2 := pow_pos (w_pos (by linarith)) 2
    have hpt : ∀ t ∈ Set.Ioc c (2 * c), (h t) ^ 2
        ≤ (1 / (Work.Spaces.w (2 * c)) ^ 2) * ((h t) ^ 2 * (Work.Spaces.w t) ^ 2) := by
      intro t ht
      have hwt : Work.Spaces.w (2 * c) ≤ Work.Spaces.w t :=
        w_two_le_of_mem hc ⟨ht.1.le, ht.2⟩
      have h2 : (1 : ℝ) ≤ (Work.Spaces.w t) ^ 2 / (Work.Spaces.w (2 * c)) ^ 2 := by
        rw [one_le_div hm0]
        exact pow_le_pow_left₀ (le_of_lt (w_pos (by linarith))) hwt 2
      calc (h t) ^ 2 = (h t) ^ 2 * 1 := (mul_one _).symm
        _ ≤ (h t) ^ 2 * ((Work.Spaces.w t) ^ 2 / (Work.Spaces.w (2 * c)) ^ 2) :=
              mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
        _ = (1 / (Work.Spaces.w (2 * c)) ^ 2) * ((h t) ^ 2 * (Work.Spaces.w t) ^ 2) := by ring
    have hIntR : MeasureTheory.IntegrableOn
        (fun t : ℝ => (1 / (Work.Spaces.w (2 * c)) ^ 2) * ((h t) ^ 2 * (Work.Spaces.w t) ^ 2))
        (Set.Ioc c (2 * c)) :=
      (hA.mono_set hIoc_sub).const_mul _
    have hmono : ∫ t in Set.Ioc c (2 * c), (h t) ^ 2
        ≤ ∫ t in Set.Ioc c (2 * c),
            (1 / (Work.Spaces.w (2 * c)) ^ 2) * ((h t) ^ 2 * (Work.Spaces.w t) ^ 2) :=
      integral_mono_of_nonneg (ae_of_all _ fun t => sq_nonneg _) hIntR
        ((ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ hpt))
    have hstep : ∫ t in Set.Ioc c (2 * c),
          (1 / (Work.Spaces.w (2 * c)) ^ 2) * ((h t) ^ 2 * (Work.Spaces.w t) ^ 2)
        = (1 / (Work.Spaces.w (2 * c)) ^ 2) *
            ∫ t in Set.Ioc c (2 * c), (h t) ^ 2 * (Work.Spaces.w t) ^ 2 :=
      MeasureTheory.integral_const_mul _ _
    have hdom : ∫ t in Set.Ioc c (2 * c), (h t) ^ 2 * (Work.Spaces.w t) ^ 2
        ≤ ∫ t in Set.Ioi (0 : ℝ), (h t) ^ 2 * (Work.Spaces.w t) ^ 2 :=
      setIntegral_mono_set hA (ae_of_all _ fun t => by positivity) hIoc_sub.eventuallySubset
    calc ∫ t in Set.Ioc c (2 * c), (h t) ^ 2
        ≤ ∫ t in Set.Ioc c (2 * c),
            (1 / (Work.Spaces.w (2 * c)) ^ 2) * ((h t) ^ 2 * (Work.Spaces.w t) ^ 2) := hmono
      _ = (1 / (Work.Spaces.w (2 * c)) ^ 2) *
            ∫ t in Set.Ioc c (2 * c), (h t) ^ 2 * (Work.Spaces.w t) ^ 2 := hstep
      _ ≤ (1 / (Work.Spaces.w (2 * c)) ^ 2) *
            ∫ t in Set.Ioi (0 : ℝ), (h t) ^ 2 * (Work.Spaces.w t) ^ 2 :=
          mul_le_mul_of_nonneg_left hdom (by positivity)
  have hb2 : ∫ t in Set.Ioc c (2 * c), (deriv h t) ^ 2
      ≤ (1 / (c * Work.Spaces.w (2 * c)) ^ 2) *
          ∫ t in Set.Ioi (0 : ℝ), (t * deriv h t) ^ 2 * (Work.Spaces.w t) ^ 2 := by
    have hm0 : 0 < (c * Work.Spaces.w (2 * c)) ^ 2 := by
      have := w_pos (show (0 : ℝ) < 2 * c by linarith)
      positivity
    have hpt : ∀ t ∈ Set.Ioc c (2 * c), (deriv h t) ^ 2
        ≤ (1 / (c * Work.Spaces.w (2 * c)) ^ 2) *
            ((t * deriv h t) ^ 2 * (Work.Spaces.w t) ^ 2) := by
      intro t ht
      have ht0 : 0 < t := lt_of_lt_of_le hc ht.1.le
      have hwt : Work.Spaces.w (2 * c) ≤ Work.Spaces.w t :=
        w_two_le_of_mem hc ⟨ht.1.le, ht.2⟩
      have hct : c ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hc.le ht.1.le 2
      have hwt2 : (Work.Spaces.w (2 * c)) ^ 2 ≤ (Work.Spaces.w t) ^ 2 :=
        pow_le_pow_left₀ (le_of_lt (w_pos (by linarith))) hwt 2
      have hkey : (deriv h t) ^ 2 * (c * Work.Spaces.w (2 * c)) ^ 2
          ≤ (t * deriv h t) ^ 2 * (Work.Spaces.w t) ^ 2 := by
        have hdh : (0 : ℝ) ≤ (deriv h t) ^ 2 := sq_nonneg _
        have htw : (0 : ℝ) ≤ (Work.Spaces.w (2 * c)) ^ 2 := sq_nonneg _
        have hcur : (deriv h t) ^ 2 * c ^ 2 * (Work.Spaces.w (2 * c)) ^ 2
            ≤ (deriv h t) ^ 2 * t ^ 2 * (Work.Spaces.w (2 * c)) ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hct hdh) htw
        have hcur2 : (deriv h t) ^ 2 * t ^ 2 * (Work.Spaces.w (2 * c)) ^ 2
            ≤ (deriv h t) ^ 2 * t ^ 2 * (Work.Spaces.w t) ^ 2 :=
          mul_le_mul_of_nonneg_left hwt2 (by positivity)
        have e1 : (deriv h t) ^ 2 * (c * Work.Spaces.w (2 * c)) ^ 2
            = (deriv h t) ^ 2 * c ^ 2 * (Work.Spaces.w (2 * c)) ^ 2 := by ring
        have e2 : (t * deriv h t) ^ 2 = (deriv h t) ^ 2 * t ^ 2 := by ring
        rw [e1, e2]
        linarith
      rw [show (1 / (c * Work.Spaces.w (2 * c)) ^ 2)
            * ((t * deriv h t) ^ 2 * (Work.Spaces.w t) ^ 2)
          = ((t * deriv h t) ^ 2 * (Work.Spaces.w t) ^ 2)
            / (c * Work.Spaces.w (2 * c)) ^ 2 by ring,
        le_div_iff₀ hm0]
      exact hkey
    have hIntR : MeasureTheory.IntegrableOn
        (fun t : ℝ => (1 / (c * Work.Spaces.w (2 * c)) ^ 2)
          * ((t * deriv h t) ^ 2 * (Work.Spaces.w t) ^ 2))
        (Set.Ioc c (2 * c)) :=
      (hB'.mono_set hIoc_sub).const_mul _
    have hmono : ∫ t in Set.Ioc c (2 * c), (deriv h t) ^ 2
        ≤ ∫ t in Set.Ioc c (2 * c),
            (1 / (c * Work.Spaces.w (2 * c)) ^ 2)
              * ((t * deriv h t) ^ 2 * (Work.Spaces.w t) ^ 2) :=
      integral_mono_of_nonneg (ae_of_all _ fun t => sq_nonneg _) hIntR
        ((ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ hpt))
    have hstep : ∫ t in Set.Ioc c (2 * c),
          (1 / (c * Work.Spaces.w (2 * c)) ^ 2)
            * ((t * deriv h t) ^ 2 * (Work.Spaces.w t) ^ 2)
        = (1 / (c * Work.Spaces.w (2 * c)) ^ 2) *
            ∫ t in Set.Ioc c (2 * c), (t * deriv h t) ^ 2 * (Work.Spaces.w t) ^ 2 :=
      MeasureTheory.integral_const_mul _ _
    have hdom : ∫ t in Set.Ioc c (2 * c), (t * deriv h t) ^ 2 * (Work.Spaces.w t) ^ 2
        ≤ ∫ t in Set.Ioi (0 : ℝ), (t * deriv h t) ^ 2 * (Work.Spaces.w t) ^ 2 :=
      setIntegral_mono_set hB' (ae_of_all _ fun t => by positivity) hIoc_sub.eventuallySubset
    calc ∫ t in Set.Ioc c (2 * c), (deriv h t) ^ 2
        ≤ ∫ t in Set.Ioc c (2 * c),
            (1 / (c * Work.Spaces.w (2 * c)) ^ 2)
              * ((t * deriv h t) ^ 2 * (Work.Spaces.w t) ^ 2) := hmono
      _ = (1 / (c * Work.Spaces.w (2 * c)) ^ 2) *
            ∫ t in Set.Ioc c (2 * c), (t * deriv h t) ^ 2 * (Work.Spaces.w t) ^ 2 := hstep
      _ ≤ (1 / (c * Work.Spaces.w (2 * c)) ^ 2) *
            ∫ t in Set.Ioi (0 : ℝ), (t * deriv h t) ^ 2 * (Work.Spaces.w t) ^ 2 :=
          mul_le_mul_of_nonneg_left hdom (by positivity)
  -- ### Step 6: the coefficient is at most `1`
  have hcoef : 2 / (c * (Work.Spaces.w (2 * c)) ^ 2) ≤ 1 := by
    have hcm0 : 0 < c * (Work.Spaces.w (2 * c)) ^ 2 := by
      have := w_pos (show (0 : ℝ) < 2 * c by linarith)
      positivity
    rw [div_le_one hcm0]
    -- it remains to see `2 ≤ c · w(2c)²`
    have hmain : 4 ≤ z * (Work.Spaces.w z) ^ 2 := by
      have hwz : (Work.Spaces.w z) ^ 2 = (1 + z) ^ 4 / z ^ 4 := by
        rw [Work.Spaces.w, div_pow]
        ring_nf
      have hz0ne : z ≠ 0 := ne_of_gt hz0
      have hz4 : (0 : ℝ) < z ^ 4 := by positivity
      have hzsplit : z * ((1 + z) ^ 4 / z ^ 4) = (1 + z) ^ 4 / z ^ 3 := by
        field_simp
      rw [hwz, hzsplit]
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < z ^ 3)]
      have hexp : (1 + z) ^ 4 = 1 + 4 * z + 6 * z ^ 2 + 4 * z ^ 3 + z ^ 4 := by ring
      have hnn : (0 : ℝ) ≤ 1 + 4 * z + 6 * z ^ 2 + z ^ 4 := by positivity
      nlinarith [hexp, hnn]
    have hceq : c * (Work.Spaces.w (2 * c)) ^ 2 = (z * (Work.Spaces.w z) ^ 2) / 2 := by
      rw [hc_def, h2c]
      ring
    rw [hceq]
    linarith
  -- ### Step 7: assembly
  have hAB : 0 ≤ (∫ z in Set.Ioi (0 : ℝ), (h z) ^ 2 * (Work.Spaces.w z) ^ 2)
      + (∫ z in Set.Ioi (0 : ℝ), (z * deriv h z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
    have h1 : 0 ≤ ∫ z in Set.Ioi (0 : ℝ), (h z) ^ 2 * (Work.Spaces.w z) ^ 2 :=
      integral_nonneg_of_ae (ae_of_all _ fun t => by positivity)
    have h2 : 0 ≤ ∫ z in Set.Ioi (0 : ℝ), (z * deriv h z) ^ 2 * (Work.Spaces.w z) ^ 2 :=
      integral_nonneg_of_ae (ae_of_all _ fun t => by positivity)
    linarith
  have hfinal : (h z) ^ 2 ≤ 1 *
      ((∫ z in Set.Ioi (0 : ℝ), (h z) ^ 2 * (Work.Spaces.w z) ^ 2)
        + (∫ z in Set.Ioi (0 : ℝ), (z * deriv h z) ^ 2 * (Work.Spaces.w z) ^ 2)) := by
    simp only [intervalIntegral.integral_of_le hc2c] at hZg
    have hstep1 := mul_le_mul_of_nonneg_left hb1 (show (0 : ℝ) ≤ 2 / c by positivity)
    have hstep2 := mul_le_mul_of_nonneg_left hb2 (show (0 : ℝ) ≤ 2 * c by positivity)
    have harith :
        (2 / c) * ((1 / (Work.Spaces.w (2 * c)) ^ 2) *
            ∫ z in Set.Ioi (0 : ℝ), (h z) ^ 2 * (Work.Spaces.w z) ^ 2)
          + (2 * c) * ((1 / (c * Work.Spaces.w (2 * c)) ^ 2) *
            ∫ z in Set.Ioi (0 : ℝ), (z * deriv h z) ^ 2 * (Work.Spaces.w z) ^ 2)
        = (2 / (c * (Work.Spaces.w (2 * c)) ^ 2)) *
          ((∫ z in Set.Ioi (0 : ℝ), (h z) ^ 2 * (Work.Spaces.w z) ^ 2)
            + (∫ z in Set.Ioi (0 : ℝ), (z * deriv h z) ^ 2 * (Work.Spaces.w z) ^ 2)) := by
      have hcne : c ≠ 0 := ne_of_gt hc
      have hmne : (Work.Spaces.w (2 * c)) ^ 2 ≠ 0 :=
        ne_of_gt (pow_pos (w_pos (show (0 : ℝ) < 2 * c by linarith)) 2)
      field_simp
    calc (h z) ^ 2
        ≤ (2 / c) * (∫ t in Set.Ioc c (2 * c), (h t) ^ 2)
            + (2 * c) * (∫ t in Set.Ioc c (2 * c), (deriv h t) ^ 2) := hZg
      _ ≤ (2 / c) * ((1 / (Work.Spaces.w (2 * c)) ^ 2) *
              ∫ z in Set.Ioi (0 : ℝ), (h z) ^ 2 * (Work.Spaces.w z) ^ 2)
            + (2 * c) * ((1 / (c * Work.Spaces.w (2 * c)) ^ 2) *
              ∫ z in Set.Ioi (0 : ℝ), (z * deriv h z) ^ 2 * (Work.Spaces.w z) ^ 2) :=
          add_le_add hstep1 hstep2
      _ = (2 / (c * (Work.Spaces.w (2 * c)) ^ 2)) *
            ((∫ z in Set.Ioi (0 : ℝ), (h z) ^ 2 * (Work.Spaces.w z) ^ 2)
              + (∫ z in Set.Ioi (0 : ℝ), (z * deriv h z) ^ 2 * (Work.Spaces.w z) ^ 2)) := harith
      _ ≤ 1 * ((∫ z in Set.Ioi (0 : ℝ), (h z) ^ 2 * (Work.Spaces.w z) ^ 2)
              + (∫ z in Set.Ioi (0 : ℝ), (z * deriv h z) ^ 2 * (Work.Spaces.w z) ^ 2)) :=
          mul_le_mul_of_nonneg_right hcoef hAB
  -- rewrite the `D_z` occurrence of the statement into `z * deriv h z`
  have hBeq : (∫ z in Set.Ioi (0 : ℝ),
        (Work.Spaces.Dz (fun z _ => h z) z 0) ^ 2 * (Work.Spaces.w z) ^ 2)
      = ∫ z in Set.Ioi (0 : ℝ), (z * deriv h z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro t _
    show Work.Spaces.Dz (fun z _ => h z) t 0 ^ 2 * (Work.Spaces.w t) ^ 2
      = (t * deriv h t) ^ 2 * (Work.Spaces.w t) ^ 2
    rw [hDz t]
  rw [hBeq]
  exact hfinal

end Work.FTS.StrongPersist.L3Rhs.NfkAux
