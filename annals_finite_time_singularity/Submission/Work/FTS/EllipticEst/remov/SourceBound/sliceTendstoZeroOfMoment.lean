import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.integrableAbsOfSqSeta
import Submission.Work.FTS.EllipticEst.SliceLocal.integrableOn_sinCos2_Lzero1
import Submission.Work.Elliptic.Lzero_orthogonal
import Submission.Work.FTS.EllipticEst.exists_tendsto_nhdsGT_zero_of_integrableOn_deriv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov.SourceBound

set_option autoImplicit false

/-! ## Auxiliary facts

The proof of `sliceTendstoZeroOfMoment` goes through the exact derivative
`(Lzero1 u θ) · sinθcos²θ = d/dθ [ -u'(θ) sinθcos²θ + u(θ) cosθcos2θ ]`
(`Work.Elliptic.hasDerivAt_Lzero_antideriv`), whose boundary values are `lim_{0⁺} u` at `0` and
`0` at `π/2`.  Hence `∫_{Iθ} Lzero1 u · sinCos2 = -lim_{0⁺} u`, and the assumed moment condition
forces the limit to vanish.  The two lemmas below supply the control of `u'` (from the weighted
square-integrability of `u''`) and the existence of the left endpoint limit. -/

/-- **`u'` is bounded on the open quadrant.**  Since `sEta θ = sin(2θ)^{-η} ≥ 1` on `(0,π/2)`,
the hypothesis makes `|u''|` integrable on `Iθ` (`integrableAbsOfSqSeta`), and the fundamental
theorem of calculus based at `π/4` bounds `u'` by `|u'(π/4)| + ∫_{Iθ}|u''|`. -/
lemma auxDerivBound {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hint : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv u t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ) :
    ∃ M : ℝ, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |deriv u θ| ≤ M := by
  have hIoo : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / 2)) := isOpen_Ioo
  have hd1 : ContDiffOn ℝ 1 (deriv u) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hu.deriv_of_isOpen hIoo (m := 1) (by norm_num)
  have hd2 : ContinuousOn (deriv (fun t => deriv u t)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    contDiffOn_zero.1 (hd1.deriv_of_isOpen hIoo (m := 0) (by norm_num))
  have hdc : ContinuousOn (deriv u) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hu.continuousOn_deriv_of_isOpen hIoo (by norm_num)
  have hdiff1 : DifferentiableOn ℝ (deriv u) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hd1.differentiableOn (by norm_num)
  have habs : MeasureTheory.IntegrableOn
      (fun θ : ℝ => |deriv (fun t => deriv u t) θ|) Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.integrableAbsOfSqSeta hd2 hint
  have hpi4 : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hpi4lt : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  -- increment estimate on any subinterval `[a,b] ⊆ (0,π/2)`
  have hkey : ∀ a b : ℝ, a ≤ b → 0 < a → b < Real.pi / 2 →
      |deriv u b - deriv u a|
        ≤ ∫ x in Work.Spaces.Iθ, |deriv (fun t => deriv u t) x| := by
    intro a b hab ha hb
    have hsub : Set.uIcc a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
      rw [Set.uIcc_of_le hab]
      intro x hx
      exact ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hb⟩
    have hcont : ContinuousOn (deriv u) (Set.uIcc a b) := hdc.mono hsub
    have hdder : ∀ x ∈ Set.uIoo a b, DifferentiableAt ℝ (deriv u) x := by
      intro x hx
      rw [Set.uIoo_of_le hab] at hx
      exact hdiff1.differentiableAt (isOpen_Ioo.mem_nhds
        ⟨lt_trans ha hx.1, lt_trans hx.2 hb⟩)
    have hintI : IntervalIntegrable (deriv (fun t => deriv u t)) volume a b :=
      (hd2.mono hsub).intervalIntegrable
    have hftc : ∫ y in a..b, deriv (fun t => deriv u t) y = deriv u b - deriv u a :=
      intervalIntegral.integral_deriv_eq_sub_uIoo hcont hdder hintI
    have hle : ∫ y in a..b, |deriv (fun t => deriv u t) y|
        ≤ ∫ x in Work.Spaces.Iθ, |deriv (fun t => deriv u t) x| := by
      rw [intervalIntegral.integral_of_le hab]
      refine setIntegral_mono_set habs (Eventually.of_forall (fun x => abs_nonneg _)) ?_
      exact Eventually.of_forall (fun x hx =>
        ⟨le_of_lt (lt_trans ha hx.1), le_of_lt (lt_of_le_of_lt hx.2 hb)⟩)
    calc |deriv u b - deriv u a|
        = |∫ y in a..b, deriv (fun t => deriv u t) y| := by rw [hftc]
      _ ≤ ∫ y in a..b, |deriv (fun t => deriv u t) y| :=
          intervalIntegral.abs_integral_le_integral_abs
            (f := fun y => deriv (fun t => deriv u t) y) hab
      _ ≤ _ := hle
  refine ⟨|deriv u (Real.pi / 4)|
      + ∫ x in Work.Spaces.Iθ, |deriv (fun t => deriv u t) x|, ?_⟩
  intro θ hθ
  have hsum : |deriv u θ| ≤ |deriv u θ - deriv u (Real.pi / 4)|
      + |deriv u (Real.pi / 4)| := by
    have h := abs_add_le (deriv u θ - deriv u (Real.pi / 4)) (deriv u (Real.pi / 4))
    rwa [sub_add_cancel] at h
  have hstep : |deriv u θ - deriv u (Real.pi / 4)|
      ≤ ∫ x in Work.Spaces.Iθ, |deriv (fun t => deriv u t) x| := by
    rcases le_total θ (Real.pi / 4) with hle | hge
    · rw [abs_sub_comm]
      exact hkey θ (Real.pi / 4) hle hθ.1 hpi4lt
    · exact hkey (Real.pi / 4) θ hge hpi4 hθ.2
  calc |deriv u θ| ≤ |deriv u θ - deriv u (Real.pi / 4)| + |deriv u (Real.pi / 4)| := hsum
    _ ≤ (∫ x in Work.Spaces.Iθ, |deriv (fun t => deriv u t) x|) + |deriv u (Real.pi / 4)| :=
        add_le_add hstep le_rfl
    _ = |deriv u (Real.pi / 4)|
        + ∫ x in Work.Spaces.Iθ, |deriv (fun t => deriv u t) x| := by ring

/-- **The left endpoint limit exists.**  A `C²` function on `(0,π/2)` whose second derivative
satisfies the weighted square-integrability hypothesis has a finite limit at `0⁺`: the weight
forces `|u''| ∈ L¹`, hence `u'` is bounded on `(0,π/4)` and therefore integrable there, and
`exists_tendsto_nhdsGT_zero_of_integrableOn_deriv` applies. -/
lemma auxLimitAtZero {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hint : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv u t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ) :
    ∃ α : ℝ, Filter.Tendsto u (nhdsWithin 0 (Set.Ioi 0)) (nhds α) := by
  obtain ⟨M, hM⟩ := auxDerivBound hu hint
  have hpi4 : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hpi4lt : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  refine Work.FTS.EllipticEst.exists_tendsto_nhdsGT_zero_of_integrableOn_deriv
    (f := u) (f' := deriv u) (δ := Real.pi / 4) hpi4 ?_ ?_
  · intro x hx
    have hx' : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hx.1, lt_of_lt_of_le hx.2 hpi4lt.le⟩
    exact ((hu.contDiffAt (isOpen_Ioo.mem_nhds hx')).differentiableAt (by norm_num)).hasDerivAt
  · refine MeasureTheory.IntegrableOn.of_bound ?_ (measurable_deriv u).aestronglyMeasurable M ?_
    · rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
    · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun x hx => by
        rw [Real.norm_eq_abs]
        exact hM x ⟨hx.1, lt_of_lt_of_le hx.2 hpi4lt.le⟩)

/-- **The angular moment identity.**  Under the hypotheses of
`sliceTendstoZeroOfMoment` (except the moment condition) one has
`∫_{Iθ} Lzero1 u · sinθcos²θ = -lim_{0⁺} u`. -/
lemma auxMoment {u : ℝ → ℝ} {α : ℝ}
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hint : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv u t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ)
    (hg : MeasureTheory.IntegrableOn
      (fun θ => (Work.FTS.EllipticEst.Lzero1 u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ)
    (hlim : Filter.Tendsto u (nhdsWithin 0 (Set.Ioi 0)) (nhds α)) :
    (∫ θ in Work.Spaces.Iθ,
      Work.FTS.EllipticEst.Lzero1 u θ * Work.Elliptic.sinCos2 θ) = -α := by
  obtain ⟨M, hM⟩ := auxDerivBound hu hint
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpi4 : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hpi4lt : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hle_pi : (0 : ℝ) ≤ Real.pi / 2 := by linarith
  -- ## the exact derivative
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun θ : ℝ => -(deriv u θ) * Work.Elliptic.sinCos2 θ
          + u θ * (Real.cos θ * Real.cos (2 * θ)))
        (Work.FTS.EllipticEst.Lzero1 u x * Work.Elliptic.sinCos2 x) x := by
    intro x hx
    have h2 : ContDiffAt ℝ 2 u x := hu.contDiffAt (isOpen_Ioo.mem_nhds hx)
    have h3 := Work.Elliptic.hasDerivAt_Lzero_antideriv (fun _ θ' => u θ') 0 x hx h2
    have hL : Work.Elliptic.Lzero (fun _ θ' => u θ') 0 x
        = Work.FTS.EllipticEst.Lzero1 u x := by
      simpa using (congrFun (Work.FTS.EllipticEst.Lzero1_eq_Lzero u 0) x).symm
    rw [hL] at h3
    simpa using h3
  -- ## integrability of the integrand
  have hgint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.FTS.EllipticEst.Lzero1 u θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ := by
    have h0 := Work.FTS.EllipticEst.SliceLocal.integrableOn_sinCos2_Lzero1 u hu hg
    rw [MeasureTheory.IntegrableOn] at h0 ⊢
    refine h0.congr (Eventually.of_forall (fun θ => ?_))
    simp only [Work.Elliptic.sinCos2]
    ring
  have hint' : IntervalIntegrable
      (fun θ : ℝ => Work.FTS.EllipticEst.Lzero1 u θ * Work.Elliptic.sinCos2 θ)
      volume 0 (Real.pi / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hle_pi).mpr
      (hgint.mono_set (fun x hx => ⟨le_of_lt hx.1, hx.2⟩))
  -- ## continuity facts for the boundary terms
  have hScont : Continuous (fun θ : ℝ => Work.Elliptic.sinCos2 θ) := by
    have hfun : (fun θ : ℝ => Work.Elliptic.sinCos2 θ)
        = fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2 := rfl
    rw [hfun]
    exact Real.continuous_sin.mul (Real.continuous_cos.pow 2)
  have hcoscont : Continuous (fun θ : ℝ => Real.cos θ * Real.cos (2 * θ)) := by fun_prop
  -- ## the left endpoint limit of the antiderivative
  have hA0 : Tendsto (fun θ : ℝ => -(deriv u θ) * Work.Elliptic.sinCos2 θ)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have hmaj : Tendsto (fun θ : ℝ => M * |Work.Elliptic.sinCos2 θ|)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      have h0 : (fun θ : ℝ => Work.Elliptic.sinCos2 θ) 0 = 0 := by
        simp only [Work.Elliptic.sinCos2]
        norm_num
      have hS : Tendsto (fun θ : ℝ => Work.Elliptic.sinCos2 θ)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
        simpa [h0] using ((hScont.continuousAt (x := 0)).tendsto).mono_left nhdsWithin_le_nhds
      simpa using hS.abs.const_mul M
    have hsqueeze : Tendsto (fun θ : ℝ => ‖-(deriv u θ) * Work.Elliptic.sinCos2 θ‖)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      refine squeeze_zero' (Eventually.of_forall (fun θ => norm_nonneg _)) ?_ hmaj
      rw [eventually_nhdsWithin_iff]
      filter_upwards [Iio_mem_nhds (show (0 : ℝ) < Real.pi / 2 by linarith)] with θ hθ hθmem
      rw [Real.norm_eq_abs, abs_mul, abs_neg]
      exact mul_le_mul_of_nonneg_right (hM θ ⟨hθmem, hθ⟩) (abs_nonneg _)
    rwa [tendsto_zero_iff_norm_tendsto_zero]
  have hB0 : Tendsto (fun θ : ℝ => u θ * (Real.cos θ * Real.cos (2 * θ)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds α) := by
    have hc : Tendsto (fun θ : ℝ => Real.cos θ * Real.cos (2 * θ))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 1) := by
      have h0 : (fun θ : ℝ => Real.cos θ * Real.cos (2 * θ)) 0 = 1 := by norm_num
      simpa [h0] using ((hcoscont.continuousAt (x := 0)).tendsto).mono_left nhdsWithin_le_nhds
    simpa using hlim.mul hc
  have hQ0 : Tendsto (fun θ : ℝ => -(deriv u θ) * Work.Elliptic.sinCos2 θ
      + u θ * (Real.cos θ * Real.cos (2 * θ)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds α) := by
    simpa using hA0.add hB0
  -- ## `u` is bounded near `π/2`
  have hu_bound : ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
      |u θ| ≤ |u (Real.pi / 4)| + M * (Real.pi / 2 - Real.pi / 4) := by
    intro θ hθ
    have hsub : Set.uIcc (Real.pi / 4) θ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
      rw [Set.uIcc_of_le hθ.1.le]
      intro x hx
      exact ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, hθ.2]⟩
    have hcont : ContinuousOn u (Set.uIcc (Real.pi / 4) θ) := hu.continuousOn.mono hsub
    have hdder : ∀ x ∈ Set.uIoo (Real.pi / 4) θ, DifferentiableAt ℝ u x := by
      intro x hx
      rw [Set.uIoo_of_le hθ.1.le] at hx
      have hx' : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
        ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, hθ.2]⟩
      exact (hu.contDiffAt (isOpen_Ioo.mem_nhds hx')).differentiableAt (by norm_num)
    have hdc1 : ContinuousOn (deriv u) (Set.uIcc (Real.pi / 4) θ) :=
      (hu.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)).mono hsub
    have hftc : ∫ y in (Real.pi / 4)..θ, deriv u y = u θ - u (Real.pi / 4) :=
      intervalIntegral.integral_deriv_eq_sub_uIoo hcont hdder hdc1.intervalIntegrable
    have h1 : |u θ - u (Real.pi / 4)| ≤ M * (θ - Real.pi / 4) := by
      have hb : ∀ x ∈ Set.uIoc (Real.pi / 4) θ, ‖deriv u x‖ ≤ M := by
        intro x hx
        rw [Set.uIoc_of_le hθ.1.le] at hx
        rw [Real.norm_eq_abs]
        exact hM x ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, hθ.2]⟩
      have hkey := intervalIntegral.norm_integral_le_of_norm_le_const
        (f := deriv u) (a := Real.pi / 4) (b := θ) hb
      rw [hftc, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hθ.1.le)] at hkey
      exact hkey
    have h2 : |u θ| ≤ |u (Real.pi / 4)| + |u θ - u (Real.pi / 4)| := by
      have h := abs_add_le (u (Real.pi / 4)) (u θ - u (Real.pi / 4))
      rwa [add_sub_cancel] at h
    have hMnn : 0 ≤ M := by
      have h := hM (Real.pi / 4) ⟨hpi4, hpi4lt⟩
      linarith [abs_nonneg (deriv u (Real.pi / 4))]
    have h3 : M * (θ - Real.pi / 4) ≤ M * (Real.pi / 2 - Real.pi / 4) :=
      mul_le_mul_of_nonneg_left (by linarith [hθ.2]) hMnn
    linarith [h1, h2, h3]
  have hA1 : Tendsto (fun θ : ℝ => -(deriv u θ) * Work.Elliptic.sinCos2 θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    have hmaj : Tendsto (fun θ : ℝ => M * |Work.Elliptic.sinCos2 θ|)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
      have h0 : (fun θ : ℝ => Work.Elliptic.sinCos2 θ) (Real.pi / 2) = 0 := by
        simp only [Work.Elliptic.sinCos2, Real.sin_pi_div_two, Real.cos_pi_div_two]
        norm_num
      have hS : Tendsto (fun θ : ℝ => Work.Elliptic.sinCos2 θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
        simpa [h0] using
          ((hScont.continuousAt (x := Real.pi / 2)).tendsto).mono_left nhdsWithin_le_nhds
      simpa using hS.abs.const_mul M
    have hsqueeze : Tendsto (fun θ : ℝ => ‖-(deriv u θ) * Work.Elliptic.sinCos2 θ‖)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
      refine squeeze_zero' (Eventually.of_forall (fun θ => norm_nonneg _)) ?_ hmaj
      rw [eventually_nhdsWithin_iff]
      filter_upwards [Ioi_mem_nhds (show Real.pi / 4 < Real.pi / 2 by linarith)]
        with θ hθ hθmem
      rw [Real.norm_eq_abs, abs_mul, abs_neg]
      exact mul_le_mul_of_nonneg_right (hM θ ⟨lt_trans hpi4 hθ, hθmem⟩) (abs_nonneg _)
    rwa [tendsto_zero_iff_norm_tendsto_zero]
  have hB1 : Tendsto (fun θ : ℝ => u θ * (Real.cos θ * Real.cos (2 * θ)))
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    have hc : Tendsto (fun θ : ℝ => Real.cos θ * Real.cos (2 * θ))
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
      have h0 : (fun θ : ℝ => Real.cos θ * Real.cos (2 * θ)) (Real.pi / 2) = 0 := by
        simp only [Real.cos_pi_div_two]
        norm_num
      simpa [h0] using
        ((hcoscont.continuousAt (x := Real.pi / 2)).tendsto).mono_left nhdsWithin_le_nhds
    have hmaj : Tendsto (fun θ : ℝ => (|u (Real.pi / 4)|
        + M * (Real.pi / 2 - Real.pi / 4)) * |Real.cos θ * Real.cos (2 * θ)|)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
      simpa using hc.abs.const_mul (|u (Real.pi / 4)| + M * (Real.pi / 2 - Real.pi / 4))
    have hsqueeze : Tendsto (fun θ : ℝ => ‖u θ * (Real.cos θ * Real.cos (2 * θ))‖)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
      refine squeeze_zero' (Eventually.of_forall (fun θ => norm_nonneg _)) ?_ hmaj
      rw [eventually_nhdsWithin_iff]
      filter_upwards [Ioi_mem_nhds (show Real.pi / 4 < Real.pi / 2 by linarith)]
        with θ hθ hθmem
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hu_bound θ ⟨hθ, hθmem⟩) (abs_nonneg _)
    rwa [tendsto_zero_iff_norm_tendsto_zero]
  have hQpi : Tendsto (fun θ : ℝ => -(deriv u θ) * Work.Elliptic.sinCos2 θ
      + u θ * (Real.cos θ * Real.cos (2 * θ)))
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    simpa using hA1.add hB1
  -- ## the fundamental theorem of calculus on the whole interval
  have hFTC : ∫ y in (0 : ℝ)..(Real.pi / 2),
      Work.FTS.EllipticEst.Lzero1 u y * Work.Elliptic.sinCos2 y = 0 - α :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
      (f := fun θ : ℝ => -(deriv u θ) * Work.Elliptic.sinCos2 θ
        + u θ * (Real.cos θ * Real.cos (2 * θ)))
      (f' := fun θ : ℝ => Work.FTS.EllipticEst.Lzero1 u θ * Work.Elliptic.sinCos2 θ)
      (fa := α) (fb := 0) (by linarith) hderiv hint' hQ0 hQpi
  change (∫ θ in Set.Icc (0 : ℝ) (Real.pi / 2),
      Work.FTS.EllipticEst.Lzero1 u θ * Work.Elliptic.sinCos2 θ) = -α
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle_pi,
    hFTC]
  ring

theorem sliceTendstoZeroOfMoment :
    ∀ u : ℝ → ℝ,
      ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)) →
      MeasureTheory.IntegrableOn
        (fun θ => (deriv (fun t => deriv u t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn
        (fun θ => (Work.FTS.EllipticEst.Lzero1 u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ →
      (∫ θ in Work.Spaces.Iθ,
        Work.FTS.EllipticEst.Lzero1 u θ * Work.Elliptic.sinCos2 θ) = 0 →
      Filter.Tendsto u (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  intro u hu h1 h2 _h3 hmom
  obtain ⟨α, hα⟩ := auxLimitAtZero hu h1
  have hid := auxMoment hu h1 h2 hα
  have hα0 : α = 0 := by linarith
  simpa [hα0] using hα

end Work.FTS.EllipticEst.remov.SourceBound
