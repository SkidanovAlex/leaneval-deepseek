/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Work.FTS.EllSol.VthAux.traceAux.hardySinWeight`

The weighted Hardy inequality for the second derivative with the **`sin(2·)`-weight** at both
endpoints, deduced from the power-weight version `hardySecondPow`:

* `sinWeight_left` — for `0 < a < 1`, `0 < ε ≤ π/4`, `h` of class `C²` on `(0,ε)` with
  `h → 0` at `0⁺` and `∫_0^ε sin(2θ)^a |h''(θ)| dθ < ∞`, the singular integral
  `∫_0^ε sin(2θ)^{a-2} |h(θ)| dθ` is finite;
* `sinWeight_right` — the mirror statement at `π/2`, obtained by reflecting
  `t ↦ π/2 - t` (under which `sin(2(π/2-t)) = sin(2t)` exactly).

The comparison is Jordan's inequality `(4/π)t ≤ sin(2t)` on `(0,π/4)`, which on the one hand
gives `θ^a ≤ (π/4)^a sin(2θ)^a` and on the other `sin(2θ)^{a-2} ≤ (4/π)^{a-2} θ^{a-2}` (since
`a - 2 < 0`).
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllSol.VthAux.traceAux.hardySecondPow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.VthAux.traceAux

/-! ## Comparison tools -/

/-- Jordan's inequality in the form used below: `(4/π) t ≤ sin (2t)` for `t ∈ (0, π/4)`. -/
lemma sin_two_ge {t : ℝ} (ht : t ∈ Set.Ioo 0 (Real.pi / 4)) :
    (4 / Real.pi) * t ≤ Real.sin (2 * t) := by
  have h1 : 2 / Real.pi * (2 * t) ≤ Real.sin (2 * t) :=
    Real.mul_le_sin (by linarith [ht.1]) (by linarith [ht.2, Real.pi_pos])
  have h3 : 2 / Real.pi * (2 * t) = (4 / Real.pi) * t := by ring
  rwa [h3] at h1

/-- `sin (2 (π/2 - t)) = sin (2t)`. -/
lemma sin_two_reflect (t : ℝ) : Real.sin (2 * (Real.pi / 2 - t)) = Real.sin (2 * t) := by
  rw [show 2 * (Real.pi / 2 - t) = Real.pi - 2 * t from by ring, Real.sin_pi_sub]

/-- Reflection of `IntegrableOn` about `π/2`: the map `t ↦ π/2 - t` carries `(0,ε)` onto
`(π/2 - ε, π/2)`. -/
lemma reflectIntegrableOn_iff (F : ℝ → ℝ) {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn F (Set.Ioo (Real.pi / 2 - ε) (Real.pi / 2)) ↔
      IntegrableOn (fun t => F (Real.pi / 2 - t)) (Set.Ioo 0 ε) := by
  have h1 := intervalIntegrable_iff_integrableOn_Ioo_of_le (f := F) (μ := volume)
      (a := Real.pi / 2 - ε) (b := Real.pi / 2) (by linarith)
  have h2 := intervalIntegrable_iff_integrableOn_Ioo_of_le
      (f := fun t => F (Real.pi / 2 - t)) (μ := volume) (a := 0) (b := ε) (le_of_lt hε)
  have h3 : IntervalIntegrable (fun x => F (Real.pi / 2 - x)) volume ε 0 ↔
      IntervalIntegrable F volume (Real.pi / 2 - ε) (Real.pi / 2) := by
    have h := IntervalIntegrable.comp_sub_left_iff (f := F)
      (a := Real.pi / 2 - ε) (b := Real.pi / 2) (Real.pi / 2)
    rw [show Real.pi / 2 - (Real.pi / 2 - ε) = ε from by ring,
        show Real.pi / 2 - Real.pi / 2 = 0 from by ring] at h
    exact h
  rw [← h1, ← h2, ← h3]
  exact IntervalIntegrable.symm_iff

/-- Second derivative of the reflection: `(h (π/2 - ·))'' = h'' (π/2 - ·)`. -/
lemma reflect_deriv_deriv {h : ℝ → ℝ} {ε : ℝ}
    (hC2 : ContDiffOn ℝ 2 h (Set.Ioo (Real.pi / 2 - ε) (Real.pi / 2)))
    {t : ℝ} (ht : t ∈ Set.Ioo 0 ε) :
    deriv (deriv (fun y => h (Real.pi / 2 - y))) t = deriv (deriv h) (Real.pi / 2 - t) := by
  have hmem : Real.pi / 2 - t ∈ Set.Ioo (Real.pi / 2 - ε) (Real.pi / 2) :=
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hC1 : ContDiffOn ℝ 1 (deriv h) (Set.Ioo (Real.pi / 2 - ε) (Real.pi / 2)) :=
    hC2.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hd2 : DifferentiableAt ℝ (deriv h) (Real.pi / 2 - t) :=
    (hC1.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hmem)
  have hderiv_loc : deriv (fun y => h (Real.pi / 2 - y)) =ᶠ[nhds t]
      fun y => -deriv h (Real.pi / 2 - y) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with y hy
    have hmy : Real.pi / 2 - y ∈ Set.Ioo (Real.pi / 2 - ε) (Real.pi / 2) :=
      ⟨by linarith [hy.2], by linarith [hy.1]⟩
    have hdy : DifferentiableAt ℝ h (Real.pi / 2 - y) :=
      (hC2.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hmy)
    have h1 : HasDerivAt (fun y : ℝ => Real.pi / 2 - y) (-1) y := by
      simpa using (hasDerivAt_id y).const_sub (Real.pi / 2)
    have h2 : HasDerivAt (fun y : ℝ => h (Real.pi / 2 - y))
        (deriv h (Real.pi / 2 - y) * (-1)) y := hdy.hasDerivAt.comp y h1
    rw [h2.deriv]
    ring
  have hdfun : DifferentiableAt ℝ (fun y => deriv h (Real.pi / 2 - y)) t := by
    have h1 : HasDerivAt (fun y : ℝ => Real.pi / 2 - y) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub (Real.pi / 2)
    exact (hd2.hasDerivAt.comp t h1).differentiableAt
  calc deriv (deriv (fun y => h (Real.pi / 2 - y))) t
      = deriv (fun y => -deriv h (Real.pi / 2 - y)) t := Filter.EventuallyEq.deriv_eq hderiv_loc
    _ = deriv (fun y => (-1 : ℝ) * deriv h (Real.pi / 2 - y)) t := by
          congr 1
          funext y
          ring
    _ = (-1) * deriv (fun y => deriv h (Real.pi / 2 - y)) t := deriv_const_mul (-1) hdfun
    _ = deriv (deriv h) (Real.pi / 2 - t) := by
          have h1 : HasDerivAt (fun y : ℝ => Real.pi / 2 - y) (-1) t := by
            simpa using (hasDerivAt_id t).const_sub (Real.pi / 2)
          have h2 : HasDerivAt (fun y : ℝ => deriv h (Real.pi / 2 - y))
              (deriv (deriv h) (Real.pi / 2 - t) * (-1)) t := hd2.hasDerivAt.comp t h1
          rw [h2.deriv]
          ring

/-! ## The two `sin`-weighted Hardy inequalities -/

/-- **Weighted Hardy inequality for the second derivative, `sin(2·)`-weight, left endpoint.** -/
theorem sinWeight_left {a ε : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hε : 0 < ε)
    (hεπ : ε ≤ Real.pi / 4) {h : ℝ → ℝ}
    (hC2 : ContDiffOn ℝ 2 h (Set.Ioo 0 ε))
    (h0 : Filter.Tendsto h (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ a * |deriv (deriv h) θ|) (Set.Ioo 0 ε)) :
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (a - 2) * |h θ|) (Set.Ioo 0 ε) := by
  have hmem : ∀ θ ∈ Set.Ioo (0 : ℝ) ε, (4 / Real.pi) * θ ≤ Real.sin (2 * θ) := fun θ hθ =>
    sin_two_ge ⟨hθ.1, lt_of_lt_of_le hθ.2 hεπ⟩
  -- step 1: the power-weight hypothesis
  have hc_a : ContinuousOn (fun θ : ℝ => θ ^ a) (Set.Ioo 0 ε) :=
    continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt hx.1))
  have hc_h2 : ContinuousOn (deriv (deriv h)) (Set.Ioo 0 ε) := by
    have h1 : ContDiffOn ℝ 1 (deriv h) (Set.Ioo 0 ε) :=
      hC2.deriv_of_isOpen isOpen_Ioo (by norm_num)
    exact h1.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl
  have hcont : ContinuousOn (fun θ : ℝ => θ ^ a * |deriv (deriv h) θ|) (Set.Ioo 0 ε) :=
    hc_a.mul hc_h2.abs
  have hmeas : AEStronglyMeasurable (fun θ : ℝ => θ ^ a * |deriv (deriv h) θ|)
      (volume.restrict (Set.Ioo 0 ε)) :=
    (hcont.aemeasurable measurableSet_Ioo).aestronglyMeasurable
  have hbound : ∀ᵐ θ ∂(volume.restrict (Set.Ioo (0 : ℝ) ε)),
      ‖θ ^ a * |deriv (deriv h) θ|‖
        ≤ (Real.pi / 4) ^ a * ((Real.sin (2 * θ)) ^ a * |deriv (deriv h) θ|) := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo ?_
    intro θ hθ
    have hsin := hmem θ hθ
    have hsin_nn : 0 ≤ Real.sin (2 * θ) :=
      le_trans (mul_nonneg (by positivity) hθ.1.le) hsin
    have hX : 0 ≤ |deriv (deriv h) θ| := abs_nonneg _
    have hpow : θ ^ a ≤ (Real.pi / 4) ^ a * (Real.sin (2 * θ)) ^ a := by
      have h1 : ((4 / Real.pi) * θ) ^ a ≤ (Real.sin (2 * θ)) ^ a :=
        Real.rpow_le_rpow (mul_nonneg (by positivity) hθ.1.le) hsin ha0.le
      have h2 : ((4 / Real.pi) * θ) ^ a = (4 / Real.pi) ^ a * θ ^ a :=
        Real.mul_rpow (by positivity) hθ.1.le
      have h3 : (Real.pi / 4) ^ a * (4 / Real.pi) ^ a = 1 := by
        rw [← Real.mul_rpow (by positivity) (by positivity),
          show Real.pi / 4 * (4 / Real.pi) = 1 from by field_simp, Real.one_rpow]
      have h4 : (4 / Real.pi) ^ a * θ ^ a ≤ (Real.sin (2 * θ)) ^ a := by rwa [h2] at h1
      have h5 := mul_le_mul_of_nonneg_left h4
        (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ Real.pi / 4) a)
      calc θ ^ a = ((Real.pi / 4) ^ a * (4 / Real.pi) ^ a) * θ ^ a := by rw [h3, one_mul]
        _ = (Real.pi / 4) ^ a * ((4 / Real.pi) ^ a * θ ^ a) := by rw [mul_assoc]
        _ ≤ (Real.pi / 4) ^ a * (Real.sin (2 * θ)) ^ a := h5
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hθ.1.le a) hX)]
    calc θ ^ a * |deriv (deriv h) θ|
        ≤ ((Real.pi / 4) ^ a * (Real.sin (2 * θ)) ^ a) * |deriv (deriv h) θ| :=
          mul_le_mul_of_nonneg_right hpow hX
      _ = (Real.pi / 4) ^ a * ((Real.sin (2 * θ)) ^ a * |deriv (deriv h) θ|) := by ring
  have hint2 : MeasureTheory.IntegrableOn (fun θ : ℝ => θ ^ a * |deriv (deriv h) θ|)
      (Set.Ioo 0 ε) :=
    (hint.integrable.const_mul ((Real.pi / 4) ^ a)).mono' hmeas hbound
  have hp := hardySecondPow ha0 ha1 hε hC2 h0 hint2
  -- step 2: compare the two singular weights
  have hcont2 : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (a - 2) * |h θ|)
      (Set.Ioo 0 ε) := by
    have hs : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 ε) :=
      (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
    have hsp : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (a - 2)) (Set.Ioo 0 ε) :=
      hs.rpow_const (fun x hx => Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi
        (by linarith [hx.1]) (by linarith [hx.2, hεπ, Real.pi_pos]))))
    exact hsp.mul hC2.continuousOn.abs
  have hmeas2 : AEStronglyMeasurable
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (a - 2) * |h θ|)
      (volume.restrict (Set.Ioo 0 ε)) :=
    (hcont2.aemeasurable measurableSet_Ioo).aestronglyMeasurable
  have hbound2 : ∀ᵐ θ ∂(volume.restrict (Set.Ioo (0 : ℝ) ε)),
      ‖(Real.sin (2 * θ)) ^ (a - 2) * |h θ|‖
        ≤ (4 / Real.pi) ^ (a - 2) * (θ ^ (a - 2) * |h θ|) := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo ?_
    intro θ hθ
    have hsin := hmem θ hθ
    have hsin_pos : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
        (by linarith [hθ.2, hεπ, Real.pi_pos])
    have hbase_pos : 0 < (4 / Real.pi) * θ := mul_pos (by positivity) hθ.1
    have hX : 0 ≤ |h θ| := abs_nonneg _
    have hpow : (Real.sin (2 * θ)) ^ (a - 2) ≤ (4 / Real.pi) ^ (a - 2) * θ ^ (a - 2) := by
      have h1 : (Real.sin (2 * θ)) ^ (a - 2) ≤ ((4 / Real.pi) * θ) ^ (a - 2) :=
        Real.rpow_le_rpow_of_nonpos hbase_pos hsin (by linarith : a - 2 ≤ 0)
      have h2 : ((4 / Real.pi) * θ) ^ (a - 2) = (4 / Real.pi) ^ (a - 2) * θ ^ (a - 2) :=
        Real.mul_rpow (by positivity) hθ.1.le
      rwa [h2] at h1
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hsin_pos.le _) hX)]
    calc (Real.sin (2 * θ)) ^ (a - 2) * |h θ|
        ≤ ((4 / Real.pi) ^ (a - 2) * θ ^ (a - 2)) * |h θ| :=
          mul_le_mul_of_nonneg_right hpow hX
      _ = (4 / Real.pi) ^ (a - 2) * (θ ^ (a - 2) * |h θ|) := by rw [mul_assoc]
  exact (hp.integrable.const_mul ((4 / Real.pi) ^ (a - 2))).mono' hmeas2 hbound2

/-- **Weighted Hardy inequality for the second derivative, `sin(2·)`-weight, right endpoint.** -/
theorem sinWeight_right {a ε : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hε : 0 < ε)
    (hεπ : ε ≤ Real.pi / 4) {h : ℝ → ℝ}
    (hC2 : ContDiffOn ℝ 2 h (Set.Ioo (Real.pi / 2 - ε) (Real.pi / 2)))
    (h0 : Filter.Tendsto h (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0))
    (hint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ a * |deriv (deriv h) θ|)
      (Set.Ioo (Real.pi / 2 - ε) (Real.pi / 2))) :
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (a - 2) * |h θ|)
      (Set.Ioo (Real.pi / 2 - ε) (Real.pi / 2)) := by
  set g : ℝ → ℝ := fun y => h (Real.pi / 2 - y) with hg
  -- the reflected function satisfies the left-endpoint hypotheses
  have hC2g : ContDiffOn ℝ 2 g (Set.Ioo 0 ε) := by
    have hlin : ContDiffOn ℝ 2 (fun y : ℝ => Real.pi / 2 - y) (Set.Ioo 0 ε) :=
      ((contDiff_const.sub contDiff_id).contDiffOn)
    have hcomp := hC2.comp hlin (fun y hy => ⟨by linarith [hy.2], by linarith [hy.1]⟩)
    simpa only [hg, Function.comp_def] using hcomp
  have h0g : Filter.Tendsto g (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h1 : Filter.Tendsto (fun y : ℝ => Real.pi / 2 - y) (nhdsWithin 0 (Set.Ioi 0))
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have hcf : Continuous (fun y : ℝ => Real.pi / 2 - y) :=
          continuous_const.sub continuous_id
        have hc : Filter.Tendsto (fun y : ℝ => Real.pi / 2 - y) (nhds (0 : ℝ))
            (nhds (Real.pi / 2)) := by simpa using hcf.tendsto 0
        exact hc.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with y hy
        have hy' : (0 : ℝ) < y := hy
        show Real.pi / 2 - y < Real.pi / 2
        linarith
    have h2 := h0.comp h1
    simpa only [hg, Function.comp_def] using h2
  have hintg : MeasureTheory.IntegrableOn
      (fun y : ℝ => (Real.sin (2 * y)) ^ a * |deriv (deriv g) y|) (Set.Ioo 0 ε) := by
    have h0' : MeasureTheory.IntegrableOn
        (fun t : ℝ => (Real.sin (2 * (Real.pi / 2 - t))) ^ a
          * |deriv (deriv h) (Real.pi / 2 - t)|) (Set.Ioo 0 ε) :=
      (reflectIntegrableOn_iff (fun θ => (Real.sin (2 * θ)) ^ a * |deriv (deriv h) θ|) hε).mp
        hint
    have h1 : MeasureTheory.IntegrableOn
        (fun t : ℝ => (Real.sin (2 * t)) ^ a * |deriv (deriv h) (Real.pi / 2 - t)|)
        (Set.Ioo 0 ε) :=
      h0'.congr_fun (fun t _ => by
        show (Real.sin (2 * (Real.pi / 2 - t))) ^ a * |deriv (deriv h) (Real.pi / 2 - t)|
          = (Real.sin (2 * t)) ^ a * |deriv (deriv h) (Real.pi / 2 - t)|
        rw [sin_two_reflect]) measurableSet_Ioo
    refine h1.congr_fun ?_ measurableSet_Ioo
    intro y hy
    show (Real.sin (2 * y)) ^ a * |deriv (deriv h) (Real.pi / 2 - y)|
        = (Real.sin (2 * y)) ^ a * |deriv (deriv g) y|
    rw [show deriv (deriv g) y = deriv (deriv h) (Real.pi / 2 - y) from by
      simpa only [hg] using reflect_deriv_deriv hC2 hy]
  have hres := sinWeight_left ha0 ha1 hε hεπ hC2g h0g hintg
  -- transport the conclusion back
  refine (reflectIntegrableOn_iff
    (fun θ => (Real.sin (2 * θ)) ^ (a - 2) * |h θ|) hε).mpr ?_
  refine hres.congr_fun ?_ measurableSet_Ioo
  intro y hy
  show (Real.sin (2 * y)) ^ (a - 2) * |g y|
      = (Real.sin (2 * (Real.pi / 2 - y))) ^ (a - 2) * |h (Real.pi / 2 - y)|
  rw [sin_two_reflect]

end Work.FTS.EllSol.VthAux.traceAux
