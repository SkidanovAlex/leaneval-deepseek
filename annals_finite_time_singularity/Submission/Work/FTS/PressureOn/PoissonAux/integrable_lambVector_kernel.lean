/-
# Integrability of the Lamb-vector kernel

This file proves that the kernel of the Newtonian representation of the pressure potential,

  `(p : ℝ³ × ℝ³) ↦ ⟪∇N(p.1 − p.2), f p.2⟫ * Δφ(p.1)`,

is integrable on `ℝ³ × ℝ³` whenever `f : ℝ³ → ℝ³` is continuous with compact support and
`φ : ℝ³ → ℝ` is `C²` with compact support.  This is the Fubini hypothesis needed to exchange the
order of the two integrations in the weak Poisson identity (`Work.FTS.PressureOn.weakPoisson`).

## Why it is true, and where the hypotheses enter

* `‖∇N z‖ = (4π)⁻¹‖z‖⁻²` in dimension three (`norm_newtonGrad`), and `‖·‖⁻²` is integrable on a
  *bounded* region of `ℝ³` (`Work.FTS.PressureOn.joint.majorant_integrable`): the singularity at
  `z = 0` sits exactly at the integrability threshold in dimension `3`, where the volume element
  `4πr² dr` cancels `r⁻²`.
* The decay at infinity of `‖∇N z‖` is only `‖z‖⁻²`, which is *not* integrable at infinity.  So the
  compact support of `φ` is essential: `Δφ` vanishes off `tsupport φ` (the second derivatives of a
  function that is eventually zero at a point vanish there too, which uses only eventual constancy
  and no differentiability — see `laplaceTrace_eq_zero_of_notMem_tsupport`), so `p.1` stays in a
  fixed ball.  Likewise the compact support of `f` confines `p.2` to a ball and gives the
  pointwise bound `‖f y‖ ≤ M · 1_{‖y‖ ≤ R}`.
* The integrability of the resulting product
  `(u, v) ↦ 1_{‖v‖ ≤ R} · (‖u − v‖⁻² · 1_{‖u − v‖ ≤ R + S})` is the convolution-integrability
  lemma `MeasureTheory.Integrable.convolution_integrand` (applied with the multiplication
  `ContinuousLinearMap.mul ℝ ℝ`), both factors being integrable on `ℝ³`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.PressureOn.PoissonAux.Defs
import Submission.Work.FTS.PressureOn.joint.majorant_integrable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set FiniteTimeSingularity
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.PressureOn.PoissonAux

/-! ## Pointwise bounds on the Newtonian kernel -/

/-- `(a³)⁻¹ · a ≤ (a²)⁻¹` for `a ≥ 0`; in fact equality holds for `a > 0`. -/
private lemma inv_cube_mul_self_le (a : ℝ) (ha : 0 ≤ a) : (a ^ 3)⁻¹ * a ≤ (a ^ 2)⁻¹ := by
  rcases eq_or_lt_of_le ha with h | h
  · rw [← h]; norm_num
  · refine le_of_eq ?_
    field_simp

/-- **Pointwise bound on `∇N`**: `‖∇N z‖ ≤ (4π)⁻¹‖z‖⁻²`. -/
private lemma norm_newtonGrad_le (z : R3) :
    ‖newtonGrad z‖ ≤ (4 * Real.pi)⁻¹ * (‖z‖ ^ 2)⁻¹ := by
  rw [norm_newtonGrad]
  calc (4 * Real.pi)⁻¹ * (‖z‖ ^ (3 : ℕ))⁻¹ * ‖z‖
      = (4 * Real.pi)⁻¹ * ((‖z‖ ^ (3 : ℕ))⁻¹ * ‖z‖) := by ring
    _ ≤ (4 * Real.pi)⁻¹ * (‖z‖ ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_left (inv_cube_mul_self_le _ (norm_nonneg z)) (by positivity)

/-! ## Boundedness and support of the data -/

/-- A continuous compactly supported function `g : ℝ³ → E` is dominated by `K · 1_{‖x‖ ≤ S}` for
suitable `K ≥ 0`, `S > 0`. -/
private lemma bounded_indicator_of_compactSupport {E : Type*} [NormedAddCommGroup E]
    {g : R3 → E} (hg : Continuous g) (hcs : HasCompactSupport g) :
    ∃ K S : ℝ, 0 ≤ K ∧ 0 < S ∧
      ∀ x : R3, ‖g x‖ ≤ K * (Metric.closedBall (0 : R3) S).indicator
        (fun _ => (1 : ℝ)) x := by
  obtain ⟨K, hK⟩ := hg.bounded_above_of_compact_support hcs
  obtain ⟨S, hSpos, hS⟩ := hcs.isBounded.exists_pos_norm_le
  refine ⟨max K 0, S, le_max_right _ _, hSpos, fun x => ?_⟩
  by_cases hx : x ∈ Metric.closedBall (0 : R3) S
  · rw [Set.indicator_of_mem hx, mul_one]
    exact le_trans (hK x) (le_max_left _ _)
  · have h0 : g x = 0 := by
      by_contra h
      exact hx (by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact hS x (subset_tsupport g (Function.mem_support.mpr h)))
    rw [h0, norm_zero]
    exact mul_nonneg (le_max_right _ _) (Set.indicator_nonneg (fun _ _ => zero_le_one) x)

/-! ## The trace of the Hessian of a compactly supported `C²` function -/

/-- **`Δφ` vanishes off `tsupport φ`.**  The proof uses the eventual constancy of `φ` at `x` and at
every point of a whole neighbourhood of `x` (which is what differentiating twice needs). -/
private lemma laplaceTrace_eq_zero_of_notMem_tsupport {φ : R3 → ℝ} {x : R3}
    (hx : x ∉ tsupport φ) : laplaceTrace φ x = 0 := by
  have hopen : IsOpen (tsupport φ)ᶜ := (isClosed_tsupport φ).isOpen_compl
  refine Finset.sum_eq_zero fun i _ => ?_
  have hD : (fun w : R3 => fderiv ℝ φ w (e i)) =ᶠ[𝓝 x] 0 := by
    filter_upwards [hopen.mem_nhds hx] with z hz
    have hz0 : φ =ᶠ[𝓝 z] 0 := by
      filter_upwards [hopen.mem_nhds hz] with w hw
      exact image_eq_zero_of_notMem_tsupport hw
    have : fderiv ℝ φ z = 0 := by rw [hz0.fderiv_eq]; simp
    simp [this]
  have hD2 : fderiv ℝ (fun w : R3 => fderiv ℝ φ w (e i)) x = 0 := by
    rw [hD.fderiv_eq]; simp
  rw [hD2]; simp

/-- The topological support of `Δφ` is contained in that of `φ`. -/
private lemma tsupport_laplaceTrace_subset (φ : R3 → ℝ) :
    tsupport (laplaceTrace φ) ⊆ tsupport φ :=
  closure_minimal (fun x hx => by
    by_contra h
    exact hx (laplaceTrace_eq_zero_of_notMem_tsupport h)) (isClosed_tsupport φ)

/-- `Δφ` has compact support when `φ` does. -/
private lemma hasCompactSupport_laplaceTrace {φ : R3 → ℝ} (hφcs : HasCompactSupport φ) :
    HasCompactSupport (laplaceTrace φ) :=
  hφcs.of_isClosed_subset (isClosed_tsupport _) (tsupport_laplaceTrace_subset φ)

/-- **`Δφ` is continuous for a `C²` function `φ`.**  It is a finite sum of the functions
`x ↦ ∂ᵢ∂ᵢφ(x)`, each of which is the derivative of the `C¹` function `x ↦ ∂ᵢφ(x)`. -/
private lemma continuous_laplaceTrace {φ : R3 → ℝ} (hφ : ContDiff ℝ 2 φ) :
    Continuous (laplaceTrace φ) := by
  have hfun : laplaceTrace φ = fun x : R3 => ∑ i : Fin 3,
      fderiv ℝ (fun w : R3 => fderiv ℝ φ w (e i)) x (e i) := rfl
  rw [hfun]
  refine continuous_finsetSum _ fun i _ => ?_
  have hD : ContDiff ℝ 1 (fun w : R3 => fderiv ℝ φ w (e i)) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  exact (hD.continuous_fderiv (by norm_num)).clm_apply continuous_const

/-- `Δφ` is dominated by `K · 1_{‖x‖ ≤ S}` when `φ` is `C²` with compact support. -/
private lemma exists_bound_laplaceTrace {φ : R3 → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφcs : HasCompactSupport φ) :
    ∃ K S : ℝ, 0 ≤ K ∧ 0 < S ∧
      ∀ x : R3, ‖laplaceTrace φ x‖ ≤ K * (Metric.closedBall (0 : R3) S).indicator
        (fun _ => (1 : ℝ)) x :=
  bounded_indicator_of_compactSupport (continuous_laplaceTrace hφ)
    (hasCompactSupport_laplaceTrace hφcs)

/-- `∇N` is measurable: it is a measurable scalar times the identity (`∇N` is *not* continuous,
since `‖z‖⁻²` blows up at the origin). -/
private lemma measurable_newtonGrad : Measurable (fun z : R3 => newtonGrad z) := by
  have h : (fun z : R3 => newtonGrad z)
      = fun z => -((4 * Real.pi)⁻¹ * (‖z‖ ^ (3 : ℕ))⁻¹) • z := by
    funext z; rw [newtonGrad_apply]
  rw [h]
  have h1 : Measurable (fun z : R3 => ((4 * Real.pi)⁻¹ * (‖z‖ ^ (3 : ℕ))⁻¹ : ℝ)) := by
    fun_prop
  exact h1.neg.smul measurable_id

/-! ## The dominating function -/

/-- The truncated singular majorant `(‖z‖²)⁻¹ 1_{‖z‖ ≤ T}` is integrable in dimension three (this
is `joint.majorant_integrable`, with the harmless constant `(4π)⁻¹` removed). -/
private lemma integrable_inv_normSq_indicator (T : ℝ) :
    Integrable (fun z : R3 => (‖z‖ ^ 2)⁻¹ *
      (Metric.closedBall (0 : R3) T).indicator (fun _ => (1 : ℝ)) z) := by
  refine (MeasureTheory.Integrable.const_mul (joint.majorant_integrable T) (4 * Real.pi)).congr
    (Filter.Eventually.of_forall fun z => ?_)
  simp only
  rw [← mul_assoc, mul_inv_cancel₀ (by positivity : (4 * Real.pi) ≠ 0), one_mul]

/-- **Geometric core of the domination.**  If `p.2` lies in the ball of radius `R`, then the
indicator of the ball of radius `S` in the first variable is dominated by the indicator of the ball
of radius `R + S` in the *difference* variable. -/
private lemma ind_le_ind_sub {R S : ℝ} {p : R3 × R3}
    (h2 : p.2 ∈ Metric.closedBall (0 : R3) R) :
    (Metric.closedBall (0 : R3) S).indicator (fun _ => (1 : ℝ)) p.1
      ≤ (Metric.closedBall (0 : R3) (R + S)).indicator (fun _ => (1 : ℝ)) (p.1 - p.2) := by
  by_cases h1 : p.1 ∈ Metric.closedBall (0 : R3) S
  · rw [Set.indicator_of_mem h1]
    have : p.1 - p.2 ∈ Metric.closedBall (0 : R3) (R + S) := by
      rw [Metric.mem_closedBall, dist_zero_right] at h1 h2 ⊢
      calc ‖p.1 - p.2‖ ≤ ‖p.1‖ + ‖p.2‖ := norm_sub_le _ _
        _ ≤ S + R := add_le_add h1 h2
        _ = R + S := by ring
    rw [Set.indicator_of_mem this]
  · rw [Set.indicator_of_notMem h1]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) _

/-- The indicator form of `ind_le_ind_sub`, keeping the factor `1_{‖p.2‖ ≤ R}` on both sides. -/
private lemma indR_mul_indS_le (R S : ℝ) (p : R3 × R3) :
    (Metric.closedBall (0 : R3) R).indicator (fun _ => (1 : ℝ)) p.2 *
      (Metric.closedBall (0 : R3) S).indicator (fun _ => (1 : ℝ)) p.1
    ≤ (Metric.closedBall (0 : R3) R).indicator (fun _ => (1 : ℝ)) p.2 *
      (Metric.closedBall (0 : R3) (R + S)).indicator (fun _ => (1 : ℝ)) (p.1 - p.2) := by
  by_cases h2 : p.2 ∈ Metric.closedBall (0 : R3) R
  · rw [Set.indicator_of_mem h2, one_mul, one_mul]
    exact ind_le_ind_sub h2
  · rw [Set.indicator_of_notMem h2, zero_mul, zero_mul]

/-- **Integrability of the dominating function.**  The function
`(u, v) ↦ 1_{‖v‖ ≤ R} · ‖u − v‖⁻² 1_{‖u − v‖ ≤ T}` is integrable on `ℝ³ × ℝ³`: it is
`f v · g (u − v)` with `f = 1_{‖·‖ ≤ R}` and `g = ‖·‖⁻² 1_{‖·‖ ≤ T}` both integrable on `ℝ³`, and
subtracting `v` is measure preserving in the first variable
(`MeasureTheory.Integrable.convolution_integrand`). -/
private lemma integrable_shifted_kernel (R T : ℝ) :
    Integrable (fun p : R3 × R3 =>
      (Metric.closedBall (0 : R3) R).indicator (fun _ => (1 : ℝ)) p.2 *
        ((‖p.1 - p.2‖ ^ 2)⁻¹ * (Metric.closedBall (0 : R3) T).indicator (fun _ => (1 : ℝ))
          (p.1 - p.2))) := by
  have hB : Integrable (fun v : R3 =>
      (Metric.closedBall (0 : R3) R).indicator (fun _ => (1 : ℝ)) v) := by
    rw [MeasureTheory.integrable_indicator_iff Metric.isClosed_closedBall.measurableSet]
    exact MeasureTheory.integrableOn_const (C := (1 : ℝ))
      (MeasureTheory.measure_closedBall_lt_top).ne
  have hA := integrable_inv_normSq_indicator T
  have h := MeasureTheory.Integrable.convolution_integrand
    (L := ContinuousLinearMap.mul ℝ ℝ) hB hA
  exact h

/-! ## The target -/

theorem integrable_lambVector_kernel {f : Work.FTS.PressureOn.R3 → Work.FTS.PressureOn.R3}
    (hf : Continuous f) (hcs : HasCompactSupport f)
    {φ : Work.FTS.PressureOn.R3 → ℝ} (hφ : ContDiff ℝ 2 φ) (hφcs : HasCompactSupport φ) :
    MeasureTheory.Integrable (fun p : Work.FTS.PressureOn.R3 × Work.FTS.PressureOn.R3 =>
      inner ℝ (Work.FTS.PressureOn.newtonGrad (p.1 - p.2)) (f p.2)
        * Work.FTS.PressureOn.laplaceTrace φ p.1) := by
  obtain ⟨M, R, hM0, _hR0, hfb⟩ := bounded_indicator_of_compactSupport hf hcs
  obtain ⟨K, S, _hK0, _hS0, hφb⟩ := exists_bound_laplaceTrace hφ hφcs
  -- measurability of the integrand
  have hmeas : AEStronglyMeasurable (fun p : R3 × R3 =>
      inner ℝ (newtonGrad (p.1 - p.2)) (f p.2) * laplaceTrace φ p.1) := by
    refine Measurable.aestronglyMeasurable ?_
    refine Measurable.mul ?_ ?_
    · exact continuous_inner.measurable.comp
        ((measurable_newtonGrad.comp (measurable_fst.sub measurable_snd)).prodMk
          (hf.measurable.comp measurable_snd))
    · exact (continuous_laplaceTrace hφ).measurable.comp measurable_fst
  -- the dominating function
  have hDint : Integrable (fun p : R3 × R3 =>
      (4 * Real.pi)⁻¹ * M * K *
        ((Metric.closedBall (0 : R3) R).indicator (fun _ => (1 : ℝ)) p.2 *
          ((‖p.1 - p.2‖ ^ 2)⁻¹ *
            (Metric.closedBall (0 : R3) (R + S)).indicator (fun _ => (1 : ℝ)) (p.1 - p.2)))) :=
    (integrable_shifted_kernel R (R + S)).const_mul ((4 * Real.pi)⁻¹ * M * K)
  refine MeasureTheory.Integrable.mono' hDint hmeas
    (Filter.Eventually.of_forall fun p => ?_)
  -- the pointwise bound
  have hq0 : (0 : ℝ) ≤ (‖p.1 - p.2‖ ^ 2)⁻¹ := inv_nonneg.mpr (by positivity)
  have hcoef0 : (0 : ℝ) ≤ (4 * Real.pi)⁻¹ * (‖p.1 - p.2‖ ^ 2)⁻¹ := by positivity
  have ha : ‖inner ℝ (newtonGrad (p.1 - p.2)) (f p.2)‖
      ≤ (4 * Real.pi)⁻¹ * (‖p.1 - p.2‖ ^ 2)⁻¹ *
        (M * (Metric.closedBall (0 : R3) R).indicator (fun _ => (1 : ℝ)) p.2) := by
    calc ‖inner ℝ (newtonGrad (p.1 - p.2)) (f p.2)‖
        ≤ ‖newtonGrad (p.1 - p.2)‖ * ‖f p.2‖ := norm_inner_le_norm _ _
      _ ≤ ((4 * Real.pi)⁻¹ * (‖p.1 - p.2‖ ^ 2)⁻¹) *
            (M * (Metric.closedBall (0 : R3) R).indicator (fun _ => (1 : ℝ)) p.2) :=
          mul_le_mul (norm_newtonGrad_le _) (hfb p.2) (norm_nonneg _) hcoef0
  have hb : ‖laplaceTrace φ p.1‖ ≤
      K * (Metric.closedBall (0 : R3) S).indicator (fun _ => (1 : ℝ)) p.1 := hφb p.1
  rw [norm_mul]
  refine le_trans (mul_le_mul ha hb (norm_nonneg _)
    (mul_nonneg hcoef0 (mul_nonneg hM0
      (Set.indicator_nonneg (fun _ _ => zero_le_one) _)))) ?_
  have h2 : (4 * Real.pi)⁻¹ * (‖p.1 - p.2‖ ^ 2)⁻¹ *
        (M * (Metric.closedBall (0 : R3) R).indicator (fun _ => (1 : ℝ)) p.2) *
        (K * (Metric.closedBall (0 : R3) S).indicator (fun _ => (1 : ℝ)) p.1)
      = (4 * Real.pi)⁻¹ * M * K *
        ((‖p.1 - p.2‖ ^ 2)⁻¹ *
          ((Metric.closedBall (0 : R3) R).indicator (fun _ => (1 : ℝ)) p.2 *
           (Metric.closedBall (0 : R3) S).indicator (fun _ => (1 : ℝ)) p.1)) := by ring
  have h3 : (‖p.1 - p.2‖ ^ 2)⁻¹ *
          ((Metric.closedBall (0 : R3) R).indicator (fun _ => (1 : ℝ)) p.2 *
           (Metric.closedBall (0 : R3) S).indicator (fun _ => (1 : ℝ)) p.1)
      ≤ (‖p.1 - p.2‖ ^ 2)⁻¹ *
          ((Metric.closedBall (0 : R3) R).indicator (fun _ => (1 : ℝ)) p.2 *
           (Metric.closedBall (0 : R3) (R + S)).indicator (fun _ => (1 : ℝ)) (p.1 - p.2)) :=
    mul_le_mul_of_nonneg_left (indR_mul_indS_le R S p) hq0
  have h4 : (4 * Real.pi)⁻¹ * M * K *
        ((‖p.1 - p.2‖ ^ 2)⁻¹ *
          ((Metric.closedBall (0 : R3) R).indicator (fun _ => (1 : ℝ)) p.2 *
           (Metric.closedBall (0 : R3) (R + S)).indicator (fun _ => (1 : ℝ)) (p.1 - p.2)))
      = (4 * Real.pi)⁻¹ * M * K *
        ((Metric.closedBall (0 : R3) R).indicator (fun _ => (1 : ℝ)) p.2 *
          ((‖p.1 - p.2‖ ^ 2)⁻¹ *
           (Metric.closedBall (0 : R3) (R + S)).indicator (fun _ => (1 : ℝ)) (p.1 - p.2))) := by
    ring
  calc (4 * Real.pi)⁻¹ * (‖p.1 - p.2‖ ^ 2)⁻¹ *
        (M * (Metric.closedBall (0 : R3) R).indicator (fun _ => (1 : ℝ)) p.2) *
        (K * (Metric.closedBall (0 : R3) S).indicator (fun _ => (1 : ℝ)) p.1)
      = (4 * Real.pi)⁻¹ * M * K *
        ((‖p.1 - p.2‖ ^ 2)⁻¹ *
          ((Metric.closedBall (0 : R3) R).indicator (fun _ => (1 : ℝ)) p.2 *
           (Metric.closedBall (0 : R3) S).indicator (fun _ => (1 : ℝ)) p.1)) := h2
    _ ≤ (4 * Real.pi)⁻¹ * M * K *
        ((‖p.1 - p.2‖ ^ 2)⁻¹ *
          ((Metric.closedBall (0 : R3) R).indicator (fun _ => (1 : ℝ)) p.2 *
           (Metric.closedBall (0 : R3) (R + S)).indicator (fun _ => (1 : ℝ)) (p.1 - p.2))) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = (4 * Real.pi)⁻¹ * M * K *
        ((Metric.closedBall (0 : R3) R).indicator (fun _ => (1 : ℝ)) p.2 *
          ((‖p.1 - p.2‖ ^ 2)⁻¹ *
           (Metric.closedBall (0 : R3) (R + S)).indicator (fun _ => (1 : ℝ)) (p.1 - p.2))) := h4

end Work.FTS.PressureOn.PoissonAux
