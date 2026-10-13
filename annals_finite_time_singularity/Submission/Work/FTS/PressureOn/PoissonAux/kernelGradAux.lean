/-
# Auxiliary lemmas for the gradient form of the fundamental-solution identity (part 1)

Basic regularity, translation-invariance and integrability lemmas about `laplaceTrace`, the
Newtonian kernel and the cut-off kernel `cutNewton`, in the namespace
`Work.FTS.PressureOn.PoissonAux.kgiAux`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.PressureOn.PoissonAux.Defs
import Submission.Work.FTS.PressureOn.PoissonAux.Ibp
import Submission.Work.FTS.PressureOn.PoissonAux.Ibp2
import Submission.Work.FTS.PressureOn.PoissonAux.laplaceTrace_cutKernel
import Submission.Work.FTS.PressureOn.PoissonAux.tendsto_integral_massKernel_mul
import Submission.Work.FTS.PressureOn.PoissonAux.integral_radial
import Submission.Work.FTS.PressureOn.PoissonAux.gradient_newtonKernel
import Submission.Work.FTS.PressureOn.PoissonAux.laplaceTrace_fderiv_comm
import Submission.Work.FTS.PressureOn.Green.integral_mul_laplaceTrace_comm
import Submission.Work.FTS.PressureOn.Green.integrableOn_newtonKernel_ball

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter Topology
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.PressureOn.PoissonAux

namespace kgiAux
noncomputable abbrev cutNewton (ε : ℝ) : R3 → ℝ := fun z => smallCut ε z * newtonKernel z

theorem cutNewton_eq_cutProfile (ε : ℝ) (z : R3) :
    cutNewton ε z = cutProfile ε (‖z‖ ^ 2) := (cutProfile_normSq ε z).symm

theorem contDiff_cutNewton (ε : ℝ) (hε : 0 < ε) : ContDiff ℝ 2 (cutNewton ε) := by
  have h : cutNewton ε = fun z : R3 => cutProfile ε (‖z‖ ^ 2) :=
    funext (cutNewton_eq_cutProfile ε)
  rw [h]
  exact (contDiff_cutProfile ε hε).comp (contDiff_norm_sq (𝕜 := ℝ) (n := 2))

/-! ## Regularity of `laplaceTrace` -/

/-- The first partial derivative of a `C³` function is `C²`. -/
theorem contDiff_two_fderiv_apply_e {u : R3 → ℝ} (hu : ContDiff ℝ 3 u) (i : Fin 3) :
    ContDiff ℝ 2 (fun x : R3 => fderiv ℝ u x (FiniteTimeSingularity.e i)) := by
  have h : ContDiff ℝ 2 (fun p : R3 × R3 => fderiv ℝ u p.1 p.2) :=
    ContDiff.contDiff_fderiv_apply hu (by norm_num)
  have h2 : ContDiff ℝ 2 (fun x : R3 => (x, FiniteTimeSingularity.e i)) := by
    have h3 : ContDiff ℝ 2 (fun x : R3 => ((x, (0 : R3)) : R3 × R3)) :=
      (ContinuousLinearMap.inl ℝ R3 R3).contDiff
    simpa using h3.add (contDiff_const (c := ((0 : R3), FiniteTimeSingularity.e i)))
  exact h.comp h2

/-- `laplaceTrace Ψ` is `C¹` when `Ψ` is smooth. -/
theorem contDiff_one_laplaceTrace {Ψ : R3 → ℝ} (hΨ : ∀ n : ℕ, ContDiff ℝ n Ψ) :
    ContDiff ℝ 1 (laplaceTrace Ψ) := by
  change ContDiff ℝ 1 (fun x : R3 => ∑ i : Fin 3, fderiv ℝ
    (fun w : R3 => fderiv ℝ Ψ w (FiniteTimeSingularity.e i)) x (FiniteTimeSingularity.e i))
  exact ContDiff.sum fun i _ =>
    contDiff_fderiv_apply_e (contDiff_two_fderiv_apply_e (hΨ 3) i) i

/-- The Laplacian of a compactly supported function is compactly supported. -/
theorem hasCompactSupport_laplaceTrace {Ψ : R3 → ℝ} (hcs : HasCompactSupport Ψ) :
    HasCompactSupport (laplaceTrace Ψ) := by
  refine hcs.mono' fun z hz => ?_
  by_contra hzt
  exact hz (Work.FTS.PressureOn.Green.laplaceTrace_eq_zero_of_notMem_tsupport hzt)

/-! ## Translation invariance of `laplaceTrace` -/

/-- `laplaceTrace` is invariant under translations of the argument. -/
theorem laplaceTrace_comp_add (g : R3 → ℝ) (a : R3) (z : R3) :
    laplaceTrace (fun z' : R3 => g (a + z')) z = laplaceTrace g (a + z) := by
  rw [laplaceTrace, laplaceTrace]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : (fun w : R3 => fderiv ℝ (fun z' : R3 => g (a + z')) w (FiniteTimeSingularity.e i))
      = fun w : R3 => fderiv ℝ g (a + w) (FiniteTimeSingularity.e i) := by
    funext w
    exact congrArg (fun L : R3 →L[ℝ] ℝ => L (FiniteTimeSingularity.e i))
      (fderiv_comp_add_left (𝕜 := ℝ) (f := g) (x := w) a)
  rw [h1]
  exact congrArg (fun L : R3 →L[ℝ] ℝ => L (FiniteTimeSingularity.e i))
    (fderiv_comp_add_left (𝕜 := ℝ)
      (f := fun u : R3 => fderiv ℝ g u (FiniteTimeSingularity.e i)) (x := z) a)

/-- The gradient of a translated function at the origin is the gradient at the centre. -/
theorem gradient_comp_add_const (g : R3 → ℝ) (a : R3) :
    gradient (fun z : R3 => g (a + z)) 0 = gradient g a := by
  rw [gradient, gradient, fderiv_comp_add_left (𝕜 := ℝ) (f := g) (x := 0) a, add_zero]

/-! ## Integrability of the Newtonian gradient -/

/-- `x ^ (-2) = (x ^ 2)⁻¹` for `x ≥ 0`. -/
theorem rpow_neg_two {x : ℝ} (hx : 0 ≤ x) : x ^ (-2 : ℝ) = (x ^ 2)⁻¹ := by
  rw [Real.rpow_neg hx (2 : ℝ), Real.rpow_two]

/-- The pointwise size of `newtonGrad`: `‖∇N(z)‖ = (4π)⁻¹‖z‖^{-2}`. -/
theorem norm_newtonGrad_rpow (z : R3) :
    ‖newtonGrad z‖ = (4 * Real.pi)⁻¹ * ‖z‖ ^ (-2 : ℝ) := by
  rw [norm_newtonGrad]
  rcases eq_or_lt_of_le (norm_nonneg z) with h | h
  · have hz0 : z = 0 := norm_eq_zero.mp h.symm
    subst hz0
    simp [Real.zero_rpow (by norm_num : (-2 : ℝ) ≠ 0)]
  · rw [rpow_neg_two (le_of_lt h)]
    have h2 : (‖z‖ ^ (3 : ℕ))⁻¹ * ‖z‖ = (‖z‖ ^ 2)⁻¹ := by
      have hne : ‖z‖ ≠ 0 := ne_of_gt h
      field_simp
    rw [show (4 * Real.pi)⁻¹ * (‖z‖ ^ (3 : ℕ))⁻¹ * ‖z‖
        = (4 * Real.pi)⁻¹ * ((‖z‖ ^ (3 : ℕ))⁻¹ * ‖z‖) by ring, h2]

/-- A compactly supported function is supported inside some open ball. -/
theorem exists_ball_tsupport_subset {f : R3 → ℝ} (hcs : HasCompactSupport f) :
    ∃ R : ℝ, tsupport f ⊆ Metric.ball 0 R := by
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : R3)).mp hcs.isBounded
  refine ⟨r + 1, fun z hz => ?_⟩
  have h1 := hr hz
  rw [Metric.mem_closedBall, dist_zero_right] at h1
  rw [Metric.mem_ball, dist_zero_right]
  linarith

/-- **The Newtonian gradient times a compactly supported continuous function is integrable.** -/
theorem integrable_smul_newtonGrad {f : R3 → ℝ} (hf : Continuous f)
    (hcs : HasCompactSupport f) :
    Integrable (fun z : R3 => f z • newtonGrad z) := by
  obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuousOn hf.continuousOn
  have hCglob : ∀ z : R3, ‖f z‖ ≤ max C 0 := by
    intro z
    by_cases hz : z ∈ tsupport f
    · exact le_trans (hC z hz) (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport hz, norm_zero]
      exact le_max_right _ _
  obtain ⟨R, hR⟩ := exists_ball_tsupport_subset hcs
  have hsubset : Function.support (fun z : R3 => f z • newtonGrad z) ⊆ Metric.ball 0 R := by
    intro z hz
    rw [Function.mem_support] at hz
    by_contra h
    exact hz (by
      rw [image_eq_zero_of_notMem_tsupport (fun hz' => h (hR hz')), zero_smul])
  have hmeas : AEStronglyMeasurable (fun z : R3 => f z • newtonGrad z) volume := by
    have hfun : (fun z : R3 => f z • newtonGrad z)
        = fun z : R3 => (-(f z * (4 * Real.pi * ‖z‖ ^ 3)⁻¹)) • z := by
      funext z
      rw [newtonGrad_apply, mul_inv]
      simp only [neg_smul, smul_neg, smul_smul]
      ring_nf
    rw [hfun]
    exact (((hf.measurable.mul
      (((continuous_norm.pow 3).const_mul (4 * Real.pi)).measurable.inv)).neg).smul
        measurable_id).aestronglyMeasurable
  refine (MeasureTheory.integrableOn_iff_integrable_of_support_subset hsubset).mp ?_
  refine MeasureTheory.integrableOn_ball_of_norm_le_rpow (μ := volume) (F := R3)
    (C := max C 0 * (4 * Real.pi)⁻¹) (α := 2) (r := R) ?_ ?_ ?_ hmeas
  · rw [show Module.finrank ℝ R3 = 3 from by simp]
    norm_num
  · rw [show Module.finrank ℝ R3 = 3 from by simp]
    norm_num
  · filter_upwards with z
    have hnn : (0 : ℝ) ≤ (4 * Real.pi)⁻¹ * ‖z‖ ^ (-2 : ℝ) :=
      mul_nonneg (by positivity) (Real.rpow_nonneg (norm_nonneg z) _)
    rw [norm_smul, norm_newtonGrad_rpow]
    calc ‖f z‖ * ((4 * Real.pi)⁻¹ * ‖z‖ ^ (-2 : ℝ))
        = (4 * Real.pi)⁻¹ * ‖z‖ ^ (-2 : ℝ) * ‖f z‖ := by ring
      _ ≤ (4 * Real.pi)⁻¹ * ‖z‖ ^ (-2 : ℝ) * max C 0 :=
            mul_le_mul_of_nonneg_left (hCglob z) hnn
      _ = max C 0 * (4 * Real.pi)⁻¹ * ‖z‖ ^ (-2 : ℝ) := by ring

/-! ## Integration by parts against the cut-off kernel -/

/-- The origin is a null set of `ℝ³`. -/
theorem ae_ne_zero_volume : ∀ᵐ z ∂(volume : Measure R3), z ≠ 0 := by
  rw [MeasureTheory.ae_iff]
  have h : {z : R3 | ¬ z ≠ 0} = {0} := by
    ext z
    simp
  rw [h]
  exact measure_singleton 0

/-- **The cut-off identity.**  For `ε > 0` and every coordinate `i`, the integral of `ΔΨ` against
the `i`-th partial derivative of the cut-off kernel `M_ε` equals `-∫ massKernel ε · ∂ᵢΨ`. -/
theorem truncated_eq {Ψ : R3 → ℝ} (hΨ : ∀ n : ℕ, ContDiff ℝ n Ψ) (hcs : HasCompactSupport Ψ)
    {ε : ℝ} (hε : 0 < ε) (i : Fin 3) :
    ∫ z, laplaceTrace Ψ z * fderiv ℝ (cutNewton ε) z (FiniteTimeSingularity.e i)
      = -∫ z, massKernel ε z * fderiv ℝ Ψ z (FiniteTimeSingularity.e i) := by
  have hcd : ContDiff ℝ 1 (cutNewton ε) := (contDiff_cutNewton ε hε).of_le (by norm_num)
  have hgreen := Work.FTS.PressureOn.Green.integral_mul_laplaceTrace_comm (cutNewton ε)
    (fun z : R3 => fderiv ℝ Ψ z (FiniteTimeSingularity.e i)) (contDiff_cutNewton ε hε)
    (contDiff_two_fderiv_apply_e (hΨ 3) i) (hasCompactSupport_fderiv_apply_e hcs i)
  calc ∫ z, laplaceTrace Ψ z * fderiv ℝ (cutNewton ε) z (FiniteTimeSingularity.e i)
      = ∫ z, fderiv ℝ (cutNewton ε) z (FiniteTimeSingularity.e i) * laplaceTrace Ψ z :=
        integral_congr_ae (Eventually.of_forall fun z => mul_comm _ _)
    _ = -∫ z, cutNewton ε z * fderiv ℝ (laplaceTrace Ψ) z (FiniteTimeSingularity.e i) :=
        integral_fderiv_mul_eq_neg hcd (contDiff_one_laplaceTrace hΨ)
          (hasCompactSupport_laplaceTrace hcs) i
    _ = -∫ z, cutNewton ε z * laplaceTrace
          (fun z' : R3 => fderiv ℝ Ψ z' (FiniteTimeSingularity.e i)) z := by
        congr 1
        refine integral_congr_ae ?_
        filter_upwards with z
        rw [show fderiv ℝ (laplaceTrace Ψ) z (FiniteTimeSingularity.e i)
            = laplaceTrace (fun z' : R3 => fderiv ℝ Ψ z' (FiniteTimeSingularity.e i)) z from
          congrFun (laplaceTrace_fderiv_comm (hΨ 3) i).symm z]
    _ = -∫ z, laplaceTrace (cutNewton ε) z * fderiv ℝ Ψ z (FiniteTimeSingularity.e i) := by
        rw [hgreen]
    _ = -∫ z, massKernel ε z * fderiv ℝ Ψ z (FiniteTimeSingularity.e i) := by
        congr 1
        refine integral_congr_ae ?_
        filter_upwards [ae_ne_zero_volume] with z hz
        have hcut : laplaceTrace (fun y : R3 => smallCut ε y * newtonKernel y) z
            = massKernel ε z := laplaceTrace_cutKernel ε hε hz
        change laplaceTrace (fun y : R3 => smallCut ε y * newtonKernel y) z
            * fderiv ℝ Ψ z (FiniteTimeSingularity.e i)
          = massKernel ε z * fderiv ℝ Ψ z (FiniteTimeSingularity.e i)
        rw [hcut]

end kgiAux

end Work.FTS.PressureOn.PoissonAux
