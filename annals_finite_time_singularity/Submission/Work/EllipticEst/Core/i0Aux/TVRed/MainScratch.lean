/-
Copyright: work module for the Elgindi finite-time singularity project.

# The open-class interpolation from the trace-vanishing interpolation

From the trace-vanishing weighted slice interpolation `TV` we deduce the open-class inequality
for functions whose only endpoint hypothesis is `f 0 = f (π/2) = 0`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.EllipticEst.Core.sliceBoundaryLimit
import Submission.Work.FTS.EllipticEst.Honest.sliceInterp
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.Defs
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.BumpFacts
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.Helpers
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.endpointParamLeftW
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.endpointParamRightW
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.surrIntegrals
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.ibpSurr
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.csThEta
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.integralSqSub
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.tvHypBundle
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.sScaleBounds
import Submission.Work.FTS.EllipticEst.AngAWeak.corrSlice_limits
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core.i0Aux

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 4000000

noncomputable section

/-- `|a| ≤ √B` from `a² ≤ B` and `0 ≤ B`. -/
lemma tvc_abs_le_sqrt {a B : ℝ} (hB : 0 ≤ B) (h : a ^ 2 ≤ B) : |a| ≤ Real.sqrt B := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt h

/-- The derivative identities for `g = f - surrFun ψ F₀ F₁ L` on `Iθ`. -/
lemma tvc_deriv_g_ae {f : ℝ → ℝ} {ψ : ℝ → ℝ} {F₀ F₁ L : ℝ} (hL : L ≠ 0)
    (hψ : ContDiff ℝ 2 ψ)
    (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2))) :
    ((fun θ : ℝ => deriv (fun θ : ℝ => f θ - surrFun ψ F₀ F₁ L θ) θ)
        =ᵐ[volume.restrict Work.Spaces.Iθ]
        (fun θ : ℝ => deriv f θ - deriv (surrFun ψ F₀ F₁ L) θ)) ∧
    ((fun θ : ℝ => deriv (deriv (fun θ : ℝ => f θ - surrFun ψ F₀ F₁ L θ)) θ)
        =ᵐ[volume.restrict Work.Spaces.Iθ]
        (fun θ : ℝ => deriv (deriv f) θ - deriv (deriv (surrFun ψ F₀ F₁ L)) θ)) := by
  have hsmooth : ContDiff ℝ 2 (surrFun ψ F₀ F₁ L) := by
    have hdiv1 : ContDiff ℝ 2 (fun θ : ℝ => θ / L) := by
      have he : (fun θ : ℝ => θ / L) = fun θ : ℝ => θ * (1 / L) := by funext θ; ring
      rw [he]; fun_prop
    have hdiv2 : ContDiff ℝ 2 (fun θ : ℝ => (Real.pi / 2 - θ) / L) := by
      have he : (fun θ : ℝ => (Real.pi / 2 - θ) / L)
          = fun θ : ℝ => (Real.pi / 2 - θ) * (1 / L) := by funext θ; ring
      rw [he]; fun_prop
    have h1 : ContDiff ℝ 2 (fun θ : ℝ => ψ (θ / L)) := hψ.comp hdiv1
    have h2 : ContDiff ℝ 2 (fun θ : ℝ => ψ ((Real.pi / 2 - θ) / L)) := hψ.comp hdiv2
    have h3 : ContDiff ℝ 2 (fun θ : ℝ => F₀ * ψ (θ / L) + F₁ * ψ ((Real.pi / 2 - θ) / L)) :=
      (contDiff_const.mul h1).add (contDiff_const.mul h2)
    have hfun : surrFun ψ F₀ F₁ L
        = fun θ : ℝ => F₀ * ψ (θ / L) + F₁ * ψ ((Real.pi / 2 - θ) / L) := rfl
    rw [hfun]; exact h3
  have hae : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo 0 (Real.pi / 2) := by
    rw [Measure.restrict_congr_set tvc_ae_eq_Iθ_Ioo]
    exact MeasureTheory.ae_restrict_mem measurableSet_Ioo
  have hpt1 : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      deriv (fun θ : ℝ => f θ - surrFun ψ F₀ F₁ L θ) θ
        = deriv f θ - deriv (surrFun ψ F₀ F₁ L) θ := by
    intro θ hθ
    have h1 : DifferentiableAt ℝ f θ :=
      (hf.contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt (by norm_num)
    have h2 : DifferentiableAt ℝ (surrFun ψ F₀ F₁ L) θ :=
      (hsmooth.differentiable (by norm_num)).differentiableAt
    exact deriv_sub h1 h2
  have hpt2 : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      deriv (deriv (fun θ : ℝ => f θ - surrFun ψ F₀ F₁ L θ)) θ
        = deriv (deriv f) θ - deriv (deriv (surrFun ψ F₀ F₁ L)) θ := by
    intro θ hθ
    have hd1 : DifferentiableAt ℝ (deriv f) θ := by
      have h1 : ContDiffOn ℝ 1 (deriv f) (Set.Ioo 0 (Real.pi / 2)) :=
        hf.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
      exact (h1.contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt (by norm_num)
    have hd2 : DifferentiableAt ℝ (deriv (surrFun ψ F₀ F₁ L)) θ := by
      have h1 : ContDiffOn ℝ 1 (deriv (surrFun ψ F₀ F₁ L)) (Set.Ioo 0 (Real.pi / 2)) :=
        (hsmooth.contDiffOn).deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
      exact (h1.contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt (by norm_num)
    have hev : deriv (fun θ : ℝ => f θ - surrFun ψ F₀ F₁ L θ)
        =ᶠ[𝓝 θ] (fun y : ℝ => deriv f y - deriv (surrFun ψ F₀ F₁ L) y) := by
      filter_upwards [isOpen_Ioo.mem_nhds hθ] with y hy
      exact hpt1 y hy
    rw [hev.deriv_eq]
    exact deriv_sub hd1 hd2
  exact ⟨by
      filter_upwards [hae] with θ hθ
      exact hpt1 θ hθ, by
      filter_upwards [hae] with θ hθ
      exact hpt2 θ hθ⟩

/-- The first-order bound for `g = f - surrFun ψ F₀ F₁ L`. -/
lemma tvc_g1_bound {f : ℝ → ℝ} {ψ : ℝ → ℝ} {F₀ F₁ L : ℝ} (hL : L ≠ 0)
    (hψ : ContDiff ℝ 2 ψ)
    (hP : IntegrableOn (fun θ : ℝ => (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ)
    (hX1int : IntegrableOn
      (fun θ : ℝ => (surrFun ψ F₀ F₁ L θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ)
    (hG1int : IntegrableOn
      (fun θ : ℝ => (f θ - surrFun ψ F₀ F₁ L θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, (f θ - surrFun ψ F₀ F₁ L θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      ≤ 2 * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        + 2 * (∫ θ in Work.Spaces.Iθ, (surrFun ψ F₀ F₁ L θ) ^ 2
            * Work.FTS.EllipticEst.thEta θ) := by
  have hRint : IntegrableOn
      (fun θ : ℝ => 2 * ((f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        + 2 * ((surrFun ψ F₀ F₁ L θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)) Work.Spaces.Iθ :=
    (hP.const_mul 2).add (hX1int.const_mul 2)
  have hmono : (∫ θ in Work.Spaces.Iθ,
        (f θ - surrFun ψ F₀ F₁ L θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      ≤ ∫ θ in Work.Spaces.Iθ, 2 * ((f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        + 2 * ((surrFun ψ F₀ F₁ L θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
    refine MeasureTheory.integral_mono_ae hG1int hRint ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    have hs : 0 ≤ Work.FTS.EllipticEst.thEta θ := Work.FTS.EllipticEst.thEta_nonneg hθ
    have h2 : (f θ - surrFun ψ F₀ F₁ L θ) ^ 2
        ≤ 2 * (f θ) ^ 2 + 2 * (surrFun ψ F₀ F₁ L θ) ^ 2 := by
      nlinarith [sq_nonneg (f θ + surrFun ψ F₀ F₁ L θ)]
    calc (f θ - surrFun ψ F₀ F₁ L θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
        ≤ (2 * (f θ) ^ 2 + 2 * (surrFun ψ F₀ F₁ L θ) ^ 2) * Work.FTS.EllipticEst.thEta θ :=
          mul_le_mul_of_nonneg_right h2 hs
      _ = 2 * ((f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        + 2 * ((surrFun ψ F₀ F₁ L θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) := by ring
  calc (∫ θ in Work.Spaces.Iθ, (f θ - surrFun ψ F₀ F₁ L θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      ≤ ∫ θ in Work.Spaces.Iθ, 2 * ((f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        + 2 * ((surrFun ψ F₀ F₁ L θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) := hmono
    _ = 2 * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        + 2 * (∫ θ in Work.Spaces.Iθ, (surrFun ψ F₀ F₁ L θ) ^ 2
            * Work.FTS.EllipticEst.thEta θ) := by
        rw [MeasureTheory.integral_add (hP.const_mul 2) (hX1int.const_mul 2),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]

/-- The second-order bound for `g = f - surrFun ψ F₀ F₁ L`. -/
lemma tvc_g2_bound {f : ℝ → ℝ} {ψ : ℝ → ℝ} {F₀ F₁ L : ℝ} (hL : L ≠ 0)
    (hψ : ContDiff ℝ 2 ψ)
    (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (hE : IntegrableOn
      (fun θ : ℝ => (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ)
    (hX3int : IntegrableOn
      (fun θ : ℝ => (deriv (deriv (surrFun ψ F₀ F₁ L)) θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ)
    (hG2int : IntegrableOn
      (fun θ : ℝ => (deriv (deriv (fun θ : ℝ => f θ - surrFun ψ F₀ F₁ L θ)) θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, (deriv (deriv (fun θ : ℝ => f θ - surrFun ψ F₀ F₁ L θ)) θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ)
      ≤ 2 * (∫ θ in Work.Spaces.Iθ, (deriv (deriv f) θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ)
        + 2 * (∫ θ in Work.Spaces.Iθ, (deriv (deriv (surrFun ψ F₀ F₁ L)) θ) ^ 2
            * Work.FTS.EllipticEst.thEta θ) := by
  have hcongr : (fun θ : ℝ => (deriv (deriv (fun θ : ℝ => f θ - surrFun ψ F₀ F₁ L θ)) θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ)
      =ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ : ℝ => (deriv (deriv f) θ - deriv (deriv (surrFun ψ F₀ F₁ L)) θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ) := by
    filter_upwards [(tvc_deriv_g_ae hL hψ hf).2] with θ hθ
    rw [hθ]
  rw [integral_congr_ae hcongr]
  have hRint : IntegrableOn
      (fun θ : ℝ => 2 * ((deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        + 2 * ((deriv (deriv (surrFun ψ F₀ F₁ L)) θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ)) Work.Spaces.Iθ :=
    (hE.const_mul 2).add (hX3int.const_mul 2)
  have hmono : (∫ θ in Work.Spaces.Iθ,
        (deriv (deriv f) θ - deriv (deriv (surrFun ψ F₀ F₁ L)) θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ)
      ≤ ∫ θ in Work.Spaces.Iθ, 2 * ((deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        + 2 * ((deriv (deriv (surrFun ψ F₀ F₁ L)) θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ) := by
    refine MeasureTheory.integral_mono_ae
      (hG2int.congr hcongr) hRint ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    have hs : 0 ≤ Work.FTS.EllipticEst.thEta θ := Work.FTS.EllipticEst.thEta_nonneg hθ
    have h2 : (deriv (deriv f) θ - deriv (deriv (surrFun ψ F₀ F₁ L)) θ) ^ 2
        ≤ 2 * (deriv (deriv f) θ) ^ 2 + 2 * (deriv (deriv (surrFun ψ F₀ F₁ L)) θ) ^ 2 := by
      nlinarith [sq_nonneg (deriv (deriv f) θ + deriv (deriv (surrFun ψ F₀ F₁ L)) θ)]
    calc (deriv (deriv f) θ - deriv (deriv (surrFun ψ F₀ F₁ L)) θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ
        ≤ (2 * (deriv (deriv f) θ) ^ 2
            + 2 * (deriv (deriv (surrFun ψ F₀ F₁ L)) θ) ^ 2) * Work.FTS.EllipticEst.thEta θ :=
          mul_le_mul_of_nonneg_right h2 hs
      _ = 2 * ((deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        + 2 * ((deriv (deriv (surrFun ψ F₀ F₁ L)) θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ) := by ring
  calc (∫ θ in Work.Spaces.Iθ, (deriv (deriv f) θ - deriv (deriv (surrFun ψ F₀ F₁ L)) θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ)
      ≤ ∫ θ in Work.Spaces.Iθ, 2 * ((deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        + 2 * ((deriv (deriv (surrFun ψ F₀ F₁ L)) θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ) := hmono
    _ = 2 * (∫ θ in Work.Spaces.Iθ, (deriv (deriv f) θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ)
        + 2 * (∫ θ in Work.Spaces.Iθ, (deriv (deriv (surrFun ψ F₀ F₁ L)) θ) ^ 2
            * Work.FTS.EllipticEst.thEta θ) := by
        rw [MeasureTheory.integral_add (hE.const_mul 2) (hX3int.const_mul 2),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]

/-- Auxiliary: `X2`-type bound helpers (kept local to the main proof are inlined). -/
lemma tvc_integrableOn_cross {f : ℝ → ℝ} {ψ : ℝ → ℝ} {F₀ F₁ L : ℝ}
    (hψ : ContDiff ℝ 2 ψ)
    (hA : IntegrableOn (fun θ : ℝ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ)
    (hℓ1int : IntegrableOn
      (fun θ : ℝ => (deriv (surrFun ψ F₀ F₁ L) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      Work.Spaces.Iθ) :
    IntegrableOn (fun θ : ℝ => deriv f θ * deriv (surrFun ψ F₀ F₁ L) θ
      * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ := by
  refine Integrable.mono' (hA.add hℓ1int) ?_ ?_
  · exact (((measurable_deriv f).mul (measurable_deriv _)).aestronglyMeasurable.mul tvc_aesm_thEta)
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    have hs : 0 ≤ Work.FTS.EllipticEst.thEta θ := Work.FTS.EllipticEst.thEta_nonneg hθ
    rw [Real.norm_eq_abs,
      show |deriv f θ * deriv (surrFun ψ F₀ F₁ L) θ * Work.FTS.EllipticEst.thEta θ|
          = |deriv f θ| * |deriv (surrFun ψ F₀ F₁ L) θ| * Work.FTS.EllipticEst.thEta θ by
        rw [abs_mul, abs_mul, abs_of_nonneg hs]]
    have h2 : |deriv f θ| * |deriv (surrFun ψ F₀ F₁ L) θ|
        ≤ (deriv f θ) ^ 2 / 2 + (deriv (surrFun ψ F₀ F₁ L) θ) ^ 2 / 2 := by
      nlinarith [sq_nonneg (|deriv f θ| - |deriv (surrFun ψ F₀ F₁ L) θ|), sq_abs (deriv f θ),
        sq_abs (deriv (surrFun ψ F₀ F₁ L) θ)]
    calc |deriv f θ| * |deriv (surrFun ψ F₀ F₁ L) θ| * Work.FTS.EllipticEst.thEta θ
        ≤ ((deriv f θ) ^ 2 / 2 + (deriv (surrFun ψ F₀ F₁ L) θ) ^ 2 / 2)
            * Work.FTS.EllipticEst.thEta θ := mul_le_mul_of_nonneg_right h2 hs
      _ = (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ / 2
          + (deriv (surrFun ψ F₀ F₁ L) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ / 2 := by ring
      _ ≤ (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
          + (deriv (surrFun ψ F₀ F₁ L) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
          nlinarith [mul_nonneg (sq_nonneg (deriv f θ)) hs,
            mul_nonneg (sq_nonneg (deriv (surrFun ψ F₀ F₁ L) θ)) hs]

/-- The `∫(deriv g)²σ` identity. -/
lemma tvc_derivg2_eq {f : ℝ → ℝ} {ψ : ℝ → ℝ} {F₀ F₁ L : ℝ} (hL : L ≠ 0)
    (hψ : ContDiff ℝ 2 ψ)
    (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (hA : IntegrableOn (fun θ : ℝ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ)
    (hℓ1int : IntegrableOn
      (fun θ : ℝ => (deriv (surrFun ψ F₀ F₁ L) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      Work.Spaces.Iθ)
    (hcross : IntegrableOn (fun θ : ℝ => deriv f θ * deriv (surrFun ψ F₀ F₁ L) θ
      * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ,
        (deriv (fun θ : ℝ => f θ - surrFun ψ F₀ F₁ L θ) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      = (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        - 2 * (∫ θ in Work.Spaces.Iθ, deriv f θ * deriv (surrFun ψ F₀ F₁ L) θ
            * Work.FTS.EllipticEst.thEta θ)
        + (∫ θ in Work.Spaces.Iθ,
            (deriv (surrFun ψ F₀ F₁ L) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
  have hcongr : (fun θ : ℝ =>
        (deriv (fun θ : ℝ => f θ - surrFun ψ F₀ F₁ L θ) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      =ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ : ℝ => (deriv f θ - deriv (surrFun ψ F₀ F₁ L) θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ) := by
    filter_upwards [(tvc_deriv_g_ae hL hψ hf).1] with θ hθ
    rw [hθ]
  rw [integral_congr_ae hcongr]
  exact Work.EllipticEst.Core.i0Aux.TVRed.integralSqSub hA hℓ1int hcross

end

end Work.EllipticEst.Core.i0Aux
