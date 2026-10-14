import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.CompMul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Geometry.Euclidean.Angle.Unoriented.CrossProduct
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Trace
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PressureOn.integral_div_eq_zero_of_hasFDerivAt
import Submission.Work.FTS.PressureOn.weakCurl.int2_integrable
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.conv_shift_sq_integral_le
import Submission.Work.FTS_MuLamOK.Rows.rl0_final
import Submission.Work.LWP.BiotSavart.nearField_bound
import Submission.Work.Spaces.mixed_sq_integrableOn
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.BSSwirl.contDiff_vorticity_and_support =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Filter Topology

namespace Work.FTS.BSSwirl

noncomputable section

/-- **The vorticity of a smooth, compactly supported field is smooth and compactly supported.**

`vorticity Ψ` is the fixed continuous linear function `curlCLM` of the derivative `DΨ`, so the
`Cⁿ`-clause follows from `ContDiff.fderiv_right` and `ContDiff.comp`; and the vorticity vanishes
wherever `Ψ` is locally constant (in particular off `tsupport Ψ`), which gives the compact
support. -/
theorem contDiff_vorticity_and_support {Ψ : Work.FTS.BSSwirl.R3 → Work.FTS.BSSwirl.R3}
    (hΨ : ∀ n : ℕ, ContDiff ℝ n Ψ) (hc : HasCompactSupport Ψ) :
    (∀ n : ℕ, ContDiff ℝ n (fun x => FiniteTimeSingularity.vorticity Ψ x)) ∧
      HasCompactSupport (fun x => FiniteTimeSingularity.vorticity Ψ x) := by
  -- the vorticity is the fixed continuous linear map `curlCLM` evaluated at the derivative
  have hcurlv : (fun x : R3 => FiniteTimeSingularity.vorticity Ψ x)
      = fun x => Work.FTS.Physical.Pressure.curlCLM (fderiv ℝ Ψ x) :=
    funext fun x => Work.FTS.Physical.Pressure.vorticity_eq_curlCLM Ψ x
  -- the vorticity vanishes where `Ψ` is locally zero
  have hsub : Function.support (fun x : R3 => FiniteTimeSingularity.vorticity Ψ x) ⊆ tsupport Ψ := by
    intro x hx
    by_contra hxt
    -- `x` is in the complement of the closed set `tsupport Ψ`, an open neighbourhood of `x` ...
    have hnhds : (Function.support Ψ)ᶜ ∈ 𝓝 x :=
      mem_of_superset (((isClosed_tsupport Ψ).isOpen_compl).mem_nhds hxt)
        (compl_subset_compl.mpr subset_closure)
    -- ... on which `Ψ` therefore vanishes
    have hev : Ψ =ᶠ[𝓝 x] Function.const R3 0 := by
      filter_upwards [hnhds] with y hy
      have : Ψ y = 0 := by
        by_contra h
        exact hy (Function.mem_support.mpr h)
      simpa using this
    have hfd : fderiv ℝ Ψ x = 0 := by
      rw [hev.fderiv_eq]
      simp
    exact hx (by rw [hcurlv]; simp [hfd])
  refine ⟨fun n => ?_, ?_⟩
  · rw [hcurlv]
    exact (Work.FTS.Physical.Pressure.curlCLM.contDiff).comp
      ((hΨ (n + 1)).fderiv_right (by norm_num))
  · exact hc.isCompact.of_isClosed_subset (isClosed_tsupport _)
      (closure_minimal hsub (isClosed_tsupport Ψ))

end

end Work.FTS.BSSwirl
end
-- ===== merged: Submission.Work.FTS.Physical.Clock.T_sub_t_eq_tail =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set
open scoped Topology

namespace Work.FTS.Physical.Clock


end Work.FTS.Physical.Clock
end
-- ===== merged: Submission.Work.FTS.Physical.Pressure.vorticity_materialAccel_eq_zero_at =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FTS.Physical.Pressure

/-! ## Calculus lemmas for a jointly `C²` spacetime field `U : ℝ³ × ℝ → ℝ³` -/










/-! ## Additivity and germ-invariance of the curl -/



/-! ## The theorem -/


end Work.FTS.Physical.Pressure
end
-- ===== merged: Submission.Work.FTS.PressureOn.Auxiliary.HeatKernel =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The heat kernel on `ℝ³`

`heatKernel t z = (4πt)^{-3/2} exp(-‖z‖²/(4t))` is the heat kernel on `ℝ³` (the fundamental
solution of the heat equation `∂_t u = Δu`).

This file collects the definition and the elementary pointwise facts; the analytic facts
(`∫ γ_t = 1`, the heat equation `∂_t γ_t = Δ γ_t`, the `L¹` modulus of continuity, the tail decay
at `t → 0` and the integration-by-parts identity against a harmonic function) are proved in the
sibling files, and are used to prove Liouville's theorem for bounded harmonic functions
(`Work.FTS.PressureOn.Auxiliary.bounded_harmonic_const`).
-/

open MeasureTheory Set Filter Topology
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.PressureOn.Auxiliary

noncomputable section

/-- **The heat kernel on `ℝ³`**: `heatKernel t z = (4πt)^{-3/2} exp(-‖z‖²/(4t))`.  It solves the
heat equation `∂_t γ = Δγ`, integrates to `1` and is an approximate identity as `t → 0⁺`. -/
def heatKernel (t : ℝ) (z : R3) : ℝ :=
  (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * Real.exp (-(‖z‖ ^ 2 / (4 * t)))

@[simp] lemma heatKernel_apply (t : ℝ) (z : R3) :
    heatKernel t z = (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * Real.exp (-(‖z‖ ^ 2 / (4 * t))) := rfl

lemma heatKernel_nonneg {t : ℝ} (ht : 0 ≤ t) (z : R3) : 0 ≤ heatKernel t z := by
  have h1 : (0 : ℝ) ≤ 4 * Real.pi * t := by positivity
  exact mul_nonneg (Real.rpow_nonneg h1 _) (Real.exp_nonneg _)


lemma heatKernel_even (t : ℝ) (z : R3) : heatKernel t (-z) = heatKernel t z := by
  simp [heatKernel, norm_neg]


/-- The kernel written as a constant times a Gaussian, with the exponent parameter `c = 1/(4t)`. -/
lemma heatKernel_eq_const_mul_exp {t : ℝ} (ht : 0 < t) (z : R3) :
    heatKernel t z = (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * Real.exp (-((4 * t)⁻¹ * ‖z‖ ^ 2)) := by
  have h : ‖z‖ ^ 2 / (4 * t) = (4 * t)⁻¹ * ‖z‖ ^ 2 := by rw [div_eq_inv_mul]
  rw [heatKernel_apply, h]

end

end Work.FTS.PressureOn.Auxiliary
end
-- ===== merged: Submission.Work.FTS.PressureOn.Auxiliary.div_convolution =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Auxiliary

-- The divergence commutes with convolution with a locally integrable kernel `ρ`:
-- for `f : ℝ³ → ℝ³` of class `C¹` with compact support,
-- `div (ρ ⋆ f) x = (ρ ⋆ div f) x` for every `x`.
--
-- Proof.  `HasCompactSupport.hasFDerivAt_convolution_right` differentiates the convolution in the
-- second argument, so `fderiv ℝ (ρ ⋆ f) x = (ρ ⋆[L.precompR ℝ³] fderiv ℝ f) x`.  The trace of an
-- endomorphism of `ℝ³` is the sum of the diagonal entries in the standard basis
-- (`trace_eq_sum_single`), and `convolution_precompR_apply` evaluates the precompR-convolution at
-- each basis vector as a scalar convolution.  Coordinate extraction from the Bochner integral is
-- `eval_integral_piLp` (integrability of the integrands is `ConvolutionExists` for the compactly
-- supported functions `y ↦ fderiv ℝ f y (e i)`, which is `HasCompactSupport.fderiv_apply`), and
-- the sum of the diagonal entries is `div f` by `div_eq_sum_single`.
theorem div_convolution (ρ : EuclideanSpace ℝ (Fin 3) → ℝ)
    (f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hρ : MeasureTheory.LocallyIntegrable ρ MeasureTheory.volume)
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) :
    ∀ x, FiniteTimeSingularity.div
        (fun y => MeasureTheory.convolution ρ f (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume y) x
      = MeasureTheory.convolution ρ (fun y => FiniteTimeSingularity.div f y)
          (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume x := by
  intro x
  have hFcont : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  have hFcs : HasCompactSupport (fderiv ℝ f) := hfc.fderiv ℝ
  -- Differentiate the convolution in the second argument.
  have hderiv : HasFDerivAt
      (MeasureTheory.convolution ρ f (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume)
      (MeasureTheory.convolution ρ (fderiv ℝ f)
        ((ContinuousLinearMap.lsmul ℝ ℝ).precompR R3) MeasureTheory.volume x) x :=
    hfc.hasFDerivAt_convolution_right (L := ContinuousLinearMap.lsmul ℝ ℝ) hρ hf x
  change (fderiv ℝ
      (MeasureTheory.convolution ρ f (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume) x).trace ℝ R3
      = MeasureTheory.convolution ρ (fun y => FiniteTimeSingularity.div f y)
          (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume x
  rw [hderiv.fderiv, Work.FTS.PressureOn.trace_eq_sum_single]
  -- `convolution_precompR_apply`: value of the derivative on a vector.
  have hpre : ∀ v : R3,
      (MeasureTheory.convolution ρ (fderiv ℝ f)
        ((ContinuousLinearMap.lsmul ℝ ℝ).precompR R3) MeasureTheory.volume x) v
      = MeasureTheory.convolution ρ (fun a => fderiv ℝ f a v)
          (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume x := fun v =>
    MeasureTheory.convolution_precompR_apply (L := ContinuousLinearMap.lsmul ℝ ℝ) hρ
      hFcs hFcont x v
  -- Integrability of the (compactly supported) integrands, in vector and in coordinate form.
  have hVint : ∀ i : Fin 3,
      MeasureTheory.Integrable
        (fun t : R3 => ρ t • (fderiv ℝ f (x - t) (WithLp.toLp 2 (Pi.single i (1 : ℝ))))) := by
    intro i
    have hGcont : Continuous
        (fun y : R3 => fderiv ℝ f y (WithLp.toLp 2 (Pi.single i (1 : ℝ)))) :=
      hFcont.clm_apply continuous_const
    have hGcs : HasCompactSupport
        (fun y : R3 => fderiv ℝ f y (WithLp.toLp 2 (Pi.single i (1 : ℝ)))) :=
      hfc.fderiv_apply ℝ (WithLp.toLp 2 (Pi.single i (1 : ℝ)))
    exact hGcs.convolutionExists_right (L := ContinuousLinearMap.lsmul ℝ ℝ) hρ hGcont x
  have hcoordint : ∀ i j : Fin 3, MeasureTheory.Integrable
      (fun t : R3 => ρ t *
        (fderiv ℝ f (x - t) (WithLp.toLp 2 (Pi.single i (1 : ℝ)))).ofLp j) :=
    fun i j => by simpa [PiLp.smul_apply] using (hVint i).eval_piLp j
  -- The `i`-th diagonal entry of the derivative, as a scalar convolution.
  have hcoord : ∀ i : Fin 3,
      ((MeasureTheory.convolution ρ (fderiv ℝ f)
        ((ContinuousLinearMap.lsmul ℝ ℝ).precompR R3) MeasureTheory.volume x)
          (WithLp.toLp 2 (Pi.single i (1 : ℝ)))).ofLp i
      = ∫ t : R3, ρ t *
          (fderiv ℝ f (x - t) (WithLp.toLp 2 (Pi.single i (1 : ℝ)))).ofLp i := by
    intro i
    rw [hpre]
    rw [show MeasureTheory.convolution ρ
          (fun a => fderiv ℝ f a (WithLp.toLp 2 (Pi.single i (1 : ℝ))))
          (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume x
        = ∫ t : R3, ρ t •
            (fderiv ℝ f (x - t) (WithLp.toLp 2 (Pi.single i (1 : ℝ)))) from rfl]
    rw [MeasureTheory.eval_integral_piLp
      (f := fun t : R3 => ρ t •
        (fderiv ℝ f (x - t) (WithLp.toLp 2 (Pi.single i (1 : ℝ)))))
      (fun j => by simpa [PiLp.smul_apply] using (hVint i).eval_piLp j) i]
    simp [PiLp.smul_apply]
  -- The right-hand side, as an integral.
  have hdiv : MeasureTheory.convolution ρ (fun y => FiniteTimeSingularity.div f y)
      (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume x
      = ∫ t : R3, ρ t * FiniteTimeSingularity.div f (x - t) := by
    rw [show MeasureTheory.convolution ρ (fun y => FiniteTimeSingularity.div f y)
        (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume x
        = ∫ t : R3, ρ t • FiniteTimeSingularity.div f (x - t) from rfl]
    simp
  rw [hdiv, Finset.sum_congr rfl (fun i _ => hcoord i)]
  rw [← MeasureTheory.integral_finsetSum Finset.univ (fun i _ => hcoordint i i)]
  congr 1
  funext t
  rw [← Finset.mul_sum, ← Work.FTS.PressureOn.div_eq_sum_single]

end Work.FTS.PressureOn.Auxiliary
end
-- ===== merged: Submission.Work.FTS.PressureOn.Auxiliary.hasFDerivAt_of_weakGrad =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity MeasureTheory Filter Set
open scoped Topology Pointwise

namespace Work.FTS.PressureOn.Auxiliary

/-- **Integrability of a continuous function vanishing off a compact set in its second
variable.**  For a continuous `φ : ℝ → ℝ³ → ℝ` which vanishes on the interval `uIoc a b` whenever
its second argument lies outside a fixed compact set `K`, the uncurried function is integrable for
the product of Lebesgue measure on the interval `uIoc a b` (restricted) with Lebesgue measure on
`ℝ³`.  This is the Fubini hypothesis needed to swap an interval integral in the first variable
with an integral over `ℝ³` in the second. -/
lemma integrable_uncurry_prod_restrict_aux {a b : ℝ} {K : Set (EuclideanSpace ℝ (Fin 3))}
    (hK : IsCompact K)
    {φ : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ} (hφ : Continuous (Function.uncurry φ))
    (hvan : ∀ σ ∈ Set.uIoc a b, ∀ u, u ∉ K → φ σ u = 0) :
    Integrable (Function.uncurry φ)
      ((volume.restrict (Set.uIoc a b)).prod volume) := by
  have hmeas : MeasurableSet (Set.uIcc a b ×ˢ K) :=
    isCompact_uIcc.isClosed.measurableSet.prod hK.isClosed.measurableSet
  have hmeas2 : MeasurableSet (Set.uIoc a b ×ˢ (Set.univ : Set (EuclideanSpace ℝ (Fin 3)))) :=
    measurableSet_uIoc.prod MeasurableSet.univ
  obtain ⟨C, hC⟩ := (isCompact_uIcc.prod hK).exists_bound_of_continuousOn hφ.continuousOn
  have hbox : IntegrableOn (Function.uncurry φ) (Set.uIcc a b ×ˢ K) (volume.prod volume) := by
    refine IntegrableOn.of_bound ?_ ?_ C ?_
    · rw [Measure.prod_prod]
      exact ENNReal.mul_lt_top isCompact_uIcc.measure_lt_top hK.measure_lt_top
    · exact hφ.aestronglyMeasurable.restrict
    · rw [ae_restrict_iff' hmeas]
      exact Eventually.of_forall fun p hp => hC p hp
  have hind : Integrable (Set.indicator (Set.uIcc a b ×ˢ K) (Function.uncurry φ))
      (volume.prod volume) := (integrable_indicator_iff hmeas).mpr hbox
  have hsub : Set.uIcc a b \ Set.uIoc a b ⊆ ({a, b} : Set ℝ) := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    rw [Set.mem_uIcc] at hx1
    rw [Set.mem_uIoc] at hx2
    rw [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases hx1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · by_cases h : a < x
      · exact absurd (Or.inl ⟨h, h2⟩) hx2
      · left; exact le_antisymm (not_lt.mp h) h1
    · by_cases h : b < x
      · exact absurd (Or.inr ⟨h, h2⟩) hx2
      · right; exact le_antisymm (not_lt.mp h) h1
  have hae : Set.indicator (Set.uIcc a b ×ˢ K) (Function.uncurry φ)
      =ᵐ[volume.prod volume]
      Set.indicator (Set.uIoc a b ×ˢ (Set.univ : Set (EuclideanSpace ℝ (Fin 3))))
        (Function.uncurry φ) := by
    rw [Filter.EventuallyEq, ae_iff]
    refine measure_mono_null (t := ({a, b} : Set ℝ) ×ˢ K) ?_ ?_
    · intro p hp
      rw [Set.mem_ofPred_eq] at hp
      have hmem1 : p.2 ∈ K := by
        by_contra h2c
        apply hp
        have h1 : (Set.uIcc a b ×ˢ K).indicator (Function.uncurry φ) p = 0 :=
          Set.indicator_of_notMem (fun hc => h2c hc.2) _
        have h2 : (Set.uIoc a b ×ˢ (Set.univ : Set (EuclideanSpace ℝ (Fin 3)))).indicator
            (Function.uncurry φ) p = 0 := by
          by_cases h3 : p.1 ∈ Set.uIoc a b
          · rw [Set.indicator_of_mem (show p ∈ Set.uIoc a b ×ˢ Set.univ from
              ⟨h3, Set.mem_univ _⟩)]
            exact hvan p.1 h3 p.2 h2c
          · exact Set.indicator_of_notMem (fun hc => h3 hc.1) _
        rw [h1, h2]
      have hmem2 : p.1 ∈ ({a, b} : Set ℝ) := by
        by_contra h1c
        apply hp
        by_cases h3 : p.1 ∈ Set.uIoc a b
        · rw [Set.indicator_of_mem (show p ∈ Set.uIcc a b ×ˢ K from
                ⟨Set.uIoc_subset_uIcc h3, hmem1⟩),
              Set.indicator_of_mem (show p ∈ Set.uIoc a b ×ˢ Set.univ from
                ⟨h3, Set.mem_univ _⟩)]
        · have h4 : p.1 ∉ Set.uIcc a b := fun hc => h1c (hsub ⟨hc, h3⟩)
          rw [Set.indicator_of_notMem (fun hc => h4 hc.1),
            Set.indicator_of_notMem (fun hc => h3 hc.1)]
      exact Set.mem_prod.mpr ⟨hmem2, hmem1⟩
    · rw [Measure.prod_prod, show (volume : Measure ℝ) ({a, b} : Set ℝ) = 0 from by
        rw [show ({a, b} : Set ℝ) = {a} ∪ {b} from rfl,
          measure_union_null (measure_singleton a) (measure_singleton b)], zero_mul]
  have hind2 : Integrable (Set.indicator (Set.uIoc a b ×ˢ
      (Set.univ : Set (EuclideanSpace ℝ (Fin 3)))) (Function.uncurry φ))
      (volume.prod volume) := hind.congr hae
  have h1' : IntegrableOn (Function.uncurry φ)
      (Set.uIoc a b ×ˢ (Set.univ : Set (EuclideanSpace ℝ (Fin 3))))
      (volume.prod volume) := (integrable_indicator_iff hmeas2).mp hind2
  have hEq := Measure.prod_restrict (μ := (volume : Measure ℝ))
    (ν := (volume : Measure (EuclideanSpace ℝ (Fin 3)))) (Set.uIoc a b) Set.univ
  rw [Measure.restrict_univ] at hEq
  rw [hEq]
  exact h1'

/-- The chain rule for a translate of a function: the derivative of `w ↦ g (w - s • eᵢ)` is the
translated derivative of `g`. -/
lemma hasFDerivAt_sub_smul_comp (g : EuclideanSpace ℝ (Fin 3) → ℝ) (hg : Differentiable ℝ g)
    (i : Fin 3) (s : ℝ) (y : EuclideanSpace ℝ (Fin 3)) :
    fderiv ℝ (fun w : EuclideanSpace ℝ (Fin 3) => g (w - s • FiniteTimeSingularity.e i)) y
      = fderiv ℝ g (y - s • FiniteTimeSingularity.e i) := by
  have h1 : HasFDerivAt (fun w : EuclideanSpace ℝ (Fin 3) => w - s • FiniteTimeSingularity.e i)
      (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 3))) y := (hasFDerivAt_id y).sub_const _
  have h2 : HasFDerivAt g (fderiv ℝ g (y - s • FiniteTimeSingularity.e i))
      (y - s • FiniteTimeSingularity.e i) := (hg _).hasFDerivAt
  have h3 := h2.comp y h1
  simpa [Function.comp_def] using h3.fderiv

/-- A translate of a compactly supported function is compactly supported. -/
lemma hasCompactSupport_sub_smul (g : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hg : HasCompactSupport g) (i : Fin 3) (s : ℝ) :
    HasCompactSupport
      (fun y : EuclideanSpace ℝ (Fin 3) => g (y - s • FiniteTimeSingularity.e i)) := by
  refine HasCompactSupport.intro
    (K := tsupport g + ({s • FiniteTimeSingularity.e i} : Set (EuclideanSpace ℝ (Fin 3))))
    (IsCompact.add hg isCompact_singleton) ?_
  intro y hy
  refine image_eq_zero_of_notMem_tsupport (fun hmem => hy ?_)
  rw [Set.mem_add]
  exact ⟨y - s • FiniteTimeSingularity.e i, hmem, s • FiniteTimeSingularity.e i,
    Set.mem_singleton _, by abel⟩

/-- **Weak gradient ⟹ the coordinate fundamental theorem of calculus.**  If `∂ᵢq = Φᵢ` weakly
(against all smooth compactly supported test functions) with `q` and `Φ` continuous, then the
increment of `q` along every coordinate line is the integral of the corresponding component of
`Φ`. -/
theorem fTC_of_weakGradient (q : EuclideanSpace ℝ (Fin 3) → ℝ)
    (Φ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hq : Continuous q) (hΦ : Continuous Φ)
    (hgrad : ∀ i : Fin 3, ∀ k : EuclideanSpace ℝ (Fin 3) → ℝ,
      (∀ n : ℕ, ContDiff ℝ n k) → HasCompactSupport k →
      ∫ x, k x * Φ x i = -∫ x, q x * (fderiv ℝ k x) (FiniteTimeSingularity.e i)) :
    ∀ x : EuclideanSpace ℝ (Fin 3), ∀ t : ℝ, ∀ i : Fin 3,
      q (x + t • FiniteTimeSingularity.e i) - q x
        = ∫ s in (0 : ℝ)..t, Φ (x + s • FiniteTimeSingularity.e i) i := by
  intro x t i
  have hGcont : Continuous
      (fun y : EuclideanSpace ℝ (Fin 3) =>
        ∫ s in (0 : ℝ)..t, Φ (y + s • FiniteTimeSingularity.e i) i) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i).comp
      (hΦ.comp (continuous_fst.add (continuous_snd.smul continuous_const))))
  -- the pairing identity
  have hpair : ∀ (g : EuclideanSpace ℝ (Fin 3) → ℝ),
      (∀ n : ℕ, ContDiff ℝ n g) → HasCompactSupport g →
      ∫ y, g y * (q (y + t • FiniteTimeSingularity.e i) - q y
        - ∫ s in (0 : ℝ)..t, Φ (y + s • FiniteTimeSingularity.e i) i) = 0 := by
    intro g hg hgc
    have hgd : Differentiable ℝ g := (hg 1).differentiable (by norm_num)
    -- ### translation invariance
    have htrans : ∫ y, g y * q (y + t • FiniteTimeSingularity.e i)
        = ∫ y, g (y - t • FiniteTimeSingularity.e i) * q y := by
      have h := MeasureTheory.integral_sub_right_eq_self (μ := volume)
        (fun y : EuclideanSpace ℝ (Fin 3) => g y * q (y + t • FiniteTimeSingularity.e i))
        (t • FiniteTimeSingularity.e i)
      rw [← h]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only [sub_add_cancel]
    -- ### the one dimensional fundamental theorem of calculus along the line
    have hftc : ∀ y : EuclideanSpace ℝ (Fin 3), g y - g (y - t • FiniteTimeSingularity.e i)
        = ∫ s in (0 : ℝ)..t,
            (fderiv ℝ g (y - s • FiniteTimeSingularity.e i)) (FiniteTimeSingularity.e i) := by
      intro y
      have hderiv : ∀ s : ℝ,
          HasDerivAt (fun s : ℝ => g (y - s • FiniteTimeSingularity.e i))
            (-((fderiv ℝ g (y - s • FiniteTimeSingularity.e i))
              (FiniteTimeSingularity.e i))) s := by
        intro s
        have h1 : HasDerivAt (fun s : ℝ => y - s • FiniteTimeSingularity.e i)
            (-(FiniteTimeSingularity.e i)) s := by
          simpa using ((hasDerivAt_id s).smul_const (FiniteTimeSingularity.e i)).const_sub y
        have h2 : HasFDerivAt g (fderiv ℝ g (y - s • FiniteTimeSingularity.e i))
            (y - s • FiniteTimeSingularity.e i) := (hgd _).hasFDerivAt
        simpa [Function.comp_def] using h2.comp_hasDerivAt s h1
      have hint : IntervalIntegrable
          (fun s : ℝ => -((fderiv ℝ g (y - s • FiniteTimeSingularity.e i))
            (FiniteTimeSingularity.e i))) volume (0 : ℝ) t := by
        refine Continuous.intervalIntegrable ?_ 0 t
        exact (((hg 1).continuous_fderiv_apply (by norm_num)).comp
          ((continuous_const.sub (continuous_id.smul continuous_const)).prodMk
            continuous_const)).neg
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x) hint
      rw [intervalIntegral.integral_neg] at h
      simp only [zero_smul, sub_zero] at h
      linarith [h]
    -- ### the weak identity for the translated test function, for each `s`
    have hweak : ∀ s : ℝ,
        ∫ y, (fderiv ℝ g (y - s • FiniteTimeSingularity.e i)) (FiniteTimeSingularity.e i) * q y
          = -∫ y, g (y - s • FiniteTimeSingularity.e i) * Φ y i := by
      intro s
      have hwk := hgrad i (fun y : EuclideanSpace ℝ (Fin 3) =>
          g (y - s • FiniteTimeSingularity.e i))
        (fun n => (hg n).comp (contDiff_id.sub contDiff_const))
        (hasCompactSupport_sub_smul g hgc i s)
      have hfd : ∀ y : EuclideanSpace ℝ (Fin 3),
          (fderiv ℝ (fun w : EuclideanSpace ℝ (Fin 3) =>
            g (w - s • FiniteTimeSingularity.e i)) y) (FiniteTimeSingularity.e i)
            = (fderiv ℝ g (y - s • FiniteTimeSingularity.e i)) (FiniteTimeSingularity.e i) :=
        fun y => by rw [hasFDerivAt_sub_smul_comp g hgd i s y]
      have hcongr : (∫ x, q x * (fderiv ℝ (fun w : EuclideanSpace ℝ (Fin 3) =>
              g (w - s • FiniteTimeSingularity.e i)) x) (FiniteTimeSingularity.e i))
            = ∫ x, q x * (fderiv ℝ g (x - s • FiniteTimeSingularity.e i))
                (FiniteTimeSingularity.e i) := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        show q x * (fderiv ℝ (fun w : EuclideanSpace ℝ (Fin 3) =>
            g (w - s • FiniteTimeSingularity.e i)) x) (FiniteTimeSingularity.e i)
          = q x * (fderiv ℝ g (x - s • FiniteTimeSingularity.e i)) (FiniteTimeSingularity.e i)
        rw [hfd x]
      rw [hcongr] at hwk
      rw [show (∫ x, q x * (fderiv ℝ g (x - s • FiniteTimeSingularity.e i))
              (FiniteTimeSingularity.e i))
            = ∫ x, (fderiv ℝ g (x - s • FiniteTimeSingularity.e i))
                (FiniteTimeSingularity.e i) * q x
          from integral_congr_ae (Eventually.of_forall fun x => by ring)] at hwk
      simpa using (congrArg Neg.neg hwk).symm
    -- ### the translated derivative has compact support
    have hcs' : HasCompactSupport
        (fun z : EuclideanSpace ℝ (Fin 3) =>
          (fderiv ℝ g z) (FiniteTimeSingularity.e i)) := by
      refine HasCompactSupport.intro (K := tsupport g) hgc ?_
      intro z hz
      have hopen : IsOpen (tsupport g)ᶜ := (isClosed_tsupport g).isOpen_compl
      have h0 : g =ᶠ[𝓝 z] 0 := by
        filter_upwards [hopen.mem_nhds hz] with w hw
        exact image_eq_zero_of_notMem_tsupport hw
      rw [h0.fderiv_eq]
      simp
    -- ### integrability for the first Fubini
    have hInt1 : Integrable (Function.uncurry fun (s : ℝ) (y : EuclideanSpace ℝ (Fin 3)) =>
        (fderiv ℝ g (y - s • FiniteTimeSingularity.e i)) (FiniteTimeSingularity.e i) * q y)
        ((volume.restrict (Set.uIoc (0 : ℝ) t)).prod volume) := by
      refine integrable_uncurry_prod_restrict_aux (K := tsupport
        (fun z : EuclideanSpace ℝ (Fin 3) => (fderiv ℝ g z) (FiniteTimeSingularity.e i))
        + Set.image (fun σ : ℝ => σ • FiniteTimeSingularity.e i) (Set.uIcc (0 : ℝ) t)) ?_ ?_ ?_
      · exact IsCompact.add hcs'
          (isCompact_uIcc.image ((continuous_id : Continuous fun s : ℝ => s).smul
            (continuous_const : Continuous fun _ : ℝ => FiniteTimeSingularity.e i)))
      · refine Continuous.mul ?_ (hq.comp continuous_snd)
        have h1 : Continuous fun p : ℝ × EuclideanSpace ℝ (Fin 3) =>
            p.2 - p.1 • FiniteTimeSingularity.e i :=
          continuous_snd.sub (continuous_fst.smul continuous_const)
        exact (((hg 1).continuous_fderiv_apply (by norm_num)).comp
          (h1.prodMk continuous_const))
      · intro σ hσ y hy
        have hmem : y - σ • FiniteTimeSingularity.e i ∉
            tsupport (fun z : EuclideanSpace ℝ (Fin 3) =>
              (fderiv ℝ g z) (FiniteTimeSingularity.e i)) := by
          intro hcon
          exact hy (by
            rw [Set.mem_add]
            exact ⟨y - σ • FiniteTimeSingularity.e i, hcon, σ • FiniteTimeSingularity.e i,
              Set.mem_image_of_mem _ (Set.uIoc_subset_uIcc hσ), by abel⟩)
        rw [image_eq_zero_of_notMem_tsupport hmem, zero_mul]
    -- ### the first Fubini
    have hFub1 : ∫ y, (∫ s in (0 : ℝ)..t, (fderiv ℝ g (y - s • FiniteTimeSingularity.e i))
            (FiniteTimeSingularity.e i)) * q y
        = ∫ s in (0 : ℝ)..t, ∫ y, (fderiv ℝ g (y - s • FiniteTimeSingularity.e i))
            (FiniteTimeSingularity.e i) * q y := by
      rw [show (fun y : EuclideanSpace ℝ (Fin 3) =>
              (∫ s in (0 : ℝ)..t, (fderiv ℝ g (y - s • FiniteTimeSingularity.e i))
                (FiniteTimeSingularity.e i)) * q y)
            = fun y => ∫ s in (0 : ℝ)..t, (fderiv ℝ g (y - s • FiniteTimeSingularity.e i))
                (FiniteTimeSingularity.e i) * q y
          from funext fun y => (intervalIntegral.integral_mul_const (q y) _).symm]
      exact (MeasureTheory.intervalIntegral_integral_swap hInt1).symm
    -- ### integrability for the second Fubini
    have hInt2 : Integrable (Function.uncurry fun (s : ℝ) (u : EuclideanSpace ℝ (Fin 3)) =>
        g u * Φ (u + s • FiniteTimeSingularity.e i) i)
        ((volume.restrict (Set.uIoc (0 : ℝ) t)).prod volume) := by
      refine integrable_uncurry_prod_restrict_aux (K := tsupport g) ?_ ?_ ?_
      · exact hgc
      · exact ((hg 0).continuous.comp continuous_snd).mul
          ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i).comp
            (hΦ.comp (continuous_snd.add (continuous_fst.smul continuous_const))))
      · intro σ _ u hu
        rw [image_eq_zero_of_notMem_tsupport hu, zero_mul]
    -- ### the second Fubini
    have hFub2 : ∫ s in (0 : ℝ)..t, ∫ u, g u * Φ (u + s • FiniteTimeSingularity.e i) i
        = ∫ u, ∫ s in (0 : ℝ)..t, g u * Φ (u + s • FiniteTimeSingularity.e i) i :=
      MeasureTheory.intervalIntegral_integral_swap hInt2
    -- ### the change of variables in the `s`-integral
    have hshift : ∀ s : ℝ, ∫ y, g (y - s • FiniteTimeSingularity.e i) * Φ y i
        = ∫ u, g u * Φ (u + s • FiniteTimeSingularity.e i) i := by
      intro s
      have h := MeasureTheory.integral_sub_right_eq_self (μ := volume)
        (fun u : EuclideanSpace ℝ (Fin 3) => g u * Φ (u + s • FiniteTimeSingularity.e i) i)
        (s • FiniteTimeSingularity.e i)
      rw [← h]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only [sub_add_cancel]
    -- ### integrability of the three pieces of the `y`-integral
    have hi1 : Integrable (fun y : EuclideanSpace ℝ (Fin 3) =>
        g y * q (y + t • FiniteTimeSingularity.e i)) :=
      Continuous.integrable_of_hasCompactSupport
        ((hg 0).continuous.mul (hq.comp (continuous_id.add continuous_const)))
        (HasCompactSupport.intro hgc fun y hy => by
          rw [image_eq_zero_of_notMem_tsupport hy, zero_mul])
    have hi2 : Integrable (fun y : EuclideanSpace ℝ (Fin 3) => g y * q y) :=
      Continuous.integrable_of_hasCompactSupport ((hg 0).continuous.mul hq)
        (HasCompactSupport.intro hgc fun y hy => by
          rw [image_eq_zero_of_notMem_tsupport hy, zero_mul])
    have hi3 : Integrable (fun y : EuclideanSpace ℝ (Fin 3) =>
        g (y - t • FiniteTimeSingularity.e i) * q y) :=
      Continuous.integrable_of_hasCompactSupport
        (((hg 0).continuous.comp (continuous_id.sub continuous_const)).mul hq)
        (HasCompactSupport.intro (hasCompactSupport_sub_smul g hgc i t) fun y hy => by
          rw [image_eq_zero_of_notMem_tsupport hy, zero_mul])
    -- ### the assembly
    have hL : ∫ y, g y * (q (y + t • FiniteTimeSingularity.e i) - q y)
        = ∫ y, g y * (∫ s in (0 : ℝ)..t, Φ (y + s • FiniteTimeSingularity.e i) i) := by
      calc ∫ y, g y * (q (y + t • FiniteTimeSingularity.e i) - q y)
          = (∫ y, g (y - t • FiniteTimeSingularity.e i) * q y) - (∫ y, g y * q y) := by
            rw [show (fun y : EuclideanSpace ℝ (Fin 3) =>
                  g y * (q (y + t • FiniteTimeSingularity.e i) - q y))
                = fun y => g y * q (y + t • FiniteTimeSingularity.e i) - g y * q y
              from funext fun y => by ring]
            rw [integral_sub hi1 hi2, htrans]
        _ = ∫ y, (g (y - t • FiniteTimeSingularity.e i) - g y) * q y := by
            have h1 : (∫ y, (g (y - t • FiniteTimeSingularity.e i) - g y) * q y)
                = (∫ y, g (y - t • FiniteTimeSingularity.e i) * q y) - (∫ y, g y * q y) := by
              rw [show (fun y : EuclideanSpace ℝ (Fin 3) =>
                    (g (y - t • FiniteTimeSingularity.e i) - g y) * q y)
                  = fun y => g (y - t • FiniteTimeSingularity.e i) * q y - g y * q y
                from funext fun y => by ring]
              exact integral_sub hi3 hi2
            exact h1.symm
        _ = ∫ y, (-(∫ s in (0 : ℝ)..t, (fderiv ℝ g (y - s • FiniteTimeSingularity.e i))
                (FiniteTimeSingularity.e i))) * q y := by
            refine integral_congr_ae (Eventually.of_forall fun y => ?_)
            simp only [← hftc y]
            ring
        _ = -(∫ y, (∫ s in (0 : ℝ)..t, (fderiv ℝ g (y - s • FiniteTimeSingularity.e i))
                (FiniteTimeSingularity.e i)) * q y) := by
            rw [show (fun y : EuclideanSpace ℝ (Fin 3) =>
                  (-(∫ s in (0 : ℝ)..t, (fderiv ℝ g (y - s • FiniteTimeSingularity.e i))
                    (FiniteTimeSingularity.e i))) * q y)
                = fun y => -((∫ s in (0 : ℝ)..t, (fderiv ℝ g (y - s • FiniteTimeSingularity.e i))
                    (FiniteTimeSingularity.e i)) * q y)
              from funext fun y => by ring]
            rw [integral_neg]
        _ = -(∫ s in (0 : ℝ)..t, ∫ y, (fderiv ℝ g (y - s • FiniteTimeSingularity.e i))
                (FiniteTimeSingularity.e i) * q y) := by rw [hFub1]
        _ = -(∫ s in (0 : ℝ)..t,
                (-∫ y, g (y - s • FiniteTimeSingularity.e i) * Φ y i)) := by
            rw [show (fun s : ℝ => ∫ y, (fderiv ℝ g (y - s • FiniteTimeSingularity.e i))
                    (FiniteTimeSingularity.e i) * q y)
                = fun s => -∫ y, g (y - s • FiniteTimeSingularity.e i) * Φ y i
              from funext hweak]
        _ = ∫ s in (0 : ℝ)..t, ∫ y, g (y - s • FiniteTimeSingularity.e i) * Φ y i := by
            rw [intervalIntegral.integral_neg, neg_neg]
        _ = ∫ s in (0 : ℝ)..t, ∫ u, g u * Φ (u + s • FiniteTimeSingularity.e i) i := by
            rw [show (fun s : ℝ => ∫ y, g (y - s • FiniteTimeSingularity.e i) * Φ y i)
                = fun s => ∫ u, g u * Φ (u + s • FiniteTimeSingularity.e i) i
              from funext hshift]
        _ = ∫ u, ∫ s in (0 : ℝ)..t, g u * Φ (u + s • FiniteTimeSingularity.e i) i := hFub2
        _ = ∫ u, g u * (∫ s in (0 : ℝ)..t, Φ (u + s • FiniteTimeSingularity.e i) i) := by
            refine integral_congr_ae (Eventually.of_forall fun u => ?_)
            exact intervalIntegral.integral_const_mul (g u) _
    -- ### conclude
    have hA : Integrable (fun y : EuclideanSpace ℝ (Fin 3) =>
        g y * (q (y + t • FiniteTimeSingularity.e i) - q y)) := by
      refine Continuous.integrable_of_hasCompactSupport
        ((hg 0).continuous.mul ((hq.comp (continuous_id.add continuous_const)).sub hq)) ?_
      exact HasCompactSupport.intro hgc fun y hy => by
        rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
    have hB : Integrable (fun y : EuclideanSpace ℝ (Fin 3) =>
        g y * (∫ s in (0 : ℝ)..t, Φ (y + s • FiniteTimeSingularity.e i) i)) := by
      refine Continuous.integrable_of_hasCompactSupport
        ((hg 0).continuous.mul hGcont) ?_
      exact HasCompactSupport.intro hgc fun y hy => by
        rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
    rw [show (fun y : EuclideanSpace ℝ (Fin 3) => g y * (q (y + t • FiniteTimeSingularity.e i)
            - q y - ∫ s in (0 : ℝ)..t, Φ (y + s • FiniteTimeSingularity.e i) i))
        = fun y => g y * (q (y + t • FiniteTimeSingularity.e i) - q y)
            - g y * (∫ s in (0 : ℝ)..t, Φ (y + s • FiniteTimeSingularity.e i) i)
      from funext fun y => by ring]
    rw [integral_sub hA hB, hL]
    exact sub_self _
  -- the pointwise conclusion, by du Bois-Reymond + continuity
  have hFcont : Continuous (fun y : EuclideanSpace ℝ (Fin 3) =>
      q (y + t • FiniteTimeSingularity.e i) - q y
        - ∫ s in (0 : ℝ)..t, Φ (y + s • FiniteTimeSingularity.e i) i) :=
    ((hq.comp (continuous_id.add continuous_const)).sub hq).sub hGcont
  have hae : (fun y : EuclideanSpace ℝ (Fin 3) =>
      q (y + t • FiniteTimeSingularity.e i) - q y
        - ∫ s in (0 : ℝ)..t, Φ (y + s • FiniteTimeSingularity.e i) i) =ᵐ[volume] 0 := by
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hFcont.locallyIntegrable ?_
    intro g hg hgc
    simpa [smul_eq_mul] using hpair g (fun n => hg.of_le (by simp)) hgc
  have heq : (fun y : EuclideanSpace ℝ (Fin 3) =>
      q (y + t • FiniteTimeSingularity.e i) - q y
        - ∫ s in (0 : ℝ)..t, Φ (y + s • FiniteTimeSingularity.e i) i) = 0 :=
    Measure.eq_of_ae_eq hae hFcont continuous_const
  have hx : q (x + t • FiniteTimeSingularity.e i) - q x
      - (∫ s in (0 : ℝ)..t, Φ (x + s • FiniteTimeSingularity.e i) i) = 0 := congrFun heq x
  linarith [hx]

/-- **A continuous weak gradient is a strong gradient.**  If `∂ᵢq = Φᵢ` weakly against all smooth
compactly supported test functions, with `q` and `Φ` continuous, then `q` is differentiable
everywhere with gradient `Φ`. -/
theorem hasFDerivAt_of_weakGrad (q : EuclideanSpace ℝ (Fin 3) → ℝ)
    (Φ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hq : Continuous q) (hΦ : Continuous Φ)
    (hgrad : ∀ i : Fin 3, ∀ k : EuclideanSpace ℝ (Fin 3) → ℝ, (∀ n : ℕ, ContDiff ℝ n k) →
      HasCompactSupport k →
      ∫ x, k x * Φ x i = -∫ x, q x * (fderiv ℝ k x) (FiniteTimeSingularity.e i)) :
    ∀ x, HasFDerivAt q (innerSL ℝ (Φ x)) x :=
  Work.FTS.PressureOn.Weyl.hasFDerivAt_of_fTC q Φ hΦ
    (fTC_of_weakGradient q Φ hq hΦ hgrad)

end Work.FTS.PressureOn.Auxiliary
end
end
-- ===== merged: Submission.Work.FTS.PressureOn.Auxiliary.laplaceTraceVec_identity =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity
open scoped Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FTS.PressureOn.Auxiliary

/-! ## Preliminaries: the standard basis and the gradient -/

/-- Dotting with the standard basis vector `e j` gives the `j`-th coordinate. -/
private lemma inner_e_left (j : Fin 3) (v : R3) : inner ℝ (e j) v = v j := by
  simp [FiniteTimeSingularity.e, PiLp.inner_apply]

/-- The version of `inner_e_left` with the arguments swapped. -/
private lemma inner_e_right (j : Fin 3) (v : R3) : inner ℝ v (e j) = v j := by
  rw [real_inner_comm, inner_e_left]

/-- `∇f x` is the Riesz representative of `fderiv ℝ f x`. -/
private lemma inner_gradient (f : R3 → ℝ) (x y : R3) :
    inner ℝ (gradient f x) y = fderiv ℝ f x y := by
  rw [← InnerProductSpace.toDual_apply_apply, toDual_gradient]

/-- The `j`-th component of the gradient is the derivative in the direction `e j`. -/
private lemma gradient_apply_e (f : R3 → ℝ) (x : R3) (j : Fin 3) :
    (gradient f x) j = fderiv ℝ f x (e j) := by
  rw [← inner_e_right j (gradient f x), inner_gradient]

/-! ## Coordinates of derivatives and of the curl -/

/-- **The coordinate of a derivative is the derivative of the coordinate**: for a vector field `g`
differentiable at `x`, `(Dg(x) v) i = D(y ↦ g(y)_i)(x) v`. -/
private lemma fderiv_apply_ofLp (g : R3 → R3) {x : R3} (hg : DifferentiableAt ℝ g x)
    (i : Fin 3) (v : R3) :
    (fderiv ℝ g x v) i = fderiv ℝ (fun y => (g y) i) x v := by
  have h := (hasFDerivWithinAt_piLp (𝕜 := ℝ) (p := (2 : ENNReal)) (E := fun _ : Fin 3 => ℝ)
      (f := g) (f' := fderiv ℝ g x) (t := Set.univ) (y := x)).mp
      hg.hasFDerivAt.hasFDerivWithinAt i
  rw [hasFDerivWithinAt_univ] at h
  rw [h.fderiv]
  simp [PiLp.proj_apply, ContinuousLinearMap.comp_apply]

/-- Evaluation commutes with finite sums of continuous linear maps. -/
private lemma clm_sum_apply {ι : Type*} [Fintype ι] (L : ι → R3 →L[ℝ] ℝ) (v : R3) :
    (∑ i, L i) v = ∑ i, L i v := by
  rw [← ContinuousLinearMap.apply_apply v, map_sum]
  exact Finset.sum_congr rfl fun i _ => ContinuousLinearMap.apply_apply v (L i)

/-- The derivative of a finite sum of scalar functions, evaluated on a vector. -/
private lemma fderiv_fun_sum_apply {A : Fin 3 → R3 → ℝ} {x v : R3}
    (h : ∀ i, DifferentiableAt ℝ (A i) x) :
    fderiv ℝ (fun y : R3 => ∑ i : Fin 3, A i y) x v = ∑ i : Fin 3, fderiv ℝ (A i) x v := by
  have hsum : HasFDerivAt (fun y : R3 => ∑ i : Fin 3, A i y)
      (∑ i : Fin 3, fderiv ℝ (A i) x) x :=
    HasFDerivAt.fun_sum (u := Finset.univ) fun i _ => (h i).hasFDerivAt
  rw [hsum.fderiv, clm_sum_apply]

/-- **The curl in coordinates**: `(∇ × V) j = ∑ i, (e i × ∂ᵢV) j`. -/
private lemma vorticity_apply (V : R3 → R3) (x : R3) (j : Fin 3) :
    (vorticity V x) j = ∑ i : Fin 3, (e i ⨯₃ (fderiv ℝ V x (e i))) j := by
  simp only [FiniteTimeSingularity.vorticity, WithLp.ofLp_toLp, Finset.sum_apply]

/-! ## Differentiability of the pieces -/

private lemma contDiff_one_fderiv (W : R3 → R3) (hW : ∀ n : ℕ, ContDiff ℝ n W) :
    ContDiff ℝ 1 (fderiv ℝ W) :=
  (hW 2).fderiv_right (m := 1) (by norm_num)

private lemma contDiff_one_fderiv_apply (W : R3 → R3) (hW : ∀ n : ℕ, ContDiff ℝ n W) (i : Fin 3) :
    ContDiff ℝ 1 (fun y : R3 => fderiv ℝ W y (e i)) := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ W) := contDiff_one_fderiv W hW
  simpa [Function.comp_def] using
    (ContinuousLinearMap.apply ℝ R3 (e i)).contDiff.comp h1

private lemma differentiableAt_fderiv_apply (W : R3 → R3) (hW : ∀ n : ℕ, ContDiff ℝ n W)
    (x : R3) (i : Fin 3) : DifferentiableAt ℝ (fun y : R3 => fderiv ℝ W y (e i)) x :=
  (contDiff_one_fderiv_apply W hW i).differentiable one_ne_zero x

/-- The same, for a single coordinate of the derivative. -/
private lemma differentiableAt_fderiv_apply_coord (W : R3 → R3) (hW : ∀ n : ℕ, ContDiff ℝ n W)
    (x : R3) (i j : Fin 3) : DifferentiableAt ℝ (fun y : R3 => (fderiv ℝ W y (e i)) j) x :=
  ((differentiableAt_piLp (𝕜 := ℝ) (p := (2 : ENNReal)) (E := fun _ : Fin 3 => ℝ)
    (f := fun y : R3 => fderiv ℝ W y (e i)) (y := x)).mp
      (differentiableAt_fderiv_apply W hW x i)) j

/-- The composed form of `crossVec` with a constant first argument. -/
private lemma crossVec_comp' (c : R3) (h : R3 → R3) :
    (fun y : R3 => crossVec c (h y))
      = (fun p : R3 × R3 => crossVec p.1 p.2) ∘ (fun y : R3 => ((fun _ : R3 => c) y, h y)) :=
  rfl

/-- Differentiability of a cross product with a constant vector. -/
private lemma hasFDerivAt_crossVec_const (c : R3) (h : R3 → R3) {x : R3}
    (hh : HasFDerivAt h (fderiv ℝ h x) x) :
    HasFDerivAt (fun y : R3 => crossVec c (h y))
      ((vorticityCross_isBoundedBilinearMap.deriv (c, h x)).comp
        ((0 : R3 →L[ℝ] R3).prod (fderiv ℝ h x))) x := by
  rw [crossVec_comp' c h]
  exact (vorticityCross_isBoundedBilinearMap.hasFDerivAt (c, h x)).comp x
    ((hasFDerivAt_const c x).prodMk hh)

/-- **Derivative of a cross product with a constant vector.**  The `l`-th component of
`y ↦ c × h y` has derivative `(c × (Dh(x) v))_l` in the direction `v`. -/
private lemma fderiv_cross_const (c : R3) (h : R3 → R3) {x : R3}
    (hh : HasFDerivAt h (fderiv ℝ h x) x) (v : R3) (l : Fin 3) :
    fderiv ℝ (fun y : R3 => (crossProduct (WithLp.ofLp c) (WithLp.ofLp (h y))) l) x v
      = (crossProduct (WithLp.ofLp c) (WithLp.ofLp (fderiv ℝ h x v))) l := by
  have hcomp := hasFDerivAt_crossVec_const c h hh
  have h1 : fderiv ℝ (fun y : R3 => crossVec c (h y)) x v = crossVec c (fderiv ℝ h x v) := by
    rw [hcomp.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      IsBoundedBilinearMap.deriv_apply]
    simp
  have h2 := fderiv_apply_ofLp (fun y : R3 => crossVec c (h y)) hcomp.differentiableAt l v
  have h3 : (fun y : R3 => (crossProduct (WithLp.ofLp c) (WithLp.ofLp (h y))) l)
      = fun y : R3 => (crossVec c (h y)) l := by
    funext y
    simp [crossVec]
  rw [h3, ← h2, h1]
  simp [crossVec]

/-- Differentiability of the `l`-th component of a cross product with a constant vector. -/
private lemma differentiableAt_cross_apply (c : R3) (h : R3 → R3) {x : R3}
    (hh : HasFDerivAt h (fderiv ℝ h x) x) (l : Fin 3) :
    DifferentiableAt ℝ (fun y : R3 => (crossProduct (WithLp.ofLp c) (WithLp.ofLp (h y))) l) x := by
  have hcv : (fun y : R3 => (crossProduct (WithLp.ofLp c) (WithLp.ofLp (h y))) l)
      = fun y : R3 => (crossVec c (h y)) l := by
    funext y
    simp [crossVec]
  rw [hcv]
  have hdiff : DifferentiableAt ℝ (fun y : R3 => crossVec c (h y)) x :=
    (hasFDerivAt_crossVec_const c h hh).differentiableAt
  exact ((differentiableAt_piLp (𝕜 := ℝ) (p := (2 : ENNReal)) (E := fun _ : Fin 3 => ℝ)
    (f := fun y : R3 => crossVec c (h y)) (y := x)).mp hdiff) l

/-- The curl as a sum of cross products with the basis vectors. -/
private lemma vorticity_eq_sum_crossVec (V : R3 → R3) :
    vorticity V = fun y : R3 => ∑ i : Fin 3, crossVec (e i) (fderiv ℝ V y (e i)) := by
  funext y
  rw [WithLp.ext_iff]
  simp only [WithLp.ofLp_sum, FiniteTimeSingularity.vorticity, WithLp.ofLp_toLp, crossVec]

/-- The curl of a smooth vector field is differentiable. -/
private lemma differentiableAt_vorticity (V : R3 → R3) (hV : ∀ n : ℕ, ContDiff ℝ n V) (x : R3) :
    DifferentiableAt ℝ (vorticity V) x := by
  rw [vorticity_eq_sum_crossVec V]
  refine DifferentiableAt.fun_sum fun i _ => ?_
  exact (hasFDerivAt_crossVec_const (e i) (fun y : R3 => fderiv ℝ V y (e i))
    (differentiableAt_fderiv_apply V hV x i).hasFDerivAt).differentiableAt

/-! ## The identity -/

theorem laplaceTraceVec_identity (W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hW : ∀ n : ℕ, ContDiff ℝ n W) (x : EuclideanSpace ℝ (Fin 3)) :
    Work.FTS.PressureOn.laplaceTraceVec W x
      = gradient (FiniteTimeSingularity.div W) x
        - FiniteTimeSingularity.vorticity (FiniteTimeSingularity.vorticity W) x := by
  set S : Fin 3 → Fin 3 → R3 := fun i k => fderiv ℝ (fun w => fderiv ℝ W w (e i)) x (e k) with hS
  -- the second derivatives are symmetric
  have hsymm : ∀ i k l : Fin 3, (S i k) l = (S k i) l := by
    intro i k l
    rw [hS]
    exact congrArg (fun v : R3 => v l) (fderiv_fderiv_comm W hW x (e i) (e k))
  -- the Laplacian in coordinates
  have hLHS : ∀ j : Fin 3, (laplaceTraceVec W x) j = ∑ i : Fin 3, (S i i) j := by
    intro j
    rw [hS]
    simp only [laplaceTraceVec, WithLp.ofLp_sum, Finset.sum_apply]
  -- the gradient of the divergence in coordinates
  have hgrad : ∀ j : Fin 3, (gradient (div W) x) j = ∑ i : Fin 3, (S i j) i := by
    intro j
    have hdiv : div W = fun y : R3 => ∑ i : Fin 3, (fderiv ℝ W y (e i)) i := by
      funext y
      exact vorticityCross_div_eq_sum_diag W y
    rw [gradient_apply_e, hdiv, fderiv_fun_sum_apply (fun i =>
      differentiableAt_fderiv_apply_coord W hW x i i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [← fderiv_apply_ofLp (fun y : R3 => fderiv ℝ W y (e i))
      (differentiableAt_fderiv_apply W hW x i) i (e j)]
  -- the curl of the curl in coordinates
  have hcurl : ∀ j : Fin 3, (vorticity (vorticity W) x) j
      = ∑ k : Fin 3, (e k ⨯₃ (fun l : Fin 3 => ∑ i : Fin 3, (e i ⨯₃ (S i k)) l)) j := by
    intro j
    rw [vorticity_apply]
    apply Finset.sum_congr rfl
    intro k _
    have hfun : fderiv ℝ (vorticity W) x (e k)
        = fun l : Fin 3 => ∑ i : Fin 3, (e i ⨯₃ (S i k)) l := by
      funext l
      rw [fderiv_apply_ofLp (vorticity W) (differentiableAt_vorticity W hW x) l (e k)]
      have hv : (fun y : R3 => (vorticity W y) l)
          = fun y : R3 => ∑ i : Fin 3, (e i ⨯₃ (fderiv ℝ W y (e i))) l := by
        funext y
        rw [vorticity_apply]
      rw [hv, fderiv_fun_sum_apply (fun i => differentiableAt_cross_apply (e i)
        (fun y : R3 => fderiv ℝ W y (e i)) (differentiableAt_fderiv_apply W hW x i).hasFDerivAt l)]
      apply Finset.sum_congr rfl
      intro i _
      rw [fderiv_cross_const (e i) (fun y : R3 => fderiv ℝ W y (e i))
        (differentiableAt_fderiv_apply W hW x i).hasFDerivAt (e k) l]
    rw [hfun]
  -- the components agree
  have hcomp : ∀ j : Fin 3, (laplaceTraceVec W x) j
      = (gradient (div W) x) j - (vorticity (vorticity W) x) j := by
    intro j
    rw [hLHS j, hgrad j, hcurl j]
    exact curlCurl_apply S hsymm j
  -- conclude the vector identity
  rw [WithLp.ext_iff]
  funext j
  rw [WithLp.ofLp_sub, Pi.sub_apply, ← hcomp j]

end Work.FTS.PressureOn.Auxiliary
end
-- ===== merged: Submission.Work.FTS.PressureOn.Connect.continuous_timeDeriv_slice =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Set Filter
open scoped Topology

namespace Work.FTS.PressureOn.Connect

/-- **Continuity in space of the time derivative of a joint `C^{1,α}` strip field.**

If `v.uncurry` is of class `C^{1,α}` on the closed strip `ℝ³ × [0,S]`, then at every *interior*
time `t ∈ (0,S)` the time derivative `x ↦ ∂ₜ v(x,t)` is a continuous function of `x`.

The point of the lemma is that the strip hypothesis controls the *joint* derivative of
`v.uncurry`: on the open sub-strip `ℝ³ × (t-ε, t+ε)` (which is a neighbourhood of every point
`(x,t)`, because `t` is interior to `[0,S]`) the map `(x,τ) ↦ fderiv ℝ v.uncurry (x,τ)` is
continuous (`ContDiffOn.continuousOn_fderiv_of_isOpen`), and evaluating it at the time direction
`(0,1)` gives exactly `∂ₜ v(x,τ)` for points of that open strip
(`hasDerivAt_slice_of_hasFDerivAt_uncurry`). -/
theorem continuous_timeDeriv_slice {α : NNReal} {v : Work.FTS.PressureOn.R3 → ℝ → Work.FTS.PressureOn.R3}
    {S t : ℝ} (ht : t ∈ Set.Ioo 0 S)
    (hstrip : IsContDiffHolderOn ℝ α v.uncurry (Set.univ ×ˢ Set.Icc 0 S)) :
    Continuous (fun x : Work.FTS.PressureOn.R3 => FiniteTimeSingularity.timeDeriv v x t) := by
  obtain ⟨hcd, -, -⟩ := hstrip
  have ht0 : (0 : ℝ) < t := ht.1
  have htS : t < S := ht.2
  -- An open time-interval `J` around `t`, entirely inside `[0,S]`.
  set J : Set ℝ := Set.Ioo (t - min t (S - t) / 2) (t + min t (S - t) / 2) with hJ
  have hmin_pos : 0 < min t (S - t) := lt_min ht0 (sub_pos.mpr htS)
  have hJsub : J ⊆ Set.Icc (0 : ℝ) S := by
    intro s hs
    have h1 : min t (S - t) ≤ t := min_le_left _ _
    have h2 : min t (S - t) ≤ S - t := min_le_right _ _
    exact ⟨by linarith [hs.1, h1], by linarith [hs.2, h2]⟩
  have hJmem : J ∈ 𝓝 t := Ioo_mem_nhds (by linarith [hmin_pos]) (by linarith [hmin_pos])
  -- The open sub-strip and its derivative field.
  set str : Set (Work.FTS.PressureOn.R3 × ℝ) := Set.univ ×ˢ J with hstr
  have hstr_open : IsOpen str := isOpen_univ.prod isOpen_Ioo
  have hcd' : ContDiffOn ℝ 1 v.uncurry str :=
    hcd.mono (Set.prod_mono (subset_refl _) hJsub)
  have hcont : ContinuousOn (fderiv ℝ v.uncurry) str :=
    hcd'.continuousOn_fderiv_of_isOpen hstr_open le_rfl
  have hcont2 : ContinuousOn (fun p : Work.FTS.PressureOn.R3 × ℝ =>
      fderiv ℝ v.uncurry p ((0 : Work.FTS.PressureOn.R3), (1 : ℝ))) str :=
    hcont.clm_apply continuousOn_const
  have hstr_mem : ∀ x : Work.FTS.PressureOn.R3, str ∈ 𝓝 (x, t) := by
    intro x
    rw [hstr, nhds_prod_eq]
    exact prod_mem_prod univ_mem hJmem
  -- Continuity of `x ↦ fderiv ℝ v.uncurry (x,t) (0,1)`: restrict the continuous derivative
  -- field to the slice `τ = t`.
  have hmain : Continuous (fun x : Work.FTS.PressureOn.R3 =>
      fderiv ℝ v.uncurry (x, t) ((0 : Work.FTS.PressureOn.R3), (1 : ℝ))) := by
    rw [continuous_iff_continuousAt]
    intro x0
    have hg : ContinuousAt
        (fun p : Work.FTS.PressureOn.R3 × ℝ =>
          fderiv ℝ v.uncurry p ((0 : Work.FTS.PressureOn.R3), (1 : ℝ))) (x0, t) :=
      hcont2.continuousAt (hstr_mem x0)
    have hpair : ContinuousAt (fun x : Work.FTS.PressureOn.R3 => (x, t)) x0 := by fun_prop
    exact ContinuousAt.comp (f := fun x : Work.FTS.PressureOn.R3 => (x, t)) hg hpair
  -- On the strip, the time derivative is exactly the evaluation of the joint derivative.
  refine hmain.congr fun x => ?_
  have hstripmem : Set.univ ×ˢ Set.Icc (0 : ℝ) S ∈ 𝓝 (x, t) := by
    rw [nhds_prod_eq]
    exact prod_mem_prod univ_mem (Icc_mem_nhds ht0 htS)
  have hcdat : ContDiffAt ℝ 1 v.uncurry (x, t) := hcd.contDiffAt hstripmem
  have hdiff : DifferentiableAt ℝ v.uncurry (x, t) := hcdat.differentiableAt (by norm_num)
  have hfda : HasFDerivAt v.uncurry (fderiv ℝ v.uncurry (x, t)) (x, t) := hdiff.hasFDerivAt
  have hd := hasDerivAt_slice_of_hasFDerivAt_uncurry (v := v) hfda
  simp only [FiniteTimeSingularity.timeDeriv]
  exact hd.deriv.symm

end Work.FTS.PressureOn.Connect
end
-- ===== merged: Submission.Work.FTS.PressureOn.Connect.hasDerivAt_omega_slice_at =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Connect

-- required full name (path convention): Work.FTS.PressureOn.Connect.hasDerivAt_omega_slice_at
theorem hasDerivAt_omega_slice_at {α : NNReal}
    {ω : Work.FTS.PressureOn.R3 → ℝ → Work.FTS.PressureOn.R3} {T t : ℝ}
    (hstrips : ∀ S' ∈ Set.Ioo 0 T, IsContDiffHolderOn ℝ α
      (Work.FTS.Physical.physVel ω).uncurry (Set.univ ×ˢ Set.Icc 0 S'))
    (hcurl : ∀ s ∈ Set.Ico 0 T, ∀ x,
      FiniteTimeSingularity.vorticity (fun z => Work.FTS.Physical.physVel ω z s) x = ω x s)
    (hcontDt : ContinuousOn (fun q : Work.FTS.PressureOn.R3 × ℝ =>
      FiniteTimeSingularity.timeDeriv ω q.1 q.2) (Set.univ ×ˢ Set.Ico 0 T))
    (hderiv : ∀ x, ∀ s ∈ Set.Ico 0 T,
      HasDerivWithinAt (ω x) (FiniteTimeSingularity.timeDeriv ω x s) (Set.Ici s) s)
    (ht : t ∈ Set.Ioo 0 T) (y : Work.FTS.PressureOn.R3) :
    HasDerivAt (fun s => ω y s) (FiniteTimeSingularity.timeDeriv ω y t) t := by
  obtain ⟨ht0, htT⟩ := ht
  -- Choose an intermediate time `S` with `t < S < T`: the hypotheses are local near `t`, and
  -- every strip hypothesis is available strictly below `T`.
  set S : ℝ := (t + T) / 2 with hSdef
  have hS0 : 0 < S := by rw [hSdef]; linarith
  have hST : S < T := by rw [hSdef]; linarith
  have htS : t < S := by rw [hSdef]; linarith
  have hS : S ∈ Set.Ioo 0 T := ⟨hS0, hST⟩
  -- `s ↦ ω y s` is continuous on `[0,S]`, being the curl of the spatial derivative of the
  -- jointly `C^{1,α}` field `physVel ω`.
  have hg : ContinuousOn (fun s => ω y s) (Set.Icc 0 S) :=
    continuousOn_time_omega_of_strips hS hstrips hcurl y
  -- `s ↦ ∂ₜω y s` is continuous on `[0,S)`.
  have hpair : ContinuousOn (fun s : ℝ => ((y, s) : Work.FTS.PressureOn.R3 × ℝ))
      (Set.Ico 0 S) := (continuous_const.prodMk continuous_id).continuousOn
  have hc : ContinuousOn (fun s : ℝ => FiniteTimeSingularity.timeDeriv ω y s) (Set.Ico 0 S) :=
    hcontDt.comp hpair
      (fun s hs => ⟨Set.mem_univ _, ⟨hs.1, lt_of_lt_of_le hs.2 (le_of_lt hST)⟩⟩)
  -- and the one-sided (right) derivative identity holds on `[0,S)`.
  have hd : ∀ s ∈ Set.Ico 0 S,
      HasDerivWithinAt (fun s => ω y s) (FiniteTimeSingularity.timeDeriv ω y s) (Set.Ici s) s :=
    fun s hs => hderiv y s ⟨hs.1, lt_of_lt_of_le hs.2 (le_of_lt hST)⟩
  exact hasDerivAt_of_hasDerivWithinAt_Ici ⟨ht0, htS⟩ hg hc hd

end Work.FTS.PressureOn.Connect
end
-- ===== merged: Submission.Work.FTS.PressureOn.Connect.lipschitz_extendTime =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Connect

theorem lipschitz_extendTime {v : Work.FTS.PressureOn.R3 → ℝ → Work.FTS.PressureOn.R3}
    {S t C : ℝ} (hS : 0 ≤ S) (hC : 0 ≤ C) (ht : t ∈ Set.Icc 0 S)
    (hlip : ∀ x, ∀ s ∈ Set.Icc 0 S, ‖v x s - v x t‖ ≤ C * |s - t|) :
    ∀ x, ∀ s : ℝ,
      ‖Work.FTS.PressureOn.Connect.extendTime v S x s
        - Work.FTS.PressureOn.Connect.extendTime v S x t‖ ≤ C * |s - t| := by
  intro x s
  have htc : clampt S t = t := clampt_eq_self_of_mem ht
  have hmem : clampt S s ∈ Set.Icc (0 : ℝ) S := clampt_mem_Icc hS s
  have h1 : ‖v x (clampt S s) - v x t‖ ≤ C * |clampt S s - t| := hlip x _ hmem
  have h2 : |clampt S s - t| ≤ |s - t| := by
    have h := abs_clampt_sub_le S s t
    rwa [htc] at h
  calc ‖Work.FTS.PressureOn.Connect.extendTime v S x s
        - Work.FTS.PressureOn.Connect.extendTime v S x t‖
      = ‖v x (clampt S s) - v x t‖ := by
        simp only [extendTime_apply, htc]
    _ ≤ C * |clampt S s - t| := h1
    _ ≤ C * |s - t| := mul_le_mul_of_nonneg_left h2 hC

end Work.FTS.PressureOn.Connect
end
-- ===== merged: Submission.Work.FTS.PressureOn.Connect.omega_strip_continuousOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Filter
open scoped Topology NNReal Matrix

set_option autoImplicit false

namespace Work.FTS.PressureOn.Connect

-- required full name (path convention): Work.FTS.PressureOn.Connect.omega_strip_continuousOn

end Work.FTS.PressureOn.Connect
end
-- ===== merged: Submission.Work.FTS.PressureOn.Connect.timeDeriv_physVel_continuousOn_strip =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Connect

-- required full name (path convention): Work.FTS.PressureOn.Connect.timeDeriv_physVel_continuousOn_strip

/-! On the open time-strip `0 < t < S`, the time derivative `∂ₜ (physVel ω)` of the physical
velocity is continuous, as soon as the *joint* map `(x,t) ↦ physVel ω x t` is `C^{1,α}` on the
closed strip `ℝ³ × [0,S]`.

The point is that the open strip lies in the *interior* of the closed strip: there the joint
`C¹` hypothesis gives an honest Fréchet derivative, and `∂ₜ` of a slice is that Fréchet
derivative evaluated at `(0,1)`; continuity of the Fréchet derivative on the open strip (a
consequence of `ContDiffOn ℝ 1` on an open set) then transfers to `∂ₜ`. -/

-- `hS` is not needed for the argument (the open strip is empty when `S ≤ 0`).

end Work.FTS.PressureOn.Connect
end
-- ===== merged: Submission.Work.FTS.PressureOn.CurlGrad.div_crossVec_eq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Matrix

namespace Work.FTS.PressureOn.CurlGrad

open FiniteTimeSingularity Work.FTS.PressureOn

/-! ## The `Fin 3 → ℝ` cores

Writing `eᵢ = Pi.single i 1` for the standard basis of `Fin 3 → ℝ`, both sides below are
polynomial identities in the matrix entries of the linear map `B` and the coordinates of the
vector `a` (resp. `w`), so `ring` closes them after the two finite sums over `Fin 3` are expanded
and the cross-product components are unfolded by `cross_apply`. -/

/-- **The left core**: `∑ᵢ ⟪(B eᵢ) × a, eᵢ⟫ = ⟪∑ᵢ eᵢ × (B eᵢ), a⟫`. -/
private theorem cross_curl_left_core (B : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) (a : Fin 3 → ℝ) :
    (∑ i : Fin 3, (crossProduct (B (Pi.single i (1 : ℝ))) a) i)
      = ∑ r : Fin 3,
        (∑ i : Fin 3, crossProduct (Pi.single i (1 : ℝ)) (B (Pi.single i (1 : ℝ)))) r * a r := by
  simp only [Fin.sum_univ_three, cross_apply]
  norm_num
  ring

/-- **The right core**: `∑ᵢ ⟪w, eᵢ × (B eᵢ)⟫ = -⟪w, ∑ᵢ eᵢ × (B eᵢ)⟫`. -/
private theorem cross_curl_right_core (B : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) (w : Fin 3 → ℝ) :
    (∑ i : Fin 3, (crossProduct w (B (Pi.single i (1 : ℝ)))) i)
      = -∑ r : Fin 3,
        w r * (∑ i : Fin 3, crossProduct (Pi.single i (1 : ℝ)) (B (Pi.single i (1 : ℝ)))) r := by
  simp only [Fin.sum_univ_three, cross_apply]
  norm_num
  ring

/-- `∑ᵢ (D eᵢ × a)ᵢ = ⟪curl D, a⟫`: the diagonal entries of the matrix `i ↦ D eᵢ × a` sum to the
inner product with the curl of the linear field `D`. -/
private theorem sum_diag_crossVec_left (D : R3 →L[ℝ] R3) (a : R3) :
    ∑ i : Fin 3, (crossVec (D (e i)) a).ofLp i = inner ℝ (curlVec D) a := by
  rw [inner_eq_sum]
  have h1 : (∑ i : Fin 3, (crossVec (D (e i)) a).ofLp i)
      = ∑ i : Fin 3, (crossProduct (conjLin D (Pi.single i (1 : ℝ))) a.ofLp) i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rfl
  rw [h1]
  exact cross_curl_left_core (conjLin D) a.ofLp

/-- `∑ᵢ (w × D eᵢ)ᵢ = -⟪w, curl D⟫`. -/
private theorem sum_diag_crossVec_right (D : R3 →L[ℝ] R3) (w : R3) :
    ∑ i : Fin 3, (crossVec w (D (e i))).ofLp i = -inner ℝ w (curlVec D) := by
  rw [inner_eq_sum]
  have h1 : (∑ i : Fin 3, (crossVec w (D (e i))).ofLp i)
      = ∑ i : Fin 3, (crossProduct w.ofLp (conjLin D (Pi.single i (1 : ℝ)))) i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rfl
  rw [h1]
  exact cross_curl_right_core (conjLin D) w.ofLp

/-- **The divergence of a cross product.**  For fields `F G : ℝ³ → ℝ³` differentiable at `x`,
`div (F ⨯ G) x = ⟪curl F x, G x⟫ - ⟪F x, curl G x⟫`, where `div` is the trace of the Fréchet
derivative (`FiniteTimeSingularity.div`), `vorticity` is the curl
(`FiniteTimeSingularity.vorticity`) and `crossVec a b = WithLp.toLp 2 (a ⨯₃ b)`.

Please declare it in `namespace Work.FTS.PressureOn.CurlGrad` so that its full name is
`Work.FTS.PressureOn.CurlGrad.div_crossVec_eq`.

Proof hints (all available in this workspace): `Work.FTS.PressureOn.vorticityCross_div_eq_sum_diag`
(`div g x = ∑ i, (fderiv ℝ g x (e i)) i`), `Work.FTS.PressureOn.vorticityCross_fderiv_crossVec_apply`
(the product rule `fderiv ℝ (fun y => crossVec (F y) (G y)) x (e i) =
crossVec (fderiv ℝ F x (e i)) (G x) + crossVec (F x) (fderiv ℝ G x (e i))`) — both in
`Submission/Work/FTS/PressureOn/vorticity_cross_eq.lean` — and the `Fin 3` algebra in the style of
`curl_inner_core` in `Submission/Work/FTS/PressureOn/materialDeriv_eq_gradient_sub_cross.lean`.
The sign has been checked by hand on the example `F = x₁ e₀`, `G = x₂ e₁`. -/
theorem div_crossVec_eq {F G : Work.FTS.PressureOn.R3 → Work.FTS.PressureOn.R3}
    {x : Work.FTS.PressureOn.R3}
    (hF : HasFDerivAt F (fderiv ℝ F x) x) (hG : HasFDerivAt G (fderiv ℝ G x) x) :
    FiniteTimeSingularity.div (fun y => Work.FTS.PressureOn.crossVec (F y) (G y)) x
      = inner ℝ (FiniteTimeSingularity.vorticity F x) (G x)
        - inner ℝ (F x) (FiniteTimeSingularity.vorticity G x) := by
  -- `div` is the trace, i.e. the sum of the diagonal entries in the basis `e`.
  rw [vorticityCross_div_eq_sum_diag]
  -- product rule for the pointwise cross product, direction by direction
  have hd : ∀ i : Fin 3, (fderiv ℝ (fun y => crossVec (F y) (G y)) x) (e i)
      = crossVec ((fderiv ℝ F x) (e i)) (G x) + crossVec (F x) ((fderiv ℝ G x) (e i)) :=
    fun i => vorticityCross_fderiv_crossVec_apply i hF hG
  simp only [hd, WithLp.ofLp_add, Pi.add_apply, Finset.sum_add_distrib]
  -- the two families of diagonal entries are `⟪curl F, G⟫` and `-⟪F, curl G⟫`
  rw [sum_diag_crossVec_left (fderiv ℝ F x) (G x),
    sum_diag_crossVec_right (fderiv ℝ G x) (F x)]
  rfl

end Work.FTS.PressureOn.CurlGrad
end
-- ===== merged: Submission.Work.FTS.PressureOn.CurlGrad.gradient_crossVec_bundle =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set MeasureTheory
open scoped Topology

namespace Work.FTS.PressureOn.CurlGrad

/-! ## Regularity of `gradient φ` for a `C²` function `φ`

`gradient φ = (toDual ℝ ℝ³).symm ∘ fderiv ℝ φ` is the composite of the continuous linear
equivalence `toDual` with `fderiv ℝ φ`, which is `C¹` as soon as `φ` is `C²`
(`ContDiff.fderiv_right`).  Hence `gradient φ` is `C¹`, differentiable everywhere with
derivative `fderiv ℝ (gradient φ)`, and compactly supported when `φ` is. -/

/-- `gradient φ` is `C¹` when `φ` is `C²`. -/
lemma contDiff_one_gradient {φ : R3 → ℝ} (hφ : ContDiff ℝ 2 φ) : ContDiff ℝ 1 (gradient φ) :=
  (LinearIsometryEquiv.contDiff (InnerProductSpace.toDual ℝ R3).symm).comp
    (hφ.fderiv_right (m := 1) (by norm_num))

/-- `gradient φ` is differentiable everywhere, with derivative `fderiv ℝ (gradient φ)`, when `φ`
is `C²`. -/
lemma gradient_hasFDerivAt {φ : R3 → ℝ} (hφ : ContDiff ℝ 2 φ) :
    ∀ x, HasFDerivAt (gradient φ) (fderiv ℝ (gradient φ) x) x := by
  have hdf : ContDiff ℝ 1 (fderiv ℝ φ) := hφ.fderiv_right (m := 1) (by norm_num)
  have hdiff : Differentiable ℝ (fun x => (InnerProductSpace.toDual ℝ R3).symm
      (fderiv ℝ φ x)) :=
    (LinearIsometryEquiv.differentiable (InnerProductSpace.toDual ℝ R3).symm).comp
      (hdf.differentiable (by norm_num))
  intro x
  exact hdiff.differentiableAt.hasFDerivAt

/-- `gradient φ` has compact support when `φ` does: its support is contained in the support of
`fderiv ℝ φ`, which is contained in `tsupport φ`. -/
lemma gradient_hasCompactSupport {φ : R3 → ℝ} (hcs : HasCompactSupport φ) :
    HasCompactSupport (gradient φ) := by
  refine (hcs.fderiv ℝ).mono ?_
  intro x hx
  rw [Function.mem_support] at hx ⊢
  intro h
  exact hx (by simp [gradient, h])

/-- **Regularity of the field `x ↦ u x × ∇φ x`.**  For `u : ℝ³ → ℝ³` of class `C¹` and
`φ : ℝ³ → ℝ` of class `C²` with compact support, the vector field
`X := fun x => crossVec (u x) (gradient φ x)` is continuous, differentiable everywhere with
derivative `fderiv ℝ X x`, has compact support, and its divergence is integrable; moreover
`gradient φ` itself is differentiable everywhere with derivative `fderiv ℝ (gradient φ) x`:

this is exactly the list of hypotheses required by
`Work.FTS.PressureOn.integral_div_eq_zero_of_hasFDerivAt X hcs hcont hdiff hint`.

Please declare it in `namespace Work.FTS.PressureOn.CurlGrad` so that its full name is
`Work.FTS.PressureOn.CurlGrad.gradient_crossVec_bundle`.

Proof hints: `gradient φ = (toDual ℝ ℝ³).symm ∘ fderiv ℝ φ`, `ContDiffAt.fderiv_right` gives
differentiability of `fderiv ℝ φ` from `hφ` (`ContDiff ℝ 2`), and composing with the continuous
linear isometry `(toDual ℝ ℝ³).symm` gives `HasFDerivAt (gradient φ) (fderiv ℝ (gradient φ) x) x`
(`ContinuousLinearMap.hasFDerivAt` + `HasFDerivAt.comp`, then `.fderiv`).  For `X`: use
`Work.FTS.PressureOn.vorticityCross_isBoundedBilinearMap` (`IsBoundedBilinearMap.continuous`,
`IsBoundedBilinearMap.differentiableAt` and `DifferentiableAt.hasFDerivAt`) composed with the pair
`x ↦ (u x, gradient φ x)` (`Continuous.prodMk`, `DifferentiableAt.prod`/`DifferentiableAt.prod_mk`);
`HasCompactSupport` follows from `HasCompactSupport.mono'` with the compactly supported
`gradient φ` (its support is contained in `tsupport φ` via `support_fderiv_subset` and
`HasCompactSupport.fderiv`), since `crossVec a 0 = 0`.  Finally `Integrable (div X)`: `X` is locally
zero off its (compact) support, hence so is `fderiv ℝ X` and hence `div X`, which is also
continuous; use `Work.FTS.PressureOn.exists_norm_supp_bound` (in
`Submission/Work/FTS/PressureOn/integral_div_eq_zero_of_hasFDerivAt.lean`) to get a radius `R` with
`div X = 0` outside `Metric.closedBall 0 R`, then
`ContinuousOn.integrableOn_compact` plus `MeasureTheory.integrable_indicator_iff`. -/
theorem gradient_crossVec_bundle {u : Work.FTS.PressureOn.R3 → Work.FTS.PressureOn.R3}
    {φ : Work.FTS.PressureOn.R3 → ℝ} (hu : ContDiff ℝ 1 u) (hφ : ContDiff ℝ 2 φ)
    (hcs : HasCompactSupport φ) :
    (∀ x, HasFDerivAt (gradient φ) (fderiv ℝ (gradient φ) x) x)
      ∧ Continuous (fun x => Work.FTS.PressureOn.crossVec (u x) (gradient φ x))
      ∧ (∀ x, HasFDerivAt (fun x => Work.FTS.PressureOn.crossVec (u x) (gradient φ x))
          (fderiv ℝ (fun x => Work.FTS.PressureOn.crossVec (u x) (gradient φ x)) x) x)
      ∧ HasCompactSupport (fun x => Work.FTS.PressureOn.crossVec (u x) (gradient φ x))
      ∧ MeasureTheory.Integrable
          (FiniteTimeSingularity.div (fun x => Work.FTS.PressureOn.crossVec (u x) (gradient φ x))) := by
  -- `gradient φ` is `C¹`, hence continuous and differentiable everywhere
  have hgrad_cd : ContDiff ℝ 1 (gradient φ) := contDiff_one_gradient hφ
  have hgrad_cont : Continuous (gradient φ) := hgrad_cd.continuous
  have hgrad_fd : ∀ x, HasFDerivAt (gradient φ) (fderiv ℝ (gradient φ) x) x :=
    gradient_hasFDerivAt hφ
  -- the pointwise cross product as a bounded bilinear map
  have hB := vorticityCross_isBoundedBilinearMap
  -- `X := x ↦ u x × ∇φ x` is `C¹`, hence continuous and differentiable everywhere
  have hX_cd : ContDiff ℝ 1 (fun x => crossVec (u x) (gradient φ x)) :=
    (hB.contDiff (n := 1)).comp (hu.prodMk hgrad_cd)
  have hX_cont : Continuous (fun x => crossVec (u x) (gradient φ x)) :=
    hB.continuous.comp (hu.continuous.prodMk hgrad_cont)
  have hX_diff : ∀ x, HasFDerivAt (fun x => crossVec (u x) (gradient φ x))
      (fderiv ℝ (fun x => crossVec (u x) (gradient φ x)) x) x := by
    intro x
    have hp : HasFDerivAt (fun y => (u y, gradient φ y))
        ((fderiv ℝ u x).prod (fderiv ℝ (gradient φ) x)) x :=
      ((hu.contDiffAt.differentiableAt (by norm_num)).hasFDerivAt).prodMk (hgrad_fd x)
    exact ((hB.hasFDerivAt (u x, gradient φ x)).comp x hp).differentiableAt.hasFDerivAt
  -- compact support: the support of `X` is contained in that of `∇φ`, which is compact
  have hcsX : HasCompactSupport (fun x => crossVec (u x) (gradient φ x)) :=
    (gradient_hasCompactSupport hcs).mono (fun x hx => by
      rw [Function.mem_support] at hx ⊢
      intro h
      exact hx (by simp [h]))
  -- `div X` vanishes off a closed ball, so it has compact support, and it is continuous
  have hdivcs : HasCompactSupport (div (fun x => crossVec (u x) (gradient φ x))) := by
    obtain ⟨R, hRpos, hR⟩ :=
      exists_norm_supp_bound (fun x => crossVec (u x) (gradient φ x)) hcsX
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 R) ?_
    intro y hy
    rw [Function.mem_support] at hy
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra h
    exact hy (hR y (le_of_lt (not_le.mp h))).2
  have hdivcont : Continuous (div (fun x => crossVec (u x) (gradient φ x))) := by
    have hfdc : Continuous (fderiv ℝ (fun x => crossVec (u x) (gradient φ x))) :=
      hX_cd.continuous_fderiv (by norm_num)
    rw [show div (fun x => crossVec (u x) (gradient φ x))
        = fun y => ∑ i : Fin 3, (fderiv ℝ (fun x => crossVec (u x) (gradient φ x)) y
            (WithLp.toLp 2 (Pi.single i (1 : ℝ)))) i from
      funext (div_eq_sum_single (fun x => crossVec (u x) (gradient φ x)))]
    refine continuous_finsetSum _ (fun i _ => ?_)
    have h1 : Continuous (fun y : R3 => fderiv ℝ (fun x => crossVec (u x) (gradient φ x)) y
        (WithLp.toLp 2 (Pi.single i (1 : ℝ)))) := hfdc.clm_apply continuous_const
    exact (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 3 => ℝ) i).comp h1
  exact ⟨hgrad_fd, hX_cont, hX_diff, hcsX,
    hdivcont.integrable_of_hasCompactSupport hdivcs⟩

end Work.FTS.PressureOn.CurlGrad
end
-- ===== merged: Submission.Work.FTS.PressureOn.CurlGrad.tendsto_integral_inner_fderiv_convolution =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Filter
open scoped Convolution Topology Pointwise

namespace Work.FTS.PressureOn.CurlGrad

/-- **The smoothing limit step.**  Let `ω : ℝ³ → ℝ³` be continuous, `ψ : ℝ³ → ℝ` of class `C¹`
with compact support, and `φ n` a sequence of bump functions with `rOut → 0`.  Then the integrals of
`x ↦ d(ρ_n ⋆ ψ)(x)(ω x)` converge to the integral of `x ↦ dψ(x)(ω x)`:

`Tendsto (fun n => ∫ x, fderiv ℝ (ρ_n ⋆ ψ) x (ω x)) atTop (𝓝 (∫ x, fderiv ℝ ψ x (ω x)))`.

Please declare it in `namespace Work.FTS.PressureOn.CurlGrad` so that its full name is
`Work.FTS.PressureOn.CurlGrad.tendsto_integral_inner_fderiv_convolution`.

Route (all ingredients are in Mathlib; note `(φ n).normed volume` needs `open MeasureTheory` or the
explicit `MeasureTheory.MeasureSpace.volume`):
* For each `n` the integrand is
  `x ↦ ∫ t, (φ n).normed volume t * (fderiv ℝ ψ (x - t) (ω x)) ∂volume`: differentiate the
  convolution with `HasCompactSupport.hasFDerivAt_convolution_right`
  (`Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`) with `L := ContinuousLinearMap.lsmul ℝ ℝ`,
  `f := (φ n).normed volume`, `g := ψ`, then evaluate the `ContinuousLinearMap.precompR`-convolution
  at `ω x` with `MeasureTheory.convolution_precompR_apply`
  (`Mathlib/Analysis/Convolution.lean`); `MeasureTheory.convolution_def` unfolds the definition.
  (This is the already-proved lemma `Work.FTS.PressureOn.CurlGrad.fderiv_normed_convolution_eq` in
  `Submission/Work/FTS/PressureOn/CurlGrad/fderiv_normed_convolution_eq.lean`.)
* Pointwise convergence for fixed `x` is `ContDiffBump.convolution_tendsto_right_of_continuous`
  applied to the continuous function `g := fun y => fderiv ℝ ψ y (ω x)` — note that
  `(ρ_n ⋆ g) x = ∫ t, (φ n).normed volume t * g (x - t)`, so its value at `x` converges to
  `g x = fderiv ℝ ψ x (ω x)`.
* Domination: `‖fderiv ℝ ψ y‖ ≤ M` for all `y` and some `M ≥ 0` (use `hψcs.fderiv ℝ` and
  `(hψ.continuous_fderiv (by norm_num)).norm` / `HasCompactSupport.exists_norm_le`), and
  `fderiv ℝ ψ` vanishes off `tsupport ψ`; since the support of `(φ n).normed volume` is
  `Metric.ball 0 (φ n).rOut` (`ContDiffBump.support_normed_eq`), for all large `n` the integrand is
  dominated by `fun x => M * ‖ω x‖ * (Metric.closedBall 0 R).indicator (fun _ => 1) x` for a large
  radius `R` (with `Metric.closedBall 0 R ⊇ tsupport ψ + Metric.closedBall 0 1`); that dominator is
  integrable because `‖ω‖` is bounded on the compact set `Metric.closedBall 0 R`
  (`IsCompact.exists_bound_of_continuousOn` / `Continuous.norm`), and
  `MeasureTheory.tendsto_integral_of_dominated_convergence` closes the proof. -/
theorem tendsto_integral_inner_fderiv_convolution
    {ω : Work.FTS.PressureOn.R3 → Work.FTS.PressureOn.R3} (hω : Continuous ω)
    {ψ : Work.FTS.PressureOn.R3 → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψcs : HasCompactSupport ψ)
    {φ : ℕ → ContDiffBump (0 : Work.FTS.PressureOn.R3)}
    (hφ : Filter.Tendsto (fun n => (φ n).rOut) Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n => ∫ x, fderiv ℝ (MeasureTheory.convolution ((φ n).normed volume) ψ
          (ContinuousLinearMap.lsmul ℝ ℝ) volume) x (ω x))
      Filter.atTop
      (nhds (∫ x, fderiv ℝ ψ x (ω x))) := by
  -- ## Elementary facts about `ψ`
  -- `fderiv ψ` vanishes off the (closed) topological support of `ψ`.
  have hfderiv_zero : ∀ y ∉ tsupport ψ, fderiv ℝ ψ y = 0 := by
    intro y hy
    have hmem : (tsupport ψ)ᶜ ∈ 𝓝 y := (isClosed_tsupport ψ).isOpen_compl.mem_nhds hy
    have heq : (fun _ : R3 => (0:ℝ)) =ᶠ[𝓝 y] ψ := by
      filter_upwards [hmem] with z hz
      exact (image_eq_zero_of_notMem_tsupport hz).symm
    rw [heq.symm.fderiv_eq]
    simp
  -- A uniform bound `M` for `‖fderiv ψ‖`.
  obtain ⟨M, hM0, hM⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ y : R3, ‖fderiv ℝ ψ y‖ ≤ M := by
    obtain ⟨C, hC⟩ : ∃ C, ∀ y ∈ tsupport ψ, ‖fderiv ℝ ψ y‖ ≤ C :=
      hψcs.isCompact.exists_bound_of_continuousOn (hψ.continuous_fderiv one_ne_zero).continuousOn
    refine ⟨max C 0, le_max_right _ _, fun y => ?_⟩
    by_cases hy : y ∈ tsupport ψ
    · exact le_trans (hC y hy) (le_max_left _ _)
    · rw [hfderiv_zero y hy, norm_zero]
      exact le_max_right _ _
  -- A large radius `R` containing `tsupport ψ + closedBall 0 1`.
  obtain ⟨R, hR⟩ : ∃ R : ℝ, tsupport ψ + Metric.closedBall (0:R3) 1 ⊆ Metric.closedBall 0 R := by
    have hcomp : IsCompact (tsupport ψ + Metric.closedBall (0:R3) 1) :=
      hψcs.isCompact.add (isCompact_closedBall (0:R3) 1)
    exact (Metric.isBounded_iff_subset_closedBall (0:R3)).1 hcomp.isBounded
  -- ## Rewriting the integrand as a convolution integral
  have hF : ∀ n x, fderiv ℝ (MeasureTheory.convolution ((φ n).normed volume) ψ
        (ContinuousLinearMap.lsmul ℝ ℝ) volume) x (ω x)
      = ∫ t, (φ n).normed volume t * fderiv ℝ ψ (x - t) (ω x) := by
    intro n x
    rw [fderiv_normed_convolution_eq hψ hψcs x (ω x)]
    rw [MeasureTheory.convolution_def]
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  -- ## A uniform pointwise bound for the rewritten integrand
  have hF_le : ∀ n x, ‖∫ t, (φ n).normed volume t * fderiv ℝ ψ (x - t) (ω x)‖ ≤ M * ‖ω x‖ := by
    intro n x
    have hρ : Integrable (fun t : R3 => (φ n).normed volume t) volume := (φ n).integrable_normed
    have hdom : Integrable (fun t : R3 => (φ n).normed volume t * (M * ‖ω x‖)) volume :=
      hρ.mul_const _
    have hle : ∀ t : R3, ‖(φ n).normed volume t * fderiv ℝ ψ (x - t) (ω x)‖
        ≤ (φ n).normed volume t * (M * ‖ω x‖) := by
      intro t
      rw [norm_mul, Real.norm_of_nonneg ((φ n).nonneg_normed t)]
      have h1 : ‖fderiv ℝ ψ (x - t) (ω x)‖ ≤ M * ‖ω x‖ :=
        calc ‖fderiv ℝ ψ (x - t) (ω x)‖ ≤ ‖fderiv ℝ ψ (x - t)‖ * ‖ω x‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ ≤ M * ‖ω x‖ := mul_le_mul_of_nonneg_right (hM (x - t)) (norm_nonneg _)
      exact mul_le_mul_of_nonneg_left h1 ((φ n).nonneg_normed t)
    calc ‖∫ t, (φ n).normed volume t * fderiv ℝ ψ (x - t) (ω x)‖
        ≤ ∫ t, ‖(φ n).normed volume t * fderiv ℝ ψ (x - t) (ω x)‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ t, (φ n).normed volume t * (M * ‖ω x‖) :=
          integral_mono_of_nonneg (Eventually.of_forall fun t => norm_nonneg _) hdom
            (Eventually.of_forall hle)
      _ = M * ‖ω x‖ := by
          rw [integral_mul_const, ContDiffBump.integral_normed, one_mul]
  -- ## The integrand vanishes off `closedBall 0 R` once `rOut ≤ 1`
  have hzeroF : ∀ n, (φ n).rOut ≤ 1 → ∀ x ∉ Metric.closedBall (0:R3) R,
      (∫ t, (φ n).normed volume t * fderiv ℝ ψ (x - t) (ω x)) = 0 := by
    intro n hn x hx
    have hzero : (fun t => (φ n).normed volume t * fderiv ℝ ψ (x - t) (ω x)) = fun _ => (0:ℝ) := by
      funext t
      by_cases ht : (φ n).normed volume t = 0
      · simp [ht]
      · have ht_ball : t ∈ Metric.ball (0:R3) ((φ n).rOut) := by
          rw [← ContDiffBump.support_normed_eq (f := φ n) (μ := (volume : Measure R3))]
          exact ht
        have ht_norm : ‖t‖ < (φ n).rOut := by
          simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using ht_ball
        have ht1 : t ∈ Metric.closedBall (0:R3) 1 := by
          simp only [Metric.mem_closedBall, dist_zero_right]
          linarith
        have hxt : x - t ∉ tsupport ψ := by
          intro hcon
          exact hx (hR ⟨x - t, hcon, t, ht1, sub_add_cancel x t⟩)
        simp [hfderiv_zero (x - t) hxt]
    rw [hzero]
    simp
  -- ## The dominator, and its integrability
  have hBd_meas : MeasurableSet (Metric.closedBall (0:R3) R) :=
    (isCompact_closedBall (0:R3) R).isClosed.measurableSet
  have hbound_int : Integrable
      (fun x : R3 => M * ‖ω x‖ * (Metric.closedBall (0:R3) R).indicator (fun _ => (1:ℝ)) x)
      volume := by
    have heq : (fun x : R3 => M * ‖ω x‖ * (Metric.closedBall (0:R3) R).indicator (fun _ => (1:ℝ)) x)
        = (Metric.closedBall (0:R3) R).indicator (fun x : R3 => M * ‖ω x‖) := by
      funext x
      by_cases hx : x ∈ Metric.closedBall (0:R3) R
      · simp [Set.indicator_of_mem hx]
      · simp [Set.indicator_of_notMem hx]
    rw [heq]
    exact (integrable_indicator_iff hBd_meas).2
      ((continuous_const.mul hω.norm).continuousOn.integrableOn_compact (isCompact_closedBall 0 R))
  have hbound_ev : ∀ᶠ n in atTop, ∀ᵐ x ∂(volume : Measure R3),
      ‖∫ t, (φ n).normed volume t * fderiv ℝ ψ (x - t) (ω x)‖
        ≤ M * ‖ω x‖ * (Metric.closedBall (0:R3) R).indicator (fun _ => (1:ℝ)) x := by
    filter_upwards [hφ.eventually (eventually_le_nhds zero_lt_one)] with n hn
    refine Eventually.of_forall fun x => ?_
    by_cases hx : x ∈ Metric.closedBall (0:R3) R
    · rw [Set.indicator_of_mem hx, mul_one]
      exact hF_le n x
    · rw [Set.indicator_of_notMem hx, mul_zero, hzeroF n hn x hx, norm_zero]
  -- ## Measurability
  have hmeas : ∀ᶠ n in atTop, AEStronglyMeasurable
      (fun x : R3 => ∫ t, (φ n).normed volume t * fderiv ℝ ψ (x - t) (ω x)) volume := by
    refine Eventually.of_forall fun n => ?_
    have hconv : ContDiff ℝ 1 (MeasureTheory.convolution ((φ n).normed volume) ψ
        (ContinuousLinearMap.lsmul ℝ ℝ) volume) :=
      hψcs.contDiff_convolution_right (L := ContinuousLinearMap.lsmul ℝ ℝ)
        ((φ n).integrable_normed.locallyIntegrable) hψ
    have hcont : Continuous (fun x : R3 => fderiv ℝ (MeasureTheory.convolution ((φ n).normed volume) ψ
        (ContinuousLinearMap.lsmul ℝ ℝ) volume) x (ω x)) :=
      (hconv.continuous_fderiv one_ne_zero).clm_apply hω
    exact hcont.aestronglyMeasurable.congr (Eventually.of_forall (hF n))
  -- ## Pointwise convergence at every `x`
  have hlim : ∀ᵐ x ∂(volume : Measure R3), Tendsto
      (fun n => ∫ t, (φ n).normed volume t * fderiv ℝ ψ (x - t) (ω x)) atTop
      (𝓝 (fderiv ℝ ψ x (ω x))) := by
    refine Eventually.of_forall fun x => ?_
    have hgc : Continuous (fun y : R3 => fderiv ℝ ψ y (ω x)) :=
      (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have h := ContDiffBump.convolution_tendsto_right_of_continuous (φ := φ)
      (g := fun y : R3 => fderiv ℝ ψ y (ω x)) (μ := (volume : Measure R3)) hφ hgc x
    simpa only [MeasureTheory.convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul] using h
  -- ## Dominated convergence, and transport back to the original integrand
  refine Tendsto.congr (fun n => ?_) (tendsto_integral_filter_of_dominated_convergence
    (fun x : R3 => M * ‖ω x‖ * (Metric.closedBall (0:R3) R).indicator (fun _ => (1:ℝ)) x)
    hmeas hbound_ev hbound_int hlim)
  exact integral_congr_ae (Eventually.of_forall fun x => (hF n x).symm)

end Work.FTS.PressureOn.CurlGrad
end
-- ===== merged: Submission.Work.FTS.PressureOn.Green.integrable_gaussScale_mul_laplaceTraceVec =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Metric
open Work.FTS.PressureOn (laplaceTraceVec R3 newtonKernel)

namespace Work.FTS.PressureOn.Green


/-- **The support of the Laplacian trace is contained in the topological support of the field.**
Off `tsupport G` the field is eventually zero, hence so is each slice `fderiv ℝ G · (e i)`
(`tsupport_fderiv_apply_subset`), hence so is its derivative (`fderiv_of_notMem_tsupport`).  No
smoothness is needed for this statement. -/
theorem support_laplaceTraceVec_subset (G : R3 → R3) :
    Function.support (laplaceTraceVec G) ⊆ tsupport G := by
  intro z hz
  by_contra hzG
  apply hz
  unfold laplaceTraceVec
  refine Finset.sum_eq_zero fun i _ => ?_
  have h1 : tsupport (fun w : R3 => fderiv ℝ G w (FiniteTimeSingularity.e i)) ⊆ tsupport G :=
    tsupport_fderiv_apply_subset ℝ (FiniteTimeSingularity.e i)
  have h2 : z ∉ tsupport (fun w : R3 => fderiv ℝ G w (FiniteTimeSingularity.e i)) :=
    fun h => hzG (h1 h)
  have h3 : fderiv ℝ (fun w : R3 => fderiv ℝ G w (FiniteTimeSingularity.e i)) z = 0 :=
    fderiv_of_notMem_tsupport (𝕜 := ℝ) h2
  simp [h3]


end Work.FTS.PressureOn.Green
end
-- ===== merged: Submission.Work.FTS.PressureOn.MollAux.convolution_norm_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.MollAux

/-- **Norm bound for a convolution with a probability density.**

If `ρ ≥ 0` is integrable with `∫ ρ = 1` and `‖g y‖ ≤ Vd` for all `y`, then the convolution
`ρ ⋆[lsmul ℝ ℝ, volume] g` (i.e. `x ↦ ∫ t, ρ t • g (x - t)`) is bounded by `Vd` pointwise:
`‖∫ t, ρ t • g (x - t)‖ ≤ ∫ t, ρ t * ‖g (x - t)‖ ≤ Vd * ∫ t, ρ t = Vd`. -/
theorem convolution_norm_le (ρ : EuclideanSpace ℝ (Fin 3) → ℝ)
    (g : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hρ : ∀ z, 0 ≤ ρ z) (hρint : MeasureTheory.Integrable ρ MeasureTheory.volume)
    (hint : ∫ z, ρ z = 1) (hg : Continuous g) (hgc : HasCompactSupport g)
    (Vd : ℝ) (hVd : ∀ y, ‖g y‖ ≤ Vd) (x : EuclideanSpace ℝ (Fin 3)) :
    ‖MeasureTheory.convolution ρ g (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume x‖ ≤ Vd := by
  -- rewrite the convolution as the Bochner integral `∫ t, ρ t • g (x - t)`
  rw [MeasureTheory.convolution_lsmul]
  -- pointwise bound on the integrand
  have hb : ∀ t, ‖ρ t • g (x - t)‖ ≤ ρ t * Vd := by
    intro t
    rw [norm_smul, Real.norm_of_nonneg (hρ t)]
    exact mul_le_mul_of_nonneg_left (hVd (x - t)) (hρ t)
  have hInt : MeasureTheory.Integrable (fun t => ρ t * Vd) MeasureTheory.volume :=
    MeasureTheory.Integrable.mul_const hρint Vd
  calc ‖∫ t, ρ t • g (x - t)‖ ≤ ∫ t, ρ t * Vd :=
        MeasureTheory.norm_integral_le_of_norm_le hInt (Filter.Eventually.of_forall hb)
    _ = Vd := by rw [MeasureTheory.integral_mul_const, hint, one_mul]

end Work.FTS.PressureOn.MollAux
end
-- ===== merged: Submission.Work.FTS.PressureOn.MollAux.moll_smooth_bounded =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.MollAux

open MeasureTheory

namespace MollSB

/-- The normalised bump `rho n` is nonnegative. -/
theorem nonneg_rho (n : ℕ) (t : R3) : 0 ≤ rho n t :=
  ContDiffBump.nonneg_normed (bump n) (μ := volume) t

/-- The normalised bump `rho n` is smooth. -/
theorem contDiff_rho (n : ℕ) (m : ℕ∞) : ContDiff ℝ (m : ℕ∞) (rho n) :=
  ContDiffBump.contDiff_normed (bump n) (μ := volume)

/-- The normalised bump `rho n` has compact support. -/
theorem hasCompactSupport_rho (n : ℕ) : HasCompactSupport (rho n) :=
  ContDiffBump.hasCompactSupport_normed (bump n) (μ := volume)

/-- The normalised bump `rho n` is integrable. -/
theorem integrable_rho (n : ℕ) : Integrable (rho n) volume :=
  ContDiffBump.integrable_normed (bump n) (μ := volume)

/-- The normalised bump `rho n` has integral one. -/
theorem integral_rho (n : ℕ) : ∫ t, rho n t = 1 :=
  ContDiffBump.integral_normed (bump n) (μ := volume)


/-- The vector mollification as an integral against `rho n`. -/
theorem mollV_eq_integral_rho (n : ℕ) (G : R3 → R3) (x : R3) :
    mollV n G x = ∫ t, rho n t • G (x - t) := by
  simp only [mollV, MeasureTheory.convolution]
  refine integral_congr_ae ?_
  filter_upwards with t
  rw [ContinuousLinearMap.lsmul_apply]

/-- The scalar mollification of a continuous function is smooth. -/
theorem contDiff_moll (n : ℕ) (g : R3 → ℝ) (hg : Continuous g) :
    ∀ m : ℕ, ContDiff ℝ m (moll n g) := fun m =>
  (hasCompactSupport_rho n).contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (contDiff_rho n (m : ℕ∞)) hg.locallyIntegrable

/-- The vector mollification of a continuous function is smooth. -/
theorem contDiff_mollV (n : ℕ) (G : R3 → R3) (hG : Continuous G) :
    ∀ m : ℕ, ContDiff ℝ m (mollV n G) := fun m =>
  (hasCompactSupport_rho n).contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (contDiff_rho n (m : ℕ∞)) hG.locallyIntegrable


/-- The vector mollification does not increase the sup-norm. -/
theorem norm_mollV_le (n : ℕ) (G : R3 → R3) (D : ℝ) (hD : ∀ x, ‖G x‖ ≤ D) (x : R3) :
    ‖mollV n G x‖ ≤ D := by
  have hφ0 : ∀ t, 0 ≤ rho n t := nonneg_rho n
  rw [mollV_eq_integral_rho]
  calc ‖∫ t, rho n t • G (x - t)‖
      ≤ ∫ t, ‖rho n t • G (x - t)‖ := MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ t, rho n t * ‖G (x - t)‖ := by
        refine integral_congr_ae ?_
        filter_upwards with t
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hφ0 t)]
    _ ≤ ∫ t, rho n t * D := by
        refine MeasureTheory.integral_mono_of_nonneg (ae_of_all _ fun t => ?_)
          ((integrable_rho n).mul_const D) (ae_of_all _ fun t => ?_)
        · exact mul_nonneg (hφ0 t) (norm_nonneg _)
        · exact mul_le_mul_of_nonneg_left (hD (x - t)) (hφ0 t)
    _ = (∫ t, rho n t) * D := MeasureTheory.integral_mul_const D _
    _ = D := by rw [integral_rho n, one_mul]

/-- The total derivative of the scalar mollification, evaluated at `x`, is the convolution of
`fderiv ℝ (rho n)` with `g` under `ContinuousLinearMap.precompL R3 (lsmul ℝ ℝ)`. -/
theorem hasFDerivAt_moll (n : ℕ) (g : R3 → ℝ) (hg : Continuous g) (x : R3) :
    HasFDerivAt (moll n g)
      (MeasureTheory.convolution (fderiv ℝ (rho n)) g
        (ContinuousLinearMap.precompL R3 (ContinuousLinearMap.lsmul ℝ ℝ)) volume x) x :=
  (hasCompactSupport_rho n).hasFDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (contDiff_rho n 1) hg.locallyIntegrable x

/-- `precompL R3 (lsmul ℝ ℝ)` applied to `u : R3 →L[ℝ] ℝ` and `c : ℝ` is the map `v ↦ c * u v`,
i.e. the scalar multiple `c • u`. -/
theorem precompL_lsmul_apply (u : R3 →L[ℝ] ℝ) (c : ℝ) :
    (ContinuousLinearMap.precompL R3 (ContinuousLinearMap.lsmul ℝ ℝ)) u c = c • u := by
  ext v
  rw [ContinuousLinearMap.precompL_apply, ContinuousLinearMap.lsmul_apply, smul_apply,
    smul_eq_mul, smul_eq_mul, mul_comm]

/-- The gradient of the scalar mollification is bounded by `C ∫ ‖fderiv ℝ (rho n)‖` whenever
`|g| ≤ C`. -/
theorem norm_fderiv_moll_le (n : ℕ) (g : R3 → ℝ) (hg : Continuous g) (C : ℝ)
    (hC : ∀ x, |g x| ≤ C) (x : R3) :
    ‖fderiv ℝ (moll n g) x‖ ≤ C * ∫ t, ‖fderiv ℝ (rho n) t‖ := by
  have hcs : HasCompactSupport (rho n) := hasCompactSupport_rho n
  have hcont' : Continuous (fderiv ℝ (rho n)) :=
    (contDiff_rho n 2).continuous_fderiv (by norm_num)
  have hint : Integrable (fun t => ‖fderiv ℝ (rho n) t‖) volume :=
    (hcont'.integrable_of_hasCompactSupport (hcs.fderiv ℝ)).norm
  have hterm : ∀ t, ‖(ContinuousLinearMap.precompL R3 (ContinuousLinearMap.lsmul ℝ ℝ))
      (fderiv ℝ (rho n) t) (g (x - t))‖ ≤ C * ‖fderiv ℝ (rho n) t‖ := by
    intro t
    rw [precompL_lsmul_apply, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hC (x - t)) (norm_nonneg _)
  rw [HasFDerivAt.fderiv (hasFDerivAt_moll n g hg x)]
  simp only [MeasureTheory.convolution]
  calc ‖∫ t, (ContinuousLinearMap.precompL R3 (ContinuousLinearMap.lsmul ℝ ℝ))
        (fderiv ℝ (rho n) t) (g (x - t))‖
      ≤ ∫ t, ‖(ContinuousLinearMap.precompL R3 (ContinuousLinearMap.lsmul ℝ ℝ))
        (fderiv ℝ (rho n) t) (g (x - t))‖ := MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ t, C * ‖fderiv ℝ (rho n) t‖ := by
        refine MeasureTheory.integral_mono_of_nonneg (ae_of_all _ fun t => norm_nonneg _)
          (hint.const_mul C) (ae_of_all _ fun t => hterm t)
    _ = C * ∫ t, ‖fderiv ℝ (rho n) t‖ := MeasureTheory.integral_const_mul C _

end MollSB


end Work.FTS.PressureOn.MollAux
end
-- ===== merged: Submission.Work.FTS.PressureOn.MollAux.rho_props =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.MollAux

open MeasureTheory Filter
open scoped Topology

/-- The outer radius of `bump n` is `1 / (n + 1)`, by definition. -/
theorem bump_rOut (n : ℕ) :
    (Work.FTS.PressureOn.bump n).rOut = 1 / ((n : ℝ) + 1) := rfl



theorem rho_props (n : ℕ) :
    (∀ m : ℕ, ContDiff ℝ m (Work.FTS.PressureOn.rho n)) ∧
    HasCompactSupport (Work.FTS.PressureOn.rho n) ∧
    (∫ z, Work.FTS.PressureOn.rho n z) = 1 ∧
    (∀ z, 0 ≤ Work.FTS.PressureOn.rho n z) ∧
    (∀ z, Work.FTS.PressureOn.rho n (-z) = Work.FTS.PressureOn.rho n z) ∧
    (∀ z, Work.FTS.PressureOn.rho n z ≠ 0 → ‖z‖ ≤ 1 / ((n : ℝ) + 1)) ∧
    Filter.Tendsto (fun n : ℕ => (Work.FTS.PressureOn.bump n).rOut) Filter.atTop (nhds 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- smoothness
    intro m
    exact ContDiffBump.contDiff_normed (f := Work.FTS.PressureOn.bump n)
      (μ := MeasureTheory.volume)
  · -- compact support
    exact ContDiffBump.hasCompactSupport_normed (f := Work.FTS.PressureOn.bump n)
      (μ := MeasureTheory.volume)
  · -- normalisation
    exact ContDiffBump.integral_normed (f := Work.FTS.PressureOn.bump n)
      (μ := MeasureTheory.volume)
  · -- nonnegativity
    intro z
    exact ContDiffBump.nonneg_normed (f := Work.FTS.PressureOn.bump n)
      (μ := MeasureTheory.volume) z
  · -- symmetry
    intro z
    exact ContDiffBump.normed_neg (Work.FTS.PressureOn.bump n) z
  · -- support inside the ball of radius `rOut = 1/(n+1)`
    intro z hz
    have hmem : z ∈ Function.support
        ((Work.FTS.PressureOn.bump n).normed MeasureTheory.volume) := hz
    rw [ContDiffBump.support_normed_eq] at hmem
    rw [bump_rOut] at hmem
    rw [Metric.mem_ball, dist_zero_right] at hmem
    exact hmem.le
  · -- the outer radii tend to `0`
    simpa [Work.FTS.PressureOn.bump] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds 0))

end Work.FTS.PressureOn.MollAux
end
-- ===== merged: Submission.Work.FTS.PressureOn.PoissonAux.Ibp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set MeasureTheory Metric Gradient
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.PressureOn

/-! ## Pointwise algebra -/

/-- The coordinates of the standard basis vectors. -/
lemma inner_e_eq_apply (v : R3) (i : Fin 3) : inner ℝ v (e i) = v i := by
  simp [FiniteTimeSingularity.e, PiLp.inner_apply, RCLike.inner_apply]

/-- A constant vector field has zero divergence. -/
lemma div_const (v : R3) (x : R3) : div (fun _ : R3 => v) x = 0 := by
  rw [div_eq_sum_single]
  simp

/-- The Fréchet derivative vanishes off the topological support. -/
lemma fderiv_eq_zero_of_notMem_tsupport {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : R3 → F} {x : R3} (hx : x ∉ tsupport G) : fderiv ℝ G x = 0 := by
  have hopen : IsOpen (tsupport G)ᶜ := (isClosed_tsupport G).isOpen_compl
  have h0 : G =ᶠ[𝓝 x] 0 := by
    filter_upwards [hopen.mem_nhds hx] with z hz
    exact image_eq_zero_of_notMem_tsupport hz
  rw [← h0.symm.fderiv_eq]; simp

/-- The divergence vanishes off the topological support. -/
lemma div_eq_zero_of_notMem_tsupport {G : R3 → R3} {x : R3} (hx : x ∉ tsupport G) :
    div G x = 0 := by
  rw [div, fderiv_eq_zero_of_notMem_tsupport hx]
  simp

/-- The derivative of the pointwise product `ψ • ω` of a scalar and a vector field. -/
lemma fderiv_smul {ψ : R3 → ℝ} {ω : R3 → R3} {x : R3} (hψ : DifferentiableAt ℝ ψ x)
    (hω : DifferentiableAt ℝ ω x) :
    fderiv ℝ (fun y => ψ y • ω y) x = ψ x • fderiv ℝ ω x + (fderiv ℝ ψ x).smulRight (ω x) :=
  (hψ.hasFDerivAt.smul hω.hasFDerivAt).fderiv

/-- The Fréchet derivative of a scalar function is the inner product with its gradient. -/
lemma fderiv_eq_innerSL_gradient (ψ : R3 → ℝ) (x : R3) :
    fderiv ℝ ψ x = innerSL ℝ (∇ ψ x) := by
  rw [← toDual_gradient]
  ext v
  rw [InnerProductSpace.toDual_apply_apply, innerSL_apply_apply]

/-- The standard basis vectors of `ℝ³` agree with `EuclideanSpace.basisFun`. -/
lemma e_eq_basisFun (i : Fin 3) : e i = (EuclideanSpace.basisFun (Fin 3) ℝ) i := by
  rw [EuclideanSpace.basisFun_apply]; rfl

/-- The trace of the rank-one endomorphism `(innerSL u).smulRight v` is `⟪u, v⟫`. -/
lemma trace_innerSL_smulRight (u v : R3) :
    ((innerSL ℝ u).smulRight v).trace ℝ R3 = inner ℝ u v := by
  rw [trace_eq_sum_single]
  have h1 : ∀ i : Fin 3, ((innerSL ℝ u).smulRight v (e i)) i = inner ℝ u (e i) * inner ℝ (e i) v := by
    intro i
    rw [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
    rw [show (inner ℝ u (e i) • v) i = inner ℝ u (e i) * v i from by
      simp [smul_eq_mul]]
    rw [show inner ℝ (e i) v = v i from by rw [real_inner_comm]; exact inner_e_eq_apply v i]
  refine (Finset.sum_congr rfl fun i _ => h1 i).trans ?_
  rw [show (∑ i, inner ℝ u (e i) * inner ℝ (e i) v)
      = ∑ i, inner ℝ u ((EuclideanSpace.basisFun (Fin 3) ℝ) i) *
          inner ℝ ((EuclideanSpace.basisFun (Fin 3) ℝ) i) v from
    Finset.sum_congr rfl fun i _ => by rw [e_eq_basisFun]]
  exact OrthonormalBasis.sum_inner_mul_inner _ u v

/-- The divergence of `x ↦ ψ x • ω x` for a scalar field `ψ` and a vector field `ω`. -/
lemma div_smul {ψ : R3 → ℝ} {ω : R3 → R3} (hψ : ContDiff ℝ 1 ψ) (hω : ContDiff ℝ 1 ω)
    (x : R3) :
    div (fun y => ψ y • ω y) x = ψ x * div ω x + inner ℝ (∇ ψ x) (ω x) := by
  have h1 : DifferentiableAt ℝ ψ x := hψ.differentiable_one x
  have h2 : DifferentiableAt ℝ ω x := hω.differentiable_one x
  have hsum : div (fun y => ψ y • ω y) x
      = (ψ x • fderiv ℝ ω x + (fderiv ℝ ψ x).smulRight (ω x)).trace ℝ R3 := by
    rw [div, fderiv_smul h1 h2]
  rw [hsum, show (ψ x • fderiv ℝ ω x + (fderiv ℝ ψ x).smulRight (ω x) : R3 →L[ℝ] R3)
        = (ψ x • fderiv ℝ ω x : R3 →L[ℝ] R3) + ((fderiv ℝ ψ x).smulRight (ω x)) from rfl]
  rw [show ((ψ x • fderiv ℝ ω x : R3 →L[ℝ] R3) + ((fderiv ℝ ψ x).smulRight (ω x))).trace ℝ R3
        = (↑(ψ x • fderiv ℝ ω x : R3 →L[ℝ] R3) : R3 →ₗ[ℝ] R3).trace ℝ R3
          + (↑((fderiv ℝ ψ x).smulRight (ω x)) : R3 →ₗ[ℝ] R3).trace ℝ R3 from
      LinearMap.map_add _ _ _]
  rw [show (↑(ψ x • fderiv ℝ ω x : R3 →L[ℝ] R3) : R3 →ₗ[ℝ] R3).trace ℝ R3
        = ψ x * div ω x from by
      rw [show (↑(ψ x • fderiv ℝ ω x : R3 →L[ℝ] R3) : R3 →ₗ[ℝ] R3)
            = ψ x • (fderiv ℝ ω x : R3 →ₗ[ℝ] R3) from rfl]
      rw [LinearMap.map_smul, smul_eq_mul, div]]
  rw [show (↑((fderiv ℝ ψ x).smulRight (ω x)) : R3 →ₗ[ℝ] R3)
        = (innerSL ℝ (∇ ψ x)).smulRight (ω x) from by
      rw [fderiv_eq_innerSL_gradient]]
  rw [show ((innerSL ℝ (∇ ψ x)).smulRight (ω x) : R3 →ₗ[ℝ] R3).trace ℝ R3
        = inner ℝ (∇ ψ x) (ω x) from trace_innerSL_smulRight _ _]

/-- The coordinate `(F x) i` depends continuously on `x` in the `i`-th coordinate. -/
lemma continuous_apply_coord (F : R3 → R3) (i : Fin 3) :
    (fun x : R3 => (F x) i) = fun x => (innerSL ℝ (e i)) (F x) := by
  funext x
  rw [innerSL_apply_apply, real_inner_comm, inner_e_eq_apply]

/-- The divergence of a `C¹` vector field is continuous. -/
lemma continuous_div_of_contDiff {G : R3 → R3} (hG : ContDiff ℝ 1 G) : Continuous (div G) := by
  have h : div G = fun x => ∑ i : Fin 3, (fderiv ℝ G x (e i)) i :=
    funext fun x => div_eq_sum_single G x
  rw [h]
  refine continuous_finset_sum _ fun i _ => ?_
  have hc : Continuous fun x : R3 => fderiv ℝ G x (e i) :=
    (hG.continuous_fderiv_apply one_ne_zero).comp (continuous_id.prodMk continuous_const)
  rw [continuous_apply_coord (fun x => fderiv ℝ G x (e i)) i]
  exact (ContinuousLinearMap.continuous _).comp hc

/-- The gradient of a `C¹` function is continuous. -/
lemma continuous_gradient_of_contDiff {ψ : R3 → ℝ} (hψ : ContDiff ℝ 1 ψ) : Continuous (∇ ψ) := by
  have hf : Continuous (fderiv ℝ ψ) := hψ.continuous_fderiv one_ne_zero
  have hfun : (∇ ψ) = fun x => (InnerProductSpace.toDual ℝ R3).symm (fderiv ℝ ψ x) := by
    funext x
    rw [← toDual_gradient (𝕜 := ℝ) (F := R3) (f := ψ) (x := x)]
    exact (LinearIsometryEquiv.symm_apply_apply (InnerProductSpace.toDual ℝ R3) (∇ ψ x)).symm
  rw [hfun]
  exact (InnerProductSpace.toDual ℝ R3).symm.continuous.comp hf

/-- The divergence of a compactly supported `C¹` field is integrable. -/
lemma integrable_div_of_contDiff {G : R3 → R3} (hG : ContDiff ℝ 1 G)
    (hcs : HasCompactSupport G) : Integrable (div G) := by
  refine Continuous.integrable_of_hasCompactSupport (continuous_div_of_contDiff hG) ?_
  refine hcs.mono' ?_
  intro x hx
  by_contra hxt
  rw [Function.mem_support] at hx
  exact hx (div_eq_zero_of_notMem_tsupport hxt)

/-! ## Integration by parts -/

/-- **The vector-field form of integration by parts.**  For a compactly supported `C¹` vector
field `ω` and a `C¹` function `ψ`,
`∫ x, ⟪ω x, ∇ψ x⟫ = -∫ x, div ω x * ψ x`. -/
theorem integral_inner_gradient_mul_eq_neg (ω : R3 → R3) (hω : ContDiff ℝ 1 ω)
    (hωcs : HasCompactSupport ω) {ψ : R3 → ℝ} (hψ : ContDiff ℝ 1 ψ) :
    ∫ x, inner ℝ (ω x) (∇ ψ x) = -∫ x, div ω x * ψ x := by
  have hsm : ContDiff ℝ 1 (fun x => ψ x • ω x) := hψ.smul hω
  have hcs : HasCompactSupport (fun x => ψ x • ω x) := hωcs.mono' (by
    intro x hx
    by_contra hxt
    rw [Function.mem_support] at hx
    exact hx (by simp [image_eq_zero_of_notMem_tsupport hxt]))
  have hdiv : div (fun x => ψ x • ω x) = fun x => ψ x * div ω x + inner ℝ (ω x) (∇ ψ x) := by
    funext x
    rw [div_smul hψ hω x, real_inner_comm (∇ ψ x) (ω x)]
  have h0 : ∫ x, div (fun y => ψ y • ω y) x = 0 :=
    integral_div_eq_zero_of_hasFDerivAt _ hcs hsm.continuous
      (fun x => (hsm.differentiable_one x).hasFDerivAt)
      (integrable_div_of_contDiff hsm hcs)
  have hInt1 : Integrable fun x => ψ x * div ω x := by
    refine Continuous.integrable_of_hasCompactSupport
      (hψ.continuous.mul (continuous_div_of_contDiff hω)) ?_
    refine hωcs.mono' ?_
    intro x hx
    by_contra hxt
    rw [Function.mem_support] at hx
    exact hx (by rw [div_eq_zero_of_notMem_tsupport hxt, mul_zero])
  have hInt2 : Integrable fun x => inner ℝ (ω x) (∇ ψ x) := by
    refine Continuous.integrable_of_hasCompactSupport
      (continuous_inner.comp (hω.continuous.prodMk (continuous_gradient_of_contDiff hψ))) ?_
    refine hωcs.mono' ?_
    intro x hx
    by_contra hxt
    rw [Function.mem_support] at hx
    exact hx (by rw [image_eq_zero_of_notMem_tsupport hxt, inner_zero_left])
  rw [hdiv, integral_add hInt1 hInt2] at h0
  have hcomm : ∫ x, div ω x * ψ x = ∫ x, ψ x * div ω x :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
  rw [hcomm]
  linarith

end Work.FTS.PressureOn
end
-- ===== merged: Submission.Work.FTS.PressureOn.PoissonAux.KI.massKernel_scale =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.PoissonAux.KI

/-- The one-dimensional profiles are related by the scaling
`ρ_ε(r) = ρ_1(r/ε)`, i.e. `rhoProfile ε = fun r => rhoProfile 1 (ε⁻¹ * r)`. -/
theorem rhoProfile_scale (ε : ℝ) (r : ℝ) :
    rhoProfile ε r = rhoProfile 1 (ε⁻¹ * r) := by
  rw [rhoProfile_apply, rhoProfile_apply]
  norm_num
  congr 1
  rw [mul_pow, inv_pow, div_eq_mul_inv]
  ring

/-- The first derivative of `rhoProfile` scales as expected. -/
theorem deriv_rhoProfile_scale (ε : ℝ) :
    deriv (rhoProfile ε) = fun r => ε⁻¹ * deriv (rhoProfile 1) (ε⁻¹ * r) := by
  rw [show rhoProfile ε = fun r => rhoProfile 1 (ε⁻¹ * r) from funext (rhoProfile_scale ε)]
  funext r
  rw [deriv_comp_mul_left]
  simp [smul_eq_mul]

/-- The second derivative of `rhoProfile` scales as expected: `ρ_ε''(r) = ε⁻² ρ_1''(r/ε)`. -/
theorem deriv_deriv_rhoProfile_scale (ε : ℝ) :
    deriv (deriv (rhoProfile ε))
      = fun r => ε⁻¹ * (ε⁻¹ * deriv (deriv (rhoProfile 1)) (ε⁻¹ * r)) := by
  rw [deriv_rhoProfile_scale ε]
  funext r
  change deriv (fun x => (fun s => ε⁻¹ * deriv (rhoProfile 1) s) (ε⁻¹ * x)) r =
    ε⁻¹ * (ε⁻¹ * deriv (deriv (rhoProfile 1)) (ε⁻¹ * r))
  have h := deriv_comp_mul_left (ε⁻¹) (fun s => ε⁻¹ * deriv (rhoProfile 1) s) r
  rw [h]
  rw [deriv_const_mul_field]
  simp [smul_eq_mul]

/-- The Newtonian kernel is homogeneous of degree `-1`: `newtonKernel (ε⁻¹ • x) = ε * newtonKernel x`
for `ε > 0`. -/
theorem newtonKernel_scale {ε : ℝ} (hε : 0 < ε) (x : R3) :
    newtonKernel (ε⁻¹ • x) = ε * newtonKernel x := by
  simp only [newtonKernel]
  rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  field_simp

/-- Scaling of the norm under `ε⁻¹ • ·` for `ε > 0`. -/
theorem norm_inv_smul {ε : ℝ} (hε : 0 < ε) (x : R3) : ‖ε⁻¹ • x‖ = ε⁻¹ * ‖x‖ := by
  rw [norm_smul, Real.norm_of_nonneg (by positivity)]

/-- **Scaling of the mass kernel.** The mass kernel `massKernel ε x = (4π‖x‖)⁻¹ ρ_ε''(‖x‖)` is
homogeneous of degree `-3` in the scaling parameter: `massKernel ε = ε⁻³ (massKernel 1)(·/ε)`,
i.e. `massKernel ε x = (ε³)⁻¹ * massKernel 1 (ε⁻¹ • x)` for `ε > 0`. -/
theorem massKernel_scale (ε : ℝ) (hε : 0 < ε) (x : R3) :
    massKernel ε x = (ε ^ 3)⁻¹ * massKernel 1 (ε⁻¹ • x) := by
  rw [massKernel_eq, massKernel_eq, deriv_deriv_rhoProfile_scale ε]
  rw [newtonKernel_scale hε x, norm_inv_smul hε x]
  field_simp

end Work.FTS.PressureOn.PoissonAux.KI
end
-- ===== merged: Submission.Work.FTS.PressureOn.PoissonAux.deriv_deriv_rhoProfile_support =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.PoissonAux

open Filter
open scoped Topology

/-- If `f` is constant on an open neighbourhood `t` of `r`, then `deriv (deriv f) r = 0`.

Indeed `deriv f` is then eventually `0` at `r` (at every point of the open set `t` the function
`f` is constant on a neighbourhood, hence has derivative `0` there), so the second derivative
vanishes at `r`. -/
lemma deriv_deriv_eq_zero_of_isOpen_const {f : ℝ → ℝ} {c r : ℝ} {t : Set ℝ}
    (ht : IsOpen t) (hr : r ∈ t) (hf : ∀ s ∈ t, f s = c) :
    deriv (deriv f) r = 0 := by
  have hder : deriv f =ᶠ[𝓝 r] fun _ => (0 : ℝ) := by
    filter_upwards [ht.mem_nhds hr] with s hs
    have hfs : f =ᶠ[𝓝 s] fun _ => c := by
      filter_upwards [ht.mem_nhds hs] with x hx
      exact hf x hx
    rw [hfs.deriv_eq]
    exact deriv_const s c
  calc deriv (deriv f) r = deriv (fun _ => (0 : ℝ)) r := hder.deriv_eq
    _ = 0 := deriv_const r 0


end Work.FTS.PressureOn.PoissonAux
end
-- ===== merged: Submission.Work.FTS.PressureOn.PoissonAux.exists_bound_deriv_deriv_rhoProfile =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Metric Set
open scoped Topology

namespace Work.FTS.PressureOn.PoissonAux

/-!
# A uniform bound for `ρ_ε''`

We prove that the second derivative of the cutoff profile `rhoProfile ε` is bounded by a
*universal* constant divided by `ε²`:

`∃ B ≥ 0, ∀ ε > 0, ∀ r, |(rhoProfile ε)'' r| ≤ B / ε²`.

The mechanism is the scaling identity `rhoProfile ε r = rhoProfile 1 (r / ε)` together with the
chain-rule relation for rescalings `r ↦ g (r/ε)` (namely `(g(r/ε))'' = g''(r/ε)/ε²`).  The
universal constant is the sup of `|(rhoProfile 1)''|`, which exists because `rhoProfile 1` is
`C²` and has compact support (it equals `1` as soon as `r² ≥ 2`).
-/



/-- **Chain rule for the second derivative of a rescaling.**  If `g` is `C²`, then
`(fun r => g (r / ε))'' r = g'' (r / ε) / ε²`. -/
theorem deriv_deriv_rescale (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g) (ε r : ℝ) :
    deriv (deriv (fun s : ℝ => g (s / ε))) r = deriv (deriv g) (r / ε) / ε ^ 2 := by
  have hDiffg : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hDiffdg : Differentiable ℝ (deriv g) := hg.differentiable_deriv_two
  have hGfun : deriv (fun s : ℝ => g (s / ε)) = fun s => deriv g (s / ε) * (1 / ε) := by
    funext s
    have h1 : HasDerivAt (fun t : ℝ => t / ε) (1 / ε) s := (hasDerivAt_id s).div_const ε
    have h2 : HasDerivAt g (deriv g (s / ε)) (s / ε) :=
      (hDiffg.differentiableAt (x := s / ε)).hasDerivAt
    have h3 : HasDerivAt (fun t : ℝ => g (t / ε)) (deriv g (s / ε) * (1 / ε)) s :=
      h2.comp_of_eq s h1 rfl
    rw [h3.deriv]
  rw [hGfun]
  have h1 : HasDerivAt (fun t : ℝ => t / ε) (1 / ε) r := (hasDerivAt_id r).div_const ε
  have h2 : HasDerivAt (deriv g) (deriv (deriv g) (r / ε)) (r / ε) :=
    (hDiffdg.differentiableAt (x := r / ε)).hasDerivAt
  have h3 : HasDerivAt (fun t : ℝ => deriv g (t / ε) * (1 / ε))
      ((deriv (deriv g) (r / ε) * (1 / ε)) * (1 / ε)) r :=
    (h2.comp_of_eq r h1 rfl).mul_const (1 / ε)
  rw [h3.deriv]
  rw [mul_assoc, div_mul_div_comm, one_mul, pow_two]
  ring






end Work.FTS.PressureOn.PoissonAux
end
-- ===== merged: Submission.Work.FTS.PressureOn.PoissonAux.exists_bound_deriv_radialCut =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Metric Filter
open scoped Topology

namespace Work.FTS.PressureOn.PoissonAux

/-!
# A uniform bound for the derivative of the profile `radialCut`

The profile `χ = radialCut` is `C^∞`, equals `1` on `(-∞,1]` and `0` on `[2,∞)`.  Hence its
derivative is continuous and supported in the compact interval `[1,2]`: it is zero on the open
set where `χ` is locally the constant `1` (below `1`) or the constant `0` (above `2`).
Continuity plus compact support then gives a uniform bound.
-/

/-- For `t < 1` the profile `radialCut` is locally the constant `1`. -/
theorem eventuallyEq_one_of_lt_one {t : ℝ} (ht : t < 1) :
    radialCut =ᶠ[𝓝 t] fun _ : ℝ => (1 : ℝ) := by
  filter_upwards [isOpen_Iio.mem_nhds ht] with s hs
  exact radialCut_eq_one (le_of_lt hs)

/-- For `2 < t` the profile `radialCut` is locally the constant `0`. -/
theorem eventuallyEq_zero_of_lt {t : ℝ} (ht : 2 < t) :
    radialCut =ᶠ[𝓝 t] fun _ : ℝ => (0 : ℝ) := by
  filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
  exact radialCut_eq_zero (le_of_lt hs)

/-- The derivative of `radialCut` is supported in the ball of radius `2` about `0`. -/
theorem support_deriv_radialCut_subset :
    Function.support (deriv radialCut) ⊆ closedBall (0 : ℝ) 2 := by
  intro t ht
  rw [mem_closedBall, dist_eq_norm, sub_zero, Real.norm_eq_abs]
  by_contra h
  rw [not_le] at h
  have hz : deriv radialCut t = 0 := by
    rcases lt_abs.mp h with h2 | h2
    · rw [(eventuallyEq_zero_of_lt h2).deriv_eq]; simp
    · rw [(eventuallyEq_one_of_lt_one (by linarith)).deriv_eq]; simp
  exact (Function.mem_support.mp ht) hz

/-- The derivative of `radialCut` has compact support. -/
theorem hasCompactSupport_deriv_radialCut : HasCompactSupport (deriv radialCut) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℝ) 2)
    support_deriv_radialCut_subset

/-- The derivative of `radialCut` is continuous. -/
theorem continuous_deriv_radialCut : Continuous (deriv radialCut) :=
  (contDiff_radialCut 1).continuous_deriv_one

/-- The derivative of the cutoff profile `radialCut` (defined in
`Submission/Work/FTS/PressureOn/PoissonAux/Defs.lean` as
`Work.FTS.PressureOn.radialCut t = Real.smoothTransition (2 - t)`, so that it is `1` on
`(-∞,1]` and `0` on `[2,∞)`) is bounded on all of `ℝ`. -/
theorem exists_bound_deriv_radialCut :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, |deriv Work.FTS.PressureOn.radialCut t| ≤ B := by
  obtain ⟨C, hC⟩ := continuous_deriv_radialCut.bounded_above_of_compact_support
    hasCompactSupport_deriv_radialCut
  exact ⟨C, le_trans (norm_nonneg _) (hC 0), fun t => by
    simpa only [Real.norm_eq_abs] using hC t⟩

end Work.FTS.PressureOn.PoissonAux
end
-- ===== merged: Submission.Work.FTS.PressureOn.PoissonAux.integrable_lambVector_kernel =====
section

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
end
-- ===== merged: Submission.Work.FTS.PressureOn.PoissonAux.integral_mul_deriv_deriv_rhoProfile =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Set MeasureTheory Filter
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.PressureOn.PoissonAux

/-! ## Pointwise values of `rhoProfile` to the right of `√2 ε` -/

/-- `ρ_ε` is identically `1` at every point to the right of `√2 ε`. -/
theorem rhoProfile_eq_one_of_sqrt_two_mul_lt {ε x : ℝ} (hε : 0 < ε)
    (hx : Real.sqrt 2 * ε < x) : Work.FTS.PressureOn.rhoProfile ε x = 1 := by
  refine Work.FTS.PressureOn.rhoProfile_eq_one hε ?_
  have hs : (Real.sqrt 2 * ε) ^ 2 = 2 * ε ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have h2 : 0 < Real.sqrt 2 * ε := by positivity
  nlinarith [hx, hs, h2]

/-- `ρ_ε` is *eventually* identically `1` near every point to the right of `√2 ε`. -/
theorem eventuallyEq_one_rhoProfile_of_sqrt_two_mul_lt {ε x : ℝ} (hε : 0 < ε)
    (hx : Real.sqrt 2 * ε < x) :
    Work.FTS.PressureOn.rhoProfile ε =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact rhoProfile_eq_one_of_sqrt_two_mul_lt hε hy

/-- `ρ_ε''` vanishes to the right of `√2 ε` (where `ρ_ε ≡ 1`). -/
theorem deriv_deriv_rhoProfile_eq_zero_of_sqrt_two_mul_lt {ε x : ℝ} (hε : 0 < ε)
    (hx : Real.sqrt 2 * ε < x) :
    deriv (deriv (Work.FTS.PressureOn.rhoProfile ε)) x = 0 := by
  have h1 : Work.FTS.PressureOn.rhoProfile ε =ᶠ[𝓝 x] fun _ => (1 : ℝ) :=
    eventuallyEq_one_rhoProfile_of_sqrt_two_mul_lt hε hx
  have h2 : deriv (Work.FTS.PressureOn.rhoProfile ε) =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
    (h1.deriv).trans (Eventually.of_forall fun y => by simp)
  have h3 := h2.deriv_eq
  simpa using h3

/-! ## The integral -/

/-- **The total mass of `r ↦ r ρ_ε''(r)`**: for `ε > 0`,
`∫_0^∞ r · ρ_ε''(r) dr = -1`, where `ρ_ε = rhoProfile ε`. -/
theorem integral_mul_deriv_deriv_rhoProfile (ε : ℝ) (hε : 0 < ε) :
    ∫ r in Set.Ioi (0 : ℝ), r * deriv (deriv (Work.FTS.PressureOn.rhoProfile ε)) r = -1 := by
  -- a cutoff radius beyond the support of `ρ_ε''`
  set R : ℝ := Real.sqrt 2 * ε + 1 with hRdef
  have h2pos : 0 < Real.sqrt 2 * ε := by positivity
  have hR2 : Real.sqrt 2 * ε < R := by rw [hRdef]; linarith
  have hRpos : 0 < R := lt_trans h2pos hR2
  -- `ρ_ε` is `C²`
  have hC2 : ContDiff ℝ 2 (Work.FTS.PressureOn.rhoProfile ε) :=
    contDiff_const.sub ((Work.FTS.PressureOn.contDiff_radialCut 2).comp
      ((contDiff_id (𝕜 := ℝ)).pow 2 |>.div_const (ε ^ 2)))
  have hderiv2 : Differentiable ℝ (deriv (Work.FTS.PressureOn.rhoProfile ε)) :=
    hC2.differentiable_deriv_two
  have hderivcont : Continuous (deriv (Work.FTS.PressureOn.rhoProfile ε)) :=
    hC2.continuous_deriv (by norm_num)
  have hderiv2cont : Continuous (deriv (deriv (Work.FTS.PressureOn.rhoProfile ε))) := by
    fun_prop
  -- the integrand vanishes beyond `R`
  have hsupp : ∀ x ∈ Set.Ioi (0 : ℝ) \ Set.Ioc 0 R,
      x * deriv (deriv (Work.FTS.PressureOn.rhoProfile ε)) x = 0 := by
    intro x hx
    have hxR : R < x := by
      by_contra h
      exact hx.2 ⟨hx.1, not_lt.mp h⟩
    rw [deriv_deriv_rhoProfile_eq_zero_of_sqrt_two_mul_lt hε (lt_trans hR2 hxR), mul_zero]
  have h1 : (∫ r in Set.Ioi (0 : ℝ),
        r * deriv (deriv (Work.FTS.PressureOn.rhoProfile ε)) r)
      = ∫ r in Set.Ioc 0 R, r * deriv (deriv (Work.FTS.PressureOn.rhoProfile ε)) r :=
    MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (fun x hx => hx.1) hsupp
  rw [h1, ← intervalIntegral.integral_of_le hRpos.le]
  -- integration by parts on `[0,R]`
  have hibp : ∫ r in (0:ℝ)..R, r * deriv (deriv (Work.FTS.PressureOn.rhoProfile ε)) r
      = R * deriv (Work.FTS.PressureOn.rhoProfile ε) R
        - 0 * deriv (Work.FTS.PressureOn.rhoProfile ε) 0
        - ∫ x in (0:ℝ)..R, (1:ℝ) * deriv (Work.FTS.PressureOn.rhoProfile ε) x :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (u := fun r : ℝ => r) (v := deriv (Work.FTS.PressureOn.rhoProfile ε))
      (u' := fun _ : ℝ => (1:ℝ))
      (v' := deriv (deriv (Work.FTS.PressureOn.rhoProfile ε)))
      (fun x _ => hasDerivAt_id x)
      (fun x _ => hasDerivAt_deriv_iff.mpr (hderiv2 x))
      (continuous_const.intervalIntegrable _ _)
      (hderiv2cont.intervalIntegrable _ _)
  rw [hibp]
  -- the boundary terms and the fundamental theorem of calculus
  have hρR : Work.FTS.PressureOn.rhoProfile ε R = 1 :=
    rhoProfile_eq_one_of_sqrt_two_mul_lt hε hR2
  have hρ0 : Work.FTS.PressureOn.rhoProfile ε 0 = 0 :=
    Work.FTS.PressureOn.rhoProfile_eq_zero hε (by simpa using sq_nonneg ε)
  have hdR : deriv (Work.FTS.PressureOn.rhoProfile ε) R = 0 := by
    have h := (eventuallyEq_one_rhoProfile_of_sqrt_two_mul_lt hε hR2).deriv_eq
    simpa using h
  have hftc : ∫ x in (0:ℝ)..R, deriv (Work.FTS.PressureOn.rhoProfile ε) x
      = Work.FTS.PressureOn.rhoProfile ε R - Work.FTS.PressureOn.rhoProfile ε 0 :=
    intervalIntegral.integral_deriv_eq_sub
      (fun x _ => hC2.differentiable (by norm_num) x)
      (hderivcont.intervalIntegrable _ _)
  have hone : (∫ x in (0:ℝ)..R, (1:ℝ) * deriv (Work.FTS.PressureOn.rhoProfile ε) x)
      = ∫ x in (0:ℝ)..R, deriv (Work.FTS.PressureOn.rhoProfile ε) x := by
    simp_rw [one_mul]
  rw [hone, hftc, hdR, hρR, hρ0]
  ring

end Work.FTS.PressureOn.PoissonAux
end
-- ===== merged: Submission.Work.FTS.PressureOn.PoissonAux.integral_radial =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

set_option autoImplicit false

namespace Work.FTS.PressureOn.PoissonAux

/-- **The spherical-coordinate (radial) integral formula in `ℝ³`.**

For an arbitrary `g : ℝ → ℝ`, the integral over `ℝ³` of the radially symmetric function
`x ↦ g ‖x‖` equals `4π ∫_{(0,∞)} r² g r dr`.

No integrability hypothesis is needed: both sides are Bochner integrals with the
`integral_undef = 0` convention, and the two integrability conditions coincide.  The general
change-of-variables statement behind this (for an arbitrary additive Haar measure on a
finite-dimensional real normed space) is `MeasureTheory.integral_fun_norm_addHaar`; specialising
it to `R3 = EuclideanSpace ℝ (Fin 3)`, where `finrank ℝ R3 = 3` and the unit ball has volume
`4π/3`, gives the stated identity. -/
theorem integral_radial (g : ℝ → ℝ) :
    ∫ x : R3, g ‖x‖ = 4 * Real.pi * ∫ r in Set.Ioi (0 : ℝ), r ^ 2 * g r := by
  rw [MeasureTheory.integral_fun_norm_addHaar (μ := (volume : Measure R3)) (F := ℝ) g]
  have hfr : Module.finrank ℝ R3 = 3 := by simp
  have hvol : (volume : Measure R3).real (Metric.ball 0 1) = 4 * Real.pi / 3 := by
    rw [MeasureTheory.Measure.real, EuclideanSpace.volume_ball_fin_three]
    simp only [ENNReal.ofReal_one, one_pow, one_mul]
    rw [ENNReal.toReal_ofReal (by positivity)]
    ring
  rw [hfr, hvol]
  simp only [smul_eq_mul, nsmul_eq_mul]
  ring

end Work.FTS.PressureOn.PoissonAux
end
-- ===== merged: Submission.Work.FTS.PressureOn.PoissonAux.laplaceTrace_cutKernel =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set MeasureTheory Metric
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.PressureOn.PoissonAux

/-! ## The `t`-variable profile of the truncated kernel -/

/-- The profile of the truncated Newtonian kernel, viewed as a function of `t = ‖y‖²`:
`cutProfile ε t = (1 - χ(t/ε²))/(4π√t)`, so that
`cutProfile ε (‖y‖²) = smallCut ε y * newtonKernel y`. -/
noncomputable def cutProfile (ε t : ℝ) : ℝ :=
  (1 - radialCut (t / ε ^ 2)) / (4 * Real.pi * Real.sqrt t)

theorem cutProfile_apply (ε : ℝ) (t : ℝ) :
    cutProfile ε t = (1 - radialCut (t / ε ^ 2)) / (4 * Real.pi * Real.sqrt t) := rfl

/-- `cutProfile ε (‖y‖²)` *is* the truncated Newtonian kernel. -/
theorem cutProfile_normSq (ε : ℝ) (y : R3) :
    cutProfile ε (‖y‖ ^ 2) = smallCut ε y * newtonKernel y := by
  rw [cutProfile_apply, Real.sqrt_sq (norm_nonneg y), smallCut_apply, newtonKernel,
    div_eq_mul_inv]

/-- `cutProfile ε` is `C²` on `ℝ`: on `t < ε²` it vanishes identically, and for `t > 0` it is the
quotient of the smooth numerator `1 - χ(t/ε²)` by the smooth nonvanishing denominator `4π√t`. -/
theorem contDiff_cutProfile (ε : ℝ) (hε : 0 < ε) : ContDiff ℝ 2 (cutProfile ε) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  by_cases ht : t < ε ^ 2
  · have hmem : Iio (ε ^ 2) ∈ 𝓝 t := Iio_mem_nhds ht
    refine ContDiffAt.congr_of_eventuallyEq (f := fun _ : ℝ => (0 : ℝ)) (f₁ := cutProfile ε)
      (x := t) contDiffAt_const ?_
    filter_upwards [hmem] with s hs
    rw [cutProfile_apply]
    have hs1 : s / ε ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact le_of_lt hs
    rw [radialCut_eq_one hs1, sub_self, zero_div]
  · have htpos : 0 < t := lt_of_lt_of_le (by positivity) (not_lt.mp ht)
    have hnum : ContDiffAt ℝ 2 (fun s : ℝ => 1 - radialCut (s / ε ^ 2)) t :=
      (contDiff_const.sub ((contDiff_radialCut 2).comp (contDiff_id.div_const (ε ^ 2)))).contDiffAt
    have hsqrt : ContDiffAt ℝ 2 (fun s : ℝ => Real.sqrt s) t :=
      Real.contDiffAt_sqrt (x := t) (n := 2) (ne_of_gt htpos)
    have hden : ContDiffAt ℝ 2 (fun s : ℝ => 4 * Real.pi * Real.sqrt s) t :=
      (contDiffAt_const (c := 4 * Real.pi)).mul hsqrt
    have hne : (4 * Real.pi * Real.sqrt t) ≠ 0 := by
      have h1 : 0 < Real.sqrt t := Real.sqrt_pos.mpr htpos
      have h2 : 0 < 4 * Real.pi := by positivity
      positivity
    have hquot : ContDiffAt ℝ 2
        (fun s : ℝ => (1 - radialCut (s / ε ^ 2)) / (4 * Real.pi * Real.sqrt s)) t :=
      hnum.div hden hne
    exact hquot

/-- The one-dimensional profile `rhoProfile ε` of the cutoff is `C²`. -/
theorem contDiff_rhoProfile (ε : ℝ) : ContDiff ℝ 2 (rhoProfile ε) :=
  contDiff_const.sub ((contDiff_radialCut 2).comp ((contDiff_id (𝕜 := ℝ)).pow 2 |>.div_const (ε ^ 2)))

/-! ## The Laplacian of a function of `‖·‖²` -/

/-- **The Laplacian of a function of `‖x‖²`**: `Δ (F ∘ ‖·‖²) x = 6F'(‖x‖²) + 4‖x‖²F''(‖x‖²)`.
This is the trace, in the standard basis `FiniteTimeSingularity.e`, of the Hessian formula
`Work.FTS.PressureOn.Auxiliary.normSq_hessian`. -/
theorem laplaceTrace_normSq (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (x : R3) :
    laplaceTrace (fun y : R3 => F (‖y‖ ^ 2)) x
      = 6 * deriv F (‖x‖ ^ 2) + 4 * ‖x‖ ^ 2 * deriv (deriv F) (‖x‖ ^ 2) := by
  have hsum : ∑ i : Fin 3, (x i) ^ 2 = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq]
    rw [Real.sq_sqrt (by positivity)]
    simp only [Real.norm_eq_abs, sq_abs]
  have hee : ∀ i : Fin 3, inner ℝ (e i) (e i) = (1 : ℝ) := by
    intro i
    rw [e, PiLp.inner_apply]
    simp [Pi.single_apply]
  have hxe : ∀ i : Fin 3, inner ℝ x (e i) = x i := by
    intro i
    rw [e, PiLp.inner_apply]
    simp [Pi.single_apply]
  have hterm : ∀ i : Fin 3,
      (fderiv ℝ (fun w : R3 => fderiv ℝ (fun y : R3 => F (‖y‖ ^ 2)) w (e i)) x) (e i)
        = 2 * deriv F (‖x‖ ^ 2) + 4 * deriv (deriv F) (‖x‖ ^ 2) * (x i) ^ 2 := by
    intro i
    rw [Work.FTS.PressureOn.Auxiliary.normSq_hessian F hF x (e i) (e i), hee i, hxe i]
    ring
  rw [laplaceTrace, Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Finset.mul_sum, hsum]
  simp only [nsmul_eq_mul]
  ring

/-! ## The main computation -/

/-- **The Laplacian of the truncated Newtonian kernel.**
For `ε > 0` and `x ≠ 0`, the Laplacian of `y ↦ smallCut ε y * newtonKernel y` at `x` is
`massKernel ε x = (4π‖x‖)⁻¹ ρ_ε''(‖x‖)`. -/
theorem laplaceTrace_cutKernel (ε : ℝ) (hε : 0 < ε) {x : R3} (hx : x ≠ 0) :
    laplaceTrace (fun y : R3 => smallCut ε y * newtonKernel y) x = massKernel ε x := by
  have hρ : 0 < ‖x‖ := norm_pos_iff.mpr hx
  -- the truncated kernel is the one-dimensional profile composed with `‖·‖²`
  have hfun : (fun y : R3 => smallCut ε y * newtonKernel y)
      = fun y : R3 => cutProfile ε (‖y‖ ^ 2) := by
    funext y
    exact (cutProfile_normSq ε y).symm
  -- near `‖x‖ > 0`, `r ↦ cutProfile ε (r²)` is `r ↦ rhoProfile ε r / (4π r)`
  have hev : (fun r : ℝ => cutProfile ε (r ^ 2))
      =ᶠ[𝓝 ‖x‖] (fun r : ℝ => rhoProfile ε r / (4 * Real.pi * r)) := by
    filter_upwards [Ioi_mem_nhds hρ] with r hr
    rw [cutProfile_apply, rhoProfile_apply, Real.sqrt_sq (le_of_lt hr)]
  have hd1 : deriv (fun r : ℝ => cutProfile ε (r ^ 2)) ‖x‖
      = deriv (fun r : ℝ => rhoProfile ε r / (4 * Real.pi * r)) ‖x‖ := hev.deriv_eq
  have hd2 : deriv (deriv (fun r : ℝ => cutProfile ε (r ^ 2))) ‖x‖
      = deriv (deriv (fun r : ℝ => rhoProfile ε r / (4 * Real.pi * r))) ‖x‖ :=
    hev.deriv.deriv_eq
  rw [hfun, laplaceTrace_normSq (cutProfile ε) (contDiff_cutProfile ε hε) x,
    ← deriv_deriv_comp_sq (cutProfile ε) (contDiff_cutProfile ε hε) hρ, hd2, hd1,
    oneDim_radial_laplace (rhoProfile ε) (contDiff_rhoProfile ε) hρ]
  rw [massKernel_eq, newtonKernel, div_eq_mul_inv, mul_comm]

end Work.FTS.PressureOn.PoissonAux
end
-- ===== merged: Submission.Work.FTS.PressureOn.PoissonAux.laplaceTrace_fderiv_comm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set MeasureTheory Filter
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.PressureOn.PoissonAux

open Work.FTS.PressureOn

/-! ## Symmetry of second derivatives, in evaluation form

The library lemma `IsSymmSndFDerivAt.eq` states the symmetry of second derivatives for a `C²`
function `g` in the form
`fderiv ℝ (fderiv ℝ g) x v w = fderiv ℝ (fderiv ℝ g) x w v`,
i.e. through the bundled derivative `fderiv ℝ (fderiv ℝ g) x`.  For the computation below it is
more convenient to have the same statement in *evaluation* form, with the two directions appearing
as the directions of the outer `fderiv` and of the inner evaluation.  The two forms are related by
`fderiv_clm_apply` applied to the family `y ↦ fderiv ℝ g y` of continuous linear maps and the
constant map `y ↦ v`. -/

/-- **Symmetry of the second derivative in evaluation form.**  For a function `g` that is `C²` at
`x` and vectors `v`, `w`, the two mixed second directional derivatives agree:
`∂_w (y ↦ ∂_v g y) x = ∂_v (y ↦ ∂_w g y) x`. -/
private lemma sndFDeriv_eval_swap {g : R3 → ℝ} {x : R3}
    (hg : ContDiffAt ℝ 2 g x) (v w : R3) :
    fderiv ℝ (fun y => fderiv ℝ g y v) x w = fderiv ℝ (fun y => fderiv ℝ g y w) x v := by
  have hd : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h1 : fderiv ℝ (fun y => fderiv ℝ g y v) x = (fderiv ℝ (fderiv ℝ g) x).flip v := by
    rw [fderiv_clm_apply hd (differentiableAt_const v)]
    simp
  have h2 : fderiv ℝ (fun y => fderiv ℝ g y w) x = (fderiv ℝ (fderiv ℝ g) x).flip w := by
    rw [fderiv_clm_apply hd (differentiableAt_const w)]
    simp
  rw [h1, h2, ContinuousLinearMap.flip_apply, ContinuousLinearMap.flip_apply]
  exact ((hg.isSymmSndFDerivAt (by norm_num)).eq v w).symm

/-- The Laplacian `laplaceTrace u x = ∑ᵢ ∂ᵢ∂ᵢ u x` (trace of the Hessian in the standard basis
`FiniteTimeSingularity.e`, defined in `Submission/Work/FTS/PressureOn/Defs.lean`) commutes with a
first partial derivative: for a `C³` function `Ψ : ℝ³ → ℝ` and every coordinate `i`,
`Δ (∂ᵢ Ψ) = ∂ᵢ (Δ Ψ)` as functions.  This is a pure Clairaut/symmetry-of-second-derivatives fact. -/
theorem laplaceTrace_fderiv_comm {Ψ : Work.FTS.PressureOn.R3 → ℝ} (hΨ : ContDiff ℝ 3 Ψ)
    (i : Fin 3) :
    Work.FTS.PressureOn.laplaceTrace (fun z : Work.FTS.PressureOn.R3 => fderiv ℝ Ψ z
        (FiniteTimeSingularity.e i))
      = fun z : Work.FTS.PressureOn.R3 => fderiv ℝ (Work.FTS.PressureOn.laplaceTrace Ψ) z
          (FiniteTimeSingularity.e i) := by
  -- Both sides are sums over `j : Fin 3` of third-order partial derivatives of `Ψ`; the `j`-th
  -- summand of the left side is `∂_j ∂_j ∂_i Ψ x` and that of the right side is `∂_i ∂_j ∂_j Ψ x`.
  funext x
  -- `fun z => fderiv ℝ Ψ z v` is `C²` for every direction `v` (it is `∂_v Ψ`, and `Ψ` is `C³`).
  have hC2 : ∀ v : R3, ContDiff ℝ 2 (fun z : R3 => fderiv ℝ Ψ z v) := fun v =>
    (hΨ.contDiff_fderiv_apply (m := 2) (by norm_num)).comp
      (contDiff_id.prodMk (contDiff_const (c := v)))
  -- Likewise `y ↦ ∂_v (∂_v Ψ) y` is `C¹`, hence differentiable.
  have hC1 : ∀ v : R3, ContDiff ℝ 1 (fun y : R3 => fderiv ℝ (fun z : R3 => fderiv ℝ Ψ z v) y v) :=
    fun v => ((hC2 v).contDiff_fderiv_apply (m := 1) (by norm_num)).comp
      (contDiff_id.prodMk (contDiff_const (c := v)))
  -- The `j`-th summands agree: exchange `∂_i` and `∂_j` (second derivatives of `Ψ`), then
  -- `∂_j` and `∂_i` (second derivatives of `∂_j Ψ`).
  have key : ∀ j : Fin 3,
      fderiv ℝ (fun y : R3 => fderiv ℝ (fun z : R3 => fderiv ℝ Ψ z (FiniteTimeSingularity.e i))
          y (FiniteTimeSingularity.e j)) x (FiniteTimeSingularity.e j)
        = fderiv ℝ (fun y : R3 => fderiv ℝ (fun z : R3 => fderiv ℝ Ψ z (FiniteTimeSingularity.e j))
          y (FiniteTimeSingularity.e j)) x (FiniteTimeSingularity.e i) := by
    intro j
    have hfun : (fun y : R3 => fderiv ℝ (fun z : R3 => fderiv ℝ Ψ z (FiniteTimeSingularity.e i))
          y (FiniteTimeSingularity.e j))
        = (fun y : R3 => fderiv ℝ (fun z : R3 => fderiv ℝ Ψ z (FiniteTimeSingularity.e j))
          y (FiniteTimeSingularity.e i)) := by
      funext y
      exact sndFDeriv_eval_swap (hΨ.contDiffAt.of_le (by norm_num)) (FiniteTimeSingularity.e i)
        (FiniteTimeSingularity.e j)
    rw [hfun]
    exact sndFDeriv_eval_swap ((hC2 (FiniteTimeSingularity.e j)).contDiffAt)
      (FiniteTimeSingularity.e i) (FiniteTimeSingularity.e j)
  have hlt : laplaceTrace (fun z : R3 => fderiv ℝ Ψ z (FiniteTimeSingularity.e i)) x
      = ∑ j : Fin 3, fderiv ℝ (fun y : R3 =>
          fderiv ℝ (fun z : R3 => fderiv ℝ Ψ z (FiniteTimeSingularity.e i)) y
            (FiniteTimeSingularity.e j)) x (FiniteTimeSingularity.e j) := rfl
  have hrt : fderiv ℝ (laplaceTrace Ψ) x (FiniteTimeSingularity.e i)
      = ∑ j : Fin 3, fderiv ℝ (fun y : R3 =>
          fderiv ℝ (fun z : R3 => fderiv ℝ Ψ z (FiniteTimeSingularity.e j)) y
            (FiniteTimeSingularity.e j)) x (FiniteTimeSingularity.e i) := by
    have hfun : laplaceTrace Ψ
        = fun y : R3 => ∑ j : Fin 3, fderiv ℝ (fun z : R3 => fderiv ℝ Ψ z (FiniteTimeSingularity.e j))
            y (FiniteTimeSingularity.e j) := rfl
    rw [hfun]
    have hd : ∀ j ∈ (Finset.univ : Finset (Fin 3)),
        DifferentiableAt ℝ (fun y : R3 =>
          fderiv ℝ (fun z : R3 => fderiv ℝ Ψ z (FiniteTimeSingularity.e j)) y
            (FiniteTimeSingularity.e j)) x :=
      fun j _ => ((hC1 (FiniteTimeSingularity.e j)).differentiable (by norm_num)).differentiableAt
    rw [fderiv_fun_sum hd]
    simp
  rw [hlt, hrt]
  exact Finset.sum_congr rfl (fun j _ => key j)

end Work.FTS.PressureOn.PoissonAux
end
-- ===== merged: Submission.Work.FTS.PressureOn.PoissonAux.laplaceTrace_radial =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The Laplacian of a radial function on `ℝ³`

The classical formula

  `Δ (g ∘ ‖·‖) (x) = g''(‖x‖) + 2 g'(‖x‖) / ‖x‖`   (`x ≠ 0`)

for the Laplacian of a radially symmetric function `x ↦ g ‖x‖` on `ℝ³`, in the form computed by the
trace `laplaceTrace` of the Hessian along the standard basis `FiniteTimeSingularity.e`.

The proof is the classical computation, split into the following pieces (all in this file):

* `hasFDerivAt_norm_ne` — the Fréchet derivative of the norm on `ℝ³` at `x ≠ 0`:
  `fderiv ℝ (‖·‖) x = ‖x‖⁻¹ • innerSL ℝ x`, obtained from `hasStrictFDerivAt_norm_sq` by the chain
  rule with `Real.sqrt`.  (Mathlib does not provide this in this explicit form.)
* `hasFDerivAt_radial_comp` — the chain rule for radially symmetric functions:
  `fderiv ℝ (fun w => G ‖w‖) x = (deriv G ‖x‖) • fderiv ℝ (‖·‖) x`.
* `laplaceTrace_radial_diag` — the diagonal entries of the Hessian,
  `∂ᵢ∂ᵢ (g ∘ ‖·‖) (x) = g'(‖x‖)/‖x‖ + (g''(‖x‖)‖x‖⁻² - g'(‖x‖)‖x‖⁻³)·(xᵢ)²`,
  computed by the product rule from the two lemmas above.
* the assembly `laplaceTrace_radial`, using `∑ i, (xᵢ)² = ‖x‖²`.
-/

open FiniteTimeSingularity Set MeasureTheory Metric
open scoped Topology RealInnerProductSpace

namespace Work.FTS.PressureOn.PoissonAux

/-- The Fréchet derivative of the norm of `ℝ³` at a nonzero point: `fderiv ℝ (‖·‖) x` is the
continuous linear functional `v ↦ ‖x‖⁻¹ * ⟪x, v⟫`, i.e. `‖x‖⁻¹ • innerSL ℝ x`. -/
lemma hasFDerivAt_norm_ne {x : R3} (hx : x ≠ 0) :
    HasFDerivAt (fun y : R3 => ‖y‖) ((‖x‖)⁻¹ • innerSL ℝ x) x := by
  have hnorm_ne : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have h1 : HasFDerivAt (fun y : R3 => ‖y‖ ^ 2) ((2 : ℝ) • innerSL ℝ x) x := by
    have h := (hasStrictFDerivAt_norm_sq x).hasFDerivAt
    rwa [← ofNat_smul_eq_nsmul (R := ℝ) 2 (innerSL ℝ x)] at h
  have h2 := h1.sqrt (pow_ne_zero 2 hnorm_ne)
  have hfun : (fun y : R3 => √(‖y‖ ^ 2)) = fun y : R3 => ‖y‖ := by
    funext y
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg y)]
  rw [hfun] at h2
  convert h2 using 1
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg x)]
  rw [show (1 / (2 * ‖x‖)) • ((2 : ℝ) • (innerSL ℝ x))
        = ((1 / (2 * ‖x‖)) * 2) • (innerSL ℝ x) from smul_smul (M := ℝ) _ _ _]
  have hc : (1 / (2 * ‖x‖)) * 2 = (‖x‖)⁻¹ := by field_simp
  rw [hc]

/-- The chain rule for radially symmetric functions on `ℝ³`: if `G` has derivative `c` at `‖x‖`
with `x ≠ 0`, then `w ↦ G ‖w‖` has Fréchet derivative `c • fderiv ℝ (‖·‖) x` at `x`. -/
lemma hasFDerivAt_radial_comp {G : ℝ → ℝ} {c : ℝ} {x : R3} (hx : x ≠ 0)
    (hG : HasDerivAt G c ‖x‖) :
    HasFDerivAt (fun w : R3 => G ‖w‖) (c • ((‖x‖)⁻¹ • innerSL ℝ x)) x := by
  have h := hG.comp_hasFDerivAt x (hasFDerivAt_norm_ne hx)
  simpa only [Function.comp_def] using h



end Work.FTS.PressureOn.PoissonAux
end
-- ===== merged: Submission.Work.FTS.PressureOn.PoissonAux.mk_profile =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter Topology Metric
open scoped Topology ENNReal NNReal

set_option autoImplicit false

namespace Work.FTS.PressureOn.PoissonAux

/-! ## Smoothness -/

theorem mk_contDiff_rhoProfile (ε : ℝ) (n : ℕ∞) : ContDiff ℝ n (rhoProfile ε) := by
  have h : ContDiff ℝ n (fun r : ℝ => radialCut (r ^ 2 / ε ^ 2)) :=
    (contDiff_radialCut n).comp ((contDiff_id.pow 2).div_const (ε ^ 2))
  exact contDiff_const.sub h

theorem mk_continuous_deriv_deriv_rhoProfile (ε : ℝ) :
    Continuous (deriv (deriv (rhoProfile ε))) := by
  have h : ContDiff ℝ 2 (rhoProfile ε) := mk_contDiff_rhoProfile ε 2
  have h2 : ContDiff ℝ 0 (deriv (deriv (rhoProfile ε))) := (h.deriv').deriv'
  exact h2.continuous

/-! ## Local constancy off the transition annulus -/

theorem mk_rhoProfile_eventuallyEq_zero {ε r : ℝ} (hε : 0 < ε) (hr : |r| < ε) :
    rhoProfile ε =ᶠ[𝓝 r] fun _ => (0 : ℝ) := by
  have hpos : 0 < ε - |r| := by linarith
  filter_upwards [Metric.ball_mem_nhds r hpos] with s hs
  rw [Metric.mem_ball, Real.dist_eq] at hs
  have hs' : |s| < ε := by
    have h1 : |s - r| < ε - |r| := hs
    have h2 : |s| ≤ |s - r| + |r| := by
      calc |s| = |s - r + r| := by ring_nf
        _ ≤ |s - r| + |r| := abs_add_le (s - r) r
    linarith
  have hs2 : s ^ 2 ≤ ε ^ 2 := by
    have h3 : s ^ 2 = |s| ^ 2 := (sq_abs s).symm
    have h4 : ε ^ 2 = |ε| ^ 2 := (sq_abs ε).symm
    rw [h3, h4, abs_of_pos hε]
    nlinarith [abs_nonneg s, abs_lt.mp hs']
  rw [rhoProfile_apply, radialCut_eq_one (by rw [div_le_one (by positivity)]; exact hs2), sub_self]

theorem mk_rhoProfile_eventuallyEq_one {ε r : ℝ} (hε : 0 < ε)
    (hr : Real.sqrt 2 * ε < |r|) : rhoProfile ε =ᶠ[𝓝 r] fun _ => (1 : ℝ) := by
  have hpos : 0 < |r| - Real.sqrt 2 * ε := by linarith
  filter_upwards [Metric.ball_mem_nhds r hpos] with s hs
  rw [Metric.mem_ball, Real.dist_eq] at hs
  have hs' : Real.sqrt 2 * ε < |s| := by
    have h1 : |s - r| < |r| - Real.sqrt 2 * ε := hs
    have h2 : |r| - |s| ≤ |s - r| := by
      rw [abs_sub_comm s r]
      exact abs_sub_abs_le_abs_sub r s
    linarith
  have h2 : 2 * ε ^ 2 ≤ s ^ 2 := by
    have h3 : 0 ≤ Real.sqrt 2 * ε := by positivity
    have h4 : (Real.sqrt 2 * ε) ^ 2 < |s| ^ 2 := by nlinarith [abs_nonneg s]
    have h5 : (Real.sqrt 2 * ε) ^ 2 = 2 * ε ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    have h6 : s ^ 2 = |s| ^ 2 := (sq_abs s).symm
    rw [h6]
    linarith
  rw [rhoProfile_apply, radialCut_eq_zero (by rw [le_div_iff₀ (by positivity)]; exact h2), sub_zero]

/-- The second derivative of the profile vanishes off the transition annulus. -/
theorem mk_deriv_deriv_rhoProfile_eq_zero {ε r : ℝ} (hε : 0 < ε)
    (hr : |r| < ε ∨ Real.sqrt 2 * ε < |r|) :
    deriv (deriv (rhoProfile ε)) r = 0 := by
  rcases hr with hr | hr
  · have h1 : deriv (rhoProfile ε) =ᶠ[𝓝 r] fun _ : ℝ => (0 : ℝ) := by
      have h := (mk_rhoProfile_eventuallyEq_zero hε hr).deriv
      rwa [deriv_const'] at h
    rw [h1.deriv_eq]
    exact deriv_const r 0
  · have h1 : deriv (rhoProfile ε) =ᶠ[𝓝 r] fun _ : ℝ => (0 : ℝ) := by
      have h := (mk_rhoProfile_eventuallyEq_one hε hr).deriv
      rwa [deriv_const'] at h
    rw [h1.deriv_eq]
    exact deriv_const r 0

/-! ## The scaling identity `ρ_ε''(r) = ρ_1''(r/ε)/ε²` -/



/-! ## The uniform bound on the second derivative -/




/-! ## The total mass `∫_0^∞ r ρ_ε''(r) dr = -1` -/


end Work.FTS.PressureOn.PoissonAux
end
-- ===== merged: Submission.Work.FTS.PressureOn.biotSavart_decay =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn

/-- **Decay of the Biot–Savart field of a bounded, compactly supported vorticity.**
For `g` bounded by `M ≥ 0` and supported in the closed ball of radius `R`, the Newtonian-potential
Biot–Savart field decays like `(1 + ‖x‖²)⁻¹` at infinity:

  `∃ C ≥ 0, ∀ x, ‖biotSavart g x‖ ≤ C / (1 + ‖x‖²)`.

The proof glues the two unconditional Biot–Savart estimates:
`Work.LWP.BiotSavart.norm_biotSavart_near` (`‖x‖ ≤ 2R` gives the uniform bound `3 M R`) and
`Work.LWP.BiotSavart.farField_decay_const` (`2R ≤ ‖x‖` gives `(4/3) M R³ / ‖x‖²`).
Since the statement does not assume `0 ≤ R`, the radius is first replaced by `max R 0` — this only
enlarges the support, so both estimates still apply, and for `R < 0` the ball `closedBall 0 R` is
empty and the estimate degenerates to `0`. -/
theorem biotSavart_decay {g : R3 → R3} {R M : ℝ} (hM : 0 ≤ M)
    (hg : ∀ y, ‖g y‖ ≤ M) (hsupp : ∀ y, g y ≠ 0 → y ∈ Metric.closedBall 0 R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : R3, ‖Work.LWP.biotSavart g x‖ ≤ C / (1 + ‖x‖ ^ 2) := by
  -- Step 0: replace the radius `R` by `R' = max R 0 ≥ 0`; this only enlarges the support.
  set R' : ℝ := max R 0 with hR'def
  have hR' : 0 ≤ R' := le_max_right R 0
  have hRR' : R ≤ R' := le_max_left R 0
  have hsupp' : ∀ y, g y ≠ 0 → y ∈ Metric.closedBall (0 : R3) R' :=
    fun y hy => Metric.closedBall_subset_closedBall hRR' (hsupp y hy)
  refine ⟨3 * M * R' * (1 + 4 * R' ^ 2), ?_, ?_⟩
  · -- nonnegativity of the constant
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hM) hR')
      (by positivity)
  · intro x
    have hden : (0 : ℝ) < 1 + ‖x‖ ^ 2 := by positivity
    rcases lt_or_ge (2 * R') ‖x‖ with hx | hx
    · -- **far field**: `2R' ≤ ‖x‖`, where the field decays like `‖x‖⁻²`
      have hx' : 2 * R' ≤ ‖x‖ := le_of_lt hx
      have hn : (0 : ℝ) < ‖x‖ := by linarith
      have hb := Work.LWP.BiotSavart.farField_decay_const hR' hM hg hsupp' x hx'
      refine hb.trans ?_
      rw [div_le_div_iff₀ (pow_pos hn 2) hden]
      have hsq : 4 * R' ^ 2 ≤ ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
      have h1 : (4 / 3) * R' ^ 2 ≤ 3 * ‖x‖ ^ 2 := by nlinarith [hsq]
      have h2 : (4 / 3) * R' ^ 2 * ‖x‖ ^ 2 ≤ 12 * R' ^ 2 * ‖x‖ ^ 2 := by
        nlinarith [mul_nonneg (sq_nonneg R') (sq_nonneg ‖x‖)]
      have hmain : (4 / 3) * R' ^ 2 * (1 + ‖x‖ ^ 2)
          ≤ 3 * (1 + 4 * R' ^ 2) * ‖x‖ ^ 2 := by linarith
      have hMR : (0 : ℝ) ≤ M * R' := mul_nonneg hM hR'
      have hfin := mul_le_mul_of_nonneg_left hmain hMR
      nlinarith [hfin]
    · -- **near field**: `‖x‖ ≤ 2R'`, where the field is bounded by `3 M R'`
      have hb := Work.LWP.BiotSavart.norm_biotSavart_near hR' hM hg hsupp' hx
      have hsq : ‖x‖ ^ 2 ≤ 4 * R' ^ 2 := by nlinarith [norm_nonneg x]
      have hMR : (0 : ℝ) ≤ 3 * M * R' := mul_nonneg (mul_nonneg (by norm_num) hM) hR'
      refine hb.trans ?_
      rw [le_div_iff₀ hden]
      exact mul_le_mul_of_nonneg_left (by linarith) hMR

end Work.FTS.PressureOn
end
-- ===== merged: Submission.Work.FTS.PressureOn.continuous_timeDeriv_pressurePotential =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter Metric Bornology
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.PressureOn

/-! ## Elementary facts about the kernel `∇Nfund` -/

/-- `(a³)⁻¹ · a ≤ (a²)⁻¹` for `a ≥ 0`; equality holds for `a > 0`. -/
private lemma inv_pow_three_mul_le (a : ℝ) (ha : 0 ≤ a) : (a ^ 3)⁻¹ * a ≤ (a ^ 2)⁻¹ := by
  rcases eq_or_lt_of_le ha with h | h
  · rw [← h]; norm_num
  · refine le_of_eq ?_
    field_simp

/-- Pointwise size of the gradient of the fundamental solution:
`‖nablaNfund z‖ ≤ (4π)⁻¹‖z‖⁻²` (the value at `z = 0` is `0`, so the inequality holds there too). -/
private lemma norm_nablaNfund_le (z : R3) :
    ‖nablaNfund z‖ ≤ (4 * Real.pi)⁻¹ * (‖z‖ ^ 2)⁻¹ := by
  have h : ‖nablaNfund z‖ = ‖newtonGrad z‖ := by
    rw [nablaNfund_eq_neg_newtonGrad, norm_neg]
  rw [h, norm_newtonGrad]
  have h2 : (‖z‖ ^ 3)⁻¹ * ‖z‖ ≤ (‖z‖ ^ 2)⁻¹ := inv_pow_three_mul_le ‖z‖ (norm_nonneg z)
  calc (4 * Real.pi)⁻¹ * (‖z‖ ^ 3)⁻¹ * ‖z‖
      = (4 * Real.pi)⁻¹ * ((‖z‖ ^ 3)⁻¹ * ‖z‖) := by ring
    _ ≤ (4 * Real.pi)⁻¹ * (‖z‖ ^ 2)⁻¹ := mul_le_mul_of_nonneg_left h2 (by positivity)

/-- The kernel is Borel measurable. -/
private lemma measurable_nablaNfund_prv : Measurable (fun z : R3 => nablaNfund z) := by
  unfold nablaNfund
  have h1 : Measurable (fun z : R3 => (4 * Real.pi)⁻¹ * (‖z‖ ^ 3)⁻¹) := by fun_prop
  exact h1.smul measurable_id

/-! ## The change of variables `z = x - y` -/

/-- **The kernel integral is a convolution**: shifting the integration variable `y ↦ z = x - y`
(which preserves Lebesgue measure) turns the defining form of the potential into its convolution
form. -/
theorem integral_shift_nablaNfund (g : R3 → R3) (x : R3) :
    ∫ y, inner ℝ (nablaNfund (x - y)) (g y) = ∫ z, inner ℝ (nablaNfund z) (g (x - z)) := by
  set Φ : R3 → ℝ := fun z => inner ℝ (nablaNfund z) (g (x - z)) with hΦ
  have h1 : (fun y => inner ℝ (nablaNfund (x - y)) (g y)) = fun y => Φ (-(y - x)) := by
    funext y
    simp only [hΦ, neg_sub, sub_sub_cancel]
  rw [h1, MeasureTheory.integral_sub_right_eq_self (fun w => Φ (-w)) x,
    MeasureTheory.integral_neg_eq_self Φ volume]

/-! ## Joint continuity in the shifted form -/

/-- **Joint continuity of the shifted `∇Nfund`-integral.**  For a jointly continuous
`g : ℝ³ → ℝ → ℝ³` whose spatial support is locally uniformly bounded in time, the map
`(x, t) ↦ ∫ z, ⟪∇Nfund z, g (x - z) t⟫` is continuous on `ℝ³ × ℝ`.

The proof is dominated convergence: near a fixed `(x₀, t₀)` the integrand is dominated by the
integrable model function `z ↦ (4π)⁻¹ M ‖z‖⁻² 1_{B(0, R+‖x₀‖+1)}(z)`, where `R` is the uniform
support radius and `M` a uniform bound for `g` on the strip `B(0,R) × [t₀-1/2, t₀+1/2]`. -/
theorem continuous_shifted_integral_joint {g : R3 → ℝ → R3}
    (hg : Continuous fun p : R3 × ℝ => g p.1 p.2)
    (hsupp : ∀ t : ℝ, ∃ R, ∀ s ∈ Set.Ioo (t - 1) (t + 1), ∀ x, g x s ≠ 0 → ‖x‖ ≤ R) :
    Continuous fun p : R3 × ℝ => ∫ z, inner ℝ (nablaNfund z) (g (p.1 - z) p.2) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨x₀, t₀⟩
  obtain ⟨R, hR⟩ := hsupp t₀
  obtain ⟨M, hM0, hM⟩ := exists_bound_strip hg R t₀
  have hInt : Integrable (fun z : R3 => (4 * Real.pi)⁻¹ * M *
      ((‖z‖ ^ 2)⁻¹ *
        (Metric.closedBall (0 : R3) (R + ‖x₀‖ + 1)).indicator (fun _ => (1 : ℝ)) z)) volume := by
    have h1 := integrable_inv_normSq_indicator_closedBall (R + ‖x₀‖ + 1)
    have h2 : (fun z : R3 => (4 * Real.pi)⁻¹ * M *
          ((‖z‖ ^ 2)⁻¹ *
            (Metric.closedBall (0 : R3) (R + ‖x₀‖ + 1)).indicator (fun _ => (1 : ℝ)) z))
        = fun z : R3 => ((4 * Real.pi)⁻¹ * M) *
          ((‖z‖ ^ 2)⁻¹ *
            (Metric.closedBall (0 : R3) (R + ‖x₀‖ + 1)).indicator (fun _ => (1 : ℝ)) z) := by
      funext z; ring
    rw [h2]
    exact h1.const_mul _
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence (μ := volume)
    (l := 𝓝 (x₀, t₀))
    (fun z : R3 => (4 * Real.pi)⁻¹ * M * ((‖z‖ ^ 2)⁻¹ *
      (Metric.closedBall (0 : R3) (R + ‖x₀‖ + 1)).indicator (fun _ => (1 : ℝ)) z)) ?_ ?_ hInt ?_
  · -- a.e. strong measurability of the integrand, for every `(x,t)`
    filter_upwards with p
    refine Measurable.aestronglyMeasurable ?_
    exact measurable_nablaNfund_prv.inner (hg.measurable.comp
      ((continuous_const.sub continuous_id).prodMk continuous_const).measurable)
  · -- pointwise domination by the fixed integrable model function
    filter_upwards [Metric.ball_mem_nhds (x₀, t₀) (by norm_num : (0 : ℝ) < 1 / 2)] with p hp
    refine Eventually.of_forall fun z => ?_
    have hd : max (dist p.1 x₀) (dist p.2 t₀) < 1 / 2 := by
      rwa [Metric.mem_ball, Prod.dist_eq] at hp
    have hp1 : ‖p.1 - x₀‖ < 1 / 2 := by
      have h : dist p.1 x₀ < 1 / 2 := lt_of_le_of_lt (le_max_left _ _) hd
      rwa [dist_eq_norm] at h
    have hp2lt : |p.2 - t₀| < 1 / 2 := by
      have h : dist p.2 t₀ < 1 / 2 := lt_of_le_of_lt (le_max_right _ _) hd
      rwa [Real.dist_eq] at h
    obtain ⟨hp2lo, hp2hi⟩ := abs_lt.mp hp2lt
    have hp2Ioo : p.2 ∈ Set.Ioo (t₀ - 1) (t₀ + 1) := ⟨by linarith, by linarith⟩
    have hp2Icc : p.2 ∈ Set.Icc (t₀ - 1 / 2) (t₀ + 1 / 2) := ⟨by linarith, by linarith⟩
    by_cases hz : g (p.1 - z) p.2 = 0
    · rw [hz, inner_zero_right, norm_zero]
      exact mul_nonneg (mul_nonneg (by positivity) hM0)
        (mul_nonneg (by positivity) (Set.indicator_nonneg (fun _ _ => zero_le_one) z))
    · -- `g (p.1 - z) p.2 ≠ 0` puts `z` in a fixed ball
      have hzR : ‖p.1 - z‖ ≤ R := hR p.2 hp2Ioo (p.1 - z) hz
      have hx1 : ‖p.1‖ ≤ ‖x₀‖ + 1 / 2 := by
        have h2 : ‖p.1‖ = ‖(p.1 - x₀) + x₀‖ := by rw [sub_add_cancel]
        rw [h2]
        linarith [norm_add_le (p.1 - x₀) x₀]
      have hzx : ‖z‖ ≤ R + ‖x₀‖ + 1 := by
        have h2 : ‖z‖ = ‖(z - p.1) + p.1‖ := by rw [sub_add_cancel]
        rw [h2]
        have h3 : ‖z - p.1‖ = ‖p.1 - z‖ := norm_sub_rev z p.1
        linarith [norm_add_le (z - p.1) p.1]
      have hzball : z ∈ Metric.closedBall (0 : R3) (R + ‖x₀‖ + 1) := by
        rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]; exact hzx
      have hmem : p.1 - z ∈ Metric.closedBall (0 : R3) R := by
        rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]; exact hzR
      rw [Set.indicator_of_mem hzball, mul_one]
      calc ‖inner ℝ (nablaNfund z) (g (p.1 - z) p.2)‖
          ≤ ‖nablaNfund z‖ * ‖g (p.1 - z) p.2‖ := norm_inner_le_norm _ _
        _ ≤ ((4 * Real.pi)⁻¹ * (‖z‖ ^ 2)⁻¹) * M :=
            mul_le_mul (norm_nablaNfund_le z) (hM (p.1 - z) hmem p.2 hp2Icc)
              (norm_nonneg _) (by positivity)
        _ = (4 * Real.pi)⁻¹ * M * (‖z‖ ^ 2)⁻¹ := by ring
  · -- pointwise convergence of the integrand, at every fixed `z`
    filter_upwards with z
    exact (continuous_const.inner (hg.comp
      ((continuous_fst.sub continuous_const).prodMk continuous_snd))).continuousAt

/-- **Joint continuity of the pressure potential of a locally uniformly supported field.**  For a
jointly continuous `g : ℝ³ → ℝ → ℝ³` whose spatial support is locally uniform in time, the map
`p ↦ pressurePotential (g · p.2) p.1` is continuous on `ℝ³ × ℝ`.

This is the general form of the continuity statement needed for the pressure reconstruction of
`PressureOn.Defs`; it is `continuous_shifted_integral_joint` transported back to the defining
(unshifted) form of `pressurePotential` by `integral_shift_nablaNfund`. -/
theorem continuous_pressurePotential_joint_of_supported {g : R3 → ℝ → R3}
    (hg : Continuous fun p : R3 × ℝ => g p.1 p.2)
    (hsupp : ∀ t : ℝ, ∃ R, ∀ s ∈ Set.Ioo (t - 1) (t + 1), ∀ x, g x s ≠ 0 → ‖x‖ ≤ R) :
    Continuous fun p : R3 × ℝ => pressurePotential (fun y => g y p.2) p.1 := by
  have hcont := continuous_shifted_integral_joint hg hsupp
  have hfun : (fun p : R3 × ℝ => pressurePotential (fun y => g y p.2) p.1)
      = fun p : R3 × ℝ => -(∫ z, inner ℝ (nablaNfund z) (g (p.1 - z) p.2)) := by
    funext p
    rw [pressurePotential_apply]
    congr 1
    exact integral_shift_nablaNfund (fun y => g y p.2) p.1
  rw [hfun]
  exact hcont.neg

/-! ## The target theorem -/


end Work.FTS.PressureOn
end
-- ===== merged: Submission.Work.FTS.PressureOn.hasCompactSupport_transport =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Compact support is preserved by the transport to the coordinate space

`transport G x = WithLp.ofLp (G (WithLp.toLp 2 x))` is `G` read through the linear isometry
`toLpCLE : (Fin 3 → ℝ) ≃L[ℝ] ℝ³` (`⇑toLpCLE = WithLp.toLp 2`, whose inverse is
`ofLpCLM = WithLp.ofLp`).  Consequently `transport G = toLpCLE.symm ∘ G ∘ toLpCLE`, i.e. `G`
conjugated by a homeomorphism which is a linear isometry onto its image, and

* `Function.support (transport G) = toLpCLE ⁻¹' Function.support G`
  (the inverse is injective and maps `0` to `0`), hence
* `tsupport (transport G) = toLpCLE ⁻¹' tsupport G`
  (a homeomorphism pulls closures back to closures),

so compactness of the support of `G` transfers to the support of `transport G`.

This is the bookkeeping step that lets the divergence theorem of
`Submission.Work.FTS.PressureOn.integral_div_eq_zero_of_hasFDerivAt` — which is stated for the
transported field on `Fin 3 → ℝ` — be fed with the compact support of the physical field on `ℝ³`.
-/

open FiniteTimeSingularity Set

namespace Work.FTS.PressureOn




end Work.FTS.PressureOn
end
-- ===== merged: Submission.Work.FTS.PressureOn.integrable_mul_div =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `ψ · div ω` is integrable for compactly supported `ψ ∈ C¹` and locally integrable `Dω`

`Work.FTS.PressureOn.integrable_mul_div`: if `ω : ℝ³ → ℝ³` has *locally integrable* Jacobian
`Dω : ℝ³ → (ℝ³ →L[ℝ] ℝ³)` and `ψ : ℝ³ → ℝ` is `C¹` with compact support, then
`y ↦ ψ y * div ω y` is integrable.

This is the integrability input of the pressure reconstruction: the pressure potential is defined
by convolving the Lamb vector with the Newtonian kernel and multiplying by a cutoff `ψ`; the only
measure-theoretic ingredient is that a compactly supported continuous function times a locally
integrable function is integrable (Mathlib's
`MeasureTheory.LocallyIntegrable.integrable_smul_left_of_hasCompactSupport`), applied to the
divergence `div ω = trace (Dω)`.  The divergence inherits local integrability from `Dω` because
`div ω = ∑ᵢ (Dω · eᵢ)ᵢ` is a finite sum of compositions of `Dω` with the continuous linear maps
`L ↦ (L eᵢ)ᵢ` (`ContinuousLinearMap.locallyIntegrableOn_comp`).

The trace-in-the-standard-basis identity `div_eq_sum_single` is taken from the sibling module
`Submission/Work/FTS/PressureOn/integral_div_eq_zero_of_hasFDerivAt.lean`.
-/

open MeasureTheory Filter

namespace Work.FTS.PressureOn

/-- The `i`-th diagonal entry of the Jacobian, `y ↦ (Dω y)(eᵢ)ᵢ`, is locally integrable whenever
`Dω` is: it is the composite of `Dω` with the continuous linear map `L ↦ (L eᵢ)ᵢ`, the
composition of the evaluation `L ↦ L eᵢ` with the coordinate projection `PiLp.proj`. -/
lemma locallyIntegrable_diag (ω : R3 → R3)
    (hωint : MeasureTheory.LocallyIntegrable (fun x => fderiv ℝ ω x)) (i : Fin 3) :
    MeasureTheory.LocallyIntegrable (fun y : R3 =>
      (fderiv ℝ ω y) (WithLp.toLp 2 (Pi.single i (1 : ℝ))) i) := by
  set v : R3 := WithLp.toLp 2 (Pi.single i (1 : ℝ)) with hv
  set hL : (R3 →L[ℝ] R3) →L[ℝ] ℝ :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i).comp
      (ContinuousLinearMap.apply ℝ R3 v) with hLdef
  have key : (fun y : R3 => (fderiv ℝ ω y) v i)
      = ⇑hL ∘ (fun x => fderiv ℝ ω x) := by
    funext y
    simp only [Function.comp_apply, hLdef, ContinuousLinearMap.coe_comp,
      ContinuousLinearMap.apply_apply, PiLp.proj_apply]
  rw [key]
  exact MeasureTheory.locallyIntegrableOn_univ.mp
    (hL.locallyIntegrableOn_comp (MeasureTheory.locallyIntegrableOn_univ.mpr hωint))

/-- The diagonal-part sum `y ↦ ∑ᵢ (Dω y)(eᵢ)ᵢ = div ω y` is locally integrable whenever `Dω`
is: a finite sum of the locally integrable diagonal entries (Mathlib's
`MeasureTheory.locallyIntegrable_finsetSum`), rewritten with the trace identity
`div_eq_sum_single`. -/
lemma locallyIntegrable_div (ω : R3 → R3)
    (hωint : MeasureTheory.LocallyIntegrable (fun x => fderiv ℝ ω x)) :
    MeasureTheory.LocallyIntegrable (fun y : R3 => FiniteTimeSingularity.div ω y) := by
  have hsum : MeasureTheory.LocallyIntegrable (fun y : R3 =>
      ∑ i : Fin 3, (fderiv ℝ ω y) (WithLp.toLp 2 (Pi.single i (1 : ℝ))) i) :=
    MeasureTheory.locallyIntegrable_finsetSum (Finset.univ : Finset (Fin 3))
      (f := fun i y => (fderiv ℝ ω y) (WithLp.toLp 2 (Pi.single i (1 : ℝ))) i)
      (fun i _ => locallyIntegrable_diag ω hωint i)
  refine hsum.congr (Filter.Eventually.of_forall fun y => ?_)
  exact (div_eq_sum_single ω y).symm

theorem integrable_mul_div {ω : Work.FTS.PressureOn.R3 → Work.FTS.PressureOn.R3}
    {ψ : Work.FTS.PressureOn.R3 → ℝ}
    (hωint : MeasureTheory.LocallyIntegrable (fun x => fderiv ℝ ω x))
    (hψ : ContDiff ℝ 1 ψ) (hψcs : HasCompactSupport ψ) :
    MeasureTheory.Integrable (fun y => ψ y * FiniteTimeSingularity.div ω y) := by
  have h := (locallyIntegrable_div ω hωint).integrable_smul_left_of_hasCompactSupport
    hψ.continuous hψcs
  simpa only [smul_eq_mul] using h

end Work.FTS.PressureOn
end
-- ===== merged: Submission.Work.FTS.PressureOn.lipschitzTimeOmegaIcc =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Topology

namespace Work.FTS.PressureOn

/-- **Lipschitz (hence `α`-Hölder, `α ≤ 1`) dependence of the vorticity on time, on `[0,S]`.**
(piece of `tendsto_timeDeriv_physVel`.)

If `ω · s` is supported in a fixed ball for `s ∈ Icc 0 S` with `S ∈ (0,T)`, the right derivative
`∂ₜω` is jointly continuous on `ℝ³ × [0,T)`, `∂ₜω` is the right derivative of `ω` along `Ici s`
at every `s ∈ [0,T)`, and every curve `ω x ·` is continuous on `[0,S]`, then there is a constant
`C ≥ 0` with `‖ω x s - ω x t‖ ≤ C |s - t|` for all `x` and all `s, t ∈ [0,S]`.

Recipe:
* a *uniform* bound `∃ C ≥ 0, ∀ y, ∀ s ∈ Ico 0 S, ‖timeDeriv ω y s‖ ≤ C`: on the compact set
  `Metric.closedBall 0 (max R 0) ×ˢ Icc 0 S ⊆ univ ×ˢ Ico 0 T` use
  `IsCompact.exists_bound_of_continuousOn` and `hcontDt`; off the support ball (`‖y‖ > max R 0`)
  the slice `ω y ·` is identically `0` on `[0,S]`, so for `s ∈ Ico 0 S` the function is locally
  `0` on `Ici s` (there is room `(s, (s+S)/2) ⊆ [0,S]`), whence `HasDerivWithinAt (ω y) 0 (Ici s) s`
  (`Filter.EventuallyEq.hasDerivWithinAt_iff` + `hasDerivWithinAt_const`), and uniqueness of the
  within-derivative on the uniquely-differentiable set `Ici s` (`uniqueDiffWithinAt_Ici` together
  with `hderiv`) gives `timeDeriv ω y s = 0`.  (`HasFDerivWithinAt.unique`.)
* the Lipschitz bound then follows from `Work.FTS.PressureOn.lipschitz_time_of_hasDerivWithinAt`
  (same directory, sorry-free) applied with `T := S`, `hcont := hcontω`, `hderiv` restricted to
  `Ico 0 S ⊆ Ico 0 T`, and the bound above.

Note the bound at `s = 0` for `‖y‖ > max R 0` genuinely needs the uniqueness argument (`Ici 0` is
not a two-sided neighbourhood of `0`), which is why the compactness
`Work.StabilityFar.Decay.timeDeriv_eq_zero_of_notMem_closedBall` is *not* directly applicable. -/
theorem lipschitzTimeOmegaIcc {ω : R3 → ℝ → R3} {T S : ℝ}
    (hS : S ∈ Set.Ioo 0 T)
    (hsupp : ∃ R, ∀ s ∈ Set.Icc 0 S, ∀ x, ω x s ≠ 0 → ‖x‖ ≤ R)
    (hcontDt : ContinuousOn (fun q : R3 × ℝ => FiniteTimeSingularity.timeDeriv ω q.1 q.2)
      (Set.univ ×ˢ Set.Ico 0 T))
    (hderiv : ∀ x, ∀ s ∈ Set.Ico 0 T,
      HasDerivWithinAt (ω x) (FiniteTimeSingularity.timeDeriv ω x s) (Set.Ici s) s)
    (hcontω : ∀ x, ContinuousOn (fun s => ω x s) (Set.Icc 0 S)) :
    ∃ C, 0 ≤ C ∧ ∀ x, ∀ s ∈ Set.Icc 0 S, ∀ t ∈ Set.Icc 0 S,
      ‖ω x s - ω x t‖ ≤ C * |s - t| := by
  obtain ⟨R, hR⟩ := hsupp
  -- `[0,S]` sits inside `[0,T)`
  have hIcc_sub : Set.Icc (0 : ℝ) S ⊆ Set.Ico 0 T :=
    fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 hS.2⟩
  have hIco_sub : Set.Ico (0 : ℝ) S ⊆ Set.Ico 0 T :=
    fun x hx => ⟨hx.1, lt_of_lt_of_le hx.2 (le_of_lt hS.2)⟩
  -- the compact box `closedBall 0 (max R 0) × [0,S]` lies in the domain of `hcontDt`
  have hKcompact : IsCompact (Metric.closedBall (0 : R3) (max R 0) ×ˢ Set.Icc (0 : ℝ) S) :=
    (isCompact_closedBall 0 (max R 0)).prod isCompact_Icc
  have hKcont : ContinuousOn (fun q : R3 × ℝ => FiniteTimeSingularity.timeDeriv ω q.1 q.2)
      (Metric.closedBall (0 : R3) (max R 0) ×ˢ Set.Icc (0 : ℝ) S) :=
    hcontDt.mono (Set.prod_mono (Set.subset_univ _) hIcc_sub)
  obtain ⟨C₀, hC₀⟩ := hKcompact.exists_bound_of_continuousOn hKcont
  refine ⟨max C₀ 0, le_max_right _ _, ?_⟩
  -- uniform bound for `∂ₜω` on `[0,S]`
  have hbound : ∀ y, ∀ s ∈ Set.Ico 0 S,
      ‖FiniteTimeSingularity.timeDeriv ω y s‖ ≤ max C₀ 0 := by
    intro y s hs
    by_cases hy : ‖y‖ ≤ max R 0
    · have hmem : (y, s) ∈ Metric.closedBall (0 : R3) (max R 0) ×ˢ Set.Icc (0 : ℝ) S :=
        ⟨by simpa [Metric.mem_closedBall, dist_eq_norm] using hy, ⟨hs.1, le_of_lt hs.2⟩⟩
      exact le_trans (hC₀ (y, s) hmem) (le_max_left _ _)
    · -- off the support ball the slice is identically `0` on `[0,S]`, hence so is its derivative
      rw [not_le] at hy
      have hz : ∀ s' ∈ Set.Icc (0 : ℝ) S, ω y s' = 0 := by
        intro s' hs'
        by_contra hne
        exact absurd (hR s' hs' y hne) (not_le.mpr (lt_of_le_of_lt (le_max_left R 0) hy))
      have hzero : FiniteTimeSingularity.timeDeriv ω y s = 0 := by
        have hd1 : HasDerivWithinAt (ω y) (FiniteTimeSingularity.timeDeriv ω y s)
            (Set.Ici s) s := hderiv y s (hIco_sub hs)
        -- `ω y` agrees with `0` on a relative neighbourhood of `s` in `Ici s`
        have hmem : Set.Ici s ∩ Set.Iio S ∈ 𝓝[Set.Ici s] s := by
          rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
          exact ⟨Set.Iio S, Iio_mem_nhds hs.2, fun x hx => ⟨hx.2, hx.1⟩⟩
        have hsub : Set.EqOn (fun x => ω y x) (fun _ => (0 : R3)) (Set.Ici s ∩ Set.Iio S) :=
          fun x hx => hz x ⟨le_trans hs.1 hx.1, le_of_lt hx.2⟩
        have hev : (fun x => ω y x) =ᶠ[𝓝[Set.Ici s] s] (fun _ => (0 : R3)) :=
          Filter.eventuallyEq_of_mem hmem hsub
        have hd2 : HasDerivWithinAt (ω y) 0 (Set.Ici s) s :=
          (hev.hasDerivWithinAt_iff_of_mem (le_refl s)).mpr
            (hasDerivWithinAt_const s (Set.Ici s) (0 : R3))
        -- uniqueness of the within-derivative on the half-line `Ici s`
        have huniq := (uniqueDiffWithinAt_Ici s).eq hd1.hasFDerivWithinAt hd2.hasFDerivWithinAt
        have hval := congrArg (fun L : ℝ →L[ℝ] R3 => L 1) huniq
        simpa using hval
      rw [hzero, norm_zero]
      exact le_max_right _ _
  exact lipschitz_time_of_hasDerivWithinAt (T := S) hcontω
    (fun y s hs => hderiv y s (hIco_sub hs)) hbound

end Work.FTS.PressureOn
end
-- ===== merged: Submission.Work.FTS.PressureOn.omegaSliceRegularPos =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn

/-- The Euclidean norm of a coordinate cross product is at most the product of the norms:
`crossProduct` (`⨯₃`) is Mathlib's bilinear form on `Fin 3 → ℝ`, and
`InnerProductGeometry.norm_ofLp_crossProduct` computes `‖a × b‖ = ‖a‖ ‖b‖ sin ∠(a,b)`. -/
private lemma norm_toLp_cross_le (a b : R3) :
    ‖WithLp.toLp 2 (crossProduct a b)‖ ≤ ‖a‖ * ‖b‖ := by
  rw [InnerProductGeometry.norm_ofLp_crossProduct a b]
  calc ‖a‖ * ‖b‖ * Real.sin (InnerProductGeometry.angle a b)
      ≤ ‖a‖ * ‖b‖ * 1 := mul_le_mul_of_nonneg_left (Real.sin_le_one _) (by positivity)
    _ = ‖a‖ * ‖b‖ := by ring

/-- **The curl is bounded by three times the derivative**:
`‖vorticity u x‖ ≤ 3 * ‖fderiv ℝ u x‖`.  This holds with no hypothesis on `u`, since Lean's
`fderiv` is the junk value `0` where `u` is not differentiable (and then so is the curl). -/
theorem norm_vorticity_le_three (u : R3 → R3) (x : R3) :
    ‖FiniteTimeSingularity.vorticity u x‖ ≤ 3 * ‖fderiv ℝ u x‖ := by
  have hsplit : FiniteTimeSingularity.vorticity u x
      = ∑ i : Fin 3,
          WithLp.toLp 2 (crossProduct (FiniteTimeSingularity.e i)
            (fderiv ℝ u x (FiniteTimeSingularity.e i))) := by
    rw [show FiniteTimeSingularity.vorticity u x
        = WithLp.toLp 2 (∑ i : Fin 3,
            crossProduct (FiniteTimeSingularity.e i)
              (fderiv ℝ u x (FiniteTimeSingularity.e i))) from rfl]
    exact WithLp.toLp_sum 2 (Fin 3 → ℝ) Finset.univ _
  have he (i : Fin 3) : ‖FiniteTimeSingularity.e i‖ = (1 : ℝ) := by
    simp [FiniteTimeSingularity.e]
  rw [hsplit]
  calc ‖∑ i : Fin 3, WithLp.toLp 2 (crossProduct (FiniteTimeSingularity.e i)
          (fderiv ℝ u x (FiniteTimeSingularity.e i)))‖
      ≤ ∑ i : Fin 3, ‖WithLp.toLp 2 (crossProduct (FiniteTimeSingularity.e i)
          (fderiv ℝ u x (FiniteTimeSingularity.e i)))‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 3,
          ‖FiniteTimeSingularity.e i‖ * ‖fderiv ℝ u x (FiniteTimeSingularity.e i)‖ :=
        Finset.sum_le_sum (fun i _ => norm_toLp_cross_le _ _)
    _ ≤ ∑ _i : Fin 3, ‖fderiv ℝ u x‖ := by
        apply Finset.sum_le_sum
        intro i _
        have h := ContinuousLinearMap.le_opNorm (fderiv ℝ u x) (FiniteTimeSingularity.e i)
        rw [he i, mul_one] at h
        calc ‖FiniteTimeSingularity.e i‖ * ‖fderiv ℝ u x (FiniteTimeSingularity.e i)‖
            ≤ 1 * (‖fderiv ℝ u x‖ * 1) :=
              mul_le_mul (le_of_eq (he i)) (by simpa using h) (norm_nonneg _) (by norm_num)
          _ = ‖fderiv ℝ u x‖ := by ring
    _ = 3 * ‖fderiv ℝ u x‖ := by simp

/-- **Positive-time regularity of the vorticity slices** (piece of `tendsto_timeDeriv_physVel`).

If the Biot–Savart velocity `u = physVel ω` is jointly `C^{1,α}` on every strip `ℝ³ × [0,S']`
with `S' < T`, and ω is the pointwise curl of `u` at every time `s ∈ [0,T)`, then on the
half-open interval `(0,S]` (with `S ∈ (0,T)`) the vorticity slices `ω · s` are uniformly bounded
and almost everywhere strongly measurable.

Recipe: take `S' ∈ Ioo 0 T` with `S < S'` (e.g. `(S+T)/2`) and `hcd := ContDiffOn ℝ 1
(uncurry (physVel ω)) (univ ×ˢ Icc 0 S')` from `hstrips`.  The second component of
`IsContDiffHolderOn` bounds `fderivWithin ℝ (uncurry (physVel ω)) (univ ×ˢ Icc 0 S')` on that
strip by some `C ≥ 0` (`Bornology.IsBounded.exists_pos_norm_le`).  For `s ∈ Ioc 0 S` and any `z`
the point `(z,s)` is an *interior* point of the strip, so `ContDiffOn.contDiffAt` +
`fderivWithin_of_mem_nhds` give the honest derivative `fderiv ℝ (uncurry (physVel ω)) (z,s)` with
the same bound, and (`fderiv_comp` + `hasFDerivAt_prodMk_left`) the derivative of the slice
`fun y => physVel ω y s` is `(fderiv ℝ (uncurry (physVel ω)) (z,s)) ∘L ContinuousLinearMap.inl`.
Hence the vorticity (a finite sum of three cross products `e i ⨯₃ (Du (e i))`) is bounded by a
multiple of `C`, and (by continuity, since `fderiv ℝ (uncurry …) (·, s)` is continuous as a
composition of a continuous map on the open strip with `z ↦ (z,s)`) each slice is continuous,
hence a.e. strongly measurable.

Possible useful templates inside the workspace: `Submission/Work/SolutionDelivery/Measurable/
continuousOn_vorticity_of_contDiffOn.lean` (`fderiv_slice_eq`, `curlOf`, `continuous_curlOf` —
but note that file assumes a two-sided *open* window `extWindow T`, whereas here the strip is
`univ ×ˢ Icc 0 S'`, so only the *interior* points `s ∈ Ioo 0 S'` are covered) and
`Submission/Work/FTS/BSIdent/Liouville/continuous_vorticity_of_contDiff.lean`
(`fun_prop` handles the continuity of `vorticity`). Do not import the `SolutionDelivery` modules
(their import closure contains `sorry`s); copy the few lines you need. -/

/-
**Remark on the route.**  The strip used below is `univ ×ˢ Icc 0 S` *itself* (the hypothesis
`hstrips` applies at `S' = S` since `S ∈ Ioo 0 T`): the target half-open interval `(0,S]` lies in
the closed strip, and the only defect of the boundary line `s = S` is that the joint derivative is
available only *within* the strip — which is precisely what `IsContDiffHolderOn` bounds and what
`fderiv_slice_eq_fderivWithin_prod` (from
`Submission.Work.FTS.PressureOn.continuousOn_time_omega_of_strips`) converts into the honest
spatial derivative of the slice.  So no auxiliary `S' > S` and no interiority argument is needed. -/
theorem omegaSliceRegularPos {α : NNReal} {ω : R3 → ℝ → R3} {T S : ℝ}
    (hS : S ∈ Set.Ioo 0 T)
    (hstrips : ∀ S' ∈ Set.Ioo 0 T,
      IsContDiffHolderOn ℝ α (Work.FTS.Physical.physVel ω).uncurry (Set.univ ×ˢ Set.Icc 0 S'))
    (hcurl : ∀ s ∈ Set.Ico 0 T, ∀ x,
      FiniteTimeSingularity.vorticity (fun z => Work.FTS.Physical.physVel ω z s) x = ω x s) :
    (∃ M, 0 ≤ M ∧ ∀ s ∈ Set.Ioc 0 S, ∀ x, ‖ω x s‖ ≤ M) ∧
      ∀ s ∈ Set.Ioc 0 S,
        MeasureTheory.AEStronglyMeasurable (fun z => ω z s) MeasureTheory.volume := by
  obtain ⟨hcd, hbdd, -⟩ := hstrips S hS
  -- A uniform bound `B` on the joint derivative, within the closed strip `ℝ³ × [0,S]`.
  obtain ⟨B, hBpos, hB⟩ := hbdd.exists_pos_norm_le
  have hBdd : ∀ p ∈ (Set.univ ×ˢ Set.Icc (0 : ℝ) S : Set (R3 × ℝ)),
      ‖fderivWithin ℝ (Function.uncurry (Work.FTS.Physical.physVel ω))
        (Set.univ ×ˢ Set.Icc (0 : ℝ) S) p‖ ≤ B :=
    fun p hp => hB _ ⟨p, hp, rfl⟩
  -- The honest spatial derivative of a slice is the spatial block of the within-derivative.
  have hslice_eq : ∀ s ∈ Set.Ioc 0 S, ∀ x : R3,
      fderiv ℝ (fun y => Work.FTS.Physical.physVel ω y s) x
        = fderivWithin ℝ (Function.uncurry (Work.FTS.Physical.physVel ω))
            (Set.univ ×ˢ Set.Icc (0 : ℝ) S) (x, s)
          ∘SL ContinuousLinearMap.inl ℝ R3 ℝ := by
    intro s hs x
    have hsIcc : s ∈ Set.Icc (0 : ℝ) S := ⟨le_of_lt hs.1, hs.2⟩
    exact fderiv_slice_eq_fderivWithin_prod (u := Work.FTS.Physical.physVel ω)
      (I := Set.Icc (0 : ℝ) S) hsIcc (hcd.contDiffWithinAt ⟨trivial, hsIcc⟩)
  constructor
  · -- Uniform bound on `(0,S]`.
    refine ⟨3 * B, by positivity, fun s hs x => ?_⟩
    have hsIcc : s ∈ Set.Icc (0 : ℝ) S := ⟨le_of_lt hs.1, hs.2⟩
    have hsT : s ∈ Set.Ico 0 T := ⟨le_of_lt hs.1, lt_of_le_of_lt hs.2 hS.2⟩
    set L : (R3 × ℝ) →L[ℝ] R3 :=
      fderivWithin ℝ (Function.uncurry (Work.FTS.Physical.physVel ω))
        (Set.univ ×ˢ Set.Icc (0 : ℝ) S) (x, s) with hL
    have hLb : ‖L‖ ≤ B := hBdd (x, s) ⟨trivial, hsIcc⟩
    -- composing with `inl` does not increase the operator norm
    have hcomp : ‖L ∘SL ContinuousLinearMap.inl ℝ R3 ℝ‖ ≤ ‖L‖ := by
      refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun v => ?_)
      calc ‖(L ∘SL ContinuousLinearMap.inl ℝ R3 ℝ) v‖ = ‖L (v, (0 : ℝ))‖ := rfl
        _ ≤ ‖L‖ * ‖(v, (0 : ℝ))‖ := ContinuousLinearMap.le_opNorm L (v, (0 : ℝ))
        _ = ‖L‖ * ‖v‖ := by simp
    have h3 : ‖fderiv ℝ (fun y => Work.FTS.Physical.physVel ω y s) x‖ ≤ B := by
      rw [hslice_eq s hs x]
      exact le_trans hcomp hLb
    calc ‖ω x s‖
        = ‖FiniteTimeSingularity.vorticity (fun z => Work.FTS.Physical.physVel ω z s) x‖ := by
          rw [hcurl s hsT x]
      _ ≤ 3 * ‖fderiv ℝ (fun y => Work.FTS.Physical.physVel ω y s) x‖ :=
          norm_vorticity_le_three _ _
      _ ≤ 3 * B := by linarith
  · -- Almost-everywhere strong measurability: each slice is continuous.
    intro s hs
    have hsIcc : s ∈ Set.Icc (0 : ℝ) S := ⟨le_of_lt hs.1, hs.2⟩
    have hsT : s ∈ Set.Ico 0 T := ⟨le_of_lt hs.1, lt_of_le_of_lt hs.2 hS.2⟩
    have hUd : UniqueDiffOn ℝ (Set.univ ×ˢ Set.Icc (0 : ℝ) S : Set (R3 × ℝ)) :=
      UniqueDiffOn.prod uniqueDiffOn_univ (uniqueDiffOn_Icc hS.1)
    have hcont : ContinuousOn (fun p : R3 × ℝ =>
        fderivWithin ℝ (Function.uncurry (Work.FTS.Physical.physVel ω))
          (Set.univ ×ˢ Set.Icc (0 : ℝ) S) p) (Set.univ ×ˢ Set.Icc (0 : ℝ) S) :=
      hcd.continuousOn_fderivWithin hUd le_rfl
    have h1 : Continuous (fun z : R3 =>
        fderivWithin ℝ (Function.uncurry (Work.FTS.Physical.physVel ω))
          (Set.univ ×ˢ Set.Icc (0 : ℝ) S) (z, s)) :=
      hcont.comp_continuous (by fun_prop) (fun _ => ⟨trivial, hsIcc⟩)
    have h2 : Continuous (fun z : R3 =>
        fderivWithin ℝ (Function.uncurry (Work.FTS.Physical.physVel ω))
          (Set.univ ×ˢ Set.Icc (0 : ℝ) S) (z, s) ∘SL ContinuousLinearMap.inl ℝ R3 ℝ) :=
      h1.clm_comp continuous_const
    have h3 : Continuous (fun z : R3 => curlOf
        (fderivWithin ℝ (Function.uncurry (Work.FTS.Physical.physVel ω))
          (Set.univ ×ˢ Set.Icc (0 : ℝ) S) (z, s) ∘SL ContinuousLinearMap.inl ℝ R3 ℝ)) :=
      continuous_curlOf.comp h2
    have heq : (fun z : R3 => ω z s) = fun z : R3 => curlOf
        (fderivWithin ℝ (Function.uncurry (Work.FTS.Physical.physVel ω))
          (Set.univ ×ˢ Set.Icc (0 : ℝ) S) (z, s) ∘SL ContinuousLinearMap.inl ℝ R3 ℝ) := by
      funext z
      rw [← hcurl s hsT z, vorticity_eq_curlOf, hslice_eq s hs z]
    rw [heq]
    exact h3.aestronglyMeasurable

end Work.FTS.PressureOn
end
