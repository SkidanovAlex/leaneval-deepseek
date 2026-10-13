/-
# Pointwise algebra and integration by parts in `ℝ³`

`Work.FTS.PressureOn.integral_div_eq_zero_of_hasFDerivAt` (the divergence theorem for compactly
supported `C¹` fields, proved in this directory) yields the integration-by-parts identities needed
for the weak Poisson identity of the pressure potential.  This file collects the pointwise algebra
(`div` of a product of a scalar and a vector field, trace of a rank-one endomorphism, continuity
and integrability of `div`) and the integration-by-parts statements themselves.
-/
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.LinearAlgebra.Trace
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.integral_div_eq_zero_of_hasFDerivAt
import Submission.Work.FTS.PressureOn.PoissonAux.Defs

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
