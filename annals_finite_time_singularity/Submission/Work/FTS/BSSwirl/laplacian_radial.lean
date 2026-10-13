/-
# The Laplacian of a radially symmetric function on `ℝ³`

The classical formula

  `Δ (g ∘ ‖·‖) (z) = g''(‖z‖) + 2 g'(‖z‖) / ‖z‖`   (`z ≠ 0`)

for the Euclidean Laplacian of a radial function, in the form of Mathlib's
`Laplacian.laplacian` (the *positive* Laplacian `∑ᵢ ∂ᵢ∂ᵢ`).

The proof has three parts, all in this file:

* `basisFun_eq_e` — the standard orthonormal basis `EuclideanSpace.basisFun (Fin 3) ℝ` of `ℝ³`
  agrees with the workspace basis `FiniteTimeSingularity.e`;
* `laplacian_eq_sum_diag` — for an arbitrary function `φ : ℝ³ → ℝ` which is `C²` at `x`, the
  Laplacian is the sum of the diagonal entries of the Hessian in the standard basis,
  `Δφ(x) = ∑ᵢ ∂ᵢ∂ᵢφ(x)`;
* `fderiv_fderiv_radial_diag` — the diagonal entry of the Hessian of `g ∘ ‖·‖`,
  `∂ᵢ∂ᵢ (g ∘ ‖·‖) (x) = g'(‖x‖)/‖x‖ + (g''(‖x‖)‖x‖⁻² - g'(‖x‖)‖x‖⁻³)·(xᵢ)²`,
  for `g` merely `C²` **at `‖x‖`** (the local form, which is what the target statement
  provides).  The computation uses the Fréchet derivative of the norm away from the origin
  (`Work.FTS.PressureOn.PoissonAux.hasFDerivAt_norm_ne`) and the chain rule for radial functions
  (`Work.FTS.PressureOn.PoissonAux.hasFDerivAt_radial_comp`), both from the pressure area.

Summing the diagonal entries over `i ∈ Fin 3` and using `∑ᵢ (xᵢ)² = ‖x‖²` gives the stated
formula.
-/
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.FTS.BSSwirl.Defs
import Submission.Work.FTS.PressureOn.PoissonAux.laplaceTrace_radial

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set MeasureTheory Metric
open scoped Topology RealInnerProductSpace

namespace Work.FTS.BSSwirl

/-- The standard orthonormal basis of `ℝ³` agrees with the basis `FiniteTimeSingularity.e` used
throughout the workspace. -/
theorem basisFun_eq_e (i : Fin 3) :
    (EuclideanSpace.basisFun (Fin 3) ℝ) i = FiniteTimeSingularity.e i := by
  rw [EuclideanSpace.basisFun_apply, FiniteTimeSingularity.e]
  rfl

/-- **The Laplacian is the sum of the diagonal entries of the Hessian.**  For `φ` of class `C²`
at `x`, the Laplacian of `φ` at `x` equals `∑ᵢ ∂ᵢ∂ᵢφ(x)`, the diagonal of the Hessian in the
standard basis of `ℝ³`. -/
theorem laplacian_eq_sum_diag (φ : R3 → ℝ) (x : R3) (hφ : ContDiffAt ℝ 2 φ x) :
    Laplacian.laplacian φ x
      = ∑ i : Fin 3, fderiv ℝ (fun w : R3 => fderiv ℝ φ w (FiniteTimeSingularity.e i)) x
          (FiniteTimeSingularity.e i) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis φ
    (EuclideanSpace.basisFun (Fin 3) ℝ)]
  simp only
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [basisFun_eq_e i, iteratedFDeriv_two_apply]
  have hc : DifferentiableAt ℝ (fderiv ℝ φ) x :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  have hcl := fderiv_clm_apply (c := fderiv ℝ φ) (u := fun _ : R3 => FiniteTimeSingularity.e i)
    hc (differentiableAt_const _)
  rw [hcl]
  simp

/-- **The diagonal entry of the Hessian of a radial function.**  For `g` of class `C²` at
`‖x‖` and `x ≠ 0`,

  `∂ᵢ∂ᵢ (g ∘ ‖·‖) (x) = g'(‖x‖)/‖x‖ + (g''(‖x‖)‖x‖⁻² - g'(‖x‖)‖x‖⁻³)·(xᵢ)²`. -/
theorem fderiv_fderiv_radial_diag {g : ℝ → ℝ} {x : R3} (hx : x ≠ 0)
    (hg : ContDiffAt ℝ 2 g ‖x‖) (i : Fin 3) :
    fderiv ℝ (fun w : R3 => fderiv ℝ (fun y : R3 => g ‖y‖) w (FiniteTimeSingularity.e i)) x
        (FiniteTimeSingularity.e i)
      = deriv g ‖x‖ / ‖x‖
        + (deriv (deriv g) ‖x‖ * (‖x‖ ^ 2)⁻¹ - deriv g ‖x‖ * (‖x‖ ^ 3)⁻¹)
            * (x i) ^ 2 := by
  have hne : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  -- `g` is `C²` at `‖w‖` for `w` near `x`
  have hgc : ∀ᶠ w : R3 in 𝓝 x, ContDiffAt ℝ 2 g ‖w‖ :=
    (continuous_norm.tendsto x).eventually (hg.eventually (by norm_num))
  -- the first derivative of `g ∘ ‖·‖` away from the origin
  have hφ : ∀ᶠ w : R3 in 𝓝 x, fderiv ℝ (fun y : R3 => g ‖y‖) w
      = (deriv g ‖w‖) • ((‖w‖)⁻¹ • innerSL ℝ w) := by
    filter_upwards [isOpen_ne.mem_nhds hx, hgc] with w hw hgcw
    have hG : HasDerivAt g (deriv g ‖w‖) ‖w‖ :=
      (hgcw.differentiableAt (by norm_num)).hasDerivAt
    rw [(Work.FTS.PressureOn.PoissonAux.hasFDerivAt_radial_comp hw hG).fderiv]
  -- hence the diagonal-entry function agrees with an explicit product near `x`
  have hdiag : (fun w : R3 => fderiv ℝ (fun y : R3 => g ‖y‖) w (FiniteTimeSingularity.e i))
      =ᶠ[𝓝 x]
        (fun w : R3 =>
          deriv g ‖w‖ * ((‖w‖)⁻¹ * (innerSL ℝ (FiniteTimeSingularity.e i)) w)) := by
    filter_upwards [hφ] with w hw
    rw [hw]
    simp only [smul_apply, innerSL_apply_apply, smul_eq_mul]
    rw [real_inner_comm w (FiniteTimeSingularity.e i)]
  rw [hdiag.fderiv_eq]
  -- the derivative of the radial factor `w ↦ deriv g ‖w‖`
  have hA : HasFDerivAt (fun w : R3 => deriv g ‖w‖)
      ((deriv (deriv g) ‖x‖) • ((‖x‖)⁻¹ • innerSL ℝ x)) x := by
    refine Work.FTS.PressureOn.PoissonAux.hasFDerivAt_radial_comp hx ?_
    exact ((hg.derivWithin (m := 1) (by norm_num)).differentiableAt_one).hasDerivAt
  -- the derivative of `w ↦ ‖w‖⁻¹`
  have hD : HasFDerivAt (fun w : R3 => (‖w‖)⁻¹)
      ((-(‖x‖ ^ 2)⁻¹) • ((‖x‖)⁻¹ • innerSL ℝ x)) x := by
    have hdd : HasDerivAt (fun r : ℝ => r⁻¹) (-(‖x‖ ^ 2)⁻¹) ‖x‖ := hasDerivAt_inv hne
    have h := hdd.comp_hasFDerivAt x (Work.FTS.PressureOn.PoissonAux.hasFDerivAt_norm_ne hx)
    simpa only [Function.comp_def] using h
  -- the (linear) factor `w ↦ ⟪eᵢ, w⟫`
  have hM : HasFDerivAt (fun w : R3 => (innerSL ℝ (FiniteTimeSingularity.e i)) w)
      (innerSL ℝ (FiniteTimeSingularity.e i)) x := ContinuousLinearMap.hasFDerivAt _
  have hB := hD.mul hM
  have hAB := hA.mul hB
  -- put the derivative in the form needed by the rewrite (the function is the explicit product)
  have hAB' : HasFDerivAt
      (fun w : R3 => deriv g ‖w‖ * ((‖w‖)⁻¹ * (innerSL ℝ (FiniteTimeSingularity.e i)) w))
      (deriv g ‖x‖ • ((‖x‖)⁻¹ • innerSL ℝ (FiniteTimeSingularity.e i) +
          (innerSL ℝ (FiniteTimeSingularity.e i)) x • (-(‖x‖ ^ 2)⁻¹ • (‖x‖)⁻¹ • innerSL ℝ x)) +
        ((fun w : R3 => (‖w‖)⁻¹) *
          fun w : R3 => (innerSL ℝ (FiniteTimeSingularity.e i)) w) x •
          deriv (deriv g) ‖x‖ • (‖x‖)⁻¹ • innerSL ℝ x) x := hAB
  rw [hAB'.fderiv]
  simp only [add_apply, smul_apply, Pi.mul_apply, innerSL_apply_apply, smul_eq_mul]
  -- the standard basis is orthonormal
  have hee : inner ℝ (FiniteTimeSingularity.e i) (FiniteTimeSingularity.e i) = 1 := by
    rw [FiniteTimeSingularity.e, PiLp.inner_apply]
    simp [Pi.single_apply]
  have hze : inner ℝ x (FiniteTimeSingularity.e i) = x i := by
    rw [FiniteTimeSingularity.e, PiLp.inner_apply]
    simp [Pi.single_apply]
  have hez : inner ℝ (FiniteTimeSingularity.e i) x = x i := by
    rw [real_inner_comm, hze]
  rw [hee, hze, hez]
  field_simp
  ring

theorem laplacian_radial {g : ℝ → ℝ} {z : Work.FTS.BSSwirl.R3} (hz : z ≠ 0)
    (hg : ContDiffAt ℝ 2 g ‖z‖) :
    Laplacian.laplacian (fun y : Work.FTS.BSSwirl.R3 => g ‖y‖) z
      = deriv (deriv g) ‖z‖ + 2 * deriv g ‖z‖ / ‖z‖ := by
  have hne : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  -- `∑ i, (zᵢ)² = ‖z‖²`
  have hsum : ∑ i : Fin 3, (z i) ^ 2 = ‖z‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    simp only [Real.norm_eq_abs, sq_abs]
  have hcont : ContDiffAt ℝ 2 (fun y : R3 => g ‖y‖) z := hg.comp z (contDiffAt_norm ℝ hz)
  rw [laplacian_eq_sum_diag (fun y : R3 => g ‖y‖) z hcont]
  rw [Finset.sum_congr rfl (fun i _ => fderiv_fderiv_radial_diag hz hg i)]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsum]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp only [nsmul_eq_mul]
  field_simp
  ring

end Work.FTS.BSSwirl
