import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Trace
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.H2.STBasic
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PressureOn.Green.integral_mul_laplaceTrace_comm
import Submission.Work.FTS.PressureOn.integral_div_eq_zero_of_hasFDerivAt
import Submission.Work.FTS.PressureOn.omegaSliceRegularPos
import Submission.Work.FTS.PressureOn.weakCurl.int2_integrable
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.conv_shift_sq_integral_le
import Submission.Work.FTS_MuLamOK.Rows.rl0_final
import Submission.Work.LWP.BiotSavart.nearField_bound
import Submission.Work.LWP.VorticityAPI
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.mixed_sq_integrableOn
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.mul_rpow_le
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge
-- ===== merged: Submission.Work.FTS.BSSwirl.VortVV.curl_curl_algebra =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity

namespace Work.FTS.BSSwirl.VortVV

/-! ## The vector triple product identity for `crossR3`

The proof of `curl_curl_algebra` below is the algebraic identity
`∑ᵢ eᵢ × (∑ⱼ eⱼ × B eᵢ eⱼ) = ∑_k (∑ᵢ ⟪eᵢ, B e_k eᵢ⟫) e_k - ∑_k B e_k e_k`
for a symmetric bilinear `B` and an orthonormal basis `e`.  It rests on the vector triple
product formula `a × (b × c) = ⟪a,c⟫ b - ⟪b,a⟫ c`, the additivity of `×` in its last argument,
and the orthonormality of the basis. -/

/-- **The vector triple product formula** for the cross product `crossR3` of `ℝ³`:
`a × (b × c) = ⟪a,c⟫ b - ⟪b,a⟫ c`. -/
private lemma crossR3_crossR3 (a b c : Work.FTS.BSSwirl.R3) :
    Work.FTS.BSSwirl.crossR3 a (Work.FTS.BSSwirl.crossR3 b c)
      = (inner ℝ a c) • b - (inner ℝ b a) • c := by
  apply PiLp.ext; intro k
  simp only [Work.FTS.BSSwirl.crossR3_ofLp, WithLp.ofLp_sub, WithLp.ofLp_smul]
  rw [Work.FTS.BSSwirl.inner_eq_dot, Work.FTS.BSSwirl.inner_eq_dot]
  simpa [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using
    congr_fun (cross_cross_eq_smul_sub_smul' a.ofLp b.ofLp c.ofLp) k

/-- The cross product `crossR3` is additive in its second argument. -/
private lemma crossR3_sum (a : Work.FTS.BSSwirl.R3) (f : Fin 3 → Work.FTS.BSSwirl.R3) :
    Work.FTS.BSSwirl.crossR3 a (∑ j : Fin 3, f j)
      = ∑ j : Fin 3, Work.FTS.BSSwirl.crossR3 a (f j) :=
  map_sum (Work.FTS.BSSwirl.crossBilin a) f Finset.univ

/-- The standard basis `FiniteTimeSingularity.e` of `ℝ³` is orthonormal. -/
private lemma inner_e_e (i j : Fin 3) :
    inner ℝ (e i) (e j) = if i = j then 1 else 0 := by
  rw [show e i = EuclideanSpace.single i 1 from rfl, show e j = EuclideanSpace.single j 1 from rfl]
  rw [EuclideanSpace.inner_single_left, PiLp.single_apply]
  simp

/-- Orthonormality of the standard basis, in the form in which it resolves a vector `X i` out of
the sum `∑ j, ⟪e_j, e_i⟫ • X j`. -/
private lemma sum_inner_e_smul (X : Fin 3 → Work.FTS.BSSwirl.R3) (i : Fin 3) :
    (∑ j : Fin 3, (inner ℝ (e j) (e i)) • X j) = X i := by
  rw [Finset.sum_eq_single i]
  · rw [show inner ℝ (e i) (e i) = 1 from by simpa using inner_e_e i i]
    exact one_smul ℝ (X i)
  · intro j _ hj
    rw [show inner ℝ (e j) (e i) = 0 from by rw [inner_e_e j i]; simp [hj]]
    exact zero_smul ℝ (X j)
  · intro h; exact absurd (Finset.mem_univ i) h

theorem curl_curl_algebra
    (B : Work.FTS.BSSwirl.R3 →L[ℝ] Work.FTS.BSSwirl.R3 →L[ℝ] Work.FTS.BSSwirl.R3)
    (hB : ∀ u v, B u v = B v u) :
    (∑ i : Fin 3, Work.FTS.BSSwirl.crossR3 (FiniteTimeSingularity.e i)
        (∑ j : Fin 3, Work.FTS.BSSwirl.crossR3 (FiniteTimeSingularity.e j)
          (B (FiniteTimeSingularity.e i) (FiniteTimeSingularity.e j))))
      = (∑ k : Fin 3, (∑ i : Fin 3, inner ℝ (FiniteTimeSingularity.e i)
            (B (FiniteTimeSingularity.e k) (FiniteTimeSingularity.e i)))
              • FiniteTimeSingularity.e k)
        - ∑ k : Fin 3, B (FiniteTimeSingularity.e k) (FiniteTimeSingularity.e k) := by
  -- The value at a fixed `i` of the outer term: expand the inner cross product with the vector
  -- triple product formula and use orthonormality to kill the diagonal part.
  have key : ∀ i : Fin 3,
      Work.FTS.BSSwirl.crossR3 (e i)
        (∑ j : Fin 3, Work.FTS.BSSwirl.crossR3 (e j) (B (e i) (e j)))
        = (∑ j : Fin 3, (inner ℝ (e i) (B (e i) (e j))) • e j) - B (e i) (e i) := by
    intro i
    calc Work.FTS.BSSwirl.crossR3 (e i)
          (∑ j : Fin 3, Work.FTS.BSSwirl.crossR3 (e j) (B (e i) (e j)))
        = ∑ j : Fin 3, Work.FTS.BSSwirl.crossR3 (e i)
            (Work.FTS.BSSwirl.crossR3 (e j) (B (e i) (e j))) := crossR3_sum _ _
      _ = ∑ j : Fin 3, ((inner ℝ (e i) (B (e i) (e j))) • e j
            - (inner ℝ (e j) (e i)) • B (e i) (e j)) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [crossR3_crossR3]
      _ = (∑ j : Fin 3, (inner ℝ (e i) (B (e i) (e j))) • e j)
            - ∑ j : Fin 3, (inner ℝ (e j) (e i)) • B (e i) (e j) :=
          Finset.sum_sub_distrib _ _
      _ = (∑ j : Fin 3, (inner ℝ (e i) (B (e i) (e j))) • e j) - B (e i) (e i) := by
          rw [sum_inner_e_smul (fun j => B (e i) (e j)) i]
  -- Reassembling: interchange the two sums and use the symmetry of `B`.
  have hsum : (∑ i : Fin 3, ∑ j : Fin 3, (inner ℝ (e i) (B (e i) (e j))) • e j)
      = ∑ k : Fin 3, (∑ i : Fin 3, inner ℝ (e i) (B (e k) (e i))) • e k := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hB (e i) (e j)]
  calc (∑ i : Fin 3, Work.FTS.BSSwirl.crossR3 (e i)
          (∑ j : Fin 3, Work.FTS.BSSwirl.crossR3 (e j) (B (e i) (e j))))
      = ∑ i : Fin 3, ((∑ j : Fin 3, (inner ℝ (e i) (B (e i) (e j))) • e j)
            - B (e i) (e i)) := Finset.sum_congr rfl fun i _ => key i
    _ = (∑ i : Fin 3, ∑ j : Fin 3, (inner ℝ (e i) (B (e i) (e j))) • e j)
          - ∑ i : Fin 3, B (e i) (e i) := Finset.sum_sub_distrib _ _
    _ = (∑ k : Fin 3, (∑ i : Fin 3, inner ℝ (e i) (B (e k) (e i))) • e k)
          - ∑ k : Fin 3, B (e k) (e k) := by rw [hsum]

end Work.FTS.BSSwirl.VortVV
end
-- ===== merged: Submission.Work.FTS.BSSwirl.laplacian_radial =====
section

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
end
-- ===== merged: Submission.Work.FTS.Physical.Clock.tail_le_two_mul =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set MeasureTheory
open scoped Topology

namespace Work.FTS.Physical.Clock

/-! ### Integrability of exponentials on half-lines -/

/-- `e^{a x}` is integrable on `[c,∞)` for `a < 0` (transfer of `integrableOn_exp_mul_Ioi`
from `(c,∞)` to `[c,∞)`, which differ by a null set). -/
theorem integrable_exp_mul_Ici (a : ℝ) (ha : a < 0) (c : ℝ) :
    IntegrableOn (fun x : ℝ => Real.exp (a * x)) (Set.Ici c) :=
  (integrableOn_exp_mul_Ioi ha c).congr_set_ae Ioi_ae_eq_Ici.symm

/-- The shifted Gaussian-type exponential `s ↦ e^{-(s-τ)/2}` is integrable on `[τ,∞)`. -/
theorem integrableOn_exp_shift (τ : ℝ) :
    IntegrableOn (fun s : ℝ => Real.exp (-(s - τ) / 2)) (Set.Ici τ) := by
  have heq : (fun s : ℝ => Real.exp (-(s - τ) / 2))
      = fun s : ℝ => Real.exp (τ / 2) * Real.exp ((-1 / 2 : ℝ) * s) := by
    funext s
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq]
  exact (integrable_exp_mul_Ici (-1 / 2) (by norm_num) τ).const_mul (Real.exp (τ / 2))

/-- **`A` is integrable on `[0,∞)`**: the modulating amplitude decays at least like
`e^{-τ/2}`, so the blow-up happens in finite time and `T = ∫₀^∞ A < ∞`. -/
theorem integrableOn_A_local (C : Work.FTS.Physical.PhysClock) :
    IntegrableOn C.A (Set.Ici (0 : ℝ)) := by
  have hg : IntegrableOn (fun s : ℝ => C.A 0 * Real.exp ((-1 / 2 : ℝ) * s))
      (Set.Ici (0 : ℝ)) :=
    (integrable_exp_mul_Ici (-1 / 2) (by norm_num) 0).const_mul (C.A 0)
  refine hg.mono' (C.hAcont.aestronglyMeasurable measurableSet_Ici) ?_
  rw [ae_restrict_iff' measurableSet_Ici]
  filter_upwards with s hs
  rw [Real.norm_of_nonneg (C.hApos s hs).le]
  have h := A_le_exp_mul C (le_refl (0 : ℝ)) hs
  have hexp : Real.exp (-(s - 0) / 2) = Real.exp ((-1 / 2 : ℝ) * s) := by
    congr 1
    ring
  rw [hexp] at h
  exact h

/-! ### The tail identity and the exponential integral -/

/-- **Tail identity** `T - t(τ) = ∫_τ^∞ A ds`: the physical time left before blow-up is the
integral of the amplitude over `[τ,∞)`. -/
theorem tail_eq_integral (C : Work.FTS.Physical.PhysClock) {τ : ℝ} (hτ : 0 ≤ τ) :
    C.T - C.t τ = ∫ s in Set.Ici τ, C.A s := by
  have hf : IntegrableOn C.A (Set.Ici (0 : ℝ)) := integrableOn_A_local C
  have h1 : (∫ s in Set.Ici (0 : ℝ), C.A s) - (∫ s in Set.Ici τ, C.A s)
      = ∫ s in Set.Ico (0 : ℝ) τ, C.A s := intervalIntegral.integral_Ici_sub_Ici hf hτ
  have h2 : (∫ s in Set.Ico (0 : ℝ) τ, C.A s) = C.t τ := by
    rw [Work.FTS.Physical.PhysClock.t, intervalIntegral.integral_of_le hτ,
      integral_Ico_eq_integral_Ioc]
  rw [Work.FTS.Physical.PhysClock.T, ← h2]
  linarith

/-- `∫_τ^∞ e^{-(s-τ)/2} ds = 2`. -/
theorem integral_exp_shift (τ : ℝ) :
    ∫ s in Set.Ici τ, Real.exp (-(s - τ) / 2) = 2 := by
  rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
  have heq : (fun s : ℝ => Real.exp (-(s - τ) / 2))
      = fun s : ℝ => Real.exp (τ / 2) * Real.exp ((-1 / 2 : ℝ) * s) := by
    funext s
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq, integral_const_mul, integral_exp_mul_Ioi (by norm_num : (-1 / 2 : ℝ) < 0) τ]
  have hE : Real.exp ((-1 / 2 : ℝ) * τ) = Real.exp (-(τ / 2)) := by
    congr 1
    ring
  rw [hE]
  have hval : -Real.exp (-(τ / 2)) / (-1 / 2 : ℝ) = 2 * Real.exp (-(τ / 2)) := by
    ring
  rw [hval]
  have h1 : Real.exp (τ / 2) * Real.exp (-(τ / 2)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  calc Real.exp (τ / 2) * (2 * Real.exp (-(τ / 2)))
      = 2 * (Real.exp (τ / 2) * Real.exp (-(τ / 2))) := by ring
    _ = 2 * 1 := by rw [h1]
    _ = 2 := by ring

/-! ### The clock comparison -/

theorem tail_le_two_mul (C : Work.FTS.Physical.PhysClock) {τ : ℝ} (hτ : 0 ≤ τ) : C.T - C.t τ ≤ 2 * C.A τ := by
  rw [tail_eq_integral C hτ]
  have hIntA : IntegrableOn C.A (Set.Ici τ) :=
    (integrableOn_A_local C).mono_set (Set.Ici_subset_Ici.mpr hτ)
  have hIntg : IntegrableOn (fun s : ℝ => C.A τ * Real.exp (-(s - τ) / 2)) (Set.Ici τ) :=
    (integrableOn_exp_shift τ).const_mul (C.A τ)
  have hmono : ∫ s in Set.Ici τ, C.A s
      ≤ ∫ s in Set.Ici τ, C.A τ * Real.exp (-(s - τ) / 2) :=
    setIntegral_mono_on hIntA hIntg measurableSet_Ici (fun s hs => A_le_exp_mul C hτ hs)
  calc ∫ s in Set.Ici τ, C.A s
      ≤ ∫ s in Set.Ici τ, C.A τ * Real.exp (-(s - τ) / 2) := hmono
    _ = C.A τ * ∫ s in Set.Ici τ, Real.exp (-(s - τ) / 2) := by rw [integral_const_mul]
    _ = C.A τ * 2 := by rw [integral_exp_shift τ]
    _ = 2 * C.A τ := by ring

end Work.FTS.Physical.Clock
end
-- ===== merged: Submission.Work.FTS.Physical.Pressure =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.Physical




/- The radial primitive `radialPrim` (with its docstring) is *defined* in the lower module
`Submission.Work.FTS.Physical.Pressure.RadialPrim`, imported above, rather than in this umbrella
file: the lemma module `Submission.Work.FTS.Physical.Pressure.contDiffOn_radialPrim` (imported
below, like the other `Pressure` lemma modules) is stated in terms of `radialPrim`, so defining
`radialPrim` here would create the import cycle umbrella → lemma → umbrella. -/



/-- **The gradient is the Riesz dual of the derivative**: `fderiv ℝ f x = ⟪∇f x, ·⟫`, the bridge
between Mathlib's gradient and the `fderiv` of `ChallengeDeps`. -/
theorem fderiv_eq_innerSL_spaceGrad (p : R3 → ℝ → ℝ) (x : R3) (t : ℝ) :
    fderiv ℝ (p · t) x = innerSL ℝ (spaceGrad p x t) := by
  rw [spaceGrad]
  rw [← toDual_gradient (𝕜 := ℝ) (f := fun y : R3 => p y t) (x := x)]
  ext y
  simp

/-- **The gradient is determined by its inner products.** -/
theorem spaceGrad_eq_of_inner_eq {p : R3 → ℝ → ℝ} {x : R3} {t : ℝ} {v : R3}
    (h : ∀ y : R3, inner ℝ (spaceGrad p x t) y = inner ℝ v y) :
    spaceGrad p x t = v := by
  have hzero : inner ℝ (spaceGrad p x t - v) (spaceGrad p x t - v) = 0 := by
    have h1 : inner ℝ (spaceGrad p x t - v) (spaceGrad p x t) = 0 := by
      rw [inner_sub_left, h (spaceGrad p x t), sub_self]
    have h2 : inner ℝ (spaceGrad p x t - v) v = 0 := by
      rw [inner_sub_left, h v, sub_self]
    rw [inner_sub_right, h1, h2, sub_zero]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hzero)


end Work.FTS.Physical
end
-- ===== merged: Submission.Work.FTS.PressureOn.Auxiliary.abs_deriv_heatKernel_time_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The time derivative of the heat kernel on `ℝ³`, and its size on a multiplicative window

`∂_t γ_t(z) = (4πt)^{-3/2}·(‖z‖²/(4t²) - 3/(2t))·exp(-‖z‖²/(4t))`, and for `t > 0` and
`s ∈ [t/2, 2t]` this is bounded by
`(4π(t/2))^{-3/2}·(3/t + ‖z‖²/t²)·exp(-‖z‖²/(8t))`.

Both factors are compared on the window: the prefactor `(4π·)^{-3/2}` decreases, the polynomial
factor grows by a constant factor, and the Gaussian decays when the exponent shrinks.
-/

namespace Work.FTS.PressureOn.Auxiliary

noncomputable section

open scoped Topology

/-- The explicit time derivative of the heat kernel `γ_t(z) = (4πt)^{-3/2} exp(-‖z‖²/(4t))`. -/
lemma deriv_heatKernel_time_of_pos (r : ℝ) (hr : 0 < r) (z : R3) :
    deriv (fun x : ℝ => heatKernel x z) r
      = (4 * Real.pi * r) ^ (-(3 / 2 : ℝ)) * (‖z‖ ^ 2 / (4 * r ^ 2) - 3 / (2 * r)) *
          Real.exp (-(‖z‖ ^ 2 / (4 * r))) := by
  have hx : (4 * Real.pi * r) ^ (-(3 / 2 : ℝ))
      = (4 * Real.pi * r) ^ (-(3 / 2 : ℝ) - 1) * (4 * Real.pi * r) := by
    have h := Real.rpow_add (by positivity : (0 : ℝ) < 4 * Real.pi * r) (-(3 / 2 : ℝ) - 1) 1
    rw [show (-(3 / 2 : ℝ) - 1) + 1 = -(3 / 2 : ℝ) by norm_num] at h
    simpa using h
  have key : (-(3 / 2 : ℝ)) * (4 * Real.pi * r) ^ (-(3 / 2 : ℝ) - 1) * (4 * Real.pi)
      = (4 * Real.pi * r) ^ (-(3 / 2 : ℝ)) * (-(3 / (2 * r))) := by
    rw [hx]; field_simp
  have hA : HasDerivAt (fun x : ℝ => (4 * Real.pi * x) ^ (-(3 / 2 : ℝ)))
      ((4 * Real.pi * r) ^ (-(3 / 2 : ℝ)) * (-(3 / (2 * r)))) r := by
    have hin : HasDerivAt (fun x : ℝ => 4 * Real.pi * x) (4 * Real.pi) r := by
      simpa using (hasDerivAt_id r).const_mul (4 * Real.pi)
    have hout : HasDerivAt (fun x : ℝ => x ^ (-(3 / 2 : ℝ)))
        ((-(3 / 2 : ℝ)) * (4 * Real.pi * r) ^ (-(3 / 2 : ℝ) - 1)) (4 * Real.pi * r) :=
      Real.hasDerivAt_rpow_const (Or.inl (by positivity))
    have h := hout.comp r hin
    rw [key] at h
    exact h
  have hB : HasDerivAt (fun x : ℝ => Real.exp (-(‖z‖ ^ 2 / (4 * x))))
      (Real.exp (-(‖z‖ ^ 2 / (4 * r))) * (‖z‖ ^ 2 / (4 * r ^ 2))) r := by
    have hden : HasDerivAt (fun x : ℝ => 4 * x) 4 r := by
      simpa using (hasDerivAt_id r).const_mul (4 : ℝ)
    have hquot : HasDerivAt (fun u : ℝ => ‖z‖ ^ 2 / u) (-(‖z‖ ^ 2) / (4 * r) ^ 2) (4 * r) := by
      have h := (hasDerivAt_const (4 * r) (‖z‖ ^ 2)).div (hasDerivAt_id (4 * r))
        (by simpa using (show (4 : ℝ) * r ≠ 0 by positivity))
      have hfun : ((fun _ : ℝ => ‖z‖ ^ 2) / id : ℝ → ℝ) = fun u : ℝ => ‖z‖ ^ 2 / u := by
        ext u; simp [Pi.div_apply]
      rw [hfun] at h
      simpa using h
    have hcomp : HasDerivAt (fun x : ℝ => ‖z‖ ^ 2 / (4 * x))
        ((-(‖z‖ ^ 2) / (4 * r) ^ 2) * 4) r := hquot.comp r hden
    have hneg : HasDerivAt (fun x : ℝ => -(‖z‖ ^ 2 / (4 * x)))
        (-((-(‖z‖ ^ 2) / (4 * r) ^ 2) * 4)) r := hcomp.neg
    have hkey : -((-(‖z‖ ^ 2) / (4 * r) ^ 2) * 4) = ‖z‖ ^ 2 / (4 * r ^ 2) := by field_simp
    have hneg' : HasDerivAt (fun x : ℝ => -(‖z‖ ^ 2 / (4 * x))) (‖z‖ ^ 2 / (4 * r ^ 2)) r := by
      rw [← hkey]; exact hneg
    exact hneg'.exp
  have hprod : HasDerivAt
      (fun x : ℝ => (4 * Real.pi * x) ^ (-(3 / 2 : ℝ)) * Real.exp (-(‖z‖ ^ 2 / (4 * x))))
      ((4 * Real.pi * r) ^ (-(3 / 2 : ℝ)) * (-(3 / (2 * r))) * Real.exp (-(‖z‖ ^ 2 / (4 * r))) +
        (4 * Real.pi * r) ^ (-(3 / 2 : ℝ)) *
          (Real.exp (-(‖z‖ ^ 2 / (4 * r))) * (‖z‖ ^ 2 / (4 * r ^ 2)))) r := hA.mul hB
  simp only [heatKernel]
  rw [hprod.deriv]
  ring_nf

theorem abs_deriv_heatKernel_time_le (t : ℝ) (ht : 0 < t) (s : ℝ) (hs : t / 2 ≤ s)
    (hs2 : s ≤ 2 * t) (z : Work.FTS.PressureOn.R3) :
    |deriv (fun r : ℝ => Work.FTS.PressureOn.Auxiliary.heatKernel r z) s| ≤
      (4 * Real.pi * (t / 2)) ^ (-(3 / 2 : ℝ)) * (3 / t + ‖z‖ ^ 2 / t ^ 2) *
        Real.exp (-(‖z‖ ^ 2 / (8 * t))) := by
  have ht2 : 0 < t / 2 := by linarith
  have hs0 : 0 < s := by linarith
  rw [deriv_heatKernel_time_of_pos s hs0 z]
  have hApos : 0 < (4 * Real.pi * s) ^ (-(3 / 2 : ℝ)) := Real.rpow_pos_of_pos (by positivity) _
  have hA'pos : 0 < (4 * Real.pi * (t / 2)) ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hA'nn : 0 ≤ (4 * Real.pi * (t / 2)) ^ (-(3 / 2 : ℝ)) := hA'pos.le
  have hAle : (4 * Real.pi * s) ^ (-(3 / 2 : ℝ)) ≤ (4 * Real.pi * (t / 2)) ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [hs, Real.pi_pos]) (by norm_num)
  have h1 : ‖z‖ ^ 2 / (4 * s ^ 2) ≤ ‖z‖ ^ 2 / t ^ 2 :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith [hs, ht])
  have h2 : 3 / (2 * s) ≤ 3 / t :=
    div_le_div_of_nonneg_left (by norm_num) ht (by nlinarith [hs])
  have hBnn : 0 ≤ 3 / t + ‖z‖ ^ 2 / t ^ 2 := by positivity
  have hB : |‖z‖ ^ 2 / (4 * s ^ 2) - 3 / (2 * s)| ≤ 3 / t + ‖z‖ ^ 2 / t ^ 2 := by
    have ha : 0 ≤ ‖z‖ ^ 2 / (4 * s ^ 2) := by positivity
    have hb : 0 ≤ 3 / (2 * s) := by positivity
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  have hC : Real.exp (-(‖z‖ ^ 2 / (4 * s))) ≤ Real.exp (-(‖z‖ ^ 2 / (8 * t))) := by
    rw [Real.exp_le_exp]
    have h : ‖z‖ ^ 2 / (8 * t) ≤ ‖z‖ ^ 2 / (4 * s) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith [hs2, ht])
    linarith
  have hCpos : 0 < Real.exp (-(‖z‖ ^ 2 / (4 * s))) := Real.exp_pos _
  rw [abs_mul, abs_mul, abs_of_pos hApos, abs_of_pos hCpos]
  calc (4 * Real.pi * s) ^ (-(3 / 2 : ℝ)) * |‖z‖ ^ 2 / (4 * s ^ 2) - 3 / (2 * s)| *
          Real.exp (-(‖z‖ ^ 2 / (4 * s)))
      ≤ ((4 * Real.pi * (t / 2)) ^ (-(3 / 2 : ℝ)) * (3 / t + ‖z‖ ^ 2 / t ^ 2)) *
          Real.exp (-(‖z‖ ^ 2 / (8 * t))) :=
        mul_le_mul (mul_le_mul hAle hB (abs_nonneg _) hA'nn) hC hCpos.le (mul_nonneg hA'nn hBnn)
    _ = (4 * Real.pi * (t / 2)) ^ (-(3 / 2 : ℝ)) * (3 / t + ‖z‖ ^ 2 / t ^ 2) *
          Real.exp (-(‖z‖ ^ 2 / (8 * t))) := rfl

end

end Work.FTS.PressureOn.Auxiliary
end
-- ===== merged: Submission.Work.FTS.PressureOn.Auxiliary.deriv_heatKernel_time =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The time derivative of the heat kernel

`∂_t γ_t(z) = (4πt)^{-3/2} (‖z‖²/(4t²) - 3/(2t)) exp(-‖z‖²/(4t))` for `t > 0`, where
`γ_t(z) = heatKernel t z = (4πt)^{-3/2} exp(-‖z‖²/(4t))`.

The computation is the product rule applied to the two factors

* `t ↦ (4πt)^{-3/2}`, whose derivative is `-(3/(2t)) (4πt)^{-3/2}`
  (the shift of the exponent `-(3/2) - 1` is handled by `Real.rpow_add`/`Real.rpow_neg_one`),
* `t ↦ exp(-‖z‖²/(4t))`, whose derivative is `(‖z‖²/(4t²)) exp(-‖z‖²/(4t))`.
-/

namespace Work.FTS.PressureOn.Auxiliary

/-- Derivative of the normalising factor `t ↦ (4πt)^{-3/2}` of the heat kernel. -/
lemma hasDerivAt_heatPrefactor (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => (4 * Real.pi * s) ^ (-(3 / 2 : ℝ)))
      (-(3 / (2 * t)) * (4 * Real.pi * t) ^ (-(3 / 2 : ℝ))) t := by
  have h1 : HasDerivAt (fun s : ℝ => 4 * Real.pi * s) (4 * Real.pi) t := by
    simpa using (hasDerivAt_id t).const_mul (4 * Real.pi)
  refine (h1.rpow_const (Or.inl (by positivity))).congr_deriv ?_
  have hP : (4 * Real.pi * t) ^ (-(3 / 2 : ℝ) - 1)
      = (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * (4 * Real.pi * t)⁻¹ := by
    rw [show -(3 / 2 : ℝ) - 1 = -(3 / 2 : ℝ) + (-1) by ring, Real.rpow_add (by positivity),
      Real.rpow_neg_one]
  rw [hP]
  have key : 4 * (Real.pi : ℝ) * (-(3 / 2 : ℝ)) * (4 * Real.pi * t)⁻¹ = -(3 / (2 * t)) := by
    field_simp
  rw [show 4 * (Real.pi : ℝ) * (-(3 / 2 : ℝ)) *
        ((4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * (4 * Real.pi * t)⁻¹)
      = (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) *
          (4 * (Real.pi : ℝ) * (-(3 / 2 : ℝ)) * (4 * Real.pi * t)⁻¹) by ring]
  rw [key]
  ring

/-- Derivative of the Gaussian factor `t ↦ exp(-‖z‖²/(4t))` of the heat kernel. -/
lemma hasDerivAt_heatGauss (t : ℝ) (ht : 0 < t) (z : R3) :
    HasDerivAt (fun s : ℝ => Real.exp (-(‖z‖ ^ 2 / (4 * s))))
      (Real.exp (-(‖z‖ ^ 2 / (4 * t))) * (‖z‖ ^ 2 / (4 * t ^ 2))) t := by
  have hb : HasDerivAt (fun s : ℝ => 4 * s) (4 : ℝ) t := by
    simpa using (hasDerivAt_id t).const_mul (4 : ℝ)
  have h2 : HasDerivAt (fun s : ℝ => (4 * s)⁻¹) (-(4 : ℝ) / (4 * t) ^ 2) t :=
    hb.inv (by positivity)
  have h3 : HasDerivAt (fun s : ℝ => ‖z‖ ^ 2 * (4 * s)⁻¹)
      (‖z‖ ^ 2 * (-(4 : ℝ) / (4 * t) ^ 2)) t := h2.const_mul (‖z‖ ^ 2)
  refine (h3.neg).exp.congr_deriv ?_
  simp only [Pi.neg_apply, div_eq_mul_inv]
  field_simp

theorem deriv_heatKernel_time (t : ℝ) (ht : 0 < t) (z : Work.FTS.PressureOn.R3) :
    deriv (fun s : ℝ => Work.FTS.PressureOn.Auxiliary.heatKernel s z) t
      = (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * (‖z‖ ^ 2 / (4 * t ^ 2) - 3 / (2 * t)) *
          Real.exp (-(‖z‖ ^ 2 / (4 * t))) := by
  simp only [heatKernel_apply]
  have hprod : HasDerivAt (fun s : ℝ => (4 * Real.pi * s) ^ (-(3 / 2 : ℝ)) *
      Real.exp (-(‖z‖ ^ 2 / (4 * s))))
      (-(3 / (2 * t)) * (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) *
          Real.exp (-(‖z‖ ^ 2 / (4 * t))) +
        (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) *
          (Real.exp (-(‖z‖ ^ 2 / (4 * t))) * (‖z‖ ^ 2 / (4 * t ^ 2)))) t :=
    (hasDerivAt_heatPrefactor t ht).mul (hasDerivAt_heatGauss t ht z)
  rw [hprod.deriv]
  ring

end Work.FTS.PressureOn.Auxiliary
end
-- ===== merged: Submission.Work.FTS.PressureOn.Auxiliary.div_laplaceTraceVec =====
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

/-! ## Calculus preliminaries -/

/-- **The coordinate of a derivative is the derivative of the coordinate**: for a vector field `g`
differentiable at `x`, `(Dg(x) v) i = D(y ↦ g(y)_i)(x) v`. -/
theorem fderiv_coord (g : R3 → R3) {x : R3} (hg : DifferentiableAt ℝ g x) (i : Fin 3) (v : R3) :
    (fderiv ℝ g x v) i = fderiv ℝ (fun y => (g y) i) x v := by
  have h := (hasFDerivWithinAt_piLp (𝕜 := ℝ) (p := (2 : ENNReal)) (E := fun _ : Fin 3 => ℝ)
      (f := g) (f' := fderiv ℝ g x) (t := Set.univ) (y := x)).mp
      hg.hasFDerivAt.hasFDerivWithinAt i
  rw [hasFDerivWithinAt_univ] at h
  rw [h.fderiv]
  simp [PiLp.proj_apply, ContinuousLinearMap.comp_apply]


/-! ## The coordinates of the curl

In the standard basis the three components of `∇ × V` are the classical expressions. -/

/-- First coordinate of the curl: `(∇×V)₀ = ∂₁V₂ − ∂₂V₁`. -/
theorem vorticity_coord_zero (V : R3 → R3) (y : R3) :
    (vorticity V y) 0 = (fderiv ℝ V y (e 1)) 2 - (fderiv ℝ V y (e 2)) 1 := by
  show (vorticity V y).ofLp 0 = _
  rw [show (vorticity V y).ofLp
        = ∑ i : Fin 3, ((e i : Fin 3 → ℝ) ⨯₃ (fderiv ℝ V y (e i) : Fin 3 → ℝ)) from rfl,
      Fin.sum_univ_three]
  simp only [cross_apply, FiniteTimeSingularity.e, WithLp.ofLp_toLp]
  norm_num [PiLp.single_apply]
  ring

/-- Second coordinate of the curl: `(∇×V)₁ = ∂₂V₀ − ∂₀V₂`. -/
theorem vorticity_coord_one (V : R3 → R3) (y : R3) :
    (vorticity V y) 1 = (fderiv ℝ V y (e 2)) 0 - (fderiv ℝ V y (e 0)) 2 := by
  show (vorticity V y).ofLp 1 = _
  rw [show (vorticity V y).ofLp
        = ∑ i : Fin 3, ((e i : Fin 3 → ℝ) ⨯₃ (fderiv ℝ V y (e i) : Fin 3 → ℝ)) from rfl,
      Fin.sum_univ_three]
  simp only [cross_apply, FiniteTimeSingularity.e, WithLp.ofLp_toLp]
  norm_num [PiLp.single_apply]
  ring

/-- Third coordinate of the curl: `(∇×V)₂ = ∂₀V₁ − ∂₁V₀`. -/
theorem vorticity_coord_two (V : R3 → R3) (y : R3) :
    (vorticity V y) 2 = (fderiv ℝ V y (e 0)) 1 - (fderiv ℝ V y (e 1)) 0 := by
  show (vorticity V y).ofLp 2 = _
  rw [show (vorticity V y).ofLp
        = ∑ i : Fin 3, ((e i : Fin 3 → ℝ) ⨯₃ (fderiv ℝ V y (e i) : Fin 3 → ℝ)) from rfl,
      Fin.sum_univ_three]
  simp only [cross_apply, FiniteTimeSingularity.e, WithLp.ofLp_toLp]
  norm_num [PiLp.single_apply]
  ring

/-! ## Differentiating a coordinate of a derivative

The scalar maps `y ↦ (DV(y) · a) b` are the composites of the continuous linear functionals
`L ↦ (L a) b` with `DV`, so they are differentiable as soon as `DV` is, with the chain-rule
derivative `(D²V(x) · a) b`. -/

/-- The `b`-th coordinate of `ℝ³` as a continuous linear functional. -/
noncomputable def coordCLM (b : Fin 3) : R3 →L[ℝ] ℝ :=
  PiLp.proj (p := 2) (β := fun _ : Fin 3 => ℝ) b

theorem coordCLM_apply (b : Fin 3) (v : R3) : coordCLM b v = v b := by
  simp only [coordCLM, PiLp.proj_apply]

/-- Differentiability of `y ↦ (DV(y) · a) b`. -/
theorem differentiableAt_fderiv_coord (V : R3 → R3) {x : R3}
    (hΦd : DifferentiableAt ℝ (fderiv ℝ V) x) (a : R3) (b : Fin 3) :
    DifferentiableAt ℝ (fun y : R3 => (fderiv ℝ V y a) b) x := by
  have heq : (fun y : R3 => (fderiv ℝ V y a) b)
      = (coordCLM b) ∘ ((ContinuousLinearMap.apply ℝ R3 a) ∘ (fderiv ℝ V)) := by
    funext y
    simp only [Function.comp_apply, coordCLM_apply, ContinuousLinearMap.apply_apply]
  rw [heq]
  exact ((ContinuousLinearMap.hasFDerivAt (coordCLM b)).comp x
    ((ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.apply ℝ R3 a)).comp x
      hΦd.hasFDerivAt)).differentiableAt

/-- The chain rule for a coordinate of a derivative:
`D(y ↦ (DV(y) · a) b)(x) · v = (D²V(x) · v · a) b`. -/
theorem fderiv_fderiv_V_coord (V : R3 → R3) {x : R3}
    (hΦd : DifferentiableAt ℝ (fderiv ℝ V) x) (a : R3) (b : Fin 3) (k : Fin 3) :
    fderiv ℝ (fun y : R3 => (fderiv ℝ V y a) b) x (e k)
      = ((fderiv ℝ (fderiv ℝ V) x (e k)) a) b := by
  have heq : (fun y : R3 => (fderiv ℝ V y a) b)
      = (coordCLM b) ∘ ((ContinuousLinearMap.apply ℝ R3 a) ∘ (fderiv ℝ V)) := by
    funext y
    simp only [Function.comp_apply, coordCLM_apply, ContinuousLinearMap.apply_apply]
  have h := (ContinuousLinearMap.hasFDerivAt (coordCLM b)).comp x
    ((ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.apply ℝ R3 a)).comp x
      hΦd.hasFDerivAt)
  rw [heq, h.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply, coordCLM_apply]

/-! ## Smoothness of `div` and of the curl -/

/-- The trace as a continuous linear functional on `ℝ³ →L[ℝ] ℝ³`. -/
noncomputable def divTraceCLM : (R3 →L[ℝ] R3) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap ((LinearMap.trace ℝ R3).comp (ContinuousLinearMap.coeLM ℝ))

/-- `div` is the trace of the derivative. -/
theorem div_eq_divTraceCLM (W : R3 → R3) (x : R3) :
    div W x = divTraceCLM (fderiv ℝ W x) := rfl

/-- The divergence of a smooth vector field is smooth. -/
theorem contDiff_div (W : R3 → R3) (hW : ∀ n : ℕ, ContDiff ℝ n W) :
    ∀ n : ℕ, ContDiff ℝ n (div W) := by
  intro n
  have h : div W = fun x => divTraceCLM (fderiv ℝ W x) :=
    funext fun x => div_eq_divTraceCLM W x
  rw [h]
  exact (ContinuousLinearMap.contDiff divTraceCLM).comp
    ((hW (n + 1)).fderiv_right (by simp))

/-- The curl of a smooth vector field is smooth. -/
theorem contDiff_vorticity (V : R3 → R3) (hV : ∀ n : ℕ, ContDiff ℝ n V) :
    ∀ n : ℕ, ContDiff ℝ n (vorticity V) := by
  intro n
  have h : vorticity V = fun x => Work.FTS.Physical.Pressure.curlCLM (fderiv ℝ V x) :=
    funext fun x => Work.FTS.Physical.Pressure.vorticity_eq_curlCLM V x
  rw [h]
  exact (ContinuousLinearMap.contDiff Work.FTS.Physical.Pressure.curlCLM).comp
    ((hV (n + 1)).fderiv_right (by simp))

/-- The `k`-th coordinate of the derivative of the `k`-th coordinate of the curl, in closed form. -/
theorem fderiv_vorticity_coord (V : R3 → R3) (hV : ∀ n : ℕ, ContDiff ℝ n V) (x : R3)
    (k a b : Fin 3)
    (hcoord : (fun y : R3 => (vorticity V y) k)
        = fun y => (fderiv ℝ V y (e a)) b - (fderiv ℝ V y (e b)) a) :
    (fderiv ℝ (vorticity V) x (e k)) k
      = ((fderiv ℝ (fderiv ℝ V) x (e k) (e a)) b)
        - ((fderiv ℝ (fderiv ℝ V) x (e k) (e b)) a) := by
  have hΦd : DifferentiableAt ℝ (fderiv ℝ V) x := by
    have h : ContDiff ℝ 1 (fderiv ℝ V) := (hV 2).fderiv_right (by norm_num)
    exact (h.differentiable (by norm_num)).differentiableAt
  have hvortd : DifferentiableAt ℝ (vorticity V) x :=
    ((contDiff_vorticity V hV 1).differentiable (by norm_num)).differentiableAt
  rw [fderiv_coord (vorticity V) hvortd k (e k), hcoord,
    fderiv_fun_sub (differentiableAt_fderiv_coord V hΦd (e a) b)
      (differentiableAt_fderiv_coord V hΦd (e b) a)]
  change fderiv ℝ (fun y : R3 => (fderiv ℝ V y (e a)) b) x (e k)
      - fderiv ℝ (fun y : R3 => (fderiv ℝ V y (e b)) a) x (e k) = _
  rw [fderiv_fderiv_V_coord V hΦd (e a) b k, fderiv_fderiv_V_coord V hΦd (e b) a k]

/-! ## `div (∇×V) = 0` -/

/-- **The divergence of a curl vanishes.** -/
theorem div_vorticity_eq_zero (V : R3 → R3) (hV : ∀ n : ℕ, ContDiff ℝ n V) :
    div (vorticity V) = 0 := by
  funext x
  change div (vorticity V) x = 0
  have hS : IsSymmSndFDerivAt ℝ V x := ((hV 2).contDiffAt).isSymmSndFDerivAt (by simp)
  have hsymm : ∀ u w : R3,
      fderiv ℝ (fderiv ℝ V) x u w = fderiv ℝ (fderiv ℝ V) x w u := fun u w => hS.eq u w
  have h0 := fderiv_vorticity_coord V hV x 0 1 2 (funext (vorticity_coord_zero V))
  have h1 := fderiv_vorticity_coord V hV x 1 2 0 (funext (vorticity_coord_one V))
  have h2 := fderiv_vorticity_coord V hV x 2 0 1 (funext (vorticity_coord_two V))
  rw [vorticityCross_div_eq_sum_diag, Fin.sum_univ_three]
  rw [h0, h1, h2]
  have hD : ((fderiv ℝ (fderiv ℝ V) x (e 1)) (e 0)) 2
      = ((fderiv ℝ (fderiv ℝ V) x (e 0)) (e 1)) 2 :=
    congrArg (fun v : R3 => v 2) (hsymm (e 1) (e 0))
  have hE : ((fderiv ℝ (fderiv ℝ V) x (e 2)) (e 0)) 1
      = ((fderiv ℝ (fderiv ℝ V) x (e 0)) (e 2)) 1 :=
    congrArg (fun v : R3 => v 1) (hsymm (e 2) (e 0))
  have hF : ((fderiv ℝ (fderiv ℝ V) x (e 2)) (e 1)) 0
      = ((fderiv ℝ (fderiv ℝ V) x (e 1)) (e 2)) 0 :=
    congrArg (fun v : R3 => v 0) (hsymm (e 2) (e 1))
  rw [hD, hE, hF]
  ring

/-! ## The target -/

theorem div_laplaceTraceVec (W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hW : ∀ n : ℕ, ContDiff ℝ n W) (x : EuclideanSpace ℝ (Fin 3)) :
    FiniteTimeSingularity.div (Work.FTS.PressureOn.laplaceTraceVec W) x
      = Work.FTS.PressureOn.laplaceTrace (FiniteTimeSingularity.div W) x := by
  have hsub : laplaceTraceVec W = fun y => gradient (div W) y - vorticity (vorticity W) y :=
    funext fun y => laplaceTraceVec_identity W hW y
  have hdiv2 : ContDiff ℝ 2 (div W) := contDiff_div W hW 2
  have hdiff1 : DifferentiableAt ℝ (fun y => gradient (div W) y) x :=
    ((Green.contDiff_gradient (div W) hdiv2).differentiable (by norm_num)).differentiableAt
  have hdiff2 : DifferentiableAt ℝ (fun y => vorticity (vorticity W) y) x :=
    ((contDiff_vorticity (vorticity W) (contDiff_vorticity W hW) 1).differentiable
      (by norm_num)).differentiableAt
  rw [hsub, Green.div_sub_eq (fun y => gradient (div W) y)
        (fun y => vorticity (vorticity W) y) x hdiff1 hdiff2,
      Green.div_gradient_eq_laplaceTrace (div W) hdiv2,
      div_vorticity_eq_zero (vorticity W) (contDiff_vorticity W hW)]
  simp

end Work.FTS.PressureOn.Auxiliary
end
-- ===== merged: Submission.Work.FTS.PressureOn.Auxiliary.ihak_GaussFacts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Gaussian integrability and the Gaussian integral on `ℝ³`

Two elementary facts about the Gaussian weight `w ↦ exp (-(a ‖w‖²))` on `ℝ³` (`a > 0`):
integrability, and the value `(π/a)^{3/2}` of the integral.  They are the analytic input of the
`L¹` modulus of continuity of the heat kernel
(`Work.FTS.PressureOn.Auxiliary.integral_abs_heatKernel_sub_le`) and of the shear-averaging lemma
`Work.FTS.PressureOn.Auxiliary.ihak_interval_shift_mean`.

Both are immediate from Mathlib's `GaussianFourier.integrable_cexp_neg_mul_sq_norm_add` /
`GaussianFourier.integral_rexp_neg_mul_sq_norm` (the Gaussian integral in an arbitrary
finite dimensional real inner product space), specialised to `V = ℝ³`.
-/

open MeasureTheory
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.PressureOn.Auxiliary

noncomputable section

/-- The Gaussian `w ↦ exp (-(a ‖w‖²))` is integrable on `ℝ³` for `a > 0`. -/
theorem ihak_integrable_rexp_normSq (a : ℝ) (ha : 0 < a) :
    Integrable (fun w : R3 => Real.exp (-(a * ‖w‖ ^ 2))) volume := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := R3)
    (b := (a : ℂ)) (by simpa using ha) 0 0
  simp only [zero_mul, add_zero] at h
  refine (h.norm).congr (Filter.Eventually.of_forall fun v => ?_)
  dsimp only
  rw [show (-(↑a : ℂ)) * (↑‖v‖ : ℂ) ^ 2 = ↑(-(a * ‖v‖ ^ 2)) by push_cast; ring,
    Complex.norm_exp, Complex.ofReal_re]

/-- The Gaussian integral on `ℝ³`: `∫ w, exp (-(a ‖w‖²)) = (π/a)^{3/2}` for `a > 0`. -/
theorem ihak_integral_rexp_normSq (a : ℝ) (ha : 0 < a) :
    ∫ w : R3, Real.exp (-(a * ‖w‖ ^ 2)) = (Real.pi / a) ^ ((3 : ℝ) / 2) := by
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := R3) (b := a) ha
  simp only [neg_mul] at h ⊢
  rw [h, finrank_euclideanSpace_fin]
  norm_num



end

end Work.FTS.PressureOn.Auxiliary
end
-- ===== merged: Submission.Work.FTS.PressureOn.Auxiliary.ihak_hasDerivAt_heatKernel_sub_smul =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Auxiliary

theorem ihak_hasDerivAt_heatKernel_sub_smul (t : ℝ) (ht : 0 < t) (z h : Work.FTS.PressureOn.R3)
    (s : ℝ) :
    HasDerivAt (fun r : ℝ => Work.FTS.PressureOn.Auxiliary.heatKernel t (z - r • h))
      (Work.FTS.PressureOn.Auxiliary.heatKernel t (z - s • h) * (inner ℝ (z - s • h) h) / (2 * t))
      s := by
  -- The heat kernel along the affine line `r ↦ z - r • h` is a constant times the exponential of
  -- a quadratic polynomial in `r`; we differentiate that explicitly.
  have ht4 : (4 * t) ≠ 0 := by positivity
  -- expansion of the squared norm along the line
  have hnorm : ∀ r : ℝ, ‖z - r • h‖ ^ 2 = r^2 * ‖h‖^2 - 2*r*(inner ℝ z h) + ‖z‖^2 := by
    intro r
    rw [norm_sub_sq (𝕜 := ℝ), real_inner_smul_right, norm_smul]
    simp only [RCLike.re_to_real, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  -- the derivative of that quadratic
  have hpoly : HasDerivAt (fun r : ℝ => r^2 * ‖h‖^2 - 2*r*(inner ℝ z h) + ‖z‖^2)
      (2*s*‖h‖^2 - 2*(inner ℝ z h)) s := by
    have hA' : HasDerivAt (fun r : ℝ => r ^ 2 * ‖h‖^2) (2 * s * ‖h‖^2) s := by
      simpa using ((hasDerivAt_id s).pow 2).mul_const (‖h‖^2)
    have hB' : HasDerivAt (fun r : ℝ => 2 * r * (inner ℝ z h)) (2 * (inner ℝ z h)) s := by
      simpa using (((hasDerivAt_id s).const_mul 2).mul_const (inner ℝ z h))
    have hC' : HasDerivAt (fun r : ℝ => ‖z‖^2) 0 s := hasDerivAt_const s (‖z‖^2)
    have h := (hA'.sub hB').add hC'
    convert h using 2
    ring
  -- `⟪z - s • h, h⟫ / (2t) = -(2 s ‖h‖² - 2 ⟪z, h⟫) / (4t)`
  have hinner : (inner ℝ (z - s • h) h)/(2*t) = -(2*s*‖h‖^2 - 2*(inner ℝ z h))/(4*t) := by
    rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp
    ring
  have hG : HasDerivAt (fun r : ℝ => -((r^2 * ‖h‖^2 - 2*r*(inner ℝ z h) + ‖z‖^2)/(4*t)))
      ((inner ℝ (z - s • h) h)/(2*t)) s := by
    have h := (hpoly.div_const (4*t)).neg
    convert h using 1
    rw [← neg_div]
    exact hinner
  have hexp := hG.exp
  have hfin := hexp.const_mul ((4 * Real.pi * t) ^ (-(3 / 2 : ℝ)))
  convert hfin using 1
  · funext r
    rw [heatKernel, hnorm r]
  · rw [heatKernel, hnorm s]
    ring

end Work.FTS.PressureOn.Auxiliary
end
-- ===== merged: Submission.Work.FTS.PressureOn.Auxiliary.integrable_gaussMajorant =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Auxiliary

open MeasureTheory

set_option linter.unusedVariables false

/-- A quadratic (in fact polynomial) growth factor is integrable against a Gaussian
`exp (-(c ‖z‖²))` on `ℝ³` with `c > 0`: `z ↦ (a + b‖z‖²) exp (-(c ‖z‖²)) ∈ L¹(ℝ³)`.

This is the standard Gauss majorant estimate; it is used to dominate the Newtonian
kernel and its gradients far away from the origin.

The proof passes to polar coordinates in `EuclideanSpace ℝ (Fin 3)` with
`MeasureTheory.integrable_fun_norm_addHaar`, which reduces the claim to the integrability
on `(0,∞)` of `y ^ (2 + k) * exp (-c y²)` (`k = 0, 2`), i.e. to
`integrableOn_rpow_mul_exp_neg_mul_sq` with exponent `s = 2` resp. `s = 4`. -/
theorem integrable_gaussMajorant (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 < c) :
    MeasureTheory.Integrable (fun z : Work.FTS.PressureOn.R3 =>
      (a + b * ‖z‖ ^ 2) * Real.exp (-(c * ‖z‖ ^ 2))) := by
  rw [MeasureTheory.integrable_fun_norm_addHaar
    (μ := (MeasureTheory.volume : MeasureTheory.Measure Work.FTS.PressureOn.R3))
    (f := fun y : ℝ => (a + b * y ^ 2) * Real.exp (-(c * y ^ 2)))]
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul]
  have h2 : IntegrableOn (fun y : ℝ => y ^ (((2 : ℕ)) : ℝ) * Real.exp (-c * y ^ 2))
      (Set.Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_sq hc (by norm_num)
  have h4 : IntegrableOn (fun y : ℝ => y ^ (((4 : ℕ)) : ℝ) * Real.exp (-c * y ^ 2))
      (Set.Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_sq hc (by norm_num)
  have hsum : IntegrableOn
      (fun y : ℝ => a * (y ^ (((2 : ℕ)) : ℝ) * Real.exp (-c * y ^ 2))
        + b * (y ^ (((4 : ℕ)) : ℝ) * Real.exp (-c * y ^ 2))) (Set.Ioi 0) :=
    (h2.const_mul a).add (h4.const_mul b)
  exact MeasureTheory.IntegrableOn.congr_fun hsum (fun y hy => by
    have hy0 : 0 ≤ y := le_of_lt hy
    rw [Real.rpow_natCast, Real.rpow_natCast]
    norm_num
    rw [← neg_mul]
    ring) measurableSet_Ioi

end Work.FTS.PressureOn.Auxiliary
end
-- ===== merged: Submission.Work.FTS.PressureOn.Auxiliary.integral_heatKernel =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.PressureOn.Auxiliary

/-- The Gaussian integral on `ℝ³` with a positive quadratic coefficient:
`∫ z : ℝ³, exp (-(a‖z‖²)) = (π/a)^{3/2}` for `a > 0`.

The type `R3 = EuclideanSpace ℝ (Fin 3)` is `WithLp 2 (Fin 3 → ℝ)`, and `WithLp.toLp 2` is volume
preserving, so the integral factorises over the three coordinates; each one-dimensional factor is
the classical Gaussian integral `∫ x, exp (-a x²) = √(π/a)`. -/
private lemma integral_exp_neg_mul_normSq (a : ℝ) (ha : 0 < a) :
    ∫ z : R3, Real.exp (-(a * ‖z‖ ^ 2)) = (Real.pi / a) ^ (3 / 2 : ℝ) := by
  -- Move from `EuclideanSpace ℝ (Fin 3)` to `Fin 3 → ℝ` (volume preserving).
  rw [← (PiLp.volume_preserving_toLp (Fin 3)).integral_comp
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding
    (fun z : R3 => Real.exp (-(a * ‖z‖ ^ 2)))]
  -- Write the Gaussian as a product over the three coordinates.
  have hpoint : (fun x : Fin 3 → ℝ =>
        Real.exp (-(a * ‖(WithLp.toLp 2 x : R3)‖ ^ 2)))
      = fun x => ∏ i, Real.exp (-(a * (x i) ^ 2)) := by
    funext x
    rw [← Real.exp_sum]
    congr 1
    rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum, Finset.sum_neg_distrib]
  rw [hpoint]
  -- Fubini in three variables.
  rw [integral_fintype_prod_volume_eq_pow (f := fun x : ℝ => Real.exp (-(a * x ^ 2)))]
  rw [Fintype.card_fin]
  -- The one-dimensional Gaussian integral, and `(√(π/a))³ = (π/a)^{3/2}`.
  have h1 : (∫ x : ℝ, Real.exp (-(a * x ^ 2))) = Real.sqrt (Real.pi / a) := by
    simpa only [neg_mul] using integral_gaussian a
  have h3 : (Real.sqrt (Real.pi / a)) ^ (3 : ℕ) = (Real.pi / a) ^ (3 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast ((Real.pi / a) ^ (1 / 2 : ℝ)) 3]
    rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ Real.pi / a) (1 / 2) ((3 : ℕ) : ℝ)]
    rw [show (1 / 2 : ℝ) * ((3 : ℕ) : ℝ) = 3 / 2 by norm_num]
  rw [h1, h3]

theorem integral_heatKernel (t : ℝ) (ht : 0 < t) :
    ∫ z : Work.FTS.PressureOn.R3, Work.FTS.PressureOn.Auxiliary.heatKernel t z = 1 := by
  have ht4 : (0 : ℝ) < 4 * t := by linarith
  have ha : (0 : ℝ) < (4 * t)⁻¹ := inv_pos.mpr ht4
  -- Pull out the constant prefactor and write the exponent as `-(a‖z‖²)`.
  have hsplit : ∫ z : R3, heatKernel t z =
      (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) *
        ∫ z : R3, Real.exp (-((4 * t)⁻¹ * ‖z‖ ^ 2)) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with z
    exact heatKernel_eq_const_mul_exp ht z
  rw [hsplit, integral_exp_neg_mul_normSq ((4 * t)⁻¹) ha]
  -- `π / (4t)^{-1} = 4πt`, and `x^{-3/2} x^{3/2} = 1`.
  have hpi : Real.pi / (4 * t)⁻¹ = 4 * Real.pi * t := by
    rw [div_inv_eq_mul]
    ring
  have hpos : (0 : ℝ) < 4 * Real.pi * t := by positivity
  rw [hpi, Real.rpow_neg hpos.le (3 / 2 : ℝ)]
  exact inv_mul_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos hpos (3 / 2 : ℝ)))

end Work.FTS.PressureOn.Auxiliary
end
-- ===== merged: Submission.Work.FTS.PressureOn.Auxiliary.laplaceTrace_comp_sub =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `laplaceTrace` is invariant under the reflection `y' ↦ x - y'`

The Laplace trace `laplaceTrace φ x = ∑ᵢ ∂ᵢ∂ᵢ φ(x)` of a function on `ℝ³` is unchanged by
precomposing `φ` with the reflection `y' ↦ x - y'`:

`laplaceTrace (fun y' => φ (x - y')) y = laplaceTrace φ (x - y)`.

This is the second-derivative chain rule for the affine substitution `y' ↦ x - y'` (whose Fréchet
derivative is the constant `-1` and whose second derivative vanishes), applied twice: the first
derivative of `φ (x - ·)` at `w` is `-(fderiv ℝ φ (x - w))`, and differentiating once more the two
signs cancel against the sign produced by evaluating the reflection at `eᵢ`.

The pointwise inputs are the Mathlib chain rule `fderiv_comp` and the fact that
`fderiv ℝ (fun y' => x - y') w = -1`.
-/

set_option autoImplicit false

namespace Work.FTS.PressureOn.Auxiliary

open scoped Topology

/-- The Fréchet derivative of the reflection `y' ↦ x - y'` is the constant `-1`. -/
private lemma fderiv_sub_const_id (x w : R3) :
    fderiv ℝ (fun y' : R3 => x - y') w = -(1 : R3 →L[ℝ] R3) := by
  have hid : HasFDerivAt (fun y : R3 => y) (1 : R3 →L[ℝ] R3) w := hasFDerivAt_id w
  simpa using (hid.const_sub x).fderiv

/-- First-order chain rule for the substitution `y' ↦ x - y'`: the derivative of `f (x - ·)` at
`w` is `-(fderiv ℝ f (x - w))`. -/
private lemma fderiv_comp_sub_left (f : R3 → ℝ) (hf : Differentiable ℝ f) (x w : R3) :
    fderiv ℝ (fun y' : R3 => f (x - y')) w = -(fderiv ℝ f (x - w)) := by
  have hTdiff : DifferentiableAt ℝ (fun y' : R3 => x - y') w :=
    (differentiableAt_const x).sub differentiableAt_id
  have hcomp := fderiv_comp (𝕜 := ℝ) (x := w) (f := fun y' : R3 => x - y') (g := f)
    (hf (x - w)) hTdiff
  change fderiv ℝ (f ∘ (fun y' : R3 => x - y')) w = -(fderiv ℝ f (x - w))
  rw [hcomp, fderiv_sub_const_id x w]
  rw [show (-(1 : R3 →L[ℝ] R3)) = -(ContinuousLinearMap.id ℝ R3) from rfl,
    ContinuousLinearMap.comp_neg, ContinuousLinearMap.comp_id]

/-- Second-order chain rule for the substitution `y' ↦ x - y'`, one coordinate at a time: the
second derivative of `f (x - ·)` in the direction `eᵢ`, at `y`, equals the second derivative of `f`
at `x - y`. -/
private lemma fderiv_fderiv_comp_sub_left (f : R3 → ℝ) (hf : ContDiff ℝ 2 f) (x y : R3)
    (i : Fin 3) :
    fderiv ℝ (fun w : R3 => fderiv ℝ (fun y' : R3 => f (x - y')) w
        (FiniteTimeSingularity.e i)) y (FiniteTimeSingularity.e i)
      = fderiv ℝ (fun w : R3 => fderiv ℝ f w (FiniteTimeSingularity.e i)) (x - y)
        (FiniteTimeSingularity.e i) := by
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  set G : R3 → ℝ := fun t => fderiv ℝ f t (FiniteTimeSingularity.e i) with hG
  have hC1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (m := 1) (by norm_num)
  have hgd : Differentiable ℝ G := by
    have h := (((ContinuousLinearMap.apply ℝ ℝ) (FiniteTimeSingularity.e i)).differentiable.comp
      (hC1.differentiable (by norm_num)))
    simpa [hG, Function.comp_def, ContinuousLinearMap.apply_apply] using h
  have h1 : (fun w : R3 => fderiv ℝ (fun y' : R3 => f (x - y')) w
        (FiniteTimeSingularity.e i))
      = fun w : R3 => - G (x - w) := by
    funext w
    rw [fderiv_comp_sub_left f hfd x w]
    rfl
  rw [h1, fderiv_fun_neg, fderiv_comp_sub_left G hgd x y]
  simp

theorem laplaceTrace_comp_sub (f : Work.FTS.PressureOn.R3 → ℝ) (hf : ContDiff ℝ 2 f)
    (x y : Work.FTS.PressureOn.R3) :
    Work.FTS.PressureOn.laplaceTrace (fun y' : Work.FTS.PressureOn.R3 => f (x - y')) y
      = Work.FTS.PressureOn.laplaceTrace f (x - y) := by
  rw [laplaceTrace, laplaceTrace]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact fderiv_fderiv_comp_sub_left f hf x y i

end Work.FTS.PressureOn.Auxiliary
end
-- ===== merged: Submission.Work.FTS.PressureOn.Auxiliary.outerCutBoundsAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter Topology
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.PressureOn.Auxiliary

noncomputable section

/-! ## The cutoff `outerCut R` -/

/-- Inside the open ball of radius `R` the cutoff `outerCut R` is locally the constant `1`, hence
its derivative vanishes there. -/
lemma fderiv_outerCut_eq_zero_of_norm_lt {R : ℝ} (hR : 0 < R) {y : R3} (hy : ‖y‖ < R) :
    fderiv ℝ (Work.FTS.PressureOn.outerCut R) y = 0 := by
  have hmem : Metric.ball (0 : R3) R ∈ 𝓝 y :=
    Metric.isOpen_ball.mem_nhds (by rw [Metric.mem_ball, dist_zero_right]; exact hy)
  have hev : Work.FTS.PressureOn.outerCut R =ᶠ[𝓝 y] (fun _ : R3 => (1 : ℝ)) := by
    filter_upwards [hmem] with z hz
    rw [Metric.mem_ball, dist_zero_right] at hz
    exact Work.FTS.PressureOn.outerCut_eq_one hR hz.le
  rw [hev.fderiv_eq]
  simp

/-- Inside the open ball of radius `R` the Laplace trace of the cutoff `outerCut R` vanishes. -/
lemma laplaceTrace_outerCut_eq_zero_of_norm_lt {R : ℝ} (hR : 0 < R) {y : R3} (hy : ‖y‖ < R) :
    Work.FTS.PressureOn.laplaceTrace (Work.FTS.PressureOn.outerCut R) y = 0 := by
  have hmem : Metric.ball (0 : R3) R ∈ 𝓝 y :=
    Metric.isOpen_ball.mem_nhds (by rw [Metric.mem_ball, dist_zero_right]; exact hy)
  have hfd : (fun w : R3 => fderiv ℝ (Work.FTS.PressureOn.outerCut R) w)
      =ᶠ[𝓝 y] (fun _ : R3 => 0) := by
    filter_upwards [hmem] with z hz
    rw [Metric.mem_ball, dist_zero_right] at hz
    exact fderiv_outerCut_eq_zero_of_norm_lt hR hz
  rw [Work.FTS.PressureOn.laplaceTrace]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hev : (fun w : R3 => fderiv ℝ (Work.FTS.PressureOn.outerCut R) w
      (FiniteTimeSingularity.e i)) =ᶠ[𝓝 y] (fun _ : R3 => (0 : ℝ)) := by
    filter_upwards [hfd] with z hz
    rw [hz]
    simp
  rw [hev.fderiv_eq]
  simp

/-- The second derivative of `radialCut` vanishes above `2`. -/
lemma radialCut_deriv_deriv_eq_zero_of_two_lt {t : ℝ} (ht : 2 < t) :
    deriv (deriv Work.FTS.PressureOn.radialCut) t = 0 :=
  Work.FTS.PressureOn.PoissonAux.deriv_deriv_eq_zero_of_isOpen_const isOpen_Ioi ht
    (fun s hs => Work.FTS.PressureOn.radialCut_eq_zero hs.le)

/-- The second derivative of `radialCut` is bounded on `ℝ`. -/
lemma exists_bound_deriv_deriv_radialCut :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, |deriv (deriv Work.FTS.PressureOn.radialCut) t| ≤ B := by
  have hcont : Continuous (deriv (deriv Work.FTS.PressureOn.radialCut)) := by
    have hcd : ContDiff ℝ 1 (deriv Work.FTS.PressureOn.radialCut) := by
      simpa only [Nat.reduceAdd] using (Work.FTS.PressureOn.contDiff_radialCut 2).deriv'
    exact hcd.continuous_deriv_one
  obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support
    (Work.FTS.PressureOn.PoissonAux.hasCompactSupport_deriv_radialCut.deriv)
  exact ⟨C, le_trans (norm_nonneg _) (hC 0), fun t => by
    rw [← Real.norm_eq_abs]; exact hC t⟩

/-- The chain rule for the rescaled profile `s ↦ radialCut (s / R ^ 2)`. -/
lemma deriv_radialCut_div (R s : ℝ) :
    deriv (fun s : ℝ => Work.FTS.PressureOn.radialCut (s / R ^ 2)) s
      = deriv Work.FTS.PressureOn.radialCut (s / R ^ 2) * (1 / R ^ 2) := by
  have h1 : HasDerivAt (fun s : ℝ => s / R ^ 2) (1 / R ^ 2) s :=
    (hasDerivAt_id s).div_const _
  have h2 : HasDerivAt Work.FTS.PressureOn.radialCut
      (deriv Work.FTS.PressureOn.radialCut (s / R ^ 2)) (s / R ^ 2) :=
    ((Work.FTS.PressureOn.contDiff_radialCut 1).differentiable one_ne_zero
      (s / R ^ 2)).hasDerivAt
  exact (h2.comp s h1).deriv

/-- **Uniform bound for the derivative of the cutoff.** -/
lemma exists_bound_fderiv_outerCut :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ R : ℝ, 1 ≤ R → ∀ y : R3,
      ‖fderiv ℝ (Work.FTS.PressureOn.outerCut R) y‖ ≤ A := by
  obtain ⟨A0, hA0nn, hA0⟩ := Work.FTS.PressureOn.PoissonAux.exists_bound_deriv_radialCut
  refine ⟨4 * A0, by positivity, fun R hR y => ?_⟩
  have hRpos : (0 : ℝ) < R := lt_of_lt_of_le one_pos hR
  have hR2pos : (0 : ℝ) < R ^ 2 := by positivity
  have hfd : fderiv ℝ (Work.FTS.PressureOn.outerCut R) y
      = (2 * (deriv Work.FTS.PressureOn.radialCut (‖y‖ ^ 2 / R ^ 2) * (1 / R ^ 2))) •
          innerSL ℝ y := by
    have h1 : Work.FTS.PressureOn.outerCut R
        = fun x : R3 => Work.FTS.PressureOn.radialCut (‖x‖ ^ 2 / R ^ 2) := rfl
    rw [h1, gradient_comp_normSq (fun s : ℝ => Work.FTS.PressureOn.radialCut (s / R ^ 2))
      ((Work.FTS.PressureOn.contDiff_radialCut 1).comp (contDiff_id.div_const _)) y,
      deriv_radialCut_div]
  rw [hfd, norm_smul, innerSL_apply_norm, Real.norm_eq_abs]
  by_cases hcase : ‖y‖ ^ 2 ≤ 2 * R ^ 2
  · have hynorm : ‖y‖ ≤ 2 * R := by
      have h2 : ‖y‖ ^ 2 ≤ (Real.sqrt 2 * R) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by norm_num)]
        exact hcase
      have h3 := Real.sqrt_le_sqrt h2
      rw [Real.sqrt_sq (norm_nonneg y),
        Real.sqrt_sq (by positivity : (0 : ℝ) ≤ Real.sqrt 2 * R)] at h3
      nlinarith [h3, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2, hRpos.le,
        norm_nonneg y]
    calc |2 * (deriv Work.FTS.PressureOn.radialCut (‖y‖ ^ 2 / R ^ 2) * (1 / R ^ 2))| * ‖y‖
        = (2 * (1 / R ^ 2) * |deriv Work.FTS.PressureOn.radialCut (‖y‖ ^ 2 / R ^ 2)|) * ‖y‖ := by
          rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
            abs_of_pos (by positivity : (0 : ℝ) < 1 / R ^ 2)]
          ring
      _ ≤ (2 * (1 / R ^ 2) * A0) * (2 * R) := by
          have hb : (2 * (1 / R ^ 2)) * |deriv Work.FTS.PressureOn.radialCut (‖y‖ ^ 2 / R ^ 2)|
              ≤ (2 * (1 / R ^ 2)) * A0 :=
            mul_le_mul_of_nonneg_left (hA0 _) (by positivity)
          exact mul_le_mul hb hynorm (norm_nonneg y) (by positivity)
      _ = 4 * A0 / R := by
          have hRne : R ≠ 0 := ne_of_gt hRpos
          field_simp
          ring
      _ ≤ 4 * A0 := by
          rw [div_le_iff₀ hRpos]
          nlinarith [hA0nn, hR]
  · push_neg at hcase
    have ht : (2 : ℝ) < ‖y‖ ^ 2 / R ^ 2 := by
      rw [lt_div_iff₀ hR2pos]
      linarith
    have hz : deriv Work.FTS.PressureOn.radialCut (‖y‖ ^ 2 / R ^ 2) = 0 := by
      rw [(Work.FTS.PressureOn.PoissonAux.eventuallyEq_zero_of_lt ht).deriv_eq]
      simp
    rw [hz]
    simp only [mul_zero, abs_zero, zero_mul]
    positivity

/-- **Uniform bound for the Laplace trace of the cutoff.** -/
lemma exists_bound_laplaceTrace_outerCut :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ R : ℝ, 1 ≤ R → ∀ y : R3,
      |Work.FTS.PressureOn.laplaceTrace (Work.FTS.PressureOn.outerCut R) y| ≤ B := by
  obtain ⟨A0, hA0nn, hA0⟩ := Work.FTS.PressureOn.PoissonAux.exists_bound_deriv_radialCut
  obtain ⟨A1, hA1nn, hA1⟩ := exists_bound_deriv_deriv_radialCut
  refine ⟨6 * A0 + 8 * A1, by positivity, fun R hR y => ?_⟩
  have hRpos : (0 : ℝ) < R := lt_of_lt_of_le one_pos hR
  have hR2pos : (0 : ℝ) < R ^ 2 := by positivity
  have hlt : Work.FTS.PressureOn.laplaceTrace (Work.FTS.PressureOn.outerCut R) y
      = 6 * deriv (fun s : ℝ => Work.FTS.PressureOn.radialCut (s / R ^ 2)) (‖y‖ ^ 2)
        + 4 * ‖y‖ ^ 2
            * deriv (deriv (fun s : ℝ => Work.FTS.PressureOn.radialCut (s / R ^ 2)))
                (‖y‖ ^ 2) := by
    rw [show Work.FTS.PressureOn.outerCut R
        = fun y : R3 => (fun s : ℝ => Work.FTS.PressureOn.radialCut (s / R ^ 2)) (‖y‖ ^ 2)
        from rfl]
    exact Work.FTS.PressureOn.PoissonAux.laplaceTrace_normSq _
      ((Work.FTS.PressureOn.contDiff_radialCut 2).comp (contDiff_id.div_const _)) y
  have hd1 : |deriv (fun s : ℝ => Work.FTS.PressureOn.radialCut (s / R ^ 2)) (‖y‖ ^ 2)|
      ≤ A0 / R ^ 2 := by
    have htmp : |deriv Work.FTS.PressureOn.radialCut (‖y‖ ^ 2 / R ^ 2)| * (1 / R ^ 2)
        ≤ A0 * (1 / R ^ 2) :=
      mul_le_mul_of_nonneg_right (hA0 _) (by positivity)
    rw [deriv_radialCut_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / R ^ 2)]
    simpa [div_eq_mul_inv] using htmp
  have hd2 : |deriv (deriv (fun s : ℝ => Work.FTS.PressureOn.radialCut (s / R ^ 2))) (‖y‖ ^ 2)|
      ≤ A1 / R ^ 4 := by
    rw [Work.FTS.PressureOn.PoissonAux.deriv_deriv_rescale _
        (Work.FTS.PressureOn.contDiff_radialCut 2) (R ^ 2) (‖y‖ ^ 2),
      abs_div, abs_of_pos (by positivity : (0 : ℝ) < (R ^ 2) ^ 2),
      show (R ^ 2) ^ 2 = R ^ 4 from by ring, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (hA1 _) (by positivity)
  rw [hlt]
  by_cases hcase : ‖y‖ ^ 2 ≤ 2 * R ^ 2
  · have h1 : |6 * deriv (fun s : ℝ => Work.FTS.PressureOn.radialCut (s / R ^ 2)) (‖y‖ ^ 2)
        + 4 * ‖y‖ ^ 2
            * deriv (deriv (fun s : ℝ => Work.FTS.PressureOn.radialCut (s / R ^ 2))) (‖y‖ ^ 2)|
        ≤ 6 * (A0 / R ^ 2) + 4 * ‖y‖ ^ 2 * (A1 / R ^ 4) := by
      refine le_trans (abs_add_le _ _) ?_
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
      refine add_le_add (mul_le_mul_of_nonneg_left hd1 (by norm_num)) ?_
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * ‖y‖ ^ 2)]
      exact mul_le_mul_of_nonneg_left hd2 (by positivity)
    have h2 : 6 * (A0 / R ^ 2) + 4 * ‖y‖ ^ 2 * (A1 / R ^ 4) ≤ 6 * A0 + 8 * A1 := by
      have hA0div : 6 * (A0 / R ^ 2) ≤ 6 * A0 := by
        rw [div_eq_mul_inv]
        have h1 : (R ^ 2)⁻¹ ≤ 1 := by
          rw [inv_le_one_iff₀]
          right
          nlinarith
        nlinarith [hA0nn, h1]
      have hA1div : 4 * ‖y‖ ^ 2 * (A1 / R ^ 4) ≤ 8 * A1 := by
        have h1 : 4 * ‖y‖ ^ 2 * (A1 / R ^ 4) ≤ 4 * (2 * R ^ 2) * (A1 / R ^ 4) := by
          have h2 : (0 : ℝ) ≤ A1 / R ^ 4 := by positivity
          have h3 : 4 * ‖y‖ ^ 2 ≤ 4 * (2 * R ^ 2) := by linarith only [hcase]
          exact mul_le_mul_of_nonneg_right h3 h2
        have h2 : 4 * (2 * R ^ 2) * (A1 / R ^ 4) = 8 * A1 / R ^ 2 := by
          have hRne : R ≠ 0 := ne_of_gt hRpos
          field_simp
          ring
        rw [h2] at h1
        refine le_trans h1 ?_
        rw [div_le_iff₀ hR2pos]
        have hR2ge : (1 : ℝ) ≤ R ^ 2 := by nlinarith
        nlinarith [hA1nn, hR2ge]
      linarith
    linarith
  · push_neg at hcase
    have ht : (2 : ℝ) < ‖y‖ ^ 2 / R ^ 2 := by
      rw [lt_div_iff₀ hR2pos]
      linarith
    have hz1 : deriv (fun s : ℝ => Work.FTS.PressureOn.radialCut (s / R ^ 2)) (‖y‖ ^ 2)
        = 0 := by
      rw [deriv_radialCut_div]
      have hz : deriv Work.FTS.PressureOn.radialCut (‖y‖ ^ 2 / R ^ 2) = 0 := by
        rw [(Work.FTS.PressureOn.PoissonAux.eventuallyEq_zero_of_lt ht).deriv_eq]
        simp
      rw [hz, zero_mul]
    have hz2 : deriv (deriv (fun s : ℝ => Work.FTS.PressureOn.radialCut (s / R ^ 2)))
        (‖y‖ ^ 2) = 0 := by
      rw [Work.FTS.PressureOn.PoissonAux.deriv_deriv_rescale _
        (Work.FTS.PressureOn.contDiff_radialCut 2) (R ^ 2) (‖y‖ ^ 2),
        radialCut_deriv_deriv_eq_zero_of_two_lt ht, zero_div]
    rw [hz1, hz2]
    simp only [mul_zero, add_zero, abs_zero]
    positivity

end

end Work.FTS.PressureOn.Auxiliary
end
-- ===== merged: Submission.Work.FTS.PressureOn.Connect.BoundaryTime.continuousOn_timeDeriv_strip =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Continuity of the Newtonian time derivative of a compactly supported strip field

`Work.FTS.PressureOn.Connect.BoundaryTime.continuousOn_timeDeriv_strip`: if
`f : ℝ³ → ℝ → ℝ³` is jointly continuous on the closed strip `ℝ³ × [0,S]`, its two-sided time
derivative `∂ₜ f` is jointly continuous there, and the spatial support of `f` on the strip is
contained in a ball `B(0,R)`, then

  `(x,t) ↦ -∫ y, ⟪∇Nfund (x - y), ∂ₜ f y t⟫`

is continuous on the closed strip `ℝ³ × [0,S]`.

This is the boundary-time (`t ∈ {0, S}` included) form of
`Work.FTS.PressureOn.continuous_timeDeriv_pressurePotential`, which assumes global joint
continuity of `f` and `∂ₜ f` together with a support radius that is *locally uniform in time*.

## Route

There are three steps.

* **Support of `∂ₜ f` on the strip.**  For `‖y‖ > R` the slice `s ↦ f y s` vanishes on all of
  `[0,S]`; hence `deriv (f y) s = 0` for every `s ∈ [0,S]`, including the endpoints: at an
  endpoint the two-sided derivative, if it exists, equals the (vanishing) one-sided derivative,
  and if it does not exist `deriv` is `0` anyway.  This is
  `Work.FTS.PressureOn.Connect.BoundaryTime.deriv_zero_of_eq_zero_on_Icc`.

* **Clamping the time variable.**  `G := fun y s => ∂ₜ f y (clampt S s)` is *globally* jointly
  continuous: `s ↦ clampt S s` retracts `ℝ` onto `[0,S]` and the pair
  `(y,s) ↦ (y, clampt S s)` maps everything into the closed strip, so the hypothesis `hd`
  composes (`ContinuousOn.comp_continuous`).  Moreover `G y s = 0` unless `‖y‖ ≤ max R 0`,
  uniformly in `s`, since `clampt S s ∈ [0,S]` always.  So the global shift lemma
  `Work.FTS.PressureOn.continuous_shifted_integral_joint` applies to `G` and yields continuity
  of `p ↦ ∫ z, ⟪∇Nfund z, G (p.1 - z) p.2⟫` on all of `ℝ³ × ℝ`.

* **Restricting and shifting back.**  On the strip `clampt S s = s`, so the clamped field may be
  replaced by `∂ₜ f` itself (`ContinuousOn.congr`), and the substitution `z = x - y`
  (`Work.FTS.PressureOn.integral_shift_nablaNfund`) converts the convolution form of the kernel
  into the defining form.  Negating gives the statement.

The spatial continuity hypothesis `hf` is not needed: the only place where `f` enters is the
support hypothesis, which `∂ₜ f` inherits on the strip.
-/

open FiniteTimeSingularity Set MeasureTheory Filter
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.PressureOn.Connect.BoundaryTime

/-- **Support of the time derivative on the closed strip.**  If on the strip `ℝ³ × [0,S]` the
field `f` vanishes outside the ball `B(0,R)`, then so does `∂ₜ f`.  (The point of the statement
is the closed strip: at the boundary times the two-sided derivative is controlled by the
one-sided one, see `deriv_zero_of_eq_zero_on_Icc`.) -/
theorem timeDeriv_eq_zero_of_support_Icc
    {f : Work.FTS.PressureOn.R3 → ℝ → Work.FTS.PressureOn.R3} {S R : ℝ} (hS : 0 < S)
    (hsupp : ∀ s ∈ Set.Icc 0 S, ∀ y : Work.FTS.PressureOn.R3, f y s ≠ 0 → ‖y‖ ≤ R) :
    ∀ y : Work.FTS.PressureOn.R3, R < ‖y‖ → ∀ t ∈ Set.Icc 0 S,
      FiniteTimeSingularity.timeDeriv f y t = 0 := by
  intro y hy t ht
  have hfy : ∀ s ∈ Set.Icc 0 S, f y s = 0 := by
    intro s hs
    by_contra hne
    exact absurd (hsupp s hs y hne) (not_le.mpr hy)
  simpa only [FiniteTimeSingularity.timeDeriv] using
    deriv_zero_of_eq_zero_on_Icc hS hfy ht

set_option linter.unusedVariables false in
theorem continuousOn_timeDeriv_strip
    {f : Work.FTS.PressureOn.R3 → ℝ → Work.FTS.PressureOn.R3} {S : ℝ} (hS : 0 < S)
    (hf : ContinuousOn (fun p : Work.FTS.PressureOn.R3 × ℝ => f p.1 p.2)
      (Set.univ ×ˢ Set.Icc 0 S))
    (hd : ContinuousOn (fun p : Work.FTS.PressureOn.R3 × ℝ =>
      FiniteTimeSingularity.timeDeriv f p.1 p.2) (Set.univ ×ˢ Set.Icc 0 S))
    (hsupp : ∃ R : ℝ, ∀ s ∈ Set.Icc 0 S, ∀ y : Work.FTS.PressureOn.R3, f y s ≠ 0 → ‖y‖ ≤ R) :
    ContinuousOn (fun p : Work.FTS.PressureOn.R3 × ℝ =>
      -∫ y, inner ℝ (Work.FTS.PressureOn.nablaNfund (p.1 - y))
        (FiniteTimeSingularity.timeDeriv f y p.2)) (Set.univ ×ˢ Set.Icc 0 S) := by
  obtain ⟨R, hR⟩ := hsupp
  -- ## Step 1: the time derivative of `f` vanishes off `B(0,R)` on the strip
  have hzero : ∀ y : Work.FTS.PressureOn.R3, R < ‖y‖ → ∀ t ∈ Set.Icc 0 S,
      FiniteTimeSingularity.timeDeriv f y t = 0 :=
    timeDeriv_eq_zero_of_support_Icc hS hR
  set ρ : ℝ := max R 0 with hρ
  have hρR : R ≤ ρ := le_max_left R 0
  have hzero' : ∀ y : Work.FTS.PressureOn.R3, ρ < ‖y‖ → ∀ t ∈ Set.Icc 0 S,
      FiniteTimeSingularity.timeDeriv f y t = 0 :=
    fun y hy t ht => hzero y (lt_of_le_of_lt hρR hy) t ht
  -- ## Step 2: clamp the time variable, so that the field becomes globally continuous
  have hcontG : Continuous (fun p : Work.FTS.PressureOn.R3 × ℝ =>
      FiniteTimeSingularity.timeDeriv f p.1 (Work.FTS.PressureOn.Connect.clampt S p.2)) := by
    have hΦ : Continuous fun p : Work.FTS.PressureOn.R3 × ℝ =>
        ((p.1, Work.FTS.PressureOn.Connect.clampt S p.2) : Work.FTS.PressureOn.R3 × ℝ) :=
      continuous_fst.prodMk
        ((Work.FTS.PressureOn.Connect.lipschitzWith_clampt S).continuous.comp continuous_snd)
    have hmem : ∀ p : Work.FTS.PressureOn.R3 × ℝ,
        ((p.1, Work.FTS.PressureOn.Connect.clampt S p.2) : Work.FTS.PressureOn.R3 × ℝ) ∈
          Set.univ ×ˢ Set.Icc 0 S :=
      fun p => ⟨trivial, Work.FTS.PressureOn.Connect.clampt_mem_Icc hS.le p.2⟩
    exact hd.comp_continuous hΦ hmem
  -- the support of the clamped field is *globally* uniform in the time variable
  have hsuppG : ∀ t : ℝ, ∃ ρ' : ℝ, ∀ s ∈ Set.Ioo (t - 1) (t + 1), ∀ y : Work.FTS.PressureOn.R3,
      FiniteTimeSingularity.timeDeriv f y (Work.FTS.PressureOn.Connect.clampt S s) ≠ 0 →
        ‖y‖ ≤ ρ' := by
    refine fun _ => ⟨ρ, fun s _ y hy => ?_⟩
    by_contra hlt
    rw [not_le] at hlt
    exact hy (hzero' y hlt (Work.FTS.PressureOn.Connect.clampt S s)
      (Work.FTS.PressureOn.Connect.clampt_mem_Icc hS.le s))
  -- ## Step 3: global continuity of the shifted (convolution) form
  have hmain := Work.FTS.PressureOn.continuous_shifted_integral_joint
    (g := fun y s => FiniteTimeSingularity.timeDeriv f y (Work.FTS.PressureOn.Connect.clampt S s))
    hcontG hsuppG
  have hnon : ContinuousOn (fun p : Work.FTS.PressureOn.R3 × ℝ => ∫ z, inner ℝ
      (Work.FTS.PressureOn.nablaNfund z)
      (FiniteTimeSingularity.timeDeriv f (p.1 - z)
        (Work.FTS.PressureOn.Connect.clampt S p.2))) (Set.univ ×ˢ Set.Icc 0 S) :=
    hmain.continuousOn
  -- on the strip the clamp is the identity, so the clamped field may be replaced by `∂ₜ f`
  have hEqOn : Set.EqOn (fun p : Work.FTS.PressureOn.R3 × ℝ => ∫ z, inner ℝ
        (Work.FTS.PressureOn.nablaNfund z)
        (FiniteTimeSingularity.timeDeriv f (p.1 - z) p.2))
      (fun p : Work.FTS.PressureOn.R3 × ℝ => ∫ z, inner ℝ
        (Work.FTS.PressureOn.nablaNfund z)
        (FiniteTimeSingularity.timeDeriv f (p.1 - z)
          (Work.FTS.PressureOn.Connect.clampt S p.2))) (Set.univ ×ˢ Set.Icc 0 S) := by
    intro p hp
    simp only [Work.FTS.PressureOn.Connect.clampt_eq_self_of_mem hp.2]
  have hcont : ContinuousOn (fun p : Work.FTS.PressureOn.R3 × ℝ => ∫ z, inner ℝ
      (Work.FTS.PressureOn.nablaNfund z)
      (FiniteTimeSingularity.timeDeriv f (p.1 - z) p.2)) (Set.univ ×ˢ Set.Icc 0 S) :=
    hnon.congr hEqOn
  -- the substitution `z = x - y` turns the convolution form into the defining form
  refine (hcont.congr ?_).neg
  intro p _
  exact Work.FTS.PressureOn.integral_shift_nablaNfund
    (fun y => FiniteTimeSingularity.timeDeriv f y p.2) p.1

end Work.FTS.PressureOn.Connect.BoundaryTime
end
-- ===== merged: Submission.Work.FTS.PressureOn.Connect.BoundaryTime.lamb_derivWithinAt_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Connect.BoundaryTime

theorem lamb_derivWithinAt_zero {u ω : Work.FTS.PressureOn.R3 → ℝ → Work.FTS.PressureOn.R3}
    {y : Work.FTS.PressureOn.R3} {u' ω' : Work.FTS.PressureOn.R3}
    (hu : HasDerivWithinAt (fun s => u y s) u' (Set.Ici 0) 0)
    (hω : HasDerivWithinAt (fun s => ω y s) ω' (Set.Ici 0) 0) :
    HasDerivWithinAt (fun s => Work.FTS.PressureOn.lamb u ω y s)
      (Work.FTS.PressureOn.crossVec u' (ω y 0) + Work.FTS.PressureOn.crossVec (u y 0) ω')
      (Set.Ici 0) 0 := by
  -- `lamb u ω y s = u y s × ω y s` is (definitionally) the cross product, realised as the
  -- continuous bilinear map `BSSwirl.crossBilin`; the product rule for a bilinear map
  -- (`HasFDerivWithinAt.clm_apply`) therefore gives the claim, one-sided at `0`.
  have huy : HasFDerivWithinAt (fun s => u y s)
      (ContinuousLinearMap.toSpanSingleton ℝ u') (Set.Ici 0) 0 := hu.hasFDerivWithinAt
  have hωy : HasFDerivWithinAt (fun s => ω y s)
      (ContinuousLinearMap.toSpanSingleton ℝ ω') (Set.Ici 0) 0 := hω.hasFDerivWithinAt
  -- The partial application `fun s => crossBilin (u y s)` (a curve of continuous linear maps),
  -- with derivative `s ↦ crossBilin (s • u')`.
  have hc : HasFDerivWithinAt (fun s : ℝ => Work.FTS.BSSwirl.crossBilin (u y s))
      ((Work.FTS.BSSwirl.crossBilin).comp (ContinuousLinearMap.toSpanSingleton ℝ u'))
      (Set.Ici 0) 0 :=
    (Work.FTS.BSSwirl.crossBilin.hasFDerivWithinAt (s := Set.univ)).comp 0 huy
      (fun x _ => trivial)
  have hmain := hc.clm_apply hωy
  have hfin : HasDerivWithinAt (fun s : ℝ => Work.FTS.BSSwirl.crossBilin (u y s) (ω y s))
      (Work.FTS.PressureOn.crossVec (u y 0) ω' + Work.FTS.PressureOn.crossVec u' (ω y 0))
      (Set.Ici 0) 0 := by
    convert hmain.hasDerivWithinAt using 1
    simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.toSpanSingleton_apply, one_smul]
    rfl
  have hfs : (fun s : ℝ => Work.FTS.BSSwirl.crossBilin (u y s) (ω y s))
      = fun s => Work.FTS.PressureOn.lamb u ω y s := by
    funext s
    rfl
  rw [hfs] at hfin
  simpa only [add_comm] using hfin

end Work.FTS.PressureOn.Connect.BoundaryTime
end
-- ===== merged: Submission.Work.FTS.PressureOn.Connect.hasDerivAt_lamb_time =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Connect

/-- **The time derivative of the Lamb vector.**  If the time slices `s ↦ u y s` and `s ↦ ω y s` are
differentiable at `t`, then so is the time slice of the Lamb vector `s ↦ u y s × ω y s`, with
derivative its canonical `deriv` — i.e. `timeDeriv (lamb u ω) y t`. -/
theorem hasDerivAt_lamb_time {u ω : Work.FTS.PressureOn.R3 → ℝ → Work.FTS.PressureOn.R3}
    {y : Work.FTS.PressureOn.R3} {t : ℝ}
    (hu : HasDerivAt (fun s => u y s) (FiniteTimeSingularity.timeDeriv u y t) t)
    (hω : HasDerivAt (fun s => ω y s) (FiniteTimeSingularity.timeDeriv ω y t) t) :
    HasDerivAt (fun s => Work.FTS.PressureOn.lamb u ω y s)
      (FiniteTimeSingularity.timeDeriv (Work.FTS.PressureOn.lamb u ω) y t) t := by
  -- `lamb u ω y s` is the cross product `u y s × ω y s` (definitionally).
  have hfeq : (fun s : ℝ => Work.FTS.BSSwirl.crossBilin (u y s) (ω y s))
      = fun s => Work.FTS.PressureOn.lamb u ω y s := by
    funext s
    rfl
  -- The cross product, as a continuous bilinear map, is its own derivative; compose the first
  -- factor with the curve `s ↦ u y s`.
  have hc : HasFDerivAt (fun s : ℝ => Work.FTS.BSSwirl.crossBilin (u y s))
      (Work.FTS.BSSwirl.crossBilin.comp
        (ContinuousLinearMap.toSpanSingleton ℝ (FiniteTimeSingularity.timeDeriv u y t))) t :=
    Work.FTS.BSSwirl.crossBilin.hasFDerivAt.comp t hu.hasFDerivAt
  -- Apply the second factor (`HasFDerivAt.clm_apply`: product rule for a bilinear map).
  have hmain := hc.clm_apply hω.hasFDerivAt
  -- Only differentiability is needed: the requested derivative is the canonical `deriv`.
  have hdiff : DifferentiableAt ℝ (fun s => Work.FTS.PressureOn.lamb u ω y s) t := by
    rw [← hfeq]
    exact hmain.differentiableAt
  exact hdiff.hasDerivAt

/-- **The value of the time derivative of the Lamb vector** (the explicit product rule).  This is
the companion of `hasDerivAt_lamb_time`: it identifies the derivative that the latter only names
as `timeDeriv (lamb u ω) y t`. -/
theorem timeDeriv_lamb {u ω : Work.FTS.PressureOn.R3 → ℝ → Work.FTS.PressureOn.R3}
    {y : Work.FTS.PressureOn.R3} {t : ℝ}
    (hu : HasDerivAt (fun s => u y s) (FiniteTimeSingularity.timeDeriv u y t) t)
    (hω : HasDerivAt (fun s => ω y s) (FiniteTimeSingularity.timeDeriv ω y t) t) :
    FiniteTimeSingularity.timeDeriv (Work.FTS.PressureOn.lamb u ω) y t
      = Work.FTS.PressureOn.crossVec (FiniteTimeSingularity.timeDeriv u y t) (ω y t)
        + Work.FTS.PressureOn.crossVec (u y t) (FiniteTimeSingularity.timeDeriv ω y t) := by
  have hfeq : (fun s : ℝ => Work.FTS.BSSwirl.crossBilin (u y s) (ω y s))
      = fun s => Work.FTS.PressureOn.lamb u ω y s := by
    funext s
    rfl
  have hc : HasFDerivAt (fun s : ℝ => Work.FTS.BSSwirl.crossBilin (u y s))
      (Work.FTS.BSSwirl.crossBilin.comp
        (ContinuousLinearMap.toSpanSingleton ℝ (FiniteTimeSingularity.timeDeriv u y t))) t :=
    Work.FTS.BSSwirl.crossBilin.hasFDerivAt.comp t hu.hasFDerivAt
  have hmain := hc.clm_apply hω.hasFDerivAt
  -- `deriv` of a differentiable function is the value of its Fréchet derivative at `1`.
  rw [show FiniteTimeSingularity.timeDeriv (Work.FTS.PressureOn.lamb u ω) y t
      = deriv (fun s => Work.FTS.PressureOn.lamb u ω y s) t from rfl]
  rw [← hfeq, hmain.hasDerivAt.deriv]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.toSpanSingleton_apply, one_smul]
  rw [add_comm]
  rfl

end Work.FTS.PressureOn.Connect
end
-- ===== merged: Submission.Work.FTS.PressureOn.Connect.omega_uniform_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Connect

theorem omega_uniform_bound {α : NNReal} {ω : Work.FTS.PressureOn.R3 → ℝ → Work.FTS.PressureOn.R3}
    {T S : ℝ} (hS : S ∈ Set.Ioo 0 T)
    (hstrips : ∀ S' ∈ Set.Ioo 0 T,
      IsContDiffHolderOn ℝ α (Work.FTS.Physical.physVel ω).uncurry (Set.univ ×ˢ Set.Icc 0 S'))
    (hcurl : ∀ s ∈ Set.Ico 0 T, ∀ x,
      FiniteTimeSingularity.vorticity (fun z => Work.FTS.Physical.physVel ω z s) x = ω x s) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s ∈ Set.Icc 0 S, ∀ x, ‖ω x s‖ ≤ M := by
  -- The bound on the half-open interval `(0,S]` and the a.e. strong measurability of the slices.
  obtain ⟨⟨M, hM, hbdd⟩, hmeas⟩ := omegaSliceRegularPos hS hstrips hcurl
  -- Continuity in time of every curve `s ↦ ω x s` on `[0,S]`.
  have hcontω : ∀ x, ContinuousOn (fun s => ω x s) (Set.Icc 0 S) :=
    continuousOn_time_omega_of_strips hS hstrips hcurl
  -- The time-zero slice inherits the same bound `M`.
  obtain ⟨h0, -⟩ := aeStronglyMeasurableAndBoundAtZero hS.1 hM hbdd hmeas hcontω
  refine ⟨M, hM, fun s hs x => ?_⟩
  rcases eq_or_lt_of_le hs.1 with h | h
  · rw [← h]
    exact h0 x
  · exact hbdd s ⟨h, hs.2⟩ x

end Work.FTS.PressureOn.Connect
end
-- ===== merged: Submission.Work.FTS.PressureOn.Green.div_gradient_eq_laplaceTrace =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `div (∇u) = laplaceTrace u`

`Work.FTS.PressureOn.Green.div_gradient_eq_laplaceTrace`: for a `C²` function `u : ℝ³ → ℝ` the
divergence of the gradient field equals the trace of the Hessian,
`div (fun z => ∇u z) = laplaceTrace u`.

Both sides are traces computed from `fderiv`:

* `div G x = ∑ᵢ (fderiv ℝ G x (eᵢ))ᵢ` — the trace in the standard orthonormal basis
  (`Work.FTS.PressureOn.trace_eq_sum_single`, a colleague's lemma);
* `laplaceTrace u x = ∑ᵢ fderiv ℝ (fun w => fderiv ℝ u w (eᵢ)) x (eᵢ)` (the definition).

## Route

The whole proof is the Fréchet–Riesz bookkeeping that turns the first of these sums into the
second.  Write `Φ := fderiv ℝ u : ℝ³ → (ℝ³ →L[ℝ] ℝ)` (the derivative of `u` as a functional),
so that the gradient field is

  `G := fun z => ∇u z = L ∘ Φ`,  `L := (toDual ℝ ℝ³).symm : (ℝ³ →L[ℝ] ℝ) →L[ℝ] ℝ³`

(the inverse Fréchet–Riesz representation, packaged as a continuous linear equivalence; for `ℝ`
it is genuinely linear).

* `u ∈ C²` gives `Φ ∈ C¹` (`contDiff_succ_iff_fderiv`), hence `Φ` is differentiable and
  `fderiv ℝ G x = L.comp (fderiv ℝ Φ x)` by the chain rule.  This is the only regularity input.
* For a functional `T : ℝ³ →L[ℝ] ℝ`, `(L T) i = ⟪L T, eᵢ⟫ = T (eᵢ)`
  (`InnerProductSpace.toDual_symm_apply`), so

    `(fderiv ℝ G x (eᵢ)) i = (fderiv ℝ Φ x (eᵢ)) (eᵢ)`.
* On the other side, `w ↦ fderiv ℝ u w (eᵢ)` is the composition of `Φ` with the evaluation
  `T ↦ T (eᵢ)` (a continuous linear map), so by the chain rule again

    `fderiv ℝ (fun w => fderiv ℝ u w (eᵢ)) x (eᵢ) = (fderiv ℝ Φ x (eᵢ)) (eᵢ)`.

The two sums therefore agree termwise.  No symmetry (Clairaut) of the second derivative is
needed — both sides are evaluated in the same two slots `(eᵢ, eᵢ)`.
-/

noncomputable section

namespace Work.FTS.PressureOn.Green

open Work.FTS.PressureOn

/-- The `i`-th coordinate of a vector of `ℝ³` is the inner product with the `i`-th basis vector
`FiniteTimeSingularity.e i`. -/
theorem coord_eq_inner_R3 (y : R3) (i : Fin 3) : y i = inner ℝ y (FiniteTimeSingularity.e i) := by
  simp [FiniteTimeSingularity.e, PiLp.inner_apply]

/-- The inverse Fréchet–Riesz representation, packaged as a continuous linear map, is the
underlying function of `(InnerProductSpace.toDual ℝ ℝ³).symm`. -/
theorem toDual_symm_eq_CLM (v : R3 →L[ℝ] ℝ) :
    ((InnerProductSpace.toDual ℝ R3).symm.toContinuousLinearEquiv.toContinuousLinearMap) v
      = (InnerProductSpace.toDual ℝ R3).symm v := rfl

end Work.FTS.PressureOn.Green
end
end
-- ===== merged: Submission.Work.FTS.PressureOn.Green.integral_gauss_smul_laplaceTraceVec =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set MeasureTheory
open scoped Topology

noncomputable section

namespace Work.FTS.PressureOn.Green

open Work.FTS.PressureOn

namespace IgslvAux

/-- The `j`-th coordinate of a derivative is the derivative of the `j`-th coordinate. -/
lemma fderiv_coord (H : R3 → R3) (z : R3) (hH : DifferentiableAt ℝ H z) (j : Fin 3) (v : R3) :
    fderiv ℝ (fun w => H w j) z v = (fderiv ℝ H z v) j := by
  have hproj : HasFDerivAt (fun f : R3 => f.ofLp j)
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j) (H z) :=
    PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (H z) j
  have hc := hproj.comp z hH.hasFDerivAt
  change HasFDerivAt (fun w : R3 => (H w).ofLp j) _ z at hc
  rw [hc.fderiv]
  simp [PiLp.proj_apply]

/-- The `j`-th component of `laplaceTraceVec` is the `laplaceTrace` of the `j`-th component. -/
lemma laplaceTraceVec_coord (G : R3 → R3) (hG : ContDiff ℝ 2 G) (z : R3) (j : Fin 3) :
    laplaceTraceVec G z j = laplaceTrace (fun z => G z j) z := by
  simp only [laplaceTraceVec, laplaceTrace]
  rw [show ((∑ i : Fin 3, (fderiv ℝ (fun w => (fderiv ℝ G w) (FiniteTimeSingularity.e i)) z)
        (FiniteTimeSingularity.e i)) : R3).ofLp j
      = ∑ i : Fin 3, ((fderiv ℝ (fun w => (fderiv ℝ G w) (FiniteTimeSingularity.e i)) z)
        (FiniteTimeSingularity.e i)).ofLp j from by
    rw [show ((∑ i : Fin 3, (fderiv ℝ (fun w => (fderiv ℝ G w) (FiniteTimeSingularity.e i)) z)
        (FiniteTimeSingularity.e i)) : R3).ofLp j
        = (EuclideanSpace.proj j) (∑ i : Fin 3, (fderiv ℝ (fun w => (fderiv ℝ G w)
          (FiniteTimeSingularity.e i)) z) (FiniteTimeSingularity.e i)) from by
      rw [EuclideanSpace.proj, PiLp.proj_apply]]
    rw [map_sum]
    rfl]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← fderiv_coord (fun w => (fderiv ℝ G w) (FiniteTimeSingularity.e i)) z ?_ j
    (FiniteTimeSingularity.e i)]
  · have hfun : (fun w : R3 => ((fderiv ℝ G w) (FiniteTimeSingularity.e i)).ofLp j)
        = fun w : R3 => (fderiv ℝ (fun z => G z j) w) (FiniteTimeSingularity.e i) := by
      funext w
      exact (fderiv_coord G w (hG.differentiable (by norm_num) w) j
        (FiniteTimeSingularity.e i)).symm
    rw [hfun]
  · fun_prop

/-- The `j`-th component of a `C²` field is `C²`. -/
lemma contDiff_coord (G : R3 → R3) (hG : ContDiff ℝ 2 G) (j : Fin 3) :
    ContDiff ℝ 2 (fun z => G z j) := by
  have := (EuclideanSpace.proj j).contDiff.comp hG
  simpa [Function.comp_def, EuclideanSpace.proj, PiLp.proj_apply] using this

/-- The `j`-th component of a compactly supported field is compactly supported. -/
lemma hasCompactSupport_coord (G : R3 → R3) (hcs : HasCompactSupport G) (j : Fin 3) :
    HasCompactSupport (fun z => G z j) := by
  have := hcs.comp_left (g := fun w : R3 => w j) (by simp)
  simpa [Function.comp_def] using this


/-- `laplaceTrace` is supported in the support of the function. -/
lemma support_laplaceTrace_subset (φ : R3 → ℝ) :
    Function.support (laplaceTrace φ) ⊆ tsupport φ := by
  intro z hz
  by_contra hzt
  apply hz
  have hopen : IsOpen (tsupport φ)ᶜ := (isClosed_tsupport φ).isOpen_compl
  rw [laplaceTrace]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hderiv0 : (fun w => fderiv ℝ φ w) =ᶠ[𝓝 z] 0 := by
    filter_upwards [hopen.mem_nhds hzt] with w hw
    have h0 : φ =ᶠ[𝓝 w] 0 := by
      filter_upwards [hopen.mem_nhds hw] with v hv
      exact image_eq_zero_of_notMem_tsupport hv
    rw [h0.fderiv_eq]
    simp
  have h1 : (fun w => fderiv ℝ φ w (FiniteTimeSingularity.e i)) =ᶠ[𝓝 z] 0 := by
    filter_upwards [hderiv0] with w hw
    rw [hw]
    simp
  have h2 : fderiv ℝ (fun w => fderiv ℝ φ w (FiniteTimeSingularity.e i)) z = 0 := by
    rw [h1.fderiv_eq]
    simp
  rw [h2]
  simp

lemma hasCompactSupport_laplaceTrace (φ : R3 → ℝ) (hcs : HasCompactSupport φ) :
    HasCompactSupport (laplaceTrace φ) :=
  HasCompactSupport.of_support_subset_isCompact hcs (support_laplaceTrace_subset φ)

lemma continuous_laplaceTrace (φ : R3 → ℝ) (hφ : ContDiff ℝ 2 φ) :
    Continuous (laplaceTrace φ) := by
  unfold laplaceTrace
  refine continuous_finsetSum _ fun i _ => ?_
  have hψ : ContDiff ℝ 1 (fun w => fderiv ℝ φ w (FiniteTimeSingularity.e i)) := by fun_prop
  have hcont := hψ.continuous_fderiv (by norm_num)
  exact (ContinuousLinearMap.apply ℝ ℝ (FiniteTimeSingularity.e i)).continuous.comp hcont











end IgslvAux

open IgslvAux




end Work.FTS.PressureOn.Green
end
end
-- ===== merged: Submission.Work.FTS.PressureOn.MollAux.mollV_support_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.MollAux

open MeasureTheory

/-- The outer radius `1/(n+1)` of the mollifier bump is at most `1`. -/
theorem bump_rOut_le_one (n : ℕ) : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h2 : (1 : ℝ) ≤ 1 * ((n : ℝ) + 1) := by
    have h : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  exact (div_le_iff₀ hpos).mpr h2

/-- The support of `rho n` lies in the closed unit ball: `rho n t ≠ 0` forces `‖t‖ ≤ 1`. -/
theorem norm_le_one_of_rho_ne_zero (n : ℕ) (t : EuclideanSpace ℝ (Fin 3))
    (ht : Work.FTS.PressureOn.rho n t ≠ 0) : ‖t‖ ≤ 1 :=
  le_trans ((rho_props n).2.2.2.2.2.1 t ht) (bump_rOut_le_one n)

/-- The integrand `t ↦ rho n t • ψ (x - t)` of the mollification `mollV n ψ x` vanishes
identically as soon as `x` is at distance `> 1` from `tsupport ψ`: the support of `rho n` lies
in the unit ball, while `tsupport ψ` stays outside it. -/
theorem rho_smul_eq_zero_of_dist_gt_one (n : ℕ) (ψ : EuclideanSpace ℝ (Fin 3) →
    EuclideanSpace ℝ (Fin 3)) (x : EuclideanSpace ℝ (Fin 3))
    (hx : ∀ b ∈ tsupport ψ, 1 < dist x b) (t : EuclideanSpace ℝ (Fin 3)) :
    Work.FTS.PressureOn.rho n t • ψ (x - t) = 0 := by
  by_cases ht : Work.FTS.PressureOn.rho n t = 0
  · rw [ht, zero_smul]
  · have hdist : dist x (x - t) = ‖t‖ := by rw [dist_eq_norm, sub_sub_cancel]
    have hnot : x - t ∉ tsupport ψ := by
      intro hmem
      have hlt := hx (x - t) hmem
      rw [hdist] at hlt
      have := norm_le_one_of_rho_ne_zero n t ht
      linarith
    rw [image_eq_zero_of_notMem_tsupport hnot, smul_zero]

theorem mollV_support_bound (n : ℕ) (ψ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (M : ℝ) (hM : ∀ y, ‖ψ y‖ ≤ M) :
    (∀ x, (∀ b ∈ tsupport ψ, 1 < dist x b) → Work.FTS.PressureOn.mollV n ψ x = 0) ∧
      (∀ x, ‖Work.FTS.PressureOn.mollV n ψ x‖ ≤ M) := by
  constructor
  · intro x hx
    rw [MollSB.mollV_eq_integral_rho]
    have hzero : (fun t => Work.FTS.PressureOn.rho n t • ψ (x - t))
        =ᵐ[volume] (fun _ => (0 : EuclideanSpace ℝ (Fin 3))) :=
      Filter.Eventually.of_forall (rho_smul_eq_zero_of_dist_gt_one n ψ x hx)
    rw [integral_congr_ae hzero]
    simp
  · intro x
    exact MollSB.norm_mollV_le n ψ M hM x

end Work.FTS.PressureOn.MollAux
end
-- ===== merged: Submission.Work.FTS.PressureOn.PoissonAux.Ibp2 =====
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

/-- The partial derivatives of a `C²` function are `C¹`. -/
lemma contDiff_fderiv_apply_e {u : R3 → ℝ} (hu : ContDiff ℝ 2 u) (i : Fin 3) :
    ContDiff ℝ 1 (fun x : R3 => fderiv ℝ u x (e i)) := by
  have h : ContDiff ℝ 1 (fun p : R3 × R3 => fderiv ℝ u p.1 p.2) :=
    ContDiff.contDiff_fderiv_apply hu (by norm_num)
  have h2 : ContDiff ℝ 1 (fun x : R3 => (x, e i)) := by
    have h3 : ContDiff ℝ 1 (fun x : R3 => ((x, (0 : R3)) : R3 × R3)) :=
      (ContinuousLinearMap.inl ℝ R3 R3).contDiff
    simpa using h3.add (contDiff_const (c := ((0 : R3), e i)))
  exact h.comp h2

/-- The partial derivatives of a compactly supported function have compact support. -/
lemma hasCompactSupport_fderiv_apply_e {v : R3 → ℝ} (hvcs : HasCompactSupport v) (i : Fin 3) :
    HasCompactSupport (fun x : R3 => fderiv ℝ v x (e i)) := by
  refine hvcs.mono' ?_
  intro x hx
  by_contra hxt
  rw [Function.mem_support] at hx
  exact hx (by
    rw [fderiv_eq_zero_of_notMem_tsupport hxt]
    simp)

/-- **The product form.**  For `C¹` functions `g`, `h` with `h` of compact support,
`∫ x, ∂ᵢ(g · h) x = 0`. -/
theorem integral_fderiv_mul_eq_zero {g h : R3 → ℝ} (hg : ContDiff ℝ 1 g) (hh : ContDiff ℝ 1 h)
    (hcs : HasCompactSupport h) (i : Fin 3) :
    ∫ x, fderiv ℝ (g * h) x (e i) = 0 := by
  have hsm : ContDiff ℝ 1 (fun x : R3 => (g * h) x • e i) := (hg.mul hh).smul contDiff_const
  have hcsm : HasCompactSupport (fun x : R3 => (g * h) x • e i) := hcs.mono' (by
    intro x hx
    by_contra hxt
    rw [Function.mem_support] at hx
    exact hx (by simp [image_eq_zero_of_notMem_tsupport hxt]))
  have hdiv : div (fun x : R3 => (g * h) x • e i) = fun x => fderiv ℝ (g * h) x (e i) := by
    funext x
    show div (fun y : R3 => (g y * h y) • e i) x = fderiv ℝ (fun y : R3 => g y * h y) x (e i)
    rw [div_smul (hg.mul hh) contDiff_const x, div_const, mul_zero, zero_add,
      inner_gradient_left]
  have h0 : ∫ x, div (fun y : R3 => (g * h) y • e i) x = 0 :=
    integral_div_eq_zero_of_hasFDerivAt _ hcsm hsm.continuous
      (fun x => (hsm.differentiable_one x).hasFDerivAt)
      (integrable_div_of_contDiff hsm hcsm)
  rwa [hdiv] at h0

/-- **Integration by parts in one coordinate direction.**  For `C¹` functions `g`, `h` with `h` of
compact support, `∫ x, ∂ᵢg x * h x = -∫ x, g x * ∂ᵢh x`. -/
theorem integral_fderiv_mul_eq_neg {g h : R3 → ℝ} (hg : ContDiff ℝ 1 g) (hh : ContDiff ℝ 1 h)
    (hcs : HasCompactSupport h) (i : Fin 3) :
    ∫ x, fderiv ℝ g x (e i) * h x = -∫ x, g x * fderiv ℝ h x (e i) := by
  have h0 := integral_fderiv_mul_eq_zero hg hh hcs i
  have hfun : (fun x => fderiv ℝ (g * h) x (e i))
      = fun x => fderiv ℝ g x (e i) * h x + g x * fderiv ℝ h x (e i) := by
    funext x
    rw [((hg.differentiable_one x).hasFDerivAt.mul
      (hh.differentiable_one x).hasFDerivAt).fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  rw [hfun] at h0
  have hcontA : Continuous fun x : R3 => fderiv ℝ g x (e i) * h x :=
    ((hg.continuous_fderiv_apply one_ne_zero).comp
      (continuous_id.prodMk continuous_const)).mul hh.continuous
  have hIntA : Integrable fun x : R3 => fderiv ℝ g x (e i) * h x := by
    refine Continuous.integrable_of_hasCompactSupport hcontA (hcs.mono' ?_)
    intro x hx
    by_contra hxt
    rw [Function.mem_support] at hx
    exact hx (by simp [image_eq_zero_of_notMem_tsupport hxt])
  have hcontB : Continuous fun x : R3 => g x * fderiv ℝ h x (e i) :=
    hg.continuous.mul ((hh.continuous_fderiv_apply one_ne_zero).comp
      (continuous_id.prodMk continuous_const))
  have hIntB : Integrable fun x : R3 => g x * fderiv ℝ h x (e i) := by
    refine Continuous.integrable_of_hasCompactSupport hcontB
      ((hasCompactSupport_fderiv_apply_e hcs i).mono' ?_)
    intro x hx
    by_contra hxt
    rw [Function.mem_support] at hx
    exact hx (by simp [image_eq_zero_of_notMem_tsupport hxt])
  rw [integral_add hIntA hIntB] at h0
  linarith

end Work.FTS.PressureOn
end
-- ===== merged: Submission.Work.FTS.PressureOn.PoissonAux.KI.integrable_newtonKernel_mul_laplaceTrace =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Metric

namespace Work.FTS.PressureOn.PoissonAux.KI

/-- The Newtonian kernel is non-negative: `N z = (4π‖z‖)⁻¹ ≥ 0`. -/
lemma newtonKernel_nonneg (z : R3) : 0 ≤ newtonKernel z := by
  rw [Work.FTS.PressureOn.newtonKernel]; positivity

/-- **Integrability of the Newtonian kernel times the Laplacian trace of a compactly supported
`C²` function.**

`laplaceTrace ψ` is continuous (`Green.continuous_laplaceTrace`) and vanishes off `tsupport ψ`
(`Green.laplaceTrace_eq_zero_of_notMem_tsupport`), so it is bounded, say by `M`; the product is
then dominated by `M · N`, which is integrable on a ball containing `tsupport ψ` in dimension
three (`Green.integrableOn_newtonKernel_ball`, the borderline `‖z‖⁻¹` case).  Since the product
vanishes off that ball, `IntegrableOn` on the ball upgrades to global `Integrable`. -/
theorem integrable_newtonKernel_mul_laplaceTrace {ψ : R3 → ℝ} (hψ : ContDiff ℝ 2 ψ)
    (hcs : HasCompactSupport ψ) :
    MeasureTheory.Integrable (fun x : R3 => newtonKernel x * laplaceTrace ψ x) := by
  have hcont : Continuous (laplaceTrace ψ) := Green.continuous_laplaceTrace ψ hψ
  -- `laplaceTrace ψ` is bounded: it is continuous and vanishes off `tsupport ψ`
  obtain ⟨M, hM⟩ := hcs.isCompact.exists_bound_of_continuousOn hcont.continuousOn
  have hbound : ∀ z : R3, ‖laplaceTrace ψ z‖ ≤ max M 0 := by
    intro z
    by_cases hz : z ∈ tsupport ψ
    · exact le_trans (hM z hz) (le_max_left M 0)
    · rw [Green.laplaceTrace_eq_zero_of_notMem_tsupport hz, norm_zero]
      exact le_max_right M 0
  -- a ball containing the support of `ψ`
  obtain ⟨r, hr⟩ := hcs.isCompact.isBounded.subset_closedBall (0 : R3)
  have hball : tsupport ψ ⊆ Metric.ball (0 : R3) (|r| + 1) := fun z hz =>
    Metric.closedBall_subset_ball (by linarith [le_abs_self r]) (hr hz)
  -- the dominating function: a multiple of the Newtonian kernel, integrable on the ball
  have hIntOn : IntegrableOn (fun z : R3 => (max M 0) * newtonKernel z)
      (Metric.ball (0 : R3) (|r| + 1)) volume :=
    (Green.integrableOn_newtonKernel_ball (|r| + 1)).const_mul (max M 0)
  have hmono : IntegrableOn (fun z : R3 => newtonKernel z * laplaceTrace ψ z)
      (Metric.ball (0 : R3) (|r| + 1)) volume := by
    refine Integrable.mono' hIntOn
      ((Green.measurable_newtonKernel.mul hcont.measurable).aestronglyMeasurable) ?_
    filter_upwards with z
    have hnk : 0 ≤ newtonKernel z := newtonKernel_nonneg z
    have h1 : ‖newtonKernel z * laplaceTrace ψ z‖ = newtonKernel z * ‖laplaceTrace ψ z‖ := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnk, Real.norm_eq_abs]
    rw [h1]
    calc newtonKernel z * ‖laplaceTrace ψ z‖
        ≤ newtonKernel z * max M 0 := mul_le_mul_of_nonneg_left (hbound z) hnk
      _ = max M 0 * newtonKernel z := by ring
  -- the integrand vanishes off the ball
  exact hmono.integrable_of_forall_notMem_eq_zero fun x hx => by
    have hx' : x ∉ tsupport ψ := fun h => hx (hball h)
    rw [Green.laplaceTrace_eq_zero_of_notMem_tsupport hx', mul_zero]

end Work.FTS.PressureOn.PoissonAux.KI
end
-- ===== merged: Submission.Work.FTS.PressureOn.PoissonAux.KI.massKernel_one_mass =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.PoissonAux.KI

/-- **The total mass of the truncation kernel `massKernel 1` is `-1`.**

`massKernel 1 x = (4π‖x‖)⁻¹ ρ''(‖x‖)` with `ρ = rhoProfile 1`, so it is the radially symmetric
function `g ‖x‖`, `g r = (4πr)⁻¹ ρ''(r)`.  The radial change of variables `integral_radial` turns
the integral into `4π ∫_0^∞ r² g(r) dr = ∫_0^∞ r ρ''(r) dr` (for `r > 0`), and the one-dimensional
identity `integral_mul_deriv_deriv_rhoProfile` gives `∫_0^∞ r ρ''(r) dr = -1`. -/
theorem massKernel_one_mass : ∫ x : R3, massKernel 1 x = -1 := by
  set f : ℝ → ℝ := fun r => deriv (deriv (rhoProfile 1)) r with hf
  set g : ℝ → ℝ := fun r => (4 * Real.pi * r)⁻¹ * f r with hg
  -- the kernel is the radially symmetric function `x ↦ g ‖x‖`
  have hfun : (fun x : R3 => massKernel 1 x) = fun x : R3 => g ‖x‖ := by
    funext x
    simp only [massKernel_eq, newtonKernel, hg, hf]
  rw [hfun, integral_radial g]
  -- the radial integrand reduces to `(4π)⁻¹ r ρ''(r)` for `r > 0`
  have h1 : ∫ r in Set.Ioi (0 : ℝ), r ^ 2 * g r
      = (4 * Real.pi)⁻¹ * ∫ r in Set.Ioi (0 : ℝ), r * f r := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.setIntegral_congr_ae measurableSet_Ioi
    filter_upwards with r hr
    have hr0 : r ≠ 0 := ne_of_gt hr
    simp only [hg]
    rw [mul_inv]
    have hrr : r ^ 2 * r⁻¹ = r := by
      rw [sq, mul_assoc, mul_inv_cancel₀ hr0, mul_one]
    rw [show r ^ 2 * ((4 * Real.pi)⁻¹ * r⁻¹ * f r)
          = (4 * Real.pi)⁻¹ * ((r ^ 2 * r⁻¹) * f r) from by ring, hrr]
  rw [h1, hf, integral_mul_deriv_deriv_rhoProfile 1 (by norm_num)]
  -- `4π · ((4π)⁻¹ · (-1)) = -1`
  have hpi : (4 * Real.pi) ≠ 0 := by positivity
  rw [← mul_assoc, mul_inv_cancel₀ hpi, one_mul]

end Work.FTS.PressureOn.PoissonAux.KI
end
-- ===== merged: Submission.Work.FTS.PressureOn.PoissonAux.tendsto_integral_massKernel_mul =====
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

/-! ## The radial profile of the mass kernel -/

/-- The mass kernel as a function of `‖x‖`: `mkRad ε r = (4πr)⁻¹ ρ_ε''(r)`. -/
noncomputable def mkRad (ε : ℝ) (r : ℝ) : ℝ :=
  (4 * Real.pi * r)⁻¹ * deriv (deriv (rhoProfile ε)) r

theorem massKernel_eq_mkRad (ε : ℝ) (x : R3) : massKernel ε x = mkRad ε ‖x‖ := rfl

/-- The mass kernel vanishes outside the shrinking ball `‖x‖ ≤ √2 ε`. -/
theorem massKernel_eq_zero_of_lt {ε : ℝ} (hε : 0 < ε) {x : R3}
    (hx : Real.sqrt 2 * ε < ‖x‖) : massKernel ε x = 0 := by
  rw [massKernel_eq_mkRad, mkRad,
    mk_deriv_deriv_rhoProfile_eq_zero hε (Or.inr (by rwa [abs_of_nonneg (norm_nonneg x)])),
    mul_zero]

/-! ## Continuity -/

theorem continuousAt_mkRad (ε : ℝ) (hε : 0 < ε) (r : ℝ) : ContinuousAt (mkRad ε) r := by
  by_cases hr : |r| < ε
  · have h : mkRad ε =ᶠ[𝓝 r] fun _ : ℝ => (0 : ℝ) := by
      have hpos : 0 < ε - |r| := by linarith
      filter_upwards [Metric.ball_mem_nhds r hpos] with s hs
      rw [Metric.mem_ball, Real.dist_eq] at hs
      have hs' : |s| < ε := by
        have h1 : |s - r| < ε - |r| := hs
        have h2 : |s| ≤ |s - r| + |r| := by
          calc |s| = |s - r + r| := by ring_nf
            _ ≤ |s - r| + |r| := abs_add_le (s - r) r
        linarith
      rw [mkRad, mk_deriv_deriv_rhoProfile_eq_zero hε (Or.inl hs'), mul_zero]
    exact continuousAt_const.congr h.symm
  · have hr0 : r ≠ 0 := by
      intro h
      rw [h, abs_zero] at hr
      linarith
    have hX : ContinuousAt (fun s : ℝ => deriv (deriv (rhoProfile ε)) s) r :=
      (mk_continuous_deriv_deriv_rhoProfile ε).continuousAt
    have hinv : ContinuousAt (fun s : ℝ => (4 * Real.pi * s)⁻¹) r := by
      refine ContinuousAt.inv₀ (continuousAt_const.mul continuousAt_id) ?_
      exact mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hr0
    change ContinuousAt (fun s : ℝ => (4 * Real.pi * s)⁻¹ * deriv (deriv (rhoProfile ε)) s) r
    exact hinv.mul hX

theorem continuous_mkRad (ε : ℝ) (hε : 0 < ε) : Continuous (mkRad ε) :=
  continuous_iff_continuousAt.mpr fun r => continuousAt_mkRad ε hε r

theorem continuous_massKernel (ε : ℝ) (hε : 0 < ε) : Continuous (massKernel ε) := by
  have h : massKernel ε = fun x : R3 => mkRad ε ‖x‖ := funext (massKernel_eq_mkRad ε)
  rw [h]
  exact (continuous_mkRad ε hε).comp continuous_norm

/-! ## Compact support and integrability -/

theorem hasCompactSupport_massKernel (ε : ℝ) (hε : 0 < ε) : HasCompactSupport (massKernel ε) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (K := Metric.closedBall 0 (Real.sqrt 2 * ε)) (isCompact_closedBall 0 _) ?_
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra h
  exact hx (massKernel_eq_zero_of_lt hε (lt_of_not_ge h))

theorem integrable_massKernel (ε : ℝ) (hε : 0 < ε) : Integrable (massKernel ε) :=
  (continuous_massKernel ε hε).integrable_of_hasCompactSupport (hasCompactSupport_massKernel ε hε)

theorem integrable_massKernel_mul (ε : ℝ) (hε : 0 < ε) {Ψ : R3 → ℝ} (hΨ : Continuous Ψ) :
    Integrable (fun x : R3 => massKernel ε x * Ψ x) := by
  refine ((continuous_massKernel ε hε).mul hΨ).integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.of_support_subset_isCompact
    (K := Metric.closedBall 0 (Real.sqrt 2 * ε)) (isCompact_closedBall 0 _) ?_
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra h
  refine hx (by
    show massKernel ε x * Ψ x = 0
    rw [massKernel_eq_zero_of_lt hε (lt_of_not_ge h), zero_mul])

/-! ## The total mass `∫ massKernel ε = -1` -/


/-! ## The uniform bound on the total variation -/


/-! ## The limit -/


end Work.FTS.PressureOn.PoissonAux
end
-- ===== merged: Submission.Work.FTS.PressureOn.biotSavartDecayExplicit =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn

/-- **Explicit-constant far-field decay of the Biot–Savart field.**  For `g` bounded by `M ≥ 0` and
supported in the closed ball of radius `R ≥ 0`, the Biot–Savart field satisfies
`‖biotSavart g x‖ ≤ 3 M R (1 + 4R²)/(1 + ‖x‖²)` for every `x`.  This is the explicit-constant form of
`Work.FTS.PressureOn.biotSavart_decay`, which only produces an existential constant; the proof is the
same glue of `Work.LWP.BiotSavart.norm_biotSavart_near` (near field `‖x‖ ≤ 2R`, bound `3MR`) and
`Work.LWP.BiotSavart.farField_decay_const` (far field `2R ≤ ‖x‖`, bound `(4/3)MR³/‖x‖²`). -/
theorem biotSavartDecayExplicit {g : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {R M : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M) (hg : ∀ y, ‖g y‖ ≤ M)
    (hsupp : ∀ y, g y ≠ 0 → y ∈ Metric.closedBall 0 R) (x : EuclideanSpace ℝ (Fin 3)) :
    ‖Work.LWP.biotSavart g x‖ ≤ 3 * M * R * (1 + 4 * R ^ 2) / (1 + ‖x‖ ^ 2) := by
  have hden : (0 : ℝ) < 1 + ‖x‖ ^ 2 := by positivity
  rcases lt_or_ge (2 * R) ‖x‖ with hx | hx
  · -- **far field** `2R < ‖x‖`: the field decays like `‖x‖⁻²`, and the two weights are comparable
    have hx' : 2 * R ≤ ‖x‖ := le_of_lt hx
    have hn : (0 : ℝ) < ‖x‖ := by linarith
    have hb := Work.LWP.BiotSavart.farField_decay_const hR hM hg hsupp x hx'
    refine hb.trans ?_
    rw [div_le_div_iff₀ (pow_pos hn 2) hden]
    -- goal: `(4/3)·M·R³·(1+‖x‖²) ≤ 3·M·R·(1+4R²)·‖x‖²`
    have hsq : 4 * R ^ 2 ≤ ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
    have hmain : (4 / 3) * R ^ 2 * (1 + ‖x‖ ^ 2)
        ≤ 3 * (1 + 4 * R ^ 2) * ‖x‖ ^ 2 := by nlinarith [hsq, sq_nonneg R, sq_nonneg ‖x‖]
    have hMR : (0 : ℝ) ≤ M * R := mul_nonneg hM hR
    have hfin := mul_le_mul_of_nonneg_left hmain hMR
    nlinarith [hfin]
  · -- **near field** `‖x‖ ≤ 2R`: the field is bounded by `3MR` and the weight is `≥ 1`
    have hb := Work.LWP.BiotSavart.norm_biotSavart_near hR hM hg hsupp hx
    have hsq : ‖x‖ ^ 2 ≤ 4 * R ^ 2 := by nlinarith [norm_nonneg x]
    have hMR : (0 : ℝ) ≤ 3 * M * R := mul_nonneg (mul_nonneg (by norm_num) hM) hR
    refine hb.trans ?_
    rw [le_div_iff₀ hden]
    exact mul_le_mul_of_nonneg_left (by linarith) hMR

end Work.FTS.PressureOn
end
-- ===== merged: Submission.Work.FTS.PressureOn.integral_div_mul_of_differentiable_off_planes =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open FiniteTimeSingularity

namespace Work.FTS.PressureOn

/-! ## Endpoint normalisation for `Fin 3 → ℝ` -/

/-- The `0`-th coordinate of a `3`-vector.  These are the normal forms that make the endpoints
of the faces of the boxes below syntactically equal for neighbouring boxes. -/
@[simp] lemma vec3_0 {c0 c1 c2 : ℝ} : (![c0,c1,c2] : Fin 3 → ℝ) 0 = c0 := rfl
@[simp] lemma vec3_1 {c0 c1 c2 : ℝ} : (![c0,c1,c2] : Fin 3 → ℝ) 1 = c1 := rfl
@[simp] lemma vec3_2 {c0 c1 c2 : ℝ} : (![c0,c1,c2] : Fin 3 → ℝ) 2 = c2 := rfl

/-- The face of a box for the `0`-th coordinate, as a `2`-vector. -/
@[simp] lemma vec3_comp0 {c0 c1 c2 : ℝ} :
    ((![c0,c1,c2] : Fin 3 → ℝ) ∘ Fin.succAbove 0) = ![c1,c2] := by
  funext j; fin_cases j <;> rfl

/-- The face of a box for the `1`-st coordinate, as a `2`-vector. -/
@[simp] lemma vec3_comp1 {c0 c1 c2 : ℝ} :
    ((![c0,c1,c2] : Fin 3 → ℝ) ∘ Fin.succAbove 1) = ![c0,c2] := by
  funext j; fin_cases j <;> rfl

/-- The face of a box for the `2`-nd coordinate, as a `2`-vector. -/
@[simp] lemma vec3_comp2 {c0 c1 c2 : ℝ} :
    ((![c0,c1,c2] : Fin 3 → ℝ) ∘ Fin.succAbove 2) = ![c0,c1] := by
  funext j; fin_cases j <;> rfl

/-- **The sup norm of a `3`-vector is dominated by its `L²` norm.**  Used to transfer the
support radius between the coordinate space `Fin 3 → ℝ` and `ℝ³`. -/
lemma norm_le_norm_toLp (x : Fin 3 → ℝ) : ‖x‖ ≤ ‖(toLpCLM x : R3)‖ := by
  rw [toLpCLM_apply]
  exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
    fun i => PiLp.norm_apply_le (WithLp.toLp 2 x) i

/-! ## The two-plane divergence theorem in the coordinate space -/

/-- A face of a box lying outside the ball of radius `ρ` carries a vanishing integral. -/
lemma face_int_zero {F : (Fin 3 → ℝ) → Fin 3 → ℝ} {ρ : ℝ}
    (hF : ∀ x, ρ ≤ ‖x‖ → F x = 0) {c : ℝ} (hc : ρ ≤ |c|) (i : Fin 3) (u v : Fin 2 → ℝ) :
    (∫ x : Fin 2 → ℝ in Set.Icc u v, F (i.insertNth c x) i) = 0 := by
  have h : ∀ x : Fin 2 → ℝ, F (i.insertNth c x) i = 0 := by
    intro x
    have h0 : F (i.insertNth c x) = 0 := by
      refine hF _ ?_
      calc ρ ≤ |c| := hc
        _ = ‖c‖ := (Real.norm_eq_abs c).symm
        _ = ‖(i.insertNth c x : Fin 3 → ℝ) i‖ := by rw [Fin.insertNth_apply_same]
        _ ≤ ‖(i.insertNth c x : Fin 3 → ℝ)‖ := norm_le_pi_norm _ i
    exact congrFun h0 i
  simp [h]

/-- A box in the coordinate space, the `i`-th coordinate running over `Ioc (c i) (d i)`.  The
half-open convention makes boxes that share a face *literally* disjoint. -/
abbrev Iocc (c d : Fin 3 → ℝ) : Set (Fin 3 → ℝ) := Set.pi Set.univ (fun j => Set.Ioc (c j) (d j))

/-- Coordinates of a box with vector-literal endpoints. -/
lemma mem_pi_vals {P : ℝ → ℝ → Set ℝ} {c0 c1 c2 d0 d1 d2 : ℝ} {x : Fin 3 → ℝ} :
    x ∈ Set.pi Set.univ (fun j => P ((![c0,c1,c2] : Fin 3 → ℝ) j) ((![d0,d1,d2] : Fin 3 → ℝ) j)) ↔
      (x 0 ∈ P c0 d0) ∧ (x 1 ∈ P c1 d1) ∧ (x 2 ∈ P c2 d2) := by
  have hg : (fun j : Fin 3 => P ((![c0,c1,c2] : Fin 3 → ℝ) j) ((![d0,d1,d2] : Fin 3 → ℝ) j))
      = (![P c0 d0, P c1 d1, P c2 d2] : Fin 3 → Set ℝ) := by
    funext j
    fin_cases j <;> rfl
  have g0 : (![P c0 d0, P c1 d1, P c2 d2] : Fin 3 → Set ℝ) 0 = P c0 d0 := rfl
  have g1 : (![P c0 d0, P c1 d1, P c2 d2] : Fin 3 → Set ℝ) 1 = P c1 d1 := rfl
  have g2 : (![P c0 d0, P c1 d1, P c2 d2] : Fin 3 → Set ℝ) 2 = P c2 d2 := rfl
  rw [hg]
  refine ⟨fun h => ⟨?_, ?_, ?_⟩, fun h => ?_⟩
  · simpa only [g0] using Set.mem_pi.mp h 0 trivial
  · simpa only [g1] using Set.mem_pi.mp h 1 trivial
  · simpa only [g2] using Set.mem_pi.mp h 2 trivial
  · refine Set.mem_pi.mpr ?_
    intro j hj
    fin_cases j
    · show x 0 ∈ P c0 d0; exact h.1
    · show x 1 ∈ P c1 d1; exact h.2.1
    · show x 2 ∈ P c2 d2; exact h.2.2

/-- Coordinates of an `Iocc`-box with vector-literal endpoints. -/
lemma mem_Iocc_vals {c0 c1 c2 d0 d1 d2 : ℝ} {x : Fin 3 → ℝ} :
    x ∈ Iocc (![c0,c1,c2] : Fin 3 → ℝ) (![d0,d1,d2] : Fin 3 → ℝ) ↔
      (x 0 ∈ Set.Ioc c0 d0) ∧ (x 1 ∈ Set.Ioc c1 d1) ∧ (x 2 ∈ Set.Ioc c2 d2) :=
  mem_pi_vals (P := Set.Ioc)


/-- The big half-open box is the union of the two half-boxes cut out by the plane `x 0 = 0`. -/
lemma splitBig (R : ℝ) (hR : 0 < R) :
    Iocc ![(-R),(-R),(-R)] ![R,R,R]
      = Iocc ![0,(-R),(-R)] ![R,R,R] ∪ Iocc ![(-R),(-R),(-R)] ![0,R,R] := by
  ext x
  rw [Set.mem_union, mem_Iocc_vals, mem_Iocc_vals, mem_Iocc_vals]
  constructor
  · rintro ⟨h0, h1, h2⟩
    rw [Set.mem_Ioc] at h0 h1 h2
    rcases le_or_gt (x 0) 0 with h | h
    · exact Or.inr ⟨⟨h0.1, h⟩, h1, h2⟩
    · exact Or.inl ⟨⟨h, h0.2⟩, h1, h2⟩
  · rintro (⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩)
    · rw [Set.mem_Ioc] at h0 h1 h2 ⊢
      exact ⟨⟨by linarith, h0.2⟩, h1, h2⟩
    · rw [Set.mem_Ioc] at h0 h1 h2 ⊢
      exact ⟨⟨h0.1, by linarith⟩, h1, h2⟩

/-- The half-box `x 0 ∈ (0,R]` splits along the plane `x 2 = 0`. -/
lemma splitP (R : ℝ) (hR : 0 < R) :
    Iocc ![0,(-R),(-R)] ![R,R,R]
      = Iocc ![0,(-R),0] ![R,R,R] ∪ Iocc ![0,(-R),(-R)] ![R,R,0] := by
  ext x
  rw [Set.mem_union, mem_Iocc_vals, mem_Iocc_vals, mem_Iocc_vals]
  constructor
  · rintro ⟨h0, h1, h2⟩
    rw [Set.mem_Ioc] at h0 h1 h2
    rcases le_or_gt (x 2) 0 with h | h
    · exact Or.inr ⟨h0, h1, ⟨h2.1, h⟩⟩
    · exact Or.inl ⟨h0, h1, ⟨h, h2.2⟩⟩
  · rintro (⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩)
    · rw [Set.mem_Ioc] at h0 h1 h2 ⊢
      exact ⟨h0, h1, ⟨by linarith, h2.2⟩⟩
    · rw [Set.mem_Ioc] at h0 h1 h2 ⊢
      exact ⟨h0, h1, ⟨h2.1, by linarith⟩⟩

/-- The half-box `x 0 ∈ (-R,0]` splits along the plane `x 2 = 0`. -/
lemma splitM (R : ℝ) (hR : 0 < R) :
    Iocc ![(-R),(-R),(-R)] ![0,R,R]
      = Iocc ![(-R),(-R),0] ![0,R,R] ∪ Iocc ![(-R),(-R),(-R)] ![0,R,0] := by
  ext x
  rw [Set.mem_union, mem_Iocc_vals, mem_Iocc_vals, mem_Iocc_vals]
  constructor
  · rintro ⟨h0, h1, h2⟩
    rw [Set.mem_Ioc] at h0 h1 h2
    rcases le_or_gt (x 2) 0 with h | h
    · exact Or.inr ⟨h0, h1, ⟨h2.1, h⟩⟩
    · exact Or.inl ⟨h0, h1, ⟨h, h2.2⟩⟩
  · rintro (⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩)
    · rw [Set.mem_Ioc] at h0 h1 h2 ⊢
      exact ⟨h0, h1, ⟨by linarith, h2.2⟩⟩
    · rw [Set.mem_Ioc] at h0 h1 h2 ⊢
      exact ⟨h0, h1, ⟨h2.1, by linarith⟩⟩

lemma disjBig (R : ℝ) :
    Disjoint (Iocc ![0,(-R),(-R)] ![R,R,R]) (Iocc ![(-R),(-R),(-R)] ![0,R,R]) := by
  rw [Set.disjoint_left]
  intro x h1 h2
  rw [mem_Iocc_vals] at h1 h2
  rw [Set.mem_Ioc] at h1 h2
  exact absurd h1.1.1 (not_lt.mpr h2.1.2)

lemma disjP (R : ℝ) :
    Disjoint (Iocc ![0,(-R),0] ![R,R,R]) (Iocc ![0,(-R),(-R)] ![R,R,0]) := by
  rw [Set.disjoint_left]
  intro x h1 h2
  rw [mem_Iocc_vals] at h1 h2
  rw [Set.mem_Ioc] at h1 h2
  exact absurd h1.2.2.1 (not_lt.mpr h2.2.2.2)

lemma disjM (R : ℝ) :
    Disjoint (Iocc ![(-R),(-R),0] ![0,R,R]) (Iocc ![(-R),(-R),(-R)] ![0,R,0]) := by
  rw [Set.disjoint_left]
  intro x h1 h2
  rw [mem_Iocc_vals] at h1 h2
  rw [Set.mem_Ioc] at h1 h2
  exact absurd h1.2.2.1 (not_lt.mpr h2.2.2.2)

lemma measurableSet_Iocc (c d : Fin 3 → ℝ) : MeasurableSet (Iocc c d) := by
  rw [Iocc]
  exact MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioc)

/-- **The divergence theorem off the two planes, in the coordinate space.**  If a field
`F : (Fin 3 → ℝ) → Fin 3 → ℝ` is continuous, differentiable with derivative `F'` off the
coordinate planes `x 0 = 0` and `x 2 = 0`, has integrable "divergence"
`x ↦ ∑ i, F' x (Pi.single i 1) i`, and both `F` and its divergence vanish outside the ball of
radius `ρ`, then the integral of the divergence vanishes. -/
theorem integral_trace_eq_zero_of_diff_off_planes
    (F : (Fin 3 → ℝ) → Fin 3 → ℝ)
    (F' : (Fin 3 → ℝ) → (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ))
    (hcont : Continuous F)
    (hdiff : ∀ x, x 0 ≠ 0 → x 2 ≠ 0 → HasFDerivAt F (F' x) x)
    (hint : MeasureTheory.Integrable fun x => ∑ i, F' x (Pi.single i 1) i)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hFsupp : ∀ x, ρ ≤ ‖x‖ → F x = 0)
    (hDsupp : ∀ x, ρ ≤ ‖x‖ → (∑ i, F' x (Pi.single i 1) i) = 0) :
    (∫ x, ∑ i, F' x (Pi.single i 1) i) = 0 := by
  set R : ℝ := ρ + 1 with hRdef
  have hRpos : 0 < R := by rw [hRdef]; linarith
  have hρR : ρ ≤ R := by rw [hRdef]; linarith
  let D : (Fin 3 → ℝ) → ℝ := fun x => ∑ i, F' x (Pi.single i 1) i
  have hD0 : ∀ x, ρ ≤ ‖x‖ → D x = 0 := fun x hx => hDsupp x hx
  have hintD : MeasureTheory.Integrable D := hint
  have hRabs : ρ ≤ |R| := by rw [abs_of_pos hRpos]; exact hρR
  have hmRabs : ρ ≤ |-R| := by rw [abs_neg, abs_of_pos hRpos]; exact hρR
  -- the four boxes cut out by the two planes
  have hle1 : (![(0:ℝ),-R,0] : Fin 3 → ℝ) ≤ ![R,R,R] := by
    intro i; fin_cases i <;> simp <;> linarith [hRpos]
  have hlt1 : ∀ i, (![(0:ℝ),-R,0] : Fin 3 → ℝ) i < ![R,R,R] i := by
    intro i; fin_cases i <;> simp <;> linarith [hRpos]
  have hgood1 : ∀ x ∈ Set.pi Set.univ (fun i => Set.Ioo
      ((![(0:ℝ),-R,0] : Fin 3 → ℝ) i) ((![R,R,R] : Fin 3 → ℝ) i)), x 0 ≠ 0 ∧ x 2 ≠ 0 := by
    intro x hx
    have h := (mem_pi_vals (P := Set.Ioo)).mp hx
    exact ⟨ne_of_gt h.1.1, ne_of_gt h.2.2.1⟩
  have hbox1 : (∫ x in Set.Icc (![(0:ℝ),-R,0] : Fin 3 → ℝ) (![R,R,R] : Fin 3 → ℝ), D x)
      = ∑ i : Fin 3,
          ((∫ x in Set.Icc (((![(0:ℝ),-R,0] : Fin 3 → ℝ)) ∘ i.succAbove)
              (((![R,R,R] : Fin 3 → ℝ)) ∘ i.succAbove),
              F (i.insertNth ((![R,R,R] : Fin 3 → ℝ) i) x) i) -
            (∫ x in Set.Icc (((![(0:ℝ),-R,0] : Fin 3 → ℝ)) ∘ i.succAbove)
              (((![R,R,R] : Fin 3 → ℝ)) ∘ i.succAbove),
              F (i.insertNth ((![(0:ℝ),-R,0] : Fin 3 → ℝ) i) x) i)) := by
    exact box_divergence_identity (F := F) (F' := F') _ _ hle1 hlt1 hgood1
      hcont.continuousOn hdiff hint.integrableOn
  have hle2 : (![-R,-R,0] : Fin 3 → ℝ) ≤ ![0,R,R] := by
    intro i; fin_cases i <;> simp <;> linarith [hRpos]
  have hlt2 : ∀ i, (![-R,-R,0] : Fin 3 → ℝ) i < ![0,R,R] i := by
    intro i; fin_cases i <;> simp <;> linarith [hRpos]
  have hgood2 : ∀ x ∈ Set.pi Set.univ (fun i => Set.Ioo
      ((![-R,-R,0] : Fin 3 → ℝ) i) ((![0,R,R] : Fin 3 → ℝ) i)), x 0 ≠ 0 ∧ x 2 ≠ 0 := by
    intro x hx
    have h := (mem_pi_vals (P := Set.Ioo)).mp hx
    exact ⟨ne_of_lt h.1.2, ne_of_gt h.2.2.1⟩
  have hbox2 : (∫ x in Set.Icc (![-R,-R,0] : Fin 3 → ℝ) (![0,R,R] : Fin 3 → ℝ), D x)
      = ∑ i : Fin 3,
          ((∫ x in Set.Icc (((![-R,-R,0] : Fin 3 → ℝ)) ∘ i.succAbove)
              (((![0,R,R] : Fin 3 → ℝ)) ∘ i.succAbove),
              F (i.insertNth ((![0,R,R] : Fin 3 → ℝ) i) x) i) -
            (∫ x in Set.Icc (((![-R,-R,0] : Fin 3 → ℝ)) ∘ i.succAbove)
              (((![0,R,R] : Fin 3 → ℝ)) ∘ i.succAbove),
              F (i.insertNth ((![-R,-R,0] : Fin 3 → ℝ) i) x) i)) := by
    exact box_divergence_identity (F := F) (F' := F') _ _ hle2 hlt2 hgood2
      hcont.continuousOn hdiff hint.integrableOn
  have hle3 : (![(0:ℝ),-R,-R] : Fin 3 → ℝ) ≤ ![R,R,0] := by
    intro i; fin_cases i <;> simp <;> linarith [hRpos]
  have hlt3 : ∀ i, (![(0:ℝ),-R,-R] : Fin 3 → ℝ) i < ![R,R,0] i := by
    intro i; fin_cases i <;> simp <;> linarith [hRpos]
  have hgood3 : ∀ x ∈ Set.pi Set.univ (fun i => Set.Ioo
      ((![(0:ℝ),-R,-R] : Fin 3 → ℝ) i) ((![R,R,0] : Fin 3 → ℝ) i)), x 0 ≠ 0 ∧ x 2 ≠ 0 := by
    intro x hx
    have h := (mem_pi_vals (P := Set.Ioo)).mp hx
    exact ⟨ne_of_gt h.1.1, ne_of_lt h.2.2.2⟩
  have hbox3 : (∫ x in Set.Icc (![(0:ℝ),-R,-R] : Fin 3 → ℝ) (![R,R,0] : Fin 3 → ℝ), D x)
      = ∑ i : Fin 3,
          ((∫ x in Set.Icc (((![(0:ℝ),-R,-R] : Fin 3 → ℝ)) ∘ i.succAbove)
              (((![R,R,0] : Fin 3 → ℝ)) ∘ i.succAbove),
              F (i.insertNth ((![R,R,0] : Fin 3 → ℝ) i) x) i) -
            (∫ x in Set.Icc (((![(0:ℝ),-R,-R] : Fin 3 → ℝ)) ∘ i.succAbove)
              (((![R,R,0] : Fin 3 → ℝ)) ∘ i.succAbove),
              F (i.insertNth ((![(0:ℝ),-R,-R] : Fin 3 → ℝ) i) x) i)) := by
    exact box_divergence_identity (F := F) (F' := F') _ _ hle3 hlt3 hgood3
      hcont.continuousOn hdiff hint.integrableOn
  have hle4 : (![-R,-R,-R] : Fin 3 → ℝ) ≤ ![0,R,0] := by
    intro i; fin_cases i <;> simp <;> linarith [hRpos]
  have hlt4 : ∀ i, (![-R,-R,-R] : Fin 3 → ℝ) i < ![0,R,0] i := by
    intro i; fin_cases i <;> simp <;> linarith [hRpos]
  have hgood4 : ∀ x ∈ Set.pi Set.univ (fun i => Set.Ioo
      ((![-R,-R,-R] : Fin 3 → ℝ) i) ((![0,R,0] : Fin 3 → ℝ) i)), x 0 ≠ 0 ∧ x 2 ≠ 0 := by
    intro x hx
    have h := (mem_pi_vals (P := Set.Ioo)).mp hx
    exact ⟨ne_of_lt h.1.2, ne_of_lt h.2.2.2⟩
  have hbox4 : (∫ x in Set.Icc (![-R,-R,-R] : Fin 3 → ℝ) (![0,R,0] : Fin 3 → ℝ), D x)
      = ∑ i : Fin 3,
          ((∫ x in Set.Icc (((![-R,-R,-R] : Fin 3 → ℝ)) ∘ i.succAbove)
              (((![0,R,0] : Fin 3 → ℝ)) ∘ i.succAbove),
              F (i.insertNth ((![0,R,0] : Fin 3 → ℝ) i) x) i) -
            (∫ x in Set.Icc (((![-R,-R,-R] : Fin 3 → ℝ)) ∘ i.succAbove)
              (((![0,R,0] : Fin 3 → ℝ)) ∘ i.succAbove),
              F (i.insertNth ((![-R,-R,-R] : Fin 3 → ℝ) i) x) i)) := by
    exact box_divergence_identity (F := F) (F' := F') _ _ hle4 hlt4 hgood4
      hcont.continuousOn hdiff hint.integrableOn
  -- all faces at `x i = ±R` vanish, and the remaining faces are matched between neighbours
  rw [Fin.sum_univ_three] at hbox1 hbox2 hbox3 hbox4
  simp only [face_int_zero hFsupp hRabs, face_int_zero hFsupp hmRabs, vec3_0, vec3_1, vec3_2,
    vec3_comp0, vec3_comp1, vec3_comp2] at hbox1 hbox2 hbox3 hbox4
  -- `∫ D` over the big half-open box, and the two-stage splitting
  have hbig : (∫ x in Iocc ![(-R),(-R),(-R)] ![R,R,R], D x) = ∫ x, D x := by
    refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero ?_
    intro x hx
    refine hD0 x ?_
    by_contra hcon
    rw [not_le] at hcon
    have h0 : |x 0| < ρ := by
      rw [← Real.norm_eq_abs]
      exact lt_of_le_of_lt (norm_le_pi_norm x 0) hcon
    have h1 : |x 1| < ρ := by
      rw [← Real.norm_eq_abs]
      exact lt_of_le_of_lt (norm_le_pi_norm x 1) hcon
    have h2 : |x 2| < ρ := by
      rw [← Real.norm_eq_abs]
      exact lt_of_le_of_lt (norm_le_pi_norm x 2) hcon
    exact hx (by
      rw [mem_Iocc_vals]
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
        linarith [h0, h1, h2, neg_abs_le (x 0), le_abs_self (x 0), neg_abs_le (x 1),
          le_abs_self (x 1), neg_abs_le (x 2), le_abs_self (x 2), hρR])
  have hsplit1 : (∫ x in Iocc ![(-R),(-R),(-R)] ![R,R,R], D x)
      = (∫ x in Iocc ![0,(-R),(-R)] ![R,R,R], D x)
        + (∫ x in Iocc ![(-R),(-R),(-R)] ![0,R,R], D x) := by
    rw [splitBig R hRpos]
    exact MeasureTheory.setIntegral_union (disjBig R) (measurableSet_Iocc _ _) hintD.integrableOn
      hintD.integrableOn
  have hsplit2 : (∫ x in Iocc ![0,(-R),(-R)] ![R,R,R], D x)
      = (∫ x in Iocc ![0,(-R),0] ![R,R,R], D x)
        + (∫ x in Iocc ![0,(-R),(-R)] ![R,R,0], D x) := by
    rw [splitP R hRpos]
    exact MeasureTheory.setIntegral_union (disjP R) (measurableSet_Iocc _ _) hintD.integrableOn
      hintD.integrableOn
  have hsplit3 : (∫ x in Iocc ![(-R),(-R),(-R)] ![0,R,R], D x)
      = (∫ x in Iocc ![(-R),(-R),0] ![0,R,R], D x)
        + (∫ x in Iocc ![(-R),(-R),(-R)] ![0,R,0], D x) := by
    rw [splitM R hRpos]
    exact MeasureTheory.setIntegral_union (disjM R) (measurableSet_Iocc _ _) hintD.integrableOn
      hintD.integrableOn
  -- the half-open boxes are a.e. the closed boxes of the divergence theorem
  have hvol : (MeasureTheory.volume : MeasureTheory.Measure (Fin 3 → ℝ))
      = MeasureTheory.Measure.pi (fun _ : Fin 3 => MeasureTheory.volume) :=
    MeasureTheory.volume_pi
  have hS1 : (∫ x in Iocc ![0,(-R),0] ![R,R,R], D x)
      = ∫ x in Set.Icc (![(0:ℝ),-R,0] : Fin 3 → ℝ) (![R,R,R] : Fin 3 → ℝ), D x := by
    refine MeasureTheory.setIntegral_congr_set ?_
    have h := MeasureTheory.Measure.univ_pi_Ioc_ae_eq_Icc
      (μ := fun _ : Fin 3 => (MeasureTheory.volume : MeasureTheory.Measure ℝ))
      (f := (![(0:ℝ),-R,0] : Fin 3 → ℝ)) (g := (![R,R,R] : Fin 3 → ℝ))
    rw [← hvol] at h
    exact h
  have hS2 : (∫ x in Iocc ![(-R),(-R),0] ![0,R,R], D x)
      = ∫ x in Set.Icc (![-R,-R,0] : Fin 3 → ℝ) (![0,R,R] : Fin 3 → ℝ), D x := by
    refine MeasureTheory.setIntegral_congr_set ?_
    have h := MeasureTheory.Measure.univ_pi_Ioc_ae_eq_Icc
      (μ := fun _ : Fin 3 => (MeasureTheory.volume : MeasureTheory.Measure ℝ))
      (f := (![-R,-R,0] : Fin 3 → ℝ)) (g := (![0,R,R] : Fin 3 → ℝ))
    rw [← hvol] at h
    exact h
  have hS3 : (∫ x in Iocc ![0,(-R),(-R)] ![R,R,0], D x)
      = ∫ x in Set.Icc (![(0:ℝ),-R,-R] : Fin 3 → ℝ) (![R,R,0] : Fin 3 → ℝ), D x := by
    refine MeasureTheory.setIntegral_congr_set ?_
    have h := MeasureTheory.Measure.univ_pi_Ioc_ae_eq_Icc
      (μ := fun _ : Fin 3 => (MeasureTheory.volume : MeasureTheory.Measure ℝ))
      (f := (![(0:ℝ),-R,-R] : Fin 3 → ℝ)) (g := (![R,R,0] : Fin 3 → ℝ))
    rw [← hvol] at h
    exact h
  have hS4 : (∫ x in Iocc ![(-R),(-R),(-R)] ![0,R,0], D x)
      = ∫ x in Set.Icc (![-R,-R,-R] : Fin 3 → ℝ) (![0,R,0] : Fin 3 → ℝ), D x := by
    refine MeasureTheory.setIntegral_congr_set ?_
    have h := MeasureTheory.Measure.univ_pi_Ioc_ae_eq_Icc
      (μ := fun _ : Fin 3 => (MeasureTheory.volume : MeasureTheory.Measure ℝ))
      (f := (![-R,-R,-R] : Fin 3 → ℝ)) (g := (![0,R,0] : Fin 3 → ℝ))
    rw [← hvol] at h
    exact h
  linarith [hbig.symm, hsplit1, hsplit2, hsplit3, hS1, hS2, hS3, hS4,
    hbox1, hbox2, hbox3, hbox4]

/-! ## Integration by parts for `ψ • ω` -/


end Work.FTS.PressureOn
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsLocalPStar.TraceOfOscPiO =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology
open MeasureTheory Set Filter

/-!
## The trace at `π/2` of a function with a weighted oscillation bound

`TraceOfOscPiO` is the "right endpoint" companion of `TraceOfOsc`.  If `u : ℝ → ℝ` satisfies

  `|u b - u a| ≤ K · sin(2a)^{(γ-1)/2}`   for `π/4 ≤ a ≤ b < π/2`,   `γ > 1`, `K ≥ 0`,

then `u` has a limit `mu` at `π/2` from the left, at the weighted Hardy rate

  `(u θ - mu)² ≤ K² · sin(2θ)^{γ-1}`   for `π/4 < θ < π/2`.

The weight `sin(2a)^{(γ-1)/2}` tends to `0` as `a → π/2⁻`, so the hypothesis says precisely
that `u` is Cauchy at `π/2⁻` with an explicit modulus.  The proof extracts the limit along the
explicit sequence `a n = π/2 - 1/(n+2) ↑ π/2` (Cauchy + completeness of `ℝ`), recovers the rate
by passing the oscillation bound to the limit, and finally obtains the unrestricted filter
convergence by squeezing `|u θ - mu|` between `0` and `K · sin(2θ)^{(γ-1)/2} → 0`.
-/

theorem TraceOfOscPiO {u : ℝ → ℝ} {γ K : ℝ} (hγ : 0 < γ - 1) (hK : 0 ≤ K)
    (hbound : ∀ a b : ℝ, Real.pi / 4 ≤ a → a ≤ b → b < Real.pi / 2 →
      |u b - u a| ≤ K * (Real.sin (2 * a)) ^ ((γ - 1) / 2)) :
    ∃ mu : ℝ, Filter.Tendsto u (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds mu) ∧
      ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
        (u θ - mu) ^ 2 ≤ K ^ 2 * (Real.sin (2 * θ)) ^ (γ - 1) := by
  have hγ2 : 0 < (γ - 1) / 2 := by linarith
  -- the explicit sequence tending to `π/2` from below
  let a : ℕ → ℝ := fun n => Real.pi / 2 - 1 / ((n : ℝ) + 2)
  have ha_ge : ∀ n : ℕ, Real.pi / 4 ≤ a n := by
    intro n
    have h1 : (1 : ℝ) / ((n : ℝ) + 2) ≤ 1 / 2 := by
      refine one_div_le_one_div_of_le (show (0 : ℝ) < 2 by norm_num) ?_
      linarith [show (0 : ℝ) ≤ (n : ℝ) by positivity]
    have h2 : (1 : ℝ) / 2 ≤ Real.pi / 4 := by linarith [Real.pi_gt_three]
    dsimp only [a]
    linarith
  have ha_lt : ∀ n : ℕ, a n < Real.pi / 2 := by
    intro n
    have h1 : 0 < (1 : ℝ) / ((n : ℝ) + 2) := by positivity
    dsimp only [a]
    linarith
  have ha_mono : Monotone a := by
    refine monotone_nat_of_le_succ fun n => ?_
    have h1 : (1 : ℝ) / (((n + 1 : ℕ) : ℝ) + 2) ≤ 1 / ((n : ℝ) + 2) := by
      refine one_div_le_one_div_of_le (show (0 : ℝ) < (n : ℝ) + 2 by positivity) ?_
      push_cast
      linarith
    dsimp only [a]
    linarith
  have ha_tendsto : Tendsto a atTop (nhds (Real.pi / 2)) := by
    have h2 : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right atTop (f := fun n : ℕ => (n : ℝ)) 2
        tendsto_natCast_atTop_atTop
    have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 2)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp h2
    have h3 := (tendsto_const_nhds (x := Real.pi / 2)).sub hinv
    simpa [a, one_div, sub_zero] using h3
  -- `sin (2·) ≥ 0` on the closed angular interval `[π/4, π/2]`
  have sin_nn : ∀ θ : ℝ, Real.pi / 4 ≤ θ → θ < Real.pi / 2 → 0 ≤ Real.sin (2 * θ) := by
    intro θ h1 h2
    exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos])
  -- the weight along the testing sequence tends to `0`
  have hSseq : Tendsto (fun n : ℕ => K * Real.sin (2 * a n) ^ ((γ - 1) / 2)) atTop (nhds 0) := by
    have hsin : Tendsto (fun n : ℕ => Real.sin (2 * a n)) atTop (nhds 0) := by
      have h2 : Tendsto (fun n : ℕ => 2 * a n) atTop (nhds (2 * (Real.pi / 2))) :=
        (tendsto_const_nhds (x := (2 : ℝ))).mul ha_tendsto
      have h3 := (Real.continuous_sin.tendsto (2 * (Real.pi / 2))).comp h2
      simpa [Function.comp_def, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi] using h3
    have h4 := hsin.rpow_const_nhds_zero hγ2
    simpa using h4.const_mul K
  -- the sequence is Cauchy, hence converges
  have hcauchy : CauchySeq (fun n : ℕ => u (a n)) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hSseq (ε / 2) (by linarith)
    refine ⟨N, fun m hm n hn => ?_⟩
    have hSN : K * Real.sin (2 * a N) ^ ((γ - 1) / 2) < ε / 2 := by
      have h0 := hN N le_rfl
      rw [Real.dist_eq, sub_zero] at h0
      rwa [abs_of_nonneg
        (mul_nonneg hK (Real.rpow_nonneg (sin_nn (a N) (ha_ge N) (ha_lt N)) _))] at h0
    have h1 : dist (u (a m)) (u (a N)) ≤ K * Real.sin (2 * a N) ^ ((γ - 1) / 2) := by
      rw [Real.dist_eq]
      exact hbound (a N) (a m) (ha_ge N) (ha_mono hm) (ha_lt m)
    have h2 : dist (u (a N)) (u (a n)) ≤ K * Real.sin (2 * a N) ^ ((γ - 1) / 2) := by
      rw [Real.dist_eq, abs_sub_comm]
      exact hbound (a N) (a n) (ha_ge N) (ha_mono hn) (ha_lt n)
    linarith [dist_triangle (u (a m)) (u (a N)) (u (a n))]
  obtain ⟨mu, hmu⟩ := cauchySeq_tendsto_of_complete hcauchy
  -- the weighted rate, obtained by passing the oscillation bound to the limit
  have hbd : ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
      |u θ - mu| ≤ K * Real.sin (2 * θ) ^ ((γ - 1) / 2) := by
    intro θ hθ
    have hev : ∀ᶠ n : ℕ in atTop, θ < a n :=
      ha_tendsto.eventually (isOpen_Ioi.mem_nhds hθ.2)
    have hlim : Tendsto (fun n : ℕ => |u (a n) - u θ|) atTop (nhds |mu - u θ|) :=
      (hmu.sub_const (u θ)).abs
    have hle : |mu - u θ| ≤ K * Real.sin (2 * θ) ^ ((γ - 1) / 2) := by
      refine le_of_tendsto hlim ?_
      filter_upwards [hev] with n hn
      exact hbound θ (a n) (le_of_lt hθ.1) (le_of_lt hn) (ha_lt n)
    rwa [abs_sub_comm] at hle
  refine ⟨mu, ?_, ?_⟩
  · -- the unrestricted convergence at `π/2` from the left
    have hmem : Set.Ioo (Real.pi / 4) (Real.pi / 2) ∈
        nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) := by
      rw [mem_nhdsWithin_iff_eventually]
      filter_upwards [Ioi_mem_nhds (show Real.pi / 4 < Real.pi / 2 by linarith [Real.pi_pos])]
        with x hx hx2
      exact ⟨hx, hx2⟩
    have hS : Tendsto (fun θ : ℝ => K * Real.sin (2 * θ) ^ ((γ - 1) / 2))
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
      have hid : Tendsto (fun θ : ℝ => θ) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
          (nhds (Real.pi / 2)) := tendsto_id.mono_right nhdsWithin_le_nhds
      have h2 : Tendsto (fun θ : ℝ => 2 * θ) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
          (nhds (2 * (Real.pi / 2))) := (tendsto_const_nhds (x := (2 : ℝ))).mul hid
      have h3 : Tendsto (fun θ : ℝ => Real.sin (2 * θ))
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
          (nhds (Real.sin (2 * (Real.pi / 2)))) :=
        (Real.continuous_sin.tendsto (2 * (Real.pi / 2))).comp h2
      have h4 : Tendsto (fun θ : ℝ => Real.sin (2 * θ))
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
        simpa [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi] using h3
      have h5 := h4.rpow_const_nhds_zero hγ2
      simpa using h5.const_mul K
    have habs : Tendsto (fun θ : ℝ => |u θ - mu|)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
      refine squeeze_zero' (g := fun θ : ℝ => K * Real.sin (2 * θ) ^ ((γ - 1) / 2))
        (Eventually.of_forall fun θ => abs_nonneg _) ?_ hS
      exact eventually_of_mem hmem fun θ hθ => hbd θ hθ
    rw [tendsto_iff_dist_tendsto_zero]
    simpa [Real.dist_eq] using habs
  · -- the rate, by squaring the oscillation bound
    intro θ hθ
    have hb := hbd θ hθ
    have hspos : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, Real.pi_pos])
        (by linarith [hθ.2, Real.pi_pos])
    have hsq : (u θ - mu) ^ 2 ≤ (K * Real.sin (2 * θ) ^ ((γ - 1) / 2)) ^ 2 := by
      rw [sq_le_sq, abs_of_nonneg (mul_nonneg hK (Real.rpow_nonneg (le_of_lt hspos) _))]
      exact hb
    have hkey : (K * Real.sin (2 * θ) ^ ((γ - 1) / 2)) ^ 2
        = K ^ 2 * Real.sin (2 * θ) ^ (γ - 1) := by
      have h1 : (Real.sin (2 * θ) ^ ((γ - 1) / 2)) ^ 2 = Real.sin (2 * θ) ^ (γ - 1) := by
        rw [pow_two, ← Real.rpow_add hspos]
        congr 1
        ring
      rw [mul_pow, h1]
    rw [hkey] at hsq
    exact hsq

end Work.FTS.StrongEps.EpsLocalPStar
end
-- ===== merged: Submission.Work.FTS_EllLimOK.integrableOn_Fstar_sq_zpow =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

set_option autoImplicit false

/-- At level `k = 0` the `H^k`-integrand collapses to a single square: the `D_z`-sum has the
one term `i = 0` and the mixed double sum is empty. -/
private lemma HkIntegrand_zero_eq_prv (α : ℝ) (F : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 F z θ
      = (F z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp [Work.Spaces.HkIntegrand]

/-- The auxiliary angular function `sin(2θ)^η · (sin θ cos²θ)²`, the reciprocal weight of the
second factor in the weighted Cauchy--Schwarz inequality. -/
private def Cfun (θ : ℝ) : ℝ :=
  (Work.Elliptic.sinCos2 θ) ^ 2 * (Real.sin (2 * θ)) ^ (Work.Spaces.eta)






end Work.FTS_EllLimOK
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.majorant_Ioi_integrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.Sys

open MeasureTheory Set Filter

/-- Integrability on `(0,∞)` of the majorant `3*(π/2)*(20/(1+s)² + Cw*s^{1/2}/(1+s)²)` and its
integral bound.

PROOF RECIPE.  `∫_{Ioi 0} 1/(1+s)² = 1` via `Work.FM.integral_Ioi_Fstar_div 0 le_rfl`
(`∫_{Ioi 0} FM.Fstar s/s = 2`) together with `FM.Fstar s / s = 2/(1+s)²` for `s ≠ 0` (a.e. on
`Ioi 0`; `FM.Fstar s = 2*s/(1+s)^2`), and `∫_{Ioi 0} s^{1/2}/(1+s)² ≤ 3`: dominate by
`(1+s)^{-1/2}*(1+s)^{-1} ` -- concretely `s^{1/2}/(1+s)² ≤ (1+s)^{-3/2}` (since `s^{1/2} ≤ (1+s)^{1/2}`)
and `∫_{Ioi 0} (1+s)^{-3/2} = 2` (primitive `-2*(1+s)^{-1/2}`; e.g.
`MeasureTheory.integrableOn_Ioi_deriv_of_nonneg'`, or split `Ioi 0 = Ioc 0 1 ∪ Ioi 1` and use
`intervalIntegral` / `integral_Ioi_rpow_of_lt` after the shift).  All three integrands are
nonnegative, so `MeasureTheory.IntegrableOn` follows from the pointwise domination and the
integrability of the dominating functions (`MeasureTheory.Integrable.mono'`,
`ContinuousOn.aestronglyMeasurable`).  Finally distribute the constants with `integral_add`,
`integral_const_mul` and use `Real.pi_le_four` for `3*(π/2)*20 = 30π ≤ 120` and
`3*(π/2)*3*Cw = (9π/2)*Cw ≤ 18*Cw` (`hCw : 0 ≤ Cw`). -/
theorem majorant_Ioi_integrable {Cw : ℝ} (hCw : 0 ≤ Cw) :
    MeasureTheory.IntegrableOn
        (fun s : ℝ => 3 * (Real.pi / 2)
          * (20 / (1 + s) ^ 2 + Cw * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2)))
        (Set.Ioi 0) ∧
      (∫ s in Set.Ioi 0, 3 * (Real.pi / 2)
          * (20 / (1 + s) ^ 2 + Cw * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2)))
        ≤ 120 + 18 * Cw := by
  -- ## The first elementary tail integral: `∫_{(0,∞)} ds/(1+s)² = 1`
  -- `FM.Fstar s / s = 2/(1+s)²` on `(0,∞)`
  have hFcongr : EqOn (fun s : ℝ => Work.FM.Fstar s / s)
      (fun s : ℝ => 2 / (1 + s) ^ 2) (Set.Ioi 0) := by
    intro s hs
    have hs0 : s ≠ 0 := by have := hs.out; linarith
    unfold Work.FM.Fstar
    field_simp
  have htwo : (∫ s in Set.Ioi (0 : ℝ), 2 / (1 + s) ^ 2) = 2 := by
    have h := Work.FM.integral_Ioi_Fstar_div 0 le_rfl
    rw [setIntegral_congr_fun measurableSet_Ioi hFcongr] at h
    simpa using h
  have hA_int : IntegrableOn (fun s : ℝ => 1 / (1 + s) ^ 2) (Set.Ioi 0) := by
    have h2 := Work.FTS.MeridianDyn.Bridge.Pieces.integrableOn_two_div_one_add_sq 0 le_rfl
    refine MeasureTheory.IntegrableOn.congr_fun (h2.integrable.const_mul (1 / 2)) ?_
      measurableSet_Ioi
    intro s _
    ring
  have hA_val : (∫ s in Set.Ioi (0 : ℝ), 1 / (1 + s) ^ 2) = 1 := by
    have h2 : (∫ s in Set.Ioi (0 : ℝ), 2 * (1 / (1 + s) ^ 2)) = 2 := by
      rw [show (fun s : ℝ => 2 * (1 / (1 + s) ^ 2)) =
          fun s : ℝ => 2 / (1 + s) ^ 2 by funext s; ring]
      exact htwo
    rw [MeasureTheory.integral_const_mul (2 : ℝ)] at h2
    linarith
  -- ## The second elementary tail integral: `∫_{(0,∞)} s^{1/2}/(1+s)² ≤ 3`
  -- (the general tail bound `∫_{(z,∞)} ≤ 3` for `z ≥ 0` at `z = 0`)
  obtain ⟨hB_int, hB_val⟩ :=
    MajorantPieces.sqrt_div_sq_Ioi_integral_le (z := 0) le_rfl
  -- ## Integrability of the two summands of the majorant
  have h20_int : IntegrableOn (fun s : ℝ => 20 / (1 + s) ^ 2) (Set.Ioi 0) :=
    MeasureTheory.IntegrableOn.congr_fun (hA_int.integrable.const_mul 20)
      (fun s _ => by ring) measurableSet_Ioi
  have hCw_int : IntegrableOn (fun s : ℝ => Cw * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2))
      (Set.Ioi 0) := hB_int.integrable.const_mul Cw
  have hsum_int : IntegrableOn
      (fun s : ℝ => 20 / (1 + s) ^ 2 + Cw * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2))
      (Set.Ioi 0) := h20_int.add hCw_int
  refine ⟨hsum_int.integrable.const_mul (3 * (Real.pi / 2)), ?_⟩
  -- ## The two integral values
  have h20val : (∫ s in Set.Ioi (0 : ℝ), 20 / (1 + s) ^ 2) = 20 := by
    have hk : (∫ s in Set.Ioi (0 : ℝ), 20 * (1 / (1 + s) ^ 2))
        = 20 * (∫ s in Set.Ioi (0 : ℝ), 1 / (1 + s) ^ 2) :=
      MeasureTheory.integral_const_mul (20 : ℝ) (fun s : ℝ => 1 / (1 + s) ^ 2)
    rw [show (fun s : ℝ => 20 / (1 + s) ^ 2) = fun s : ℝ => 20 * (1 / (1 + s) ^ 2) by
      funext s; ring, hk, hA_val]
    norm_num
  have hCwval : (∫ s in Set.Ioi (0 : ℝ), Cw * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2)) ≤ 3 * Cw := by
    have hk : (∫ s in Set.Ioi (0 : ℝ), Cw * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2))
        = Cw * (∫ s in Set.Ioi (0 : ℝ), s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2) :=
      MeasureTheory.integral_const_mul (Cw : ℝ)
        (fun s : ℝ => s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2)
    rw [hk]
    calc Cw * (∫ s in Set.Ioi (0 : ℝ), s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2) ≤ Cw * 3 :=
          mul_le_mul_of_nonneg_left hB_val hCw
      _ = 3 * Cw := by ring
  have hsum_val : (∫ s in Set.Ioi (0 : ℝ),
        (20 / (1 + s) ^ 2 + Cw * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2))) ≤ 20 + 3 * Cw := by
    rw [MeasureTheory.integral_add h20_int hCw_int]
    linarith
  -- ## Distributing the constants
  have hconst : (∫ s in Set.Ioi (0 : ℝ), 3 * (Real.pi / 2)
        * (20 / (1 + s) ^ 2 + Cw * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2)))
      = 3 * (Real.pi / 2) * (∫ s in Set.Ioi (0 : ℝ),
          (20 / (1 + s) ^ 2 + Cw * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2))) :=
    MeasureTheory.integral_const_mul (3 * (Real.pi / 2)) _
  rw [hconst]
  have hstep : 3 * (Real.pi / 2) * (∫ s in Set.Ioi (0 : ℝ),
        (20 / (1 + s) ^ 2 + Cw * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2)))
      ≤ 3 * (Real.pi / 2) * (20 + 3 * Cw) :=
    mul_le_mul_of_nonneg_left hsum_val (by positivity)
  have h1 : 3 * (Real.pi / 2) * 20 ≤ 120 := by linarith [Real.pi_le_four]
  have h2 : 3 * (Real.pi / 2) * (3 * Cw) ≤ 18 * Cw := by
    have h3 : 3 * (Real.pi / 2) * 3 ≤ 18 := by linarith [Real.pi_le_four]
    calc 3 * (Real.pi / 2) * (3 * Cw) = (3 * (Real.pi / 2) * 3) * Cw := by ring
      _ ≤ 18 * Cw := mul_le_mul_of_nonneg_right h3 hCw
  linarith [hstep, h1, h2, mul_add (3 * (Real.pi / 2)) 20 (3 * Cw)]

end Work.FTS_RegExport.RXT.Sys
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.SysAux.explicit_piece_bounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT.SysAux

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## §1  The one-variable factors

Every function below is a product of one of the radial factors

`ρ₁ = z²/(1+z)³`, `ρ₂ = z²/(1+z)⁴`, `a = 2z(1-z)/(1+z)³`, `b = 2z/(1+z)²`

with one of the angular factors `1`, `c2m θ = cos 2θ − sin²θ`, `sin²θ`; the pointwise bounds
on their one-variable iterates `ZIter j` / `TIter i` are the delegated lemmas
`piece_z_bounds_rho`, `piece_z_bounds_ab`, `piece_t_bounds`, and the separation identity
`mixed_sep` (in `PieceDefs`) turns a mixed jet of a separable product into a product of the
one-variable iterates. -/

private def rho1 (z : ℝ) : ℝ := z ^ 2 / (1 + z) ^ 3

private def rho2 (z : ℝ) : ℝ := z ^ 2 / (1 + z) ^ 4

private def aF (z : ℝ) : ℝ := 2 * z * (1 - z) / (1 + z) ^ 3

private def bF (z : ℝ) : ℝ := 2 * z / (1 + z) ^ 2

private def oneF (_ : ℝ) : ℝ := 1

private def c2mF (θ : ℝ) : ℝ := Work.Construction.c2m θ

private def sinsqF (θ : ℝ) : ℝ := Real.sin θ ^ 2

/-- The "leading" combination `E` of the forcing decomposition, as a function of `(z,θ)`. -/
private def Ef (μ β : ℝ) : ℝ → ℝ → ℝ := fun z θ =>
    ((1 - μ) + Work.Construction.c2m θ * (2 * β / (1 + z))) * (2 * z * (1 - z) / (1 + z) ^ 3)
  + (-(3 / (1 + z)) + β * (2 * z / (1 + z) ^ 2) / 2)
      * ((2 * β / 3) * Work.Construction.c2m θ * (2 * z / (1 + z) ^ 2))
  + ((1 + μ) - 2 / (1 + z) + β * Real.sin θ ^ 2 * (2 * z / (1 + z) ^ 2))
      * (2 * z / (1 + z) ^ 2)

/-! ## §2  The bounds on the one-variable iterates -/

private theorem ZIter_rho1_sq (j : ℕ) (hj : j ≤ 2) {z : ℝ} (hz : 0 < z) :
    |ZIter j rho1 z| ≤ 10 * (z ^ 2 / (1 + z) ^ 2) :=
  (piece_z_bounds_rho j hj z hz).1

private theorem ZIter_rho1_lin (j : ℕ) (hj : j ≤ 2) {z : ℝ} (hz : 0 < z) :
    |ZIter j rho1 z| ≤ 10 * (z / (1 + z) ^ 2) :=
  (piece_z_bounds_rho j hj z hz).2.1

private theorem ZIter_rho2_sq (j : ℕ) (hj : j ≤ 2) {z : ℝ} (hz : 0 < z) :
    |ZIter j rho2 z| ≤ 10 * (z ^ 2 / (1 + z) ^ 2) :=
  (piece_z_bounds_rho j hj z hz).2.2

private theorem ZIter_aF_le (j : ℕ) (hj : j ≤ 2) {z : ℝ} (hz : 0 < z) :
    |ZIter j aF z| ≤ 30 * (z / (1 + z) ^ 2) :=
  (piece_z_bounds_ab j hj z hz).1

private theorem ZIter_bF_le (j : ℕ) (hj : j ≤ 2) {z : ℝ} (hz : 0 < z) :
    |ZIter j bF z| ≤ 10 * (z / (1 + z) ^ 2) :=
  (piece_z_bounds_ab j hj z hz).2

private theorem TIter_oneF_le (i : ℕ) (hi : i ≤ 2) {θ : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ < Real.pi / 2) : |TIter i oneF θ| ≤ 1 :=
  (piece_t_bounds i hi θ hθ0 hθ1).1

private theorem TIter_c2mF_le (i : ℕ) (hi : i ≤ 2) {θ : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ < Real.pi / 2) : |TIter i c2mF θ| ≤ 12 :=
  (piece_t_bounds i hi θ hθ0 hθ1).2.1

private theorem TIter_sinsqF_le (i : ℕ) (hi : i ≤ 2) {θ : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ < Real.pi / 2) : |TIter i sinsqF θ| ≤ 4 :=
  (piece_t_bounds i hi θ hθ0 hθ1).2.2

/-! ## §3  Analyticity of the one-variable factors -/

private theorem contDiffOn_rho1 : ContDiffOn ℝ ⊤ rho1 (Set.Ioi 0) := by
  have hnum : ContDiffOn ℝ ⊤ (fun z : ℝ => z ^ 2) (Set.Ioi 0) := contDiffOn_id.pow 2
  have hden : ContDiffOn ℝ ⊤ (fun z : ℝ => (1 + z) ^ 3) (Set.Ioi 0) :=
    (contDiffOn_const.add contDiffOn_id).pow 3
  have h := hnum.div hden (fun z hz => by
    have hz' : (0 : ℝ) < z := hz
    positivity)
  have hfun : rho1 = (fun z : ℝ => z ^ 2) / (fun z : ℝ => (1 + z) ^ 3) := by
    funext z
    simp only [rho1, Pi.div_apply]
  rwa [hfun]

private theorem contDiffOn_rho2 : ContDiffOn ℝ ⊤ rho2 (Set.Ioi 0) := by
  have hnum : ContDiffOn ℝ ⊤ (fun z : ℝ => z ^ 2) (Set.Ioi 0) := contDiffOn_id.pow 2
  have hden : ContDiffOn ℝ ⊤ (fun z : ℝ => (1 + z) ^ 4) (Set.Ioi 0) :=
    (contDiffOn_const.add contDiffOn_id).pow 4
  have h := hnum.div hden (fun z hz => by
    have hz' : (0 : ℝ) < z := hz
    positivity)
  have hfun : rho2 = (fun z : ℝ => z ^ 2) / (fun z : ℝ => (1 + z) ^ 4) := by
    funext z
    simp only [rho2, Pi.div_apply]
  rwa [hfun]


private theorem contDiffOn_bF : ContDiffOn ℝ ⊤ bF (Set.Ioi 0) := by
  have hnum : ContDiffOn ℝ ⊤ (fun z : ℝ => 2 * z) (Set.Ioi 0) :=
    contDiffOn_const.mul contDiffOn_id
  have hden : ContDiffOn ℝ ⊤ (fun z : ℝ => (1 + z) ^ 2) (Set.Ioi 0) :=
    (contDiffOn_const.add contDiffOn_id).pow 2
  have h := hnum.div hden (fun z hz => by
    have hz' : (0 : ℝ) < z := hz
    positivity)
  have hfun : bF = (fun z : ℝ => 2 * z) / (fun z : ℝ => (1 + z) ^ 2) := by
    funext z
    simp only [bF, Pi.div_apply]
  rwa [hfun]

private theorem contDiffOn_c2mF : ContDiffOn ℝ ⊤ c2mF (Set.Ioo 0 (π / 2)) := by
  have h : ContDiffOn ℝ ⊤ (fun θ : ℝ => Real.cos (2 * θ) - Real.sin θ ^ 2)
      (Set.Ioo 0 (π / 2)) :=
    ((Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)).sub
      ((Real.contDiff_sin.comp contDiff_id).pow 2)).contDiffOn
  have hfun : c2mF = fun θ : ℝ => Real.cos (2 * θ) - Real.sin θ ^ 2 := by
    funext θ
    simp only [c2mF, Work.Construction.c2m]
  rwa [hfun]

private theorem contDiffOn_sinsqF : ContDiffOn ℝ ⊤ sinsqF (Set.Ioo 0 (π / 2)) := by
  have h : ContDiffOn ℝ ⊤ (fun θ : ℝ => Real.sin θ ^ 2) (Set.Ioo 0 (π / 2)) :=
    ((Real.contDiff_sin.comp contDiff_id).pow 2).contDiffOn
  have hfun : sinsqF = fun θ : ℝ => Real.sin θ ^ 2 := by
    funext θ
    simp only [sinsqF]
  rwa [hfun]

private theorem contDiffOn_oneF : ContDiffOn ℝ ⊤ oneF (Set.Ioo 0 (π / 2)) :=
  contDiffOn_const

/-! ## §4  The six pointwise bounds -/

/-- **Conjunct 1.**  The leading combination `E`. -/
private theorem piece1_bound {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    {μ β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    ∀ j i : ℕ, j + i ≤ 2 →
      |Work.Spaces.mixed j i (Ef μ β) z θ| ≤ 1120 * (1 + |μ|) * (z ^ 2 / (1 + z) ^ 2) := by
  intro j i hji
  have hj : j ≤ 2 := by omega
  have hi : i ≤ 2 := by omega
  have hθ : (z, θ) ∈ Q0 := ⟨hz, hθ0, hθ1⟩
  -- the separable closed form
  have hEqOn : Set.EqOn (Function.uncurry (Ef μ β))
      (Function.uncurry ((fun z θ => (4 * μ * rho1 z) * oneF θ)
        + (fun z θ => (β * (4 * β / 3 - 8) * rho2 z) * c2mF θ)
        + (fun z θ => (4 * β * rho2 z) * sinsqF θ))) Q0 := by
    intro p hp
    obtain ⟨z', θ'⟩ := p
    have hz' : (0 : ℝ) < z' := hp.1
    have hz1' : (1 : ℝ) + z' ≠ 0 := by positivity
    simp only [Function.uncurry, Ef, rho1, rho2, oneF, c2mF, sinsqF, Pi.add_apply]
    field_simp
    ring
  rw [mixed_congr_of_isOpen isOpen_Q0 hEqOn j i z θ hθ]
  -- additivity and separation
  have hcd1 : ContDiffOn ℝ ⊤
      (Function.uncurry (fun z θ => (4 * μ * rho1 z) * oneF θ)) Q0 :=
    contDiffOn_uncurry_sep ((contDiffOn_const (c := 4 * μ)).mul contDiffOn_rho1) contDiffOn_oneF
  have hcd2 : ContDiffOn ℝ ⊤
      (Function.uncurry (fun z θ => (β * (4 * β / 3 - 8) * rho2 z) * c2mF θ)) Q0 :=
    contDiffOn_uncurry_sep
      ((contDiffOn_const (c := β * (4 * β / 3 - 8))).mul contDiffOn_rho2) contDiffOn_c2mF
  have hcd3 : ContDiffOn ℝ ⊤
      (Function.uncurry (fun z θ => (4 * β * rho2 z) * sinsqF θ)) Q0 :=
    contDiffOn_uncurry_sep ((contDiffOn_const (c := 4 * β)).mul contDiffOn_rho2)
      contDiffOn_sinsqF
  have hcd12 : ContDiffOn ℝ ⊤
      (Function.uncurry ((fun z θ => (4 * μ * rho1 z) * oneF θ)
        + (fun z θ => (β * (4 * β / 3 - 8) * rho2 z) * c2mF θ))) Q0 :=
    hcd1.add hcd2
  rw [mixed_add isOpen_Q0 hcd12 hcd3 j i hθ, mixed_add isOpen_Q0 hcd1 hcd2 j i hθ]
  rw [mixed_sep j i (fun z => 4 * μ * rho1 z) oneF,
    mixed_sep j i (fun z => β * (4 * β / 3 - 8) * rho2 z) c2mF,
    mixed_sep j i (fun z => 4 * β * rho2 z) sinsqF]
  show |ZIter j (fun z => 4 * μ * rho1 z) z * TIter i oneF θ
      + ZIter j (fun z => β * (4 * β / 3 - 8) * rho2 z) z * TIter i c2mF θ
      + ZIter j (fun z => 4 * β * rho2 z) z * TIter i sinsqF θ|
      ≤ 1120 * (1 + |μ|) * (z ^ 2 / (1 + z) ^ 2)
  -- the three terms
  have hZ1 : |ZIter j (fun z => 4 * μ * rho1 z) z| ≤ 40 * |μ| * (z ^ 2 / (1 + z) ^ 2) := by
    have h1 : ZIter j (fun z => 4 * μ * rho1 z) z = 4 * μ * ZIter j rho1 z :=
      congrFun (ZIter_const_mul (4 * μ) rho1 j) z
    rw [h1, abs_mul]
    have h4 : |(4 : ℝ) * μ| = 4 * |μ| := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    rw [h4]
    calc 4 * |μ| * |ZIter j rho1 z| ≤ 4 * |μ| * (10 * (z ^ 2 / (1 + z) ^ 2)) :=
          mul_le_mul_of_nonneg_left (ZIter_rho1_sq j hj hz) (by positivity)
      _ = 40 * |μ| * (z ^ 2 / (1 + z) ^ 2) := by ring
  have hZ2 : |ZIter j (fun z => β * (4 * β / 3 - 8) * rho2 z) z|
      ≤ 80 * β * (z ^ 2 / (1 + z) ^ 2) := by
    have h1 : ZIter j (fun z => β * (4 * β / 3 - 8) * rho2 z) z
        = β * (4 * β / 3 - 8) * ZIter j rho2 z :=
      congrFun (ZIter_const_mul (β * (4 * β / 3 - 8)) rho2 j) z
    rw [h1, abs_mul]
    have hcoef : |β * (4 * β / 3 - 8)| ≤ 8 * β := by
      rw [abs_mul, abs_of_nonneg hβ0.le]
      have hb : |(4 : ℝ) * β / 3 - 8| ≤ 8 := by
        rw [abs_le]
        constructor <;> linarith
      calc β * |(4 : ℝ) * β / 3 - 8| ≤ β * 8 := mul_le_mul_of_nonneg_left hb hβ0.le
        _ = 8 * β := by ring
    calc |β * (4 * β / 3 - 8)| * |ZIter j rho2 z|
          ≤ (8 * β) * (10 * (z ^ 2 / (1 + z) ^ 2)) :=
          mul_le_mul hcoef (ZIter_rho2_sq j hj hz) (abs_nonneg _) (by positivity)
      _ = 80 * β * (z ^ 2 / (1 + z) ^ 2) := by ring
  have hZ3 : |ZIter j (fun z => 4 * β * rho2 z) z| ≤ 40 * β * (z ^ 2 / (1 + z) ^ 2) := by
    have h1 : ZIter j (fun z => 4 * β * rho2 z) z = 4 * β * ZIter j rho2 z :=
      congrFun (ZIter_const_mul (4 * β) rho2 j) z
    rw [h1, abs_mul]
    have h4 : |(4 : ℝ) * β| = 4 * β := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4), abs_of_nonneg hβ0.le]
    rw [h4]
    calc 4 * β * |ZIter j rho2 z| ≤ 4 * β * (10 * (z ^ 2 / (1 + z) ^ 2)) :=
          mul_le_mul_of_nonneg_left (ZIter_rho2_sq j hj hz) (by positivity)
      _ = 40 * β * (z ^ 2 / (1 + z) ^ 2) := by ring
  have hb1 : |ZIter j (fun z => 4 * μ * rho1 z) z * TIter i oneF θ|
      ≤ 40 * |μ| * (z ^ 2 / (1 + z) ^ 2) := by
    rw [abs_mul]
    calc |ZIter j (fun z => 4 * μ * rho1 z) z| * |TIter i oneF θ|
          ≤ (40 * |μ| * (z ^ 2 / (1 + z) ^ 2)) * 1 :=
          mul_le_mul hZ1 (TIter_oneF_le i hi hθ0 hθ1) (abs_nonneg _) (by positivity)
      _ = 40 * |μ| * (z ^ 2 / (1 + z) ^ 2) := by ring
  have hb2 : |ZIter j (fun z => β * (4 * β / 3 - 8) * rho2 z) z * TIter i c2mF θ|
      ≤ 960 * β * (z ^ 2 / (1 + z) ^ 2) := by
    rw [abs_mul]
    calc |ZIter j (fun z => β * (4 * β / 3 - 8) * rho2 z) z| * |TIter i c2mF θ|
          ≤ (80 * β * (z ^ 2 / (1 + z) ^ 2)) * 12 :=
          mul_le_mul hZ2 (TIter_c2mF_le i hi hθ0 hθ1) (abs_nonneg _) (by positivity)
      _ = 960 * β * (z ^ 2 / (1 + z) ^ 2) := by ring
  have hb3 : |ZIter j (fun z => 4 * β * rho2 z) z * TIter i sinsqF θ|
      ≤ 160 * β * (z ^ 2 / (1 + z) ^ 2) := by
    rw [abs_mul]
    calc |ZIter j (fun z => 4 * β * rho2 z) z| * |TIter i sinsqF θ|
          ≤ (40 * β * (z ^ 2 / (1 + z) ^ 2)) * 4 :=
          mul_le_mul hZ3 (TIter_sinsqF_le i hi hθ0 hθ1) (abs_nonneg _) (by positivity)
      _ = 160 * β * (z ^ 2 / (1 + z) ^ 2) := by ring
  have hW : (0 : ℝ) ≤ z ^ 2 / (1 + z) ^ 2 := by positivity
  calc |ZIter j (fun z => 4 * μ * rho1 z) z * TIter i oneF θ
        + ZIter j (fun z => β * (4 * β / 3 - 8) * rho2 z) z * TIter i c2mF θ
        + ZIter j (fun z => 4 * β * rho2 z) z * TIter i sinsqF θ|
      ≤ |ZIter j (fun z => 4 * μ * rho1 z) z * TIter i oneF θ|
        + |ZIter j (fun z => β * (4 * β / 3 - 8) * rho2 z) z * TIter i c2mF θ|
        + |ZIter j (fun z => 4 * β * rho2 z) z * TIter i sinsqF θ| := by
        have h' := abs_add_le
          (ZIter j (fun z => 4 * μ * rho1 z) z * TIter i oneF θ
            + ZIter j (fun z => β * (4 * β / 3 - 8) * rho2 z) z * TIter i c2mF θ)
          (ZIter j (fun z => 4 * β * rho2 z) z * TIter i sinsqF θ)
        have h'' := abs_add_le (ZIter j (fun z => 4 * μ * rho1 z) z * TIter i oneF θ)
          (ZIter j (fun z => β * (4 * β / 3 - 8) * rho2 z) z * TIter i c2mF θ)
        linarith
    _ ≤ 40 * |μ| * (z ^ 2 / (1 + z) ^ 2) + 960 * β * (z ^ 2 / (1 + z) ^ 2)
        + 160 * β * (z ^ 2 / (1 + z) ^ 2) := add_le_add (add_le_add hb1 hb2) hb3
    _ ≤ 1120 * (1 + |μ|) * (z ^ 2 / (1 + z) ^ 2) := by
        have hA : (0 : ℝ) ≤ |μ| * (z ^ 2 / (1 + z) ^ 2) := mul_nonneg (abs_nonneg μ) hW
        have hB : (0 : ℝ) ≤ (1 - β) * (z ^ 2 / (1 + z) ^ 2) :=
          mul_nonneg (by linarith) hW
        nlinarith [hA, hB, hW]

/-- **Conjunct 2.**  The factor `a(z) = 2z(1-z)/(1+z)³`. -/
private theorem piece2_bound {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    ∀ j i : ℕ, j + i ≤ 2 →
      |Work.Spaces.mixed j i (fun z _ : ℝ => 2 * z * (1 - z) / (1 + z) ^ 3) z θ|
        ≤ 1120 * (z / (1 + z) ^ 2) := by
  intro j i hji
  have hj : j ≤ 2 := by omega
  have hi : i ≤ 2 := by omega
  have hθ : (z, θ) ∈ Q0 := ⟨hz, hθ0, hθ1⟩
  have hEqOn : Set.EqOn (Function.uncurry (fun z _ : ℝ => 2 * z * (1 - z) / (1 + z) ^ 3))
      (Function.uncurry (fun z θ => aF z * oneF θ)) Q0 := by
    intro p hp
    obtain ⟨z', θ'⟩ := p
    simp only [Function.uncurry, aF, oneF]
    ring
  rw [mixed_congr_of_isOpen isOpen_Q0 hEqOn j i z θ hθ]
  rw [mixed_sep j i aF oneF]
  show |ZIter j aF z * TIter i oneF θ| ≤ 1120 * (z / (1 + z) ^ 2)
  rw [abs_mul]
  calc |ZIter j aF z| * |TIter i oneF θ| ≤ (30 * (z / (1 + z) ^ 2)) * 1 :=
        mul_le_mul (ZIter_aF_le j hj hz) (TIter_oneF_le i hi hθ0 hθ1) (abs_nonneg _)
          (by positivity)
    _ ≤ 1120 * (z / (1 + z) ^ 2) := by
        have hW : (0 : ℝ) ≤ z / (1 + z) ^ 2 := by positivity
        nlinarith [hW]

/-- **Conjunct 3.**  The factor `b(z) = 2z/(1+z)²`. -/
private theorem piece3_bound {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    ∀ j i : ℕ, j + i ≤ 2 →
      |Work.Spaces.mixed j i (fun z _ : ℝ => 2 * z / (1 + z) ^ 2) z θ|
        ≤ 1120 * (z / (1 + z) ^ 2) := by
  intro j i hji
  have hj : j ≤ 2 := by omega
  have hi : i ≤ 2 := by omega
  have hθ : (z, θ) ∈ Q0 := ⟨hz, hθ0, hθ1⟩
  have hEqOn : Set.EqOn (Function.uncurry (fun z _ : ℝ => 2 * z / (1 + z) ^ 2))
      (Function.uncurry (fun z θ => bF z * oneF θ)) Q0 := by
    intro p hp
    obtain ⟨z', θ'⟩ := p
    simp only [Function.uncurry, bF, oneF]
    ring
  rw [mixed_congr_of_isOpen isOpen_Q0 hEqOn j i z θ hθ]
  rw [mixed_sep j i bF oneF]
  show |ZIter j bF z * TIter i oneF θ| ≤ 1120 * (z / (1 + z) ^ 2)
  rw [abs_mul]
  calc |ZIter j bF z| * |TIter i oneF θ| ≤ (10 * (z / (1 + z) ^ 2)) * 1 :=
        mul_le_mul (ZIter_bF_le j hj hz) (TIter_oneF_le i hi hθ0 hθ1) (abs_nonneg _)
          (by positivity)
    _ ≤ 1120 * (z / (1 + z) ^ 2) := by
        have hW : (0 : ℝ) ≤ z / (1 + z) ^ 2 := by positivity
        nlinarith [hW]

/-- **Conjunct 4.**  The factor `(2β/3)·c2m θ·b(z)`. -/
private theorem piece4_bound {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    {β : ℝ} (hβ0 : 0 < β) :
    ∀ j i : ℕ, j + i ≤ 2 →
      |Work.Spaces.mixed j i
          (fun z θ => (2 * β / 3) * Work.Construction.c2m θ * (2 * z / (1 + z) ^ 2)) z θ|
        ≤ 1120 * β * (z / (1 + z) ^ 2) := by
  intro j i hji
  have hj : j ≤ 2 := by omega
  have hi : i ≤ 2 := by omega
  have hθ : (z, θ) ∈ Q0 := ⟨hz, hθ0, hθ1⟩
  have hEqOn : Set.EqOn
      (Function.uncurry (fun z θ => (2 * β / 3) * Work.Construction.c2m θ * (2 * z / (1 + z) ^ 2)))
      (Function.uncurry (fun z θ => ((2 * β / 3) * bF z) * c2mF θ)) Q0 := by
    intro p hp
    obtain ⟨z', θ'⟩ := p
    simp only [Function.uncurry, bF, c2mF]
    ring
  rw [mixed_congr_of_isOpen isOpen_Q0 hEqOn j i z θ hθ]
  rw [mixed_sep j i (fun z => (2 * β / 3) * bF z) c2mF]
  show |ZIter j (fun z => (2 * β / 3) * bF z) z * TIter i c2mF θ|
      ≤ 1120 * β * (z / (1 + z) ^ 2)
  rw [abs_mul]
  have hZ : |ZIter j (fun z => (2 * β / 3) * bF z) z| ≤ 80 * β * (z / (1 + z) ^ 2) := by
    have h1 : ZIter j (fun z => (2 * β / 3) * bF z) z = (2 * β / 3) * ZIter j bF z :=
      congrFun (ZIter_const_mul (2 * β / 3) bF j) z
    rw [h1, abs_mul]
    have hc : |(2 * β / 3 : ℝ)| = 2 * β / 3 :=
      abs_of_nonneg (by positivity)
    rw [hc]
    calc 2 * β / 3 * |ZIter j bF z| ≤ 2 * β / 3 * (10 * (z / (1 + z) ^ 2)) :=
          mul_le_mul_of_nonneg_left (ZIter_bF_le j hj hz) (by positivity)
      _ = 20 * β / 3 * (z / (1 + z) ^ 2) := by ring
      _ ≤ 80 * β * (z / (1 + z) ^ 2) := by
          have hW : (0 : ℝ) ≤ z / (1 + z) ^ 2 := by positivity
          nlinarith [hW, hβ0]
  calc |ZIter j (fun z => (2 * β / 3) * bF z) z| * |TIter i c2mF θ|
        ≤ (80 * β * (z / (1 + z) ^ 2)) * 12 :=
        mul_le_mul hZ (TIter_c2mF_le i hi hθ0 hθ1) (abs_nonneg _) (by positivity)
    _ = 960 * β * (z / (1 + z) ^ 2) := by ring
    _ ≤ 1120 * β * (z / (1 + z) ^ 2) := by
        have hW : (0 : ℝ) ≤ z / (1 + z) ^ 2 := by positivity
        nlinarith [hW, hβ0]

/-- **Conjunct 5.**  The factor `c2m θ·(a-b)(z) - b(z)/β`. -/
private theorem piece5_bound {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    {β : ℝ} (hβ0 : 0 < β) :
    ∀ j i : ℕ, j + i ≤ 2 →
      |Work.Spaces.mixed j i
          (fun z θ => Work.Construction.c2m θ
              * (2 * z * (1 - z) / (1 + z) ^ 3 - 2 * z / (1 + z) ^ 2)
            - (1 / β) * (2 * z / (1 + z) ^ 2)) z θ|
        ≤ 1120 * (1 + 1 / β) * (z / (1 + z) ^ 2) := by
  intro j i hji
  have hj : j ≤ 2 := by omega
  have hi : i ≤ 2 := by omega
  have hθ : (z, θ) ∈ Q0 := ⟨hz, hθ0, hθ1⟩
  have hEqOn : Set.EqOn
      (Function.uncurry (fun z θ => Work.Construction.c2m θ
              * (2 * z * (1 - z) / (1 + z) ^ 3 - 2 * z / (1 + z) ^ 2)
            - (1 / β) * (2 * z / (1 + z) ^ 2)))
      (Function.uncurry ((fun z θ => (-4 * rho1 z) * c2mF θ)
        + (fun z θ => (-(1 / β) * bF z) * oneF θ))) Q0 := by
    intro p hp
    obtain ⟨z', θ'⟩ := p
    have hz' : (0 : ℝ) < z' := hp.1
    have hz1' : (1 : ℝ) + z' ≠ 0 := by positivity
    simp only [Function.uncurry, rho1, bF, c2mF, oneF, Pi.add_apply]
    field_simp
    ring
  rw [mixed_congr_of_isOpen isOpen_Q0 hEqOn j i z θ hθ]
  have hcd1 : ContDiffOn ℝ ⊤
      (Function.uncurry (fun z θ => (-4 * rho1 z) * c2mF θ)) Q0 :=
    contDiffOn_uncurry_sep
      ((contDiffOn_const (c := (-4 : ℝ))).mul contDiffOn_rho1) contDiffOn_c2mF
  have hcd2 : ContDiffOn ℝ ⊤
      (Function.uncurry (fun z θ => (-(1 / β) * bF z) * oneF θ)) Q0 :=
    contDiffOn_uncurry_sep
      ((contDiffOn_const (c := -(1 / β))).mul contDiffOn_bF) contDiffOn_oneF
  rw [mixed_add isOpen_Q0 hcd1 hcd2 j i hθ]
  rw [mixed_sep j i (fun z => -4 * rho1 z) c2mF,
    mixed_sep j i (fun z => -(1 / β) * bF z) oneF]
  show |ZIter j (fun z => -4 * rho1 z) z * TIter i c2mF θ
      + ZIter j (fun z => -(1 / β) * bF z) z * TIter i oneF θ|
      ≤ 1120 * (1 + 1 / β) * (z / (1 + z) ^ 2)
  have hZ1 : |ZIter j (fun z => -4 * rho1 z) z| ≤ 40 * (z / (1 + z) ^ 2) := by
    have h1 : ZIter j (fun z => -4 * rho1 z) z = -4 * ZIter j rho1 z :=
      congrFun (ZIter_const_mul (-4) rho1 j) z
    rw [h1, abs_mul]
    have h4 : |(-4 : ℝ)| = 4 := by norm_num
    rw [h4]
    calc 4 * |ZIter j rho1 z| ≤ 4 * (10 * (z / (1 + z) ^ 2)) :=
          mul_le_mul_of_nonneg_left (ZIter_rho1_lin j hj hz) (by norm_num)
      _ = 40 * (z / (1 + z) ^ 2) := by ring
  have hZ2 : |ZIter j (fun z => -(1 / β) * bF z) z| ≤ (1 / β) * 10 * (z / (1 + z) ^ 2) := by
    have h1 : ZIter j (fun z => -(1 / β) * bF z) z = -(1 / β) * ZIter j bF z :=
      congrFun (ZIter_const_mul (-(1 / β)) bF j) z
    rw [h1, abs_mul]
    have hc : |(-(1 / β) : ℝ)| = 1 / β := by
      rw [abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / β)]
    rw [hc]
    calc 1 / β * |ZIter j bF z| ≤ 1 / β * (10 * (z / (1 + z) ^ 2)) :=
          mul_le_mul_of_nonneg_left (ZIter_bF_le j hj hz) (by positivity)
      _ = (1 / β) * 10 * (z / (1 + z) ^ 2) := by ring
  have hb1 : |ZIter j (fun z => -4 * rho1 z) z * TIter i c2mF θ| ≤ 480 * (z / (1 + z) ^ 2) := by
    rw [abs_mul]
    calc |ZIter j (fun z => -4 * rho1 z) z| * |TIter i c2mF θ|
          ≤ (40 * (z / (1 + z) ^ 2)) * 12 :=
          mul_le_mul hZ1 (TIter_c2mF_le i hi hθ0 hθ1) (abs_nonneg _) (by positivity)
      _ = 480 * (z / (1 + z) ^ 2) := by ring
  have hb2 : |ZIter j (fun z => -(1 / β) * bF z) z * TIter i oneF θ|
      ≤ (1 / β) * 10 * (z / (1 + z) ^ 2) := by
    rw [abs_mul]
    calc |ZIter j (fun z => -(1 / β) * bF z) z| * |TIter i oneF θ|
          ≤ ((1 / β) * 10 * (z / (1 + z) ^ 2)) * 1 :=
          mul_le_mul hZ2 (TIter_oneF_le i hi hθ0 hθ1) (abs_nonneg _) (by positivity)
      _ = (1 / β) * 10 * (z / (1 + z) ^ 2) := by ring
  have hW : (0 : ℝ) ≤ z / (1 + z) ^ 2 := by positivity
  calc |ZIter j (fun z => -4 * rho1 z) z * TIter i c2mF θ
        + ZIter j (fun z => -(1 / β) * bF z) z * TIter i oneF θ|
      ≤ |ZIter j (fun z => -4 * rho1 z) z * TIter i c2mF θ|
        + |ZIter j (fun z => -(1 / β) * bF z) z * TIter i oneF θ| := abs_add_le _ _
    _ ≤ 480 * (z / (1 + z) ^ 2) + (1 / β) * 10 * (z / (1 + z) ^ 2) := add_le_add hb1 hb2
    _ ≤ 1120 * (1 + 1 / β) * (z / (1 + z) ^ 2) := by
        have hB : (0 : ℝ) ≤ (1 / β) * (z / (1 + z) ^ 2) := by positivity
        nlinarith [hB, hW]

/-- **Conjunct 6.**  The factor `(β/3)·c2m θ·b(z) + sin²θ·b(z)`. -/
private theorem piece6_bound {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    {β : ℝ} (hβ0 : 0 < β) :
    ∀ j i : ℕ, j + i ≤ 2 →
      |Work.Spaces.mixed j i
          (fun z θ => ((2 * β / 3) * Work.Construction.c2m θ * (2 * z / (1 + z) ^ 2)) / 2
            + Real.sin θ ^ 2 * (2 * z / (1 + z) ^ 2)) z θ|
        ≤ 1120 * (1 + β) * (z / (1 + z) ^ 2) := by
  intro j i hji
  have hj : j ≤ 2 := by omega
  have hi : i ≤ 2 := by omega
  have hθ : (z, θ) ∈ Q0 := ⟨hz, hθ0, hθ1⟩
  have hEqOn : Set.EqOn
      (Function.uncurry (fun z θ => ((2 * β / 3) * Work.Construction.c2m θ
            * (2 * z / (1 + z) ^ 2)) / 2 + Real.sin θ ^ 2 * (2 * z / (1 + z) ^ 2)))
      (Function.uncurry ((fun z θ => ((β / 3) * bF z) * c2mF θ)
        + (fun z θ => bF z * sinsqF θ))) Q0 := by
    intro p hp
    obtain ⟨z', θ'⟩ := p
    simp only [Function.uncurry, bF, c2mF, sinsqF, Pi.add_apply]
    ring
  rw [mixed_congr_of_isOpen isOpen_Q0 hEqOn j i z θ hθ]
  have hcd1 : ContDiffOn ℝ ⊤
      (Function.uncurry (fun z θ => ((β / 3) * bF z) * c2mF θ)) Q0 :=
    contDiffOn_uncurry_sep
      ((contDiffOn_const (c := β / 3)).mul contDiffOn_bF) contDiffOn_c2mF
  have hcd2 : ContDiffOn ℝ ⊤ (Function.uncurry (fun z θ => bF z * sinsqF θ)) Q0 :=
    contDiffOn_uncurry_sep contDiffOn_bF contDiffOn_sinsqF
  rw [mixed_add isOpen_Q0 hcd1 hcd2 j i hθ]
  rw [mixed_sep j i (fun z => (β / 3) * bF z) c2mF, mixed_sep j i bF sinsqF]
  show |ZIter j (fun z => (β / 3) * bF z) z * TIter i c2mF θ
      + ZIter j bF z * TIter i sinsqF θ| ≤ 1120 * (1 + β) * (z / (1 + z) ^ 2)
  have hZ1 : |ZIter j (fun z => (β / 3) * bF z) z| ≤ (β / 3) * 10 * (z / (1 + z) ^ 2) := by
    have h1 : ZIter j (fun z => (β / 3) * bF z) z = (β / 3) * ZIter j bF z :=
      congrFun (ZIter_const_mul (β / 3) bF j) z
    rw [h1, abs_mul]
    have hc : |(β / 3 : ℝ)| = β / 3 := abs_of_nonneg (by positivity)
    rw [hc]
    calc β / 3 * |ZIter j bF z| ≤ β / 3 * (10 * (z / (1 + z) ^ 2)) :=
          mul_le_mul_of_nonneg_left (ZIter_bF_le j hj hz) (by positivity)
      _ = (β / 3) * 10 * (z / (1 + z) ^ 2) := by ring
  have hb1 : |ZIter j (fun z => (β / 3) * bF z) z * TIter i c2mF θ|
      ≤ 40 * β * (z / (1 + z) ^ 2) := by
    rw [abs_mul]
    calc |ZIter j (fun z => (β / 3) * bF z) z| * |TIter i c2mF θ|
          ≤ ((β / 3) * 10 * (z / (1 + z) ^ 2)) * 12 :=
          mul_le_mul hZ1 (TIter_c2mF_le i hi hθ0 hθ1) (abs_nonneg _) (by positivity)
      _ = 40 * β * (z / (1 + z) ^ 2) := by ring
  have hb2 : |ZIter j bF z * TIter i sinsqF θ| ≤ 40 * (z / (1 + z) ^ 2) := by
    rw [abs_mul]
    calc |ZIter j bF z| * |TIter i sinsqF θ| ≤ (10 * (z / (1 + z) ^ 2)) * 4 :=
          mul_le_mul (ZIter_bF_le j hj hz) (TIter_sinsqF_le i hi hθ0 hθ1) (abs_nonneg _)
            (by positivity)
      _ = 40 * (z / (1 + z) ^ 2) := by ring
  have hW : (0 : ℝ) ≤ z / (1 + z) ^ 2 := by positivity
  calc |ZIter j (fun z => (β / 3) * bF z) z * TIter i c2mF θ
        + ZIter j bF z * TIter i sinsqF θ|
      ≤ |ZIter j (fun z => (β / 3) * bF z) z * TIter i c2mF θ|
        + |ZIter j bF z * TIter i sinsqF θ| := abs_add_le _ _
    _ ≤ 40 * β * (z / (1 + z) ^ 2) + 40 * (z / (1 + z) ^ 2) := add_le_add hb1 hb2
    _ ≤ 1120 * (1 + β) * (z / (1 + z) ^ 2) := by nlinarith [hW, hβ0]

/-! ## §5  The theorem -/

/-- Pointwise `mixed`-jet bounds for the explicit rational/angular pieces of the forcing
decomposition: the "leading" combination `E` (which cancels at order `z`), and the explicit
factors `A1`, `A3`, `B1`, `α₁`, `α₂` against which the radial transforms `L₁₂(g)`, `𝔽K(g)` and
the perturbation slots are paired.  All bounds are for `z > 0`, `0 < θ < π/2`, `j + i ≤ 2`. -/
theorem explicit_piece_bounds :
    ∃ C : ℝ, 0 < C ∧ ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → ∀ μ β : ℝ, 0 < β → β ≤ 1 →
      (∀ j i : ℕ, j + i ≤ 2 →
        |Work.Spaces.mixed j i (fun z θ => ((1 - μ) + Work.Construction.c2m θ * (2 * β / (1 + z)))
              * (2 * z * (1 - z) / (1 + z) ^ 3)
            + (-(3 / (1 + z)) + β * (2 * z / (1 + z) ^ 2) / 2)
              * ((2 * β / 3) * Work.Construction.c2m θ * (2 * z / (1 + z) ^ 2))
            + ((1 + μ) - 2 / (1 + z) + β * Real.sin θ ^ 2 * (2 * z / (1 + z) ^ 2))
              * (2 * z / (1 + z) ^ 2)) z θ| ≤ C * (1 + |μ|) * (z ^ 2 / (1 + z) ^ 2)) ∧
      (∀ j i : ℕ, j + i ≤ 2 →
        |Work.Spaces.mixed j i (fun z _ => 2 * z * (1 - z) / (1 + z) ^ 3) z θ|
          ≤ C * (z / (1 + z) ^ 2)) ∧
      (∀ j i : ℕ, j + i ≤ 2 →
        |Work.Spaces.mixed j i (fun z _ => 2 * z / (1 + z) ^ 2) z θ| ≤ C * (z / (1 + z) ^ 2)) ∧
      (∀ j i : ℕ, j + i ≤ 2 →
        |Work.Spaces.mixed j i (fun z θ => (2 * β / 3) * Work.Construction.c2m θ
            * (2 * z / (1 + z) ^ 2)) z θ| ≤ C * β * (z / (1 + z) ^ 2)) ∧
      (∀ j i : ℕ, j + i ≤ 2 →
        |Work.Spaces.mixed j i (fun z θ => Work.Construction.c2m θ
              * (2 * z * (1 - z) / (1 + z) ^ 3 - 2 * z / (1 + z) ^ 2)
            - (1 / β) * (2 * z / (1 + z) ^ 2)) z θ| ≤ C * (1 + 1 / β) * (z / (1 + z) ^ 2)) ∧
      (∀ j i : ℕ, j + i ≤ 2 →
        |Work.Spaces.mixed j i (fun z θ => ((2 * β / 3) * Work.Construction.c2m θ
              * (2 * z / (1 + z) ^ 2)) / 2
            + Real.sin θ ^ 2 * (2 * z / (1 + z) ^ 2)) z θ| ≤ C * (1 + β) * (z / (1 + z) ^ 2)) := by
  refine ⟨1120, by norm_num, ?_⟩
  intro z θ hz hθ0 hθ1 μ β hβ0 hβ1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j i hji
    show |Work.Spaces.mixed j i (Ef μ β) z θ|
        ≤ 1120 * (1 + |μ|) * (z ^ 2 / (1 + z) ^ 2)
    exact piece1_bound hz hθ0 hθ1 hβ0 hβ1 j i hji
  · intro j i hji
    exact piece2_bound hz hθ0 hθ1 j i hji
  · intro j i hji
    exact piece3_bound hz hθ0 hθ1 j i hji
  · intro j i hji
    exact piece4_bound hz hθ0 hθ1 hβ0 j i hji
  · intro j i hji
    exact piece5_bound hz hθ0 hθ1 hβ0 j i hji
  · intro j i hji
    exact piece6_bound hz hθ0 hθ1 hβ0 j i hji

end Work.FTS_RegExport.RXT.SysAux
end
end
