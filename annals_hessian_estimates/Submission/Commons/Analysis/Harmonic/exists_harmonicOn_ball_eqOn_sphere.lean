import Mathlib
import Submission.Commons.Analysis.Calculus.Laplacian.laplacian_mul
import Submission.Commons.Analysis.Calculus.Laplacian.laplacian_comp_norm
import Submission.Commons.Analysis.Calculus.Laplacian.laplacian_norm_sub_sq
import Submission.Commons.Analysis.InnerProductSpace.fderiv_comp_norm_eq
import Submission.Commons.Analysis.InnerProductSpace.fderiv_norm_single
import Submission.Commons.Analysis.Real.deriv_inv_pow
import Submission.Commons.Analysis.Real.deriv_deriv_inv_pow
import Submission.Commons.Analysis.Calculus.Laplacian.le_of_le_on_sphere_of_laplacian_nonneg_nontrivial
import Submission.Commons.Analysis.Measure.Integral.integral_toSphere_comp_linearIsometryEquiv
import Submission.Commons.Analysis.Measure.Integral.poissonIntegral_const_eq_one
import Submission.Commons.Analysis.Measure.Integral.poissonIntegral_tendsto_boundary
import Submission.Commons.Analysis.Calculus.Laplacian.contDiffOn_two_poissonIntegral

open MeasureTheory Metric Set Filter Function
open scoped Topology RealInnerProductSpace InnerProductSpace BigOperators ENNReal

noncomputable section

namespace Commons.Analysis.Harmonic

open Commons.Analysis.Calculus.Laplacian Commons.Analysis.InnerProductSpace

/-! ## Calculus preliminaries for the Poisson kernel -/

section Calc

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `fderiv` of `y ↦ R^2 - ‖y - c‖^2`. -/
theorem hasFDerivAt_quad (c x : E) (R : ℝ) :
    HasFDerivAt (fun y : E => R^2 - ‖y - c‖^2) ((-2:ℝ) • innerSL ℝ (x - c)) x := by
  have hshift : HasFDerivAt (fun y : E => y - c) (ContinuousLinearMap.id ℝ E) x :=
    (hasFDerivAt_id x).sub_const c
  have hsq : HasFDerivAt (fun z : E => ‖z‖^2) (2 • innerSL ℝ (x - c)) (x - c) :=
    (hasStrictFDerivAt_norm_sq (x - c)).hasFDerivAt
  have hcomp : HasFDerivAt ((fun z : E => ‖z‖^2) ∘ (fun y : E => y - c))
      ((2 • innerSL ℝ (x - c)).comp (ContinuousLinearMap.id ℝ E)) x := hsq.comp x hshift
  rw [ContinuousLinearMap.comp_id] at hcomp
  have hcomp' : HasFDerivAt (fun y : E => ‖y - c‖^2) (2 • innerSL ℝ (x - c)) x := hcomp
  have h2 : HasFDerivAt ((fun _ : E => (R^2:ℝ)) - (fun y : E => ‖y - c‖^2))
      ((0 : E →L[ℝ] ℝ) - (2 • innerSL ℝ (x - c))) x :=
    (hasFDerivAt_const (x := x) (c := (R^2:ℝ))).sub hcomp'
  have hsmul : (2 : ℕ) • (innerSL ℝ (x - c)) = (2:ℝ) • innerSL ℝ (x - c) :=
    (Nat.cast_smul_eq_nsmul ℝ 2 _).symm
  have hderiv : ((0 : E →L[ℝ] ℝ) - (2 • innerSL ℝ (x - c))) = (-2:ℝ) • innerSL ℝ (x - c) := by
    rw [zero_sub, hsmul, neg_smul]
  rw [hderiv] at h2
  have hfun : ((fun _ : E => (R^2:ℝ)) - (fun y : E => ‖y - c‖^2)) = fun y : E => R^2 - ‖y - c‖^2 := rfl
  rwa [hfun] at h2

/-- `fderiv` of `z ↦ (‖z‖^n)⁻¹` at a nonzero point. -/
theorem fderiv_inv_pow_norm {n : ℕ} {z : E} (hz : z ≠ 0) :
    fderiv ℝ (fun z : E => (‖z‖ ^ n)⁻¹) z
      = (-(n:ℝ) * (‖z‖^(n+2))⁻¹) • innerSL ℝ z := by
  have hzpow : (‖z‖ ^ n) ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hz)
  have hφdiff : DifferentiableAt ℝ (fun r : ℝ => (r^n)⁻¹) ‖z‖ :=
    (differentiableAt_id (x := (‖z‖:ℝ))).pow n |>.inv hzpow
  ext v
  rw [fderiv_comp_norm_eq (φ := fun r : ℝ => (r^n)⁻¹) hz hφdiff v, Commons.Analysis.Real.deriv_inv_pow]
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply]
  have hpow : (‖z‖ ^ (n+1)) * ‖z‖ = ‖z‖ ^ (n+2) := by
    rw [mul_comm, ← pow_succ']
  have hkey : (‖z‖ ^ (n+1))⁻¹ * ‖z‖⁻¹ = (‖z‖ ^ (n+2))⁻¹ := by
    rw [← mul_inv, hpow]
  rw [div_eq_mul_inv, ← hkey]
  try ring

/-- `fderiv` of `y ↦ (‖y - ξ‖^n)⁻¹`. -/
theorem hasFDerivAt_invPow {n : ℕ} {ξ x : E} (hx : x ≠ ξ) :
    HasFDerivAt (fun y : E => (‖y - ξ‖ ^ n)⁻¹)
      ((-(n:ℝ) * (‖x-ξ‖^(n+2))⁻¹) • innerSL ℝ (x-ξ)) x := by
  have hshift : HasFDerivAt (fun y : E => y - ξ) (ContinuousLinearMap.id ℝ E) x :=
    (hasFDerivAt_id x).sub_const ξ
  have hz : x - ξ ≠ 0 := sub_ne_zero.mpr hx
  have hzpow : (‖x - ξ‖ ^ n) ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hz)
  have hdiffnorm : DifferentiableAt ℝ (fun z : E => ‖z‖) (x - ξ) :=
    (hasFDerivAt_norm_ne_zero hz).differentiableAt
  have hdiff : DifferentiableAt ℝ (fun z : E => (‖z‖ ^ n)⁻¹) (x - ξ) :=
    (hdiffnorm.pow n).inv hzpow
  have hbase : HasFDerivAt (fun z : E => (‖z‖ ^ n)⁻¹)
      (fderiv ℝ (fun z : E => (‖z‖ ^ n)⁻¹) (x - ξ)) (x - ξ) := hdiff.hasFDerivAt
  have hcomp := hbase.comp x hshift
  rw [ContinuousLinearMap.comp_id] at hcomp
  have hfun : ((fun z : E => (‖z‖ ^ n)⁻¹) ∘ (fun y : E => y - ξ)) = fun y : E => (‖y - ξ‖ ^ n)⁻¹ := rfl
  rw [hfun] at hcomp
  rwa [fderiv_inv_pow_norm hz] at hcomp

/-- `fderiv` of the base kernel `y ↦ (R^2 - ‖y - c‖^2) * (‖y - ξ‖^n)⁻¹`. -/
def baseD1 {n : ℕ} (c ξ : E) (R : ℝ) (x : E) : E →L[ℝ] ℝ :=
  ((R^2 - ‖x - c‖^2) * (-(n:ℝ) * (‖x - ξ‖^(n+2))⁻¹)) • innerSL ℝ (x-ξ)
    + ((‖x - ξ‖^n)⁻¹ * (-2)) • innerSL ℝ (x-c)

theorem hasFDerivAt_base {n : ℕ} {c ξ x : E} {R : ℝ} (hx : x ≠ ξ) :
    HasFDerivAt (fun y : E => (R^2 - ‖y-c‖^2) * (‖y-ξ‖^n)⁻¹) (baseD1 (n := n) c ξ R x) x := by
  have hmul := (hasFDerivAt_quad c x R).mul (hasFDerivAt_invPow (n := n) hx)
  have : ((R^2 - ‖x-c‖^2) • ((-(n:ℝ) * (‖x-ξ‖^(n+2))⁻¹) • innerSL ℝ (x-ξ))
      + (‖x-ξ‖^n)⁻¹ • ((-2:ℝ) • innerSL ℝ (x-c))) = baseD1 (n := n) c ξ R x := by
    simp [baseD1, smul_add, smul_smul, mul_comm, mul_left_comm, mul_assoc]
  rw [this] at hmul
  exact hmul

/-- Translation invariance of the Laplacian. -/
theorem laplacian_comp_sub {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (u : E → ℝ) (ξ x : E) :
    Laplacian.laplacian (fun y => u (y - ξ)) x = Laplacian.laplacian u (x - ξ) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis (fun y => u (y - ξ))
      (stdOrthonormalBasis ℝ E),
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis u (stdOrthonormalBasis ℝ E)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedFDeriv_comp_sub]

end Calc

section KernelCalc

/-- `Laplacian` of `y ↦ R^2 - ‖y - c‖^2` in dimension `n`. -/
theorem laplacian_quad {n : ℕ} (c x : EuclideanSpace ℝ (Fin n)) (R : ℝ) :
    Laplacian.laplacian (fun y : EuclideanSpace ℝ (Fin n) => R^2 - ‖y - c‖^2) x
      = -2 * (n:ℝ) := by
  have h1 : ContDiffAt ℝ 2 (fun _ : EuclideanSpace ℝ (Fin n) => (R^2:ℝ)) x := contDiffAt_const
  have h2 : ContDiffAt ℝ 2 (fun y : EuclideanSpace ℝ (Fin n) => ‖y - c‖^2) x :=
    ContDiffAt.norm_sq (𝕜 := ℝ) (contDiffAt_id.sub contDiffAt_const)
  have hsub := (h1.laplacian_sub_nhds h2).self_of_nhds
  rw [show (fun y : EuclideanSpace ℝ (Fin n) => R^2 - ‖y - c‖^2)
      = (fun _ => (R^2:ℝ)) - (fun y => ‖y - c‖^2) from rfl, hsub]
  simp [laplacian_norm_sub_sq, finrank_euclideanSpace_fin]

/-- `Laplacian` of the translated inverse power of the norm. -/
theorem laplacian_invPow {n : ℕ} {ξ x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ ξ) :
    Laplacian.laplacian (fun y : EuclideanSpace ℝ (Fin n) => (‖y - ξ‖ ^ n)⁻¹) x
      = (n:ℝ) * (n + 2 - (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ))
          * (‖x - ξ‖^(n+2))⁻¹ := by
  have hz : x - ξ ≠ 0 := sub_ne_zero.mpr hx
  have hzpow : (‖x - ξ‖ ^ n) ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hz)
  have hφdiff : ContDiffAt ℝ 2 (fun r : ℝ => (r^n)⁻¹) ‖x - ξ‖ := by
    refine ContDiffAt.inv ?_ hzpow
    exact contDiffAt_id.pow n
  have hfun : (fun y : EuclideanSpace ℝ (Fin n) => (‖y-ξ‖^n)⁻¹)
      = fun y : EuclideanSpace ℝ (Fin n) => (fun z : EuclideanSpace ℝ (Fin n) => (‖z‖^n)⁻¹) (y - ξ) := rfl
  rw [hfun]
  have hcomp : Laplacian.laplacian
        (fun y : EuclideanSpace ℝ (Fin n) => (fun z : EuclideanSpace ℝ (Fin n) => (‖z‖^n)⁻¹) (y - ξ)) x
      = Laplacian.laplacian (fun z : EuclideanSpace ℝ (Fin n) => (‖z‖^n)⁻¹) (x - ξ) :=
    laplacian_comp_sub (fun z : EuclideanSpace ℝ (Fin n) => (‖z‖^n)⁻¹) ξ x
  rw [hcomp]
  rw [laplacian_comp_norm (φ := fun r : ℝ => (r^n)⁻¹) hz hφdiff]
  rw [Commons.Analysis.Real.deriv_deriv_inv_pow, Commons.Analysis.Real.deriv_inv_pow]
  -- simplify
  have hr : (0:ℝ) < ‖x - ξ‖ := norm_pos_iff.mpr hz
  have hrne : ‖x - ξ‖ ≠ 0 := ne_of_gt hr
  rw [div_eq_mul_inv]
  field_simp
  rw [show n + 2 = (n+1) + 1 by ring, pow_succ]
  ring

/-- The base Poisson kernel is harmonic in the space variable when `‖ξ - c‖ = R`. -/
theorem laplacian_base_eq_zero {n : ℕ} {c ξ x : EuclideanSpace ℝ (Fin n)} {R : ℝ}
    (hv : ‖ξ - c‖ = R) (hx : x ≠ ξ) :
    Laplacian.laplacian (fun y : EuclideanSpace ℝ (Fin n) =>
        (R^2 - ‖y - c‖^2) * (‖y - ξ‖^n)⁻¹) x = 0 := by
  classical
  set b := stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n)) with hb
  have hf2 : ContDiffAt ℝ 2 (fun y : EuclideanSpace ℝ (Fin n) => R^2 - ‖y - c‖^2) x := by
    have hd : ContDiff ℝ 2 (fun y : EuclideanSpace ℝ (Fin n) => y - c) :=
      contDiff_id.sub contDiff_const
    exact (contDiff_const.sub (ContDiff.norm_sq (𝕜 := ℝ) hd)).contDiffAt
  have hg2 : ContDiffAt ℝ 2 (fun y : EuclideanSpace ℝ (Fin n) => (‖y - ξ‖^n)⁻¹) x := by
    have hd : ContDiffAt ℝ 2 (fun y : EuclideanSpace ℝ (Fin n) => y - ξ) x :=
      contDiffAt_id.sub contDiffAt_const
    have hn : ContDiffAt ℝ 2 (fun y : EuclideanSpace ℝ (Fin n) => ‖y - ξ‖) x :=
      ContDiffAt.norm (𝕜 := ℝ) hd (by simpa using sub_ne_zero.mpr hx)
    exact (hn.pow n).inv (pow_ne_zero _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx)))
  have hdg : Laplacian.laplacian (fun y : EuclideanSpace ℝ (Fin n) => (‖y - ξ‖^n)⁻¹) x
      = 2 * (n:ℝ) * (‖x-ξ‖^(n+2))⁻¹ := by
    rw [laplacian_invPow hx]
    have hfr : (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ) = n := by simp
    rw [hfr]
    ring
  have hfi : ∀ i, (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) => R^2 - ‖y - c‖^2) x) (b i)
      = -2 * inner ℝ (x - c) (b i) := by
    intro i
    rw [(hasFDerivAt_quad c x R).fderiv]
    simp [innerSL_apply_apply, inner_sub_left]
  have hgi : ∀ i, (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) => (‖y - ξ‖^n)⁻¹) x) (b i)
      = -(n:ℝ) * (‖x-ξ‖^(n+2))⁻¹ * inner ℝ (x - ξ) (b i) := by
    intro i
    rw [(hasFDerivAt_invPow (n := n) hx).fderiv]
    simp only [smul_apply, smul_eq_mul, innerSL_apply_apply, inner_sub_left]
    try ring
  have hbr : (R^2 - ‖x - c‖^2) - ‖x - ξ‖^2 + 2 * inner ℝ (x - c) (x - ξ)
      = R^2 - ‖ξ - c‖^2 := by
    have h1 : x - ξ = (x - c) - (ξ - c) := by abel
    rw [h1]
    have h2 : ‖(x - c) - (ξ - c)‖^2
        = ‖x - c‖^2 - 2 * inner ℝ (x - c) (ξ - c) + ‖ξ - c‖^2 := norm_sub_sq_real _ _
    have h3 : inner ℝ (x - c) ((x - c) - (ξ - c))
        = ‖x - c‖^2 - inner ℝ (x - c) (ξ - c) := by
      rw [inner_sub_right, real_inner_self_eq_norm_sq]
    rw [h2, h3]
    ring
  have hrne : ‖x - ξ‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx)
  have hkey : (‖x - ξ‖^n)⁻¹ = (‖x - ξ‖^(n+2))⁻¹ * ‖x - ξ‖^2 := by
    rw [pow_add (‖x - ξ‖) n 2, mul_inv]
    rw [mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 hrne), mul_one]
  have hsum : (∑ i, ((fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) => R^2 - ‖y - c‖^2) x) (b i))
        * ((fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) => (‖y - ξ‖^n)⁻¹) x) (b i)))
      = 2*(n:ℝ)*(‖x-ξ‖^(n+2))⁻¹ * inner ℝ (x - c) (x - ξ) := by
    have hterm : ∀ i, ((fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) => R^2 - ‖y - c‖^2) x) (b i))
        * ((fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) => (‖y - ξ‖^n)⁻¹) x) (b i))
        = (2*(n:ℝ)*(‖x-ξ‖^(n+2))⁻¹) * (inner ℝ (x - c) (b i) * inner ℝ (b i) (x - ξ)) := by
      intro i; rw [hfi i, hgi i, real_inner_comm (x - ξ) (b i)]; ring
    rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.mul_sum,
      OrthonormalBasis.sum_inner_mul_inner]
  rw [show (fun y : EuclideanSpace ℝ (Fin n) => (R^2 - ‖y - c‖^2) * (‖y - ξ‖^n)⁻¹)
      = (fun y : EuclideanSpace ℝ (Fin n) => R^2 - ‖y - c‖^2)
        * (fun y : EuclideanSpace ℝ (Fin n) => (‖y - ξ‖^n)⁻¹) from rfl]
  rw [laplacian_mul b hf2 hg2, laplacian_quad c x R, hdg, hsum, hkey]
  rw [show (R^2 - ‖x-c‖^2) * (2*(n:ℝ)*(‖x-ξ‖^(n+2))⁻¹)
        + ((‖x-ξ‖^(n+2))⁻¹ * ‖x-ξ‖^2) * (-2*(n:ℝ))
        + 2 * (2*(n:ℝ)*(‖x-ξ‖^(n+2))⁻¹ * inner ℝ (x-c) (x-ξ))
      = 2*(n:ℝ)*(‖x-ξ‖^(n+2))⁻¹
        * ((R^2 - ‖x-c‖^2) - ‖x-ξ‖^2 + 2*inner ℝ (x-c) (x-ξ)) from by ring]
  rw [hbr, hv]
  ring

end KernelCalc

/-! ## The Poisson kernel on the sphere and the Poisson integral -/

section Poisson

/-- Total mass (surface area) of the unit sphere in `EuclideanSpace ℝ (Fin n)`,
computed as `volume.toSphere univ`. Positive for `n > 0`. -/
noncomputable def sphereArea (n : ℕ) : ℝ :=
  (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere.real Set.univ

theorem sphereArea_pos {n : ℕ} (hn : 0 < n) : 0 < sphereArea n := by
  rw [sphereArea, MeasureTheory.Measure.toSphere_real_apply_univ]
  have h1 : (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ) = n := by simp
  rw [h1]
  have h2 : 0 < (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))).real
      (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
    rw [MeasureTheory.Measure.real]
    refine ENNReal.toReal_pos ?_ ?_
    · exact ne_of_gt (measure_ball_pos _ 0 one_pos)
    · exact measure_ball_lt_top.ne
  positivity

/-- The Poisson kernel for the ball `ball c R` in `EuclideanSpace ℝ (Fin n)`,
evaluated at `x` and the boundary point `c + R • u` (`u` on the unit sphere). -/
noncomputable def pKern (n : ℕ) (c : EuclideanSpace ℝ (Fin n)) (R : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (u : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) : ℝ :=
  (R^n / (sphereArea n * R^2))
    * ((R^2 - ‖x - c‖^2) * (‖x - c - R • (u : EuclideanSpace ℝ (Fin n))‖^n)⁻¹)

/-- The Poisson integral of the boundary data `g` for the ball `ball c R`. -/
noncomputable def pExt (n : ℕ) (c : EuclideanSpace ℝ (Fin n)) (R : ℝ)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∫ u, pKern n c R x u * g (c + R • (u : EuclideanSpace ℝ (Fin n)))
    ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere

end Poisson

/-! ## Assembly of the main theorem -/

/-- Assembly: given the three analytic inputs (the Poisson integral is `C²` and harmonic, the mass
identity, and the boundary continuity), the Dirichlet problem on the ball is solved. -/
theorem main_of_inputs {n : ℕ} (hn : 0 < n)
    {c : EuclideanSpace ℝ (Fin n)} {R : ℝ} (hR : 0 < R)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : ContinuousOn g (sphere c R))
    (hC2 : ContDiffOn ℝ 2 (pExt n c R g) (ball c R))
    (hlap : ∀ x ∈ ball c R, Laplacian.laplacian (pExt n c R g) x = 0)
    (hmass : ∀ x ∈ ball c R, pExt n c R (fun _ => (1:ℝ)) x = 1)
    (hbd : ∀ y ∈ sphere c R, ∀ ε > 0, ∃ δ > 0, ∀ x : EuclideanSpace ℝ (Fin n),
      ‖x - c‖ < R → ‖x - y‖ < δ → |pExt n c R g x - g y| < ε) :
    ∃ v : EuclideanSpace ℝ (Fin n) → ℝ, ContDiffOn ℝ 2 v (ball c R) ∧
      (∀ x ∈ ball c R, Laplacian.laplacian v x = 0) ∧
      ContinuousOn v (closedBall c R) ∧ (∀ y ∈ sphere c R, v y = g y) := by
  classical
  refine ⟨fun x => if ‖x - c‖ < R then pExt n c R g x else g x, ?_, ?_, ?_, ?_⟩
  · -- `C²` on the ball: agree with `pExt` there
    refine (contDiffOn_congr (f := pExt n c R g) (f₁ := fun x =>
      if ‖x - c‖ < R then pExt n c R g x else g x) ?_).mpr hC2
    intro x hx
    have hx' : ‖x - c‖ < R := by simpa [mem_ball, dist_eq_norm] using hx
    simp [hx']
  · -- harmonic on the ball
    intro x hx
    have heq : (fun y : EuclideanSpace ℝ (Fin n) =>
        if ‖y - c‖ < R then pExt n c R g y else g y) =ᶠ[𝓝 x] pExt n c R g := by
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      have hy' : ‖y - c‖ < R := by simpa [mem_ball, dist_eq_norm] using hy
      simp [hy']
    have h := (_root_.InnerProductSpace.laplacian_congr_nhds heq).eq_of_nhds
    rw [h, hlap x hx]
  · -- continuity on the closed ball
    intro x hx
    by_cases hxc : ‖x - c‖ < R
    · -- interior point
      have hxb : x ∈ ball c R := by simpa [mem_ball, dist_eq_norm] using hxc
      have hp : ContinuousAt (pExt n c R g) x :=
        hC2.continuousOn.continuousAt (isOpen_ball.mem_nhds hxb)
      have hv : (fun y : EuclideanSpace ℝ (Fin n) =>
          if ‖y - c‖ < R then pExt n c R g y else g y) =ᶠ[𝓝 x] pExt n c R g := by
        filter_upwards [isOpen_ball.mem_nhds hxb] with y hy
        have hy' : ‖y - c‖ < R := by simpa [mem_ball, dist_eq_norm] using hy
        simp [hy']
      exact (hp.congr_of_eventuallyEq hv).continuousWithinAt
    · have hxR : ‖x - c‖ = R := by
        have hle : ‖x - c‖ ≤ R := by simpa [mem_closedBall, dist_eq_norm] using hx
        exact le_antisymm hle (le_of_not_gt hxc)
      rw [continuousWithinAt_iff]
      intro ε hε
      obtain ⟨δ₁, hδ₁, hδ₁p⟩ := hbd x (by simpa [mem_sphere, dist_eq_norm] using hxR) ε hε
      have hxS : x ∈ sphere c R := by simpa [mem_sphere, dist_eq_norm] using hxR
      obtain ⟨δ₂, hδ₂, hδ₂p⟩ := continuousWithinAt_iff.mp (hg x hxS) ε hε
      refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
      intro y hy hxy
      have hxy₁ : dist y x < δ₁ := lt_of_lt_of_le hxy (min_le_left _ _)
      have hxy₂ : dist y x < δ₂ := lt_of_lt_of_le hxy (min_le_right _ _)
      have hyc : ‖y - c‖ ≤ R := by simpa [mem_closedBall, dist_eq_norm] using hy
      have hxval : (if ‖x - c‖ < R then pExt n c R g x else g x) = g x := by
        simp [hxc]
      by_cases hyc' : ‖y - c‖ < R
      · have : |(if ‖y - c‖ < R then pExt n c R g y else g y) - g x| < ε := by
          simp only [hyc', if_true]
          exact hδ₁p y hyc' (by simpa [dist_eq_norm] using hxy₁)
        simpa [hxval, Real.dist_eq] using this
      · have hyR : ‖y - c‖ = R := le_antisymm hyc (le_of_not_gt hyc')
        have : |(if ‖y - c‖ < R then pExt n c R g y else g y) - g x| < ε := by
          simp only [hyc', if_false]
          have hyS : y ∈ sphere c R := by simpa [mem_sphere, dist_eq_norm] using hyR
          have := hδ₂p (x := y) hyS (by simpa [dist_eq_norm] using hxy₂)
          simpa [Real.dist_eq] using this
        simpa [hxval, Real.dist_eq] using this
  · -- boundary values
    intro y hy
    have hyR : ‖y - c‖ = R := by simpa [mem_sphere, dist_eq_norm] using hy
    simp [not_lt.mpr (le_of_eq hyR.symm)]

end Commons.Analysis.Harmonic

/-! ## The theorem -/

namespace Commons.Analysis.Harmonic

open MeasureTheory Metric Set Filter Function in
open scoped BigOperators ENNReal Topology RealInnerProductSpace InnerProductSpace in
theorem exists_harmonicOn_ball_eqOn_sphere {n : ℕ} {g : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n)} {R : ℝ} (hR : 0 < R) (hg : ContinuousOn g (sphere c R)) :
    ∃ v : EuclideanSpace ℝ (Fin n) → ℝ, ContDiffOn ℝ 2 v (ball c R) ∧
      (∀ x ∈ ball c R, Laplacian.laplacian v x = 0) ∧
      ContinuousOn v (closedBall c R) ∧ (∀ y ∈ sphere c R, v y = g y) := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · -- zero-dimensional case: `EuclideanSpace ℝ (Fin 0)` is a subsingleton, so `g` is constant
    subst hn0
    have hconst : g = fun _ : EuclideanSpace ℝ (Fin 0) => g 0 := by
      funext x
      congr 1
      exact Subsingleton.elim x 0
    refine ⟨g, ?_, ?_, ?_, ?_⟩
    · rw [hconst]; exact contDiffOn_const
    · intro x hx
      rw [hconst]
      simp
    · rw [hconst]; exact continuousOn_const
    · intro y hy; rfl
  · -- positive-dimensional case: assemble the three analytic inputs
    -- The Poisson integral of the constant function `1` is `C²` and harmonic (first component of
    -- `contDiffOn_two_poissonIntegral` applied to `g := fun _ => 1`), hence the mass identity holds.
    have hmass : ∀ x ∈ ball c R, pExt n c R (fun _ => (1:ℝ)) x = 1 := by
      have hmain1 := Commons.Analysis.Calculus.Laplacian.contDiffOn_two_poissonIntegral hn hR
        (fun _ : EuclideanSpace ℝ (Fin n) => (1:ℝ))
        (continuousOn_const : ContinuousOn (fun _ : EuclideanSpace ℝ (Fin n) => (1:ℝ)) (sphere c R))
      have h := Commons.Analysis.Measure.Integral.poissonIntegral_const_eq_one hn hR (c := c)
        (by simpa using hmain1.1) (by simpa using hmain1.2)
      intro x hx
      simpa [pExt, pKern, sphereArea] using h x hx
    have hbd : ∀ y ∈ sphere c R, ∀ ε > 0, ∃ δ > 0, ∀ x : EuclideanSpace ℝ (Fin n),
        ‖x - c‖ < R → ‖x - y‖ < δ → |pExt n c R g x - g y| < ε := by
      intro y hy ε hε
      obtain ⟨δ, hδ, hδp⟩ :=
        Commons.Analysis.Measure.Integral.poissonIntegral_tendsto_boundary hn hR g hg
          (by
            intro x hx
            simpa [pExt, pKern, sphereArea] using hmass x hx) y hy ε hε
      exact ⟨δ, hδ, fun x hxc hxy => by
        simpa [pExt, pKern, sphereArea] using hδp x hxc hxy⟩
    have hmain := Commons.Analysis.Calculus.Laplacian.contDiffOn_two_poissonIntegral hn hR g hg
    exact main_of_inputs hn hR g hg hmain.1 hmain.2 hmass hbd

end Commons.Analysis.Harmonic
