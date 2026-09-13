import Mathlib
import Submission.Commons.Analysis.Calculus.Laplacian.laplacian_mul
import Submission.Commons.Analysis.Calculus.Laplacian.laplacian_comp_norm
import Submission.Commons.Analysis.Calculus.Laplacian.laplacian_norm_sub_sq
import Submission.Commons.Analysis.Calculus.FDeriv.laplacian_eq_sum_second_partials
import Submission.Commons.Analysis.InnerProductSpace.fderiv_comp_norm_eq
import Submission.Commons.Analysis.InnerProductSpace.fderiv_norm_single
import Submission.Commons.Analysis.Real.deriv_inv_pow
import Submission.Commons.Analysis.Real.deriv_deriv_inv_pow
import Submission.Commons.Analysis.Calculus.contDiffOn_two_parametric_integral

namespace Commons.Analysis.Calculus.Laplacian

open MeasureTheory Metric Set Filter Function
open Commons.Analysis.InnerProductSpace
open scoped Topology RealInnerProductSpace InnerProductSpace BigOperators ENNReal

noncomputable section

/-! ## Calculus of the Poisson kernel of a ball

The kernel of the Poisson integral of the ball `ball c R` is, as a function of the space
variable `x` and the boundary point `ξ`,
`K x ξ = (R^2 - ‖x - c‖^2) * (‖x - ξ‖^n)⁻¹`.
In this section we collect its first and second derivatives in `x`, together with the
(crucial) fact that it is *harmonic* in `x` when `ξ` lies on the sphere `sphere c R`. -/

section KernelCalc

/-- `fderiv` of `y ↦ R^2 - ‖y - c‖^2`. -/
theorem hasFDerivAt_quad {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c x : E) (R : ℝ) :
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
theorem fderiv_inv_pow_norm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} {z : E} (hz : z ≠ 0) :
    fderiv ℝ (fun z : E => (‖z‖ ^ n)⁻¹) z
      = (-(n:ℝ) * (‖z‖^(n+2))⁻¹) • innerSL ℝ z := by
  have hzpow : (‖z‖ ^ n) ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hz)
  have hφdiff : DifferentiableAt ℝ (fun r : ℝ => (r^n)⁻¹) ‖z‖ :=
    (differentiableAt_id (x := (‖z‖:ℝ))).pow n |>.inv hzpow
  ext v
  rw [fderiv_comp_norm_eq (φ := fun r : ℝ => (r^n)⁻¹) hz hφdiff v,
      Commons.Analysis.Real.deriv_inv_pow]
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply]
  have hpow : (‖z‖ ^ (n+1)) * ‖z‖ = ‖z‖ ^ (n+2) := by
    rw [mul_comm, ← pow_succ']
  have hkey : (‖z‖ ^ (n+1))⁻¹ * ‖z‖⁻¹ = (‖z‖ ^ (n+2))⁻¹ := by
    rw [← mul_inv, hpow]
  rw [div_eq_mul_inv, ← hkey]
  try ring

/-- `fderiv` of `y ↦ (‖y - ξ‖^n)⁻¹`. -/
theorem hasFDerivAt_invPow {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} {ξ x : E} (hx : x ≠ ξ) :
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

/-- The first `x`-derivative of the base kernel `y ↦ (R^2 - ‖y - c‖^2) * (‖y - ξ‖^n)⁻¹`. -/
def baseD1 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
    (c ξ : E) (R : ℝ) (x : E) : E →L[ℝ] ℝ :=
  ((R^2 - ‖x - c‖^2) * (-(n:ℝ) * (‖x - ξ‖^(n+2))⁻¹)) • innerSL ℝ (x-ξ)
    + ((‖x - ξ‖^n)⁻¹ * (-2)) • innerSL ℝ (x-c)

theorem hasFDerivAt_base {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} {c ξ x : E} {R : ℝ} (hx : x ≠ ξ) :
    HasFDerivAt (fun y : E => (R^2 - ‖y-c‖^2) * (‖y-ξ‖^n)⁻¹)
      (baseD1 (n := n) c ξ R x) x := by
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

/-! ### The second derivative of the Poisson kernel -/

section SecondDeriv

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The inner product of `E`, bundled as a continuous linear map `E →L[ℝ] (E →L[ℝ] ℝ)`. -/
noncomputable def innerSLCLM (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    E →L[ℝ] (E →L[ℝ] ℝ) := ↑(innerSL ℝ)

lemma innerSLCLM_apply (v : E) : innerSLCLM E v = innerSL ℝ v := rfl

lemma norm_innerSLCLM_le : ‖(innerSLCLM E)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => ?_)
  rw [one_mul, innerSLCLM_apply]
  exact le_of_eq (innerSL_apply_norm ℝ v)

/-- The scalar coefficient `A` of the first derivative of the base Poisson kernel. -/
def pKcA {n : ℕ} (c ξ : E) (R : ℝ) (x : E) : ℝ :=
  (R^2 - ‖x - c‖^2) * (-(n:ℝ) * (‖x - ξ‖^(n+2))⁻¹)

/-- The scalar coefficient `B` of the first derivative of the base Poisson kernel. -/
def pKcB {n : ℕ} (ξ x : E) : ℝ := (‖x - ξ‖^n)⁻¹ * (-2)

/-- The derivative of the scalar coefficient `pKcA`. -/
def pKdA {n : ℕ} (c ξ : E) (R : ℝ) (x : E) : E →L[ℝ] ℝ :=
  (2 * (n:ℝ) * (‖x - ξ‖^(n+2))⁻¹) • innerSL ℝ (x - c)
    + ((R^2 - ‖x - c‖^2) * ((n:ℝ) * ((n:ℝ) + 2)) * (‖x - ξ‖^(n+4))⁻¹) • innerSL ℝ (x - ξ)

/-- The derivative of the scalar coefficient `pKcB`. -/
def pKdB {n : ℕ} (ξ x : E) : E →L[ℝ] ℝ :=
  (2 * (n:ℝ) * (‖x - ξ‖^(n+2))⁻¹) • innerSL ℝ (x - ξ)

lemma hasFDerivAt_pKcA {n : ℕ} {c ξ x : E} {R : ℝ} (hx : x ≠ ξ) :
    HasFDerivAt (pKcA (n := n) c ξ R) (pKdA (n := n) c ξ R x) x := by
  have hQ : HasFDerivAt (fun y : E => R^2 - ‖y - c‖^2) ((-2:ℝ) • innerSL ℝ (x - c)) x :=
    hasFDerivAt_quad c x R
  have hbase : HasFDerivAt (fun y : E => (‖y - ξ‖^(n+2))⁻¹)
      ((-((n+2 : ℕ) : ℝ) * (‖x - ξ‖^(n+4))⁻¹) • innerSL ℝ (x - ξ)) x := by
    have h := hasFDerivAt_invPow (n := n + 2) (ξ := ξ) (x := x) hx
    have he : ((n + 2 : ℕ) + 2) = n + 4 := by ring
    rw [he] at h
    exact h
  have hG : HasFDerivAt (fun y : E => -(n:ℝ) * (‖y - ξ‖^(n+2))⁻¹)
      ((-(n:ℝ)) • ((-((n+2 : ℕ) : ℝ) * (‖x - ξ‖^(n+4))⁻¹) • innerSL ℝ (x - ξ))) x :=
    hbase.const_mul (-(n:ℝ))
  have hmul := hQ.mul hG
  have hfun : ((fun y : E => R^2 - ‖y - c‖^2)
        * (fun y : E => -(n:ℝ) * (‖y - ξ‖^(n+2))⁻¹))
      = pKcA (n := n) c ξ R := by funext y; rfl
  rw [hfun] at hmul
  refine hmul.congr_fderiv ?_
  ext v
  simp only [pKdA, add_apply, smul_apply, smul_eq_mul, innerSL_apply_apply]
  push_cast
  ring

lemma hasFDerivAt_pKcB {n : ℕ} {ξ x : E} (hx : x ≠ ξ) :
    HasFDerivAt (pKcB (n := n) ξ) (pKdB (n := n) ξ x) x := by
  have hbase : HasFDerivAt (fun y : E => (‖y - ξ‖^n)⁻¹)
      ((-(n:ℝ) * (‖x - ξ‖^(n+2))⁻¹) • innerSL ℝ (x - ξ)) x :=
    hasFDerivAt_invPow (n := n) hx
  have hc := hbase.const_mul (-2 : ℝ)
  have hfun : (fun y : E => (-2:ℝ) * (‖y - ξ‖^n)⁻¹) = pKcB (n := n) ξ := by
    funext y; simp only [pKcB]; ring
  rw [hfun] at hc
  refine hc.congr_fderiv ?_
  ext v
  simp only [pKdB, smul_apply, smul_eq_mul, innerSL_apply_apply]
  ring

/-- The second `x`-derivative of the base Poisson kernel. -/
def baseD2 {n : ℕ} (c ξ : E) (R : ℝ) (x : E) : E →L[ℝ] (E →L[ℝ] ℝ) :=
  pKcA (n := n) c ξ R x • (innerSLCLM E)
    + (pKdA (n := n) c ξ R x).smulRight (innerSL ℝ (x - ξ))
    + pKcB (n := n) ξ x • (innerSLCLM E)
    + (pKdB (n := n) ξ x).smulRight (innerSL ℝ (x - c))

lemma baseD1_eq {n : ℕ} (c ξ : E) (R : ℝ) (y : E) :
    baseD1 (n := n) c ξ R y
      = pKcA (n := n) c ξ R y • innerSL ℝ (y - ξ) + pKcB (n := n) ξ y • innerSL ℝ (y - c) := rfl

lemma hasFDerivAt_baseD1 {n : ℕ} {c ξ x : E} {R : ℝ} (hx : x ≠ ξ) :
    HasFDerivAt (fun y : E => baseD1 (n := n) c ξ R y) (baseD2 (n := n) c ξ R x) x := by
  have hA := hasFDerivAt_pKcA (n := n) (c := c) (ξ := ξ) (R := R) hx
  have hB := hasFDerivAt_pKcB (n := n) (ξ := ξ) hx
  have hL1 : HasFDerivAt (fun y : E => innerSL ℝ (y - ξ)) (innerSLCLM E) x := by
    have h2 : HasFDerivAt (fun y : E => innerSL ℝ y) (innerSLCLM E) x :=
      ContinuousLinearMap.hasFDerivAt _
    have hsub := h2.sub_const (innerSL ℝ ξ)
    have hfun : (fun y : E => innerSL ℝ y - innerSL ℝ ξ) = fun y : E => innerSL ℝ (y - ξ) := by
      funext y; rw [map_sub]
    rwa [hfun] at hsub
  have hL2 : HasFDerivAt (fun y : E => innerSL ℝ (y - c)) (innerSLCLM E) x := by
    have h2 : HasFDerivAt (fun y : E => innerSL ℝ y) (innerSLCLM E) x :=
      ContinuousLinearMap.hasFDerivAt _
    have hsub := h2.sub_const (innerSL ℝ c)
    have hfun : (fun y : E => innerSL ℝ y - innerSL ℝ c) = fun y : E => innerSL ℝ (y - c) := by
      funext y; rw [map_sub]
    rwa [hfun] at hsub
  have h1 := hA.smul hL1
  have h2 := hB.smul hL2
  have hsum := h1.add h2
  have hLfun : (pKcA (n := n) c ξ R • (fun y : E => innerSL ℝ (y - ξ))
        + pKcB (n := n) ξ • (fun y : E => innerSL ℝ (y - c)))
      = fun y : E => baseD1 (n := n) c ξ R y := by
    funext y
    simp only [Pi.add_apply, Pi.smul_apply]
    exact (baseD1_eq c ξ R y).symm
  rw [hLfun] at hsum
  refine hsum.congr_fderiv ?_
  simp only [baseD2]
  abel

end SecondDeriv

/-! ### Continuity of the Poisson integrand on the sphere -/

section Contin

local notation "𝔼" n:max => EuclideanSpace ℝ (Fin n)
local notation "𝕊" n:max => sphere (0 : EuclideanSpace ℝ (Fin n)) 1

variable {n : ℕ} {c : 𝔼 n} {R : ℝ}

/-- The base kernel of the Poisson integral: `x ↦ (R² - ‖x - c‖²)‖x - ξ‖^{-n}`. -/
def pKbase (c ξ : 𝔼 n) (R : ℝ) (x : 𝔼 n) : ℝ :=
  (R^2 - ‖x - c‖^2) * (‖x - ξ‖^n)⁻¹

/-- The boundary point `c + R • u` of the ball, attached to a unit vector `u`. -/
def sphPt (c : 𝔼 n) (R : ℝ) (u : 𝕊 n) : 𝔼 n := c + R • (u : 𝔼 n)

lemma continuous_sphPt : Continuous (sphPt c R) := by
  show Continuous (fun u : 𝕊 n => c + R • (u : 𝔼 n))
  exact continuous_const.add (continuous_subtype_val.const_smul R)

lemma norm_sphPt_sub (u : 𝕊 n) : ‖sphPt c R u - c‖ = |R| := by
  rw [sphPt, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
  have hu : ‖(u : 𝔼 n)‖ = 1 := by
    simpa [Metric.mem_sphere, dist_eq_norm] using u.2
  rw [hu, mul_one]

lemma sphPt_mem_sphere (hR : 0 ≤ R) (u : 𝕊 n) : sphPt c R u ∈ sphere c R := by
  rw [Metric.mem_sphere, dist_eq_norm, norm_sphPt_sub, abs_of_nonneg hR]

lemma ne_sphPt_of_mem_ball (hR : 0 ≤ R) {x : 𝔼 n} (hx : x ∈ ball c R) (u : 𝕊 n) :
    x ≠ sphPt c R u := by
  intro h
  rw [Metric.mem_ball, dist_eq_norm] at hx
  have h1 : ‖x - c‖ = R := by rw [h, norm_sphPt_sub, abs_of_nonneg hR]
  linarith

lemma continuous_comp_sphPt_g {g : 𝔼 n → ℝ} (hg : ContinuousOn g (sphere c R)) (hR : 0 ≤ R) :
    Continuous (fun u : 𝕊 n => g (sphPt c R u)) :=
  hg.comp_continuous (continuous_sphPt) (fun u => sphPt_mem_sphere hR u)

lemma continuousOn_sphNorm_pow_inv (hR : 0 ≤ R) {m : ℕ} :
    ContinuousOn (fun p : 𝔼 n × 𝕊 n => (‖p.1 - sphPt c R p.2‖ ^ m)⁻¹)
      (ball c R ×ˢ Set.univ) := by
  refine ContinuousOn.inv₀ ?_ ?_
  · exact (((continuous_fst.sub
      ((continuous_sphPt (c := c) (R := R)).comp continuous_snd)).norm).pow m).continuousOn
  · intro p hp
    exact pow_ne_zero _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (ne_sphPt_of_mem_ball hR hp.1 p.2)))

lemma continuous_innerSL_apply : Continuous (fun v : 𝔼 n => innerSL ℝ v) :=
  (innerSLCLM (𝔼 n)).continuous

lemma continuousOn_innerSL_sub_const (hR : 0 ≤ R) :
    ContinuousOn (fun p : 𝔼 n × 𝕊 n => innerSL ℝ (p.1 - c)) (ball c R ×ˢ Set.univ) :=
  ((continuous_innerSL_apply (n := n)).comp (continuous_fst.sub continuous_const)).continuousOn

lemma continuousOn_innerSL_sub_sphPt (hR : 0 ≤ R) :
    ContinuousOn (fun p : 𝔼 n × 𝕊 n => innerSL ℝ (p.1 - sphPt c R p.2))
      (ball c R ×ˢ Set.univ) :=
  ((continuous_innerSL_apply (n := n)).comp
    (continuous_fst.sub ((continuous_sphPt (c := c) (R := R)).comp continuous_snd))).continuousOn

lemma continuousOn_pKcA_sphere (hR : 0 ≤ R) :
    ContinuousOn (fun p : 𝔼 n × 𝕊 n =>
        (R^2 - ‖p.1 - c‖^2) * (-(n:ℝ) * (‖p.1 - sphPt c R p.2‖^(n+2))⁻¹))
      (ball c R ×ˢ Set.univ) := by
  have hQ : ContinuousOn (fun p : 𝔼 n × 𝕊 n => R^2 - ‖p.1 - c‖^2) (ball c R ×ˢ Set.univ) :=
    (continuous_const.sub (((continuous_fst.sub continuous_const).norm).pow 2)).continuousOn
  have hG := continuousOn_sphNorm_pow_inv (c := c) (R := R) hR (m := n + 2)
  exact (hQ.mul (hG.const_mul (-(n:ℝ)))).congr (fun p hp => rfl)

lemma continuousOn_pKcB_sphere (hR : 0 ≤ R) :
    ContinuousOn (fun p : 𝔼 n × 𝕊 n => (‖p.1 - sphPt c R p.2‖^n)⁻¹ * (-2))
      (ball c R ×ˢ Set.univ) :=
  (continuousOn_sphNorm_pow_inv (c := c) (R := R) hR (m := n)).mul_const (-2)

lemma continuousOn_pKdA_sphere (hR : 0 ≤ R) :
    ContinuousOn (fun p : 𝔼 n × 𝕊 n =>
        (2 * (n:ℝ) * (‖p.1 - sphPt c R p.2‖^(n+2))⁻¹) • innerSL ℝ (p.1 - c)
        + ((R^2 - ‖p.1 - c‖^2) * ((n:ℝ) * ((n:ℝ) + 2))
              * (‖p.1 - sphPt c R p.2‖^(n+4))⁻¹) • innerSL ℝ (p.1 - sphPt c R p.2))
      (ball c R ×ˢ Set.univ) := by
  have hcoef1 : ContinuousOn (fun p : 𝔼 n × 𝕊 n =>
      2 * (n:ℝ) * (‖p.1 - sphPt c R p.2‖^(n+2))⁻¹) (ball c R ×ˢ Set.univ) :=
    (continuousOn_sphNorm_pow_inv (c := c) (R := R) hR (m := n + 2)).const_mul (2 * (n:ℝ))
  have hcoef2 : ContinuousOn (fun p : 𝔼 n × 𝕊 n =>
      (R^2 - ‖p.1 - c‖^2) * ((n:ℝ) * ((n:ℝ) + 2))
        * (‖p.1 - sphPt c R p.2‖^(n+4))⁻¹) (ball c R ×ˢ Set.univ) := by
    have hQ : ContinuousOn (fun p : 𝔼 n × 𝕊 n => R^2 - ‖p.1 - c‖^2) (ball c R ×ˢ Set.univ) :=
      (continuous_const.sub (((continuous_fst.sub continuous_const).norm).pow 2)).continuousOn
    have hG := continuousOn_sphNorm_pow_inv (c := c) (R := R) hR (m := n + 4)
    exact ((hQ.mul_const ((n:ℝ) * ((n:ℝ) + 2))).mul hG).congr (fun p hp => rfl)
  exact (hcoef1.smul (continuousOn_innerSL_sub_const hR)).add
    (hcoef2.smul (continuousOn_innerSL_sub_sphPt hR))

lemma continuousOn_pKdB_sphere (hR : 0 ≤ R) :
    ContinuousOn (fun p : 𝔼 n × 𝕊 n =>
        (2 * (n:ℝ) * (‖p.1 - sphPt c R p.2‖^(n+2))⁻¹) • innerSL ℝ (p.1 - sphPt c R p.2))
      (ball c R ×ˢ Set.univ) :=
  (continuousOn_sphNorm_pow_inv (c := c) (R := R) hR (m := n + 2)).const_mul (2 * (n:ℝ))
    |>.smul (continuousOn_innerSL_sub_sphPt hR)

lemma continuousOn_smulRight_pair {Y : Type*} [TopologicalSpace Y]
    {f g : Y → (𝔼 n →L[ℝ] ℝ)} {s : Set Y} (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun y => (f y).smulRight (g y)) s := by
  have houter : Continuous
      (fun q : (𝔼 n →L[ℝ] ℝ) × (𝔼 n →L[ℝ] ℝ) => q.1.smulRight q.2) :=
    (isBoundedBilinearMap_smulRight (𝕜 := ℝ) (E := 𝔼 n) (F := 𝔼 n →L[ℝ] ℝ)).continuous
  have hpair : ContinuousOn (fun y => (f y, g y)) s := hf.prodMk hg
  exact (houter.continuousOn.comp hpair (fun y _ => Set.mem_univ _)).congr (fun y _ => rfl)

lemma continuousOn_baseD1_sphere (hR : 0 ≤ R) :
    ContinuousOn (fun p : 𝔼 n × 𝕊 n => baseD1 (n := n) c (sphPt c R p.2) R p.1)
      (ball c R ×ˢ Set.univ) := by
  have hA := (continuousOn_pKcA_sphere (c := c) (R := R) hR).smul (continuousOn_innerSL_sub_sphPt hR)
  have hB := (continuousOn_pKcB_sphere (c := c) (R := R) hR).smul (continuousOn_innerSL_sub_const hR)
  exact (hA.add hB).congr (fun p hp => rfl)

lemma continuousOn_baseD2_sphere (hR : 0 ≤ R) :
    ContinuousOn (fun p : 𝔼 n × 𝕊 n => baseD2 (n := n) c (sphPt c R p.2) R p.1)
      (ball c R ×ˢ Set.univ) := by
  haveI : ContinuousAdd (𝔼 n →L[ℝ] (𝔼 n →L[ℝ] ℝ)) :=
    ContinuousLinearMap.topologicalAddGroup.toContinuousAdd
  have hKcA := continuousOn_pKcA_sphere (c := c) (R := R) hR
  have hKcB := continuousOn_pKcB_sphere (c := c) (R := R) hR
  have hKdA : ContinuousOn (fun p : 𝔼 n × 𝕊 n => pKdA (n := n) c (sphPt c R p.2) R p.1)
      (ball c R ×ˢ Set.univ) := by
    simpa only [pKdA] using continuousOn_pKdA_sphere (c := c) (R := R) hR
  have hKdB : ContinuousOn (fun p : 𝔼 n × 𝕊 n => pKdB (n := n) (sphPt c R p.2) p.1)
      (ball c R ×ˢ Set.univ) := by
    simpa only [pKdB] using continuousOn_pKdB_sphere (c := c) (R := R) hR
  have h1 : ContinuousOn (fun p : 𝔼 n × 𝕊 n =>
      ((R^2 - ‖p.1 - c‖^2) * (-(n:ℝ) * (‖p.1 - sphPt c R p.2‖^(n+2))⁻¹))
        • innerSLCLM (𝔼 n)) (ball c R ×ˢ Set.univ) :=
    hKcA.smul (continuous_const.continuousOn)
  have h3 : ContinuousOn (fun p : 𝔼 n × 𝕊 n =>
      ((‖p.1 - sphPt c R p.2‖^n)⁻¹ * (-2)) • innerSLCLM (𝔼 n)) (ball c R ×ˢ Set.univ) :=
    hKcB.smul (continuous_const.continuousOn)
  have h2 := continuousOn_smulRight_pair (n := n) hKdA (continuousOn_innerSL_sub_sphPt hR)
  have h4 := continuousOn_smulRight_pair (n := n) hKdB (continuousOn_innerSL_sub_const hR)
  exact (((h1.add h2).add h3).add h4).congr (fun p hp => rfl)


lemma hasFDerivAt_pKbase {n : ℕ} {c ξ x : 𝔼 n} {R : ℝ} (hx : x ≠ ξ) :
    HasFDerivAt (pKbase (n := n) c ξ R) (baseD1 (n := n) c ξ R x) x :=
  hasFDerivAt_base hx

lemma continuousOn_pKbase_sphere (hR : 0 ≤ R) :
    ContinuousOn (fun p : 𝔼 n × 𝕊 n => pKbase c (sphPt c R p.2) R p.1)
      (ball c R ×ˢ Set.univ) := by
  have hQ : ContinuousOn (fun p : 𝔼 n × 𝕊 n => R^2 - ‖p.1 - c‖^2) (ball c R ×ˢ Set.univ) :=
    (continuous_const.sub (((continuous_fst.sub continuous_const).norm).pow 2)).continuousOn
  have hG := continuousOn_sphNorm_pow_inv (c := c) (R := R) hR (m := n)
  exact (hQ.mul hG).congr (fun p hp => by simp only [pKbase, Pi.mul_apply])

lemma baseD2_eq_fderiv {ξ x : 𝔼 n} (hx : x ≠ ξ) :
    baseD2 (n := n) c ξ R x = fderiv ℝ (fderiv ℝ (pKbase (n := n) c ξ R)) x := by
  have h1 : (fun y => baseD1 (n := n) c ξ R y) =ᶠ[𝓝 x] (fderiv ℝ (pKbase (n := n) c ξ R)) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds
      (show x ∈ ({ξ}ᶜ : Set (𝔼 n)) from by simpa using hx)] with y hy
    exact (hasFDerivAt_pKbase (n := n) (c := c) (ξ := ξ) (R := R) hy).fderiv.symm
  rw [← (hasFDerivAt_baseD1 (n := n) (c := c) (ξ := ξ) (R := R) hx).fderiv]
  exact h1.fderiv_eq

end Contin



/-! ### `C²` regularity of a parametric integral over a sphere -/

section Parametric

local notation "𝔼" n:max => EuclideanSpace ℝ (Fin n)
local notation "𝕊" n:max => sphere (0 : EuclideanSpace ℝ (Fin n)) 1

/-- The section `x ↦ Ψ p x` of a jointly continuous family is continuous. -/
private lemma section_continuous {P X Y : Type*} [TopologicalSpace P] [TopologicalSpace X]
    [TopologicalSpace Y]
    {s : Set P} {Ψ : P → X → Y} (hΨ : ContinuousOn (Function.uncurry Ψ) (s ×ˢ Set.univ))
    {p : P} (hp : p ∈ s) : Continuous (fun x => Ψ p x) := by
  have hf : Continuous (fun x : X => (p, x)) := continuous_const.prodMk continuous_id
  have h := hΨ.comp_continuous hf (fun x => ⟨hp, Set.mem_univ x⟩)
  simpa only [Function.comp_def, Function.uncurry] using h

/-- The section `p ↦ Ψ p a` in the *first* variable is continuous at interior points. -/
private lemma section_continuousAt {P X Y : Type*} [TopologicalSpace P] [TopologicalSpace X]
    [TopologicalSpace Y] {s : Set P} (hs : IsOpen s) {Ψ : P → X → Y}
    (hΨ : ContinuousOn (Function.uncurry Ψ) (s ×ˢ Set.univ)) {p : P} (hp : p ∈ s) (a : X) :
    ContinuousAt (fun q => Ψ q a) p := by
  have hcont : ContinuousOn (fun q : P => (q, a)) s := by fun_prop
  have h1 : ContinuousOn (fun q => Ψ q a) s := by
    have h := hΨ.comp hcont (fun q hq => ⟨hq, Set.mem_univ a⟩)
    simpa only [Function.comp_def, Function.uncurry] using h
  exact (h1.continuousWithinAt hp).continuousAt (hs.mem_nhds hp)

/-- Differentiation under the integral sign, first order. -/
theorem hasFDerivAt_integral_one_parametric {n : ℕ} {μ : Measure (𝕊 n)} [IsFiniteMeasure μ]
    {s : Set (𝔼 n)} (hs : IsOpen s)
    (Φ₀ : 𝔼 n → 𝕊 n → ℝ) (Φ₁ : 𝔼 n → 𝕊 n → 𝔼 n →L[ℝ] ℝ)
    (h₀ : ContinuousOn (Function.uncurry Φ₀) (s ×ˢ Set.univ))
    (h₁ : ContinuousOn (Function.uncurry Φ₁) (s ×ˢ Set.univ))
    (hd₁ : ∀ p ∈ s, ∀ x, HasFDerivAt (fun q => Φ₀ q x) (Φ₁ p x) p) :
    (∀ p ∈ s, HasFDerivAt (fun p => ∫ x, Φ₀ p x ∂μ) (∫ x, Φ₁ p x ∂μ) p) ∧
    (∀ p ∈ s, fderiv ℝ (fun p => ∫ x, Φ₀ p x ∂μ) p = ∫ x, Φ₁ p x ∂μ) := by
  -- the uniform bound on the derivative family near any given point
  have hb : ∀ p ∈ s, ∃ ρ > 0, closedBall p ρ ⊆ s ∧
      ∃ C, ∀ q ∈ closedBall p ρ, ∀ x, ‖Φ₁ q x‖ ≤ C := by
    intro p hp
    obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (hs.mem_nhds hp)
    refine ⟨ε / 2, by positivity, ?_, ?_⟩
    · intro q hq
      refine hεsub ?_
      rw [Metric.mem_ball]
      have h2 : dist q p ≤ ε / 2 := Metric.mem_closedBall.mp hq
      linarith
    · have hsub : closedBall p (ε / 2) ⊆ s := by
        intro q hq
        refine hεsub ?_
        rw [Metric.mem_ball]
        have h2 : dist q p ≤ ε / 2 := Metric.mem_closedBall.mp hq
        linarith
      have hK : IsCompact (closedBall p (ε / 2) ×ˢ (Set.univ : Set (𝕊 n))) :=
        (isCompact_closedBall p (ε / 2)).prod isCompact_univ
      obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (f := Function.uncurry Φ₁)
        (h₁.mono (Set.prod_mono hsub (Set.subset_univ _)))
      exact ⟨C, fun q hq x => hC (q, x) ⟨hq, Set.mem_univ x⟩⟩
  have hint0 : ∀ p ∈ s, Integrable (fun x => Φ₀ p x) μ := by
    intro p hp
    obtain ⟨C, hC⟩ := (isCompact_univ (X := 𝕊 n)).exists_bound_of_continuousOn
      (f := fun x : 𝕊 n => Φ₀ p x) (section_continuous h₀ hp).continuousOn
    exact Integrable.of_bound ((section_continuous h₀ hp).aestronglyMeasurable) C
      (Filter.Eventually.of_forall (fun x => hC x (Set.mem_univ x)))
  have hderiv1 : ∀ p ∈ s, HasFDerivAt (fun p => ∫ x, Φ₀ p x ∂μ) (∫ x, Φ₁ p x ∂μ) p := by
    intro p hp
    obtain ⟨ρ, hρ, hρsub, C, hC⟩ := hb p hp
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := μ)
      (F := fun q x => Φ₀ q x) (F' := fun q x => Φ₁ q x) (bound := fun _ => C)
      (s := ball p ρ) (x₀ := p) (Metric.ball_mem_nhds p hρ) ?_ ?_ ?_ ?_ ?_ ?_
    · filter_upwards [Metric.ball_mem_nhds p hρ] with q hq
      exact (section_continuous h₀ (hρsub (Metric.ball_subset_closedBall hq))).aestronglyMeasurable
    · exact hint0 p hp
    · exact (section_continuous h₁ hp).aestronglyMeasurable
    · filter_upwards with x
      intro q hq
      exact hC q (Metric.ball_subset_closedBall hq) x
    · exact integrable_const C
    · filter_upwards with x
      intro q hq
      exact hd₁ q (hρsub (Metric.ball_subset_closedBall hq)) x
  exact ⟨hderiv1, fun p hp => (hderiv1 p hp).fderiv⟩

/-- Differentiation under the integral sign, second order.  The second derivative family only
needs a *local* uniform bound, which is supplied as a hypothesis (this is needed because the
auxiliary space `𝔼ⁿ →L (𝔼ⁿ →L ℝ)` has no usable norm instances in Mathlib). -/
theorem hasFDerivAt_integral_two_parametric {n : ℕ} {μ : Measure (𝕊 n)}
    [IsFiniteMeasure μ]
    {s : Set (𝔼 n)} (hs : IsOpen s)
    (Φ₁ : 𝔼 n → 𝕊 n → 𝔼 n →L[ℝ] ℝ)
    (Φ₂ : 𝔼 n → 𝕊 n → 𝔼 n →L[ℝ] (𝔼 n →L[ℝ] ℝ))
    (h₁ : ContinuousOn (Function.uncurry Φ₁) (s ×ˢ Set.univ))
    (h₂ : ContinuousOn (Function.uncurry Φ₂) (s ×ˢ Set.univ))
    (hb₂ : ∀ p ∈ s, ∃ ρ > 0, closedBall p ρ ⊆ s ∧
      ∃ C, ∀ q ∈ closedBall p ρ, ∀ x, ‖Φ₂ q x‖ ≤ C)
    (hd₂ : ∀ p ∈ s, ∀ x, HasFDerivAt (fun q => Φ₁ q x) (Φ₂ p x) p) :
    (∀ p ∈ s, HasFDerivAt (fun p => ∫ x, Φ₁ p x ∂μ) (∫ x, Φ₂ p x ∂μ) p) ∧
    (∀ p ∈ s, fderiv ℝ (fun p => ∫ x, Φ₁ p x ∂μ) p = ∫ x, Φ₂ p x ∂μ) ∧
    ContinuousOn (fun p => ∫ x, Φ₂ p x ∂μ) s := by
  have hb₁ : ∀ p ∈ s, ∃ ρ > 0, closedBall p ρ ⊆ s ∧
      ∃ C, ∀ q ∈ closedBall p ρ, ∀ x, ‖Φ₁ q x‖ ≤ C := by
    intro p hp
    obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (hs.mem_nhds hp)
    refine ⟨ε / 2, by positivity, ?_, ?_⟩
    · intro q hq
      refine hεsub ?_
      rw [Metric.mem_ball]
      have h2 : dist q p ≤ ε / 2 := Metric.mem_closedBall.mp hq
      linarith
    · have hsub : closedBall p (ε / 2) ⊆ s := by
        intro q hq
        refine hεsub ?_
        rw [Metric.mem_ball]
        have h2 : dist q p ≤ ε / 2 := Metric.mem_closedBall.mp hq
        linarith
      have hK : IsCompact (closedBall p (ε / 2) ×ˢ (Set.univ : Set (𝕊 n))) :=
        (isCompact_closedBall p (ε / 2)).prod isCompact_univ
      obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (f := Function.uncurry Φ₁)
        (h₁.mono (Set.prod_mono hsub (Set.subset_univ _)))
      exact ⟨C, fun q hq x => hC (q, x) ⟨hq, Set.mem_univ x⟩⟩
  have hint1 : ∀ p ∈ s, Integrable (fun x => Φ₁ p x) μ := by
    intro p hp
    obtain ⟨ρ, hρ, hρsub, C, hC⟩ := hb₁ p hp
    exact Integrable.of_bound ((section_continuous h₁ hp).aestronglyMeasurable) C
      (Filter.Eventually.of_forall (fun x => hC p (Metric.mem_closedBall_self hρ.le) x))
  have hderiv2 : ∀ p ∈ s, HasFDerivAt (fun p => ∫ x, Φ₁ p x ∂μ) (∫ x, Φ₂ p x ∂μ) p := by
    intro p hp
    obtain ⟨ρ, hρ, hρsub, C, hC⟩ := hb₂ p hp
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := μ)
      (F := fun q x => Φ₁ q x) (F' := fun q x => Φ₂ q x) (bound := fun _ => C)
      (s := ball p ρ) (x₀ := p) (Metric.ball_mem_nhds p hρ) ?_ ?_ ?_ ?_ ?_ ?_
    · filter_upwards [Metric.ball_mem_nhds p hρ] with q hq
      exact (section_continuous h₁ (hρsub (Metric.ball_subset_closedBall hq))).aestronglyMeasurable
    · exact hint1 p hp
    · exact (section_continuous h₂ hp).aestronglyMeasurable
    · filter_upwards with x
      intro q hq
      exact hC q (Metric.ball_subset_closedBall hq) x
    · exact integrable_const C
    · filter_upwards with x
      intro q hq
      exact hd₂ q (hρsub (Metric.ball_subset_closedBall hq)) x
  have hcont2 : ContinuousOn (fun p => ∫ x, Φ₂ p x ∂μ) s := by
    intro p hp
    obtain ⟨ρ, hρ, hρsub, C, hC⟩ := hb₂ p hp
    refine (continuousAt_of_dominated (μ := μ) (F := fun p x => Φ₂ p x) (x₀ := p)
      (bound := fun _ => C) ?_ ?_ ?_ ?_).continuousWithinAt
    · filter_upwards [Metric.ball_mem_nhds p hρ] with q hq
      exact (section_continuous h₂ (hρsub (Metric.ball_subset_closedBall hq))).aestronglyMeasurable
    · filter_upwards [Metric.ball_mem_nhds p hρ] with q hq
      filter_upwards with x
      exact hC q (Metric.ball_subset_closedBall hq) x
    · exact integrable_const C
    · filter_upwards with x
      exact section_continuousAt hs h₂ hp x
  exact ⟨hderiv2, fun p hp => (hderiv2 p hp).fderiv, hcont2⟩

/-- **`C²` regularity of a parametric integral.**  Combining the first and second order
differentiation under the integral sign. -/
theorem contDiffOn_two_parametric_integral_aux {n : ℕ} {μ : Measure (𝕊 n)}
    [IsFiniteMeasure μ]
    {s : Set (𝔼 n)} (hs : IsOpen s)
    (Φ₀ : 𝔼 n → 𝕊 n → ℝ) (Φ₁ : 𝔼 n → 𝕊 n → 𝔼 n →L[ℝ] ℝ)
    (Φ₂ : 𝔼 n → 𝕊 n → 𝔼 n →L[ℝ] (𝔼 n →L[ℝ] ℝ))
    (h₀ : ContinuousOn (Function.uncurry Φ₀) (s ×ˢ Set.univ))
    (h₁ : ContinuousOn (Function.uncurry Φ₁) (s ×ˢ Set.univ))
    (h₂ : ContinuousOn (Function.uncurry Φ₂) (s ×ˢ Set.univ))
    (hb₂ : ∀ p ∈ s, ∃ ρ > 0, closedBall p ρ ⊆ s ∧
      ∃ C, ∀ q ∈ closedBall p ρ, ∀ x, ‖Φ₂ q x‖ ≤ C)
    (hd₁ : ∀ p ∈ s, ∀ x, HasFDerivAt (fun q => Φ₀ q x) (Φ₁ p x) p)
    (hd₂ : ∀ p ∈ s, ∀ x, HasFDerivAt (fun q => Φ₁ q x) (Φ₂ p x) p) :
    ContDiffOn ℝ 2 (fun p => ∫ x, Φ₀ p x ∂μ) s ∧
    (∀ p ∈ s, fderiv ℝ (fun p => ∫ x, Φ₀ p x ∂μ) p = ∫ x, Φ₁ p x ∂μ) ∧
    (∀ p ∈ s, fderiv ℝ (fun p => ∫ x, Φ₁ p x ∂μ) p = ∫ x, Φ₂ p x ∂μ) := by
  obtain ⟨hderiv1, hf1⟩ := hasFDerivAt_integral_one_parametric (μ := μ) hs Φ₀ Φ₁ h₀ h₁ hd₁
  obtain ⟨hderiv2, hf2, hcont2⟩ :=
    hasFDerivAt_integral_two_parametric (μ := μ) hs Φ₁ Φ₂ h₁ h₂ hb₂ hd₂
  refine ⟨?_, hf1, hf2⟩
  rw [hs.contDiffOn_iff]
  intro p hp
  have hA : ContDiffAt ℝ 2 (fun p => ∫ x, Φ₀ p x ∂μ) p := by
    have h := (contDiffAt_succ_iff_hasFDerivAt (𝕜 := ℝ)
      (f := fun p => ∫ x, Φ₀ p x ∂μ) (x := p) (n := 1)).mpr
      ⟨fun p => ∫ x, Φ₁ p x ∂μ, ⟨s, hs.mem_nhds hp, fun q hq => hderiv1 q hq⟩, ?_⟩
    · simpa only [Nat.cast_one, one_add_one_eq_two] using h
    have hB : ContDiffAt ℝ 1 (fun p => ∫ x, Φ₁ p x ∂μ) p := by
      have h' := (contDiffAt_succ_iff_hasFDerivAt (𝕜 := ℝ)
        (f := fun p => ∫ x, Φ₁ p x ∂μ) (x := p) (n := 0)).mpr
        ⟨fun p => ∫ x, Φ₂ p x ∂μ, ⟨s, hs.mem_nhds hp, fun q hq => hderiv2 q hq⟩, ?_⟩
      · simpa only [Nat.cast_zero, zero_add] using h'
      exact (contDiffAt_zero (𝕜 := ℝ)).mpr ⟨s, hs.mem_nhds hp, hcont2⟩
    exact hB
  exact hA

end Parametric

end KernelCalc

end


local notation "𝔼" n:max => EuclideanSpace ℝ (Fin n)
local notation "𝕊" n:max => sphere (0 : EuclideanSpace ℝ (Fin n)) 1

/-- **The Poisson integral for the ball is `C²` and harmonic.**
For `n > 0`, a ball `ball c R` with `R > 0` and continuous boundary data `g` on `sphere c R`,
the function
`x ↦ ∫ u, (R^n/(A R^2)) * (R^2 - ‖x - c‖^2) * ‖x - c - R • u‖⁻ⁿ * g (c + R • u) ∂σ(u)`
(where `A = volume.toSphere univ` is the surface area of the unit sphere and `σ = volume.toSphere`
is the Haar measure on the unit sphere) is `C²` on `ball c R` and has vanishing Laplacian there.

Suggested approach: for `x` with `‖x - c‖ < R`, differentiate twice under the integral sign using
`MeasureTheory.hasFDerivAt_integral_of_dominated_of_fderiv_le`.  The `x`-derivative of the kernel
`y ↦ (R² - ‖y-c‖²)·‖y - c - v‖⁻ⁿ` (with `v = R • u`) is
`(R²-‖x-c‖²) • (-(n:ℝ)*‖x-c-v‖^{-(n+2)} • innerSL ℝ (x-c-v)) + ‖x-c-v‖^{-n} • ((-2:ℝ) • innerSL ℝ (x-c))`.
Use the `MeasureTheory.Measure.toSphere` API (`MeasureTheory.Measure.toSphere_apply_univ`,
`MeasureTheory.Measure.toSphere.real`), `IsFiniteMeasure` for the sphere measure, continuity of `u`
on the compact sphere to obtain integrability, and compactness of `closedBall x₀ ρ × univ`
(with `ρ < R - ‖x₀-c‖`) to obtain uniform bounds on the derivatives. -/
theorem contDiffOn_two_poissonIntegral {n : ℕ} (hn : 0 < n)
    {c : EuclideanSpace ℝ (Fin n)} {R : ℝ} (hR : 0 < R)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : ContinuousOn g (sphere c R)) :
    let A : ℝ := (MeasureTheory.volume : Measure
      (EuclideanSpace ℝ (Fin n))).toSphere.real Set.univ
    ContDiffOn ℝ 2 (fun x : EuclideanSpace ℝ (Fin n) =>
        ∫ u : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          (R^n / (A * R^2))
            * ((R^2 - ‖x - c‖^2) * (‖x - c - R • (u : EuclideanSpace ℝ (Fin n))‖^n)⁻¹)
            * g (c + R • (u : EuclideanSpace ℝ (Fin n)))
        ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere) (ball c R)
      ∧ (∀ x ∈ ball c R, Laplacian.laplacian (fun x : EuclideanSpace ℝ (Fin n) =>
        ∫ u : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          (R^n / (A * R^2))
            * ((R^2 - ‖x - c‖^2) * (‖x - c - R • (u : EuclideanSpace ℝ (Fin n))‖^n)⁻¹)
            * g (c + R • (u : EuclideanSpace ℝ (Fin n)))
        ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere) x = 0) := by
  intro A
  have hR0 : (0:ℝ) ≤ R := le_of_lt hR
  haveI hCpt : CompactSpace (𝕊 n) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : 𝔼 n) 1)
  let μ0 : Measure (𝕊 n) := (MeasureTheory.volume : Measure (𝔼 n)).toSphere
  haveI hfin : IsFiniteMeasure μ0 := by dsimp only [μ0]; infer_instance
  let gf : 𝕊 n → ℝ := fun u => g (c + R • (u : 𝔼 n))
  let Φ0 : 𝔼 n → 𝕊 n → ℝ := fun x u =>
    (R^n / (A * R^2)) * ((R^2 - ‖x - c‖^2) * (‖x - c - R • (u : 𝔼 n)‖^n)⁻¹) * gf u
  let Φ1 : 𝔼 n → 𝕊 n → 𝔼 n →L[ℝ] ℝ := fun x u =>
    ((R^n / (A * R^2)) * gf u) • baseD1 (n := n) c (sphPt c R u) R x
  let Φ2 : 𝔼 n → 𝕊 n → 𝔼 n →L[ℝ] (𝔼 n →L[ℝ] ℝ) := fun x u =>
    ((R^n / (A * R^2)) * gf u) • baseD2 (n := n) c (sphPt c R u) R x
  let F : 𝔼 n → ℝ := fun x => ∫ u, Φ0 x u ∂μ0
  change ContDiffOn ℝ 2 F (ball c R) ∧ (∀ x ∈ ball c R, Laplacian.laplacian F x = 0)
  have hgf_cont : Continuous gf := by
    show Continuous fun u : 𝕊 n => g (sphPt c R u)
    exact continuous_comp_sphPt_g (c := c) (R := R) hg hR0
  have hgfOn : ContinuousOn (fun p : 𝔼 n × 𝕊 n => gf p.2) (ball c R ×ˢ Set.univ) :=
    (hgf_cont.comp continuous_snd).continuousOn
  have h₀ : ContinuousOn (Function.uncurry Φ0) (ball c R ×ˢ Set.univ) := by
    have hk : ContinuousOn (fun p : 𝔼 n × 𝕊 n => pKbase c (sphPt c R p.2) R p.1)
        (ball c R ×ˢ Set.univ) := continuousOn_pKbase_sphere (c := c) (R := R) hR0
    have h : ContinuousOn (fun p : 𝔼 n × 𝕊 n =>
        (R^n / (A * R^2)) * pKbase c (sphPt c R p.2) R p.1 * gf p.2)
        (ball c R ×ˢ Set.univ) :=
      ((hk.const_mul (R^n / (A * R^2))).mul hgfOn).congr (fun p hp => by simp only [Pi.mul_apply])
    have hfun : (fun p : 𝔼 n × 𝕊 n =>
          (R^n / (A * R^2)) * pKbase c (sphPt c R p.2) R p.1 * gf p.2)
        = Function.uncurry Φ0 := by
      funext p
      simp only [Function.uncurry, Φ0, gf, pKbase, sphPt, sub_sub]
    rwa [hfun] at h
  have h₁ : ContinuousOn (Function.uncurry Φ1) (ball c R ×ˢ Set.univ) := by
    have hb : ContinuousOn (fun p : 𝔼 n × 𝕊 n => baseD1 (n := n) c (sphPt c R p.2) R p.1)
        (ball c R ×ˢ Set.univ) := continuousOn_baseD1_sphere (c := c) (R := R) hR0
    have h : ContinuousOn (fun p : 𝔼 n × 𝕊 n =>
        ((R^n / (A * R^2)) * gf p.2) • baseD1 (n := n) c (sphPt c R p.2) R p.1)
        (ball c R ×ˢ Set.univ) := (hgfOn.const_mul (R^n / (A * R^2))).smul hb
    have hfun : (fun p : 𝔼 n × 𝕊 n =>
          ((R^n / (A * R^2)) * gf p.2) • baseD1 (n := n) c (sphPt c R p.2) R p.1)
        = Function.uncurry Φ1 := rfl
    rwa [hfun] at h
  have h₂ : ContinuousOn (Function.uncurry Φ2) (ball c R ×ˢ Set.univ) := by
    have hb : ContinuousOn (fun p : 𝔼 n × 𝕊 n => baseD2 (n := n) c (sphPt c R p.2) R p.1)
        (ball c R ×ˢ Set.univ) := continuousOn_baseD2_sphere (c := c) (R := R) hR0
    have h : ContinuousOn (fun p : 𝔼 n × 𝕊 n =>
        ((R^n / (A * R^2)) * gf p.2) • baseD2 (n := n) c (sphPt c R p.2) R p.1)
        (ball c R ×ˢ Set.univ) := (hgfOn.const_mul (R^n / (A * R^2))).smul hb
    have hfun : (fun p : 𝔼 n × 𝕊 n =>
          ((R^n / (A * R^2)) * gf p.2) • baseD2 (n := n) c (sphPt c R p.2) R p.1)
        = Function.uncurry Φ2 := rfl
    rwa [hfun] at h
  have hd₁ : ∀ p ∈ ball c R, ∀ x, HasFDerivAt (fun q => Φ0 q x) (Φ1 p x) p := by
    intro p hp x
    have hx : p ≠ sphPt c R x := ne_sphPt_of_mem_ball (c := c) (R := R) hR0 hp x
    have hbase := hasFDerivAt_pKbase (n := n) (c := c) (ξ := sphPt c R x) (R := R) hx
    have h2 := hbase.const_mul (R^n / (A * R^2))
    have h3 := h2.mul_const (gf x)
    have hfun : (fun q => Φ0 q x)
        = fun q => (R^n / (A * R^2)) * pKbase c (sphPt c R x) R q * gf x := by
      funext q
      simp only [Φ0, gf, pKbase, sphPt, sub_sub]
    rw [hfun]
    refine h3.congr_fderiv ?_
    have hyl : gf x • ((R^n / (A * R^2)) • baseD1 (n := n) c (sphPt c R x) R p) = Φ1 p x := by
      rw [smul_smul, mul_comm]
    rw [hyl]
  have hd₂ : ∀ p ∈ ball c R, ∀ x, HasFDerivAt (fun q => Φ1 q x) (Φ2 p x) p := by
    intro p hp x
    have hx : p ≠ sphPt c R x := ne_sphPt_of_mem_ball (c := c) (R := R) hR0 hp x
    have h := (hasFDerivAt_baseD1 (n := n) (c := c) (ξ := sphPt c R x) (R := R) hx).const_smul
      ((R^n / (A * R^2)) * gf x)
    have hfun : (fun q => Φ1 q x)
        = fun q => ((R^n / (A * R^2)) * gf x) • baseD1 (n := n) c (sphPt c R x) R q := by
      funext q; rfl
    rw [hfun]
    refine h.congr_fderiv ?_
    simp only [Φ2]
  obtain ⟨hC2, hdF1, hdG1, hf1, hf2⟩ :=
    Commons.Analysis.Calculus.contDiffOn_two_parametric_integral (μ := μ0) (s := ball c R)
      isOpen_ball Φ0 Φ1 Φ2 h₀ h₁ h₂ hd₁ hd₂
  refine ⟨hC2, ?_⟩
  intro x hx
  set b := stdOrthonormalBasis ℝ (𝔼 n) with hb
  have hb1 : ∀ i, ‖b i‖ = 1 := fun i => b.orthonormal.norm_eq_one i
  have hΦ2int := Commons.Analysis.Calculus.integrable_slice_of_continuousOn_uncurry
      (f := Φ2) (s := ball c R) (P := 𝔼 n) (X := 𝕊 n)
      (E := 𝔼 n →L[ℝ] (𝔼 n →L[ℝ] ℝ)) (μ := μ0) hx h₂
  have hcont1 : ∀ i, ContinuousOn (Function.uncurry (fun q u => (Φ2 q u) (b i)))
      (ball c R ×ˢ Set.univ) := by
    intro i
    exact h₂.clm_apply continuous_const.continuousOn
  have hcont2 : ∀ i, ContinuousOn (Function.uncurry (fun q u => (Φ2 q u) (b i) (b i)))
      (ball c R ×ˢ Set.univ) := by
    intro i
    exact (h₂.clm_apply continuous_const.continuousOn).clm_apply continuous_const.continuousOn
  have hΦ2int1 : ∀ i, Integrable (fun u => (Φ2 x u) (b i)) μ0 := by
    intro i
    exact Commons.Analysis.Calculus.integrable_slice_of_continuousOn_uncurry
      (f := fun q u => (Φ2 q u) (b i)) (s := ball c R) (P := 𝔼 n) (X := 𝕊 n)
      (E := 𝔼 n →L[ℝ] ℝ) (μ := μ0) hx (hcont1 i)
  have hΦ2int2 : ∀ i, Integrable (fun u => (Φ2 x u) (b i) (b i)) μ0 := by
    intro i
    exact Commons.Analysis.Calculus.integrable_slice_of_continuousOn_uncurry
      (f := fun q u => (Φ2 q u) (b i) (b i)) (s := ball c R) (P := 𝔼 n) (X := 𝕊 n)
      (E := ℝ) (μ := μ0) hx (hcont2 i)
  have hfderiv : fderiv ℝ (fderiv ℝ F) x = ∫ u, Φ2 x u ∂μ0 := by
    have h1 : (fderiv ℝ F) =ᶠ[𝓝 x] (fun p => ∫ u, Φ1 p u ∂μ0) := by
      filter_upwards [isOpen_ball.mem_nhds hx] with p hp
      exact hf1 p hp
    rw [h1.fderiv_eq, hf2 x hx]
  have hpoint : ∀ u, (∑ i, (Φ2 x u) (b i) (b i)) = 0 := by
    intro u
    have hxξ : x ≠ sphPt c R u := ne_sphPt_of_mem_ball (c := c) (R := R) hR0 hx u
    have hsum0 : (∑ i, baseD2 (n := n) c (sphPt c R u) R x (b i) (b i)) = 0 := by
      have hterm : ∀ i, baseD2 (n := n) c (sphPt c R u) R x (b i) (b i)
          = bilinearIteratedFDerivTwo ℝ (pKbase (n := n) c (sphPt c R u) R) x (b i) (b i) := by
        intro i
        rw [baseD2_eq_fderiv (c := c) (R := R) hxξ,
          bilinearIteratedFDerivTwo_eq_iteratedFDeriv, iteratedFDeriv_two_apply]
        simp
      rw [Finset.sum_congr rfl (fun i _ => hterm i),
        ← Commons.Analysis.Calculus.FDeriv.laplacian_eq_sum_second_partials b
            (pKbase (n := n) c (sphPt c R u) R) x]
      exact laplacian_base_eq_zero (n := n) (c := c) (ξ := sphPt c R u) (R := R)
        (by rw [norm_sphPt_sub, abs_of_nonneg hR0]) hxξ
    have hK : (∑ i, (Φ2 x u) (b i) (b i))
        = ((R^n / (A * R^2)) * gf u) * (∑ i, baseD2 (n := n) c (sphPt c R u) R x (b i) (b i)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [Φ2, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [hK, hsum0, mul_zero]
  rw [Commons.Analysis.Calculus.FDeriv.laplacian_eq_sum_second_partials b F x]
  have hterm : ∀ i, bilinearIteratedFDerivTwo ℝ F x (b i) (b i)
      = (fderiv ℝ (fderiv ℝ F) x) (b i) (b i) := by
    intro i
    rw [bilinearIteratedFDerivTwo_eq_iteratedFDeriv, iteratedFDeriv_two_apply]
    simp
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  have hA : ∀ i, (fderiv ℝ (fderiv ℝ F) x) (b i) (b i) = ∫ u, (Φ2 x u) (b i) (b i) ∂μ0 := by
    intro i
    rw [hfderiv, ContinuousLinearMap.integral_apply hΦ2int (b i),
      ContinuousLinearMap.integral_apply (hΦ2int1 i) (b i)]
  rw [Finset.sum_congr rfl (fun i _ => hA i),
    ← integral_finsetSum Finset.univ (fun i _ => hΦ2int2 i),
    integral_congr_ae (Filter.Eventually.of_forall hpoint), integral_zero]


end Commons.Analysis.Calculus.Laplacian
