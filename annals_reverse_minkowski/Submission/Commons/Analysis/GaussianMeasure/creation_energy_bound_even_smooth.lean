import Mathlib
import Submission.Commons.Analysis.GaussianMeasure.brascamp_lieb_truncated
import Submission.Commons.Analysis.Calculus.FDeriv.laplacian_eq_sum_second_partials
import Submission.Commons.Analysis.MeasureTheory.weighted_divergence_growth
import Submission.Commons.Analysis.GaussianMeasure.even_bl_hessian_energy
import Submission.Commons.Analysis.GaussianMeasure.integrable_mul_exp_neg_stronglyConvex
open MeasureTheory Real
open scoped Real Topology InnerProductSpace BigOperators
noncomputable section
namespace Commons.Analysis.GaussianMeasure
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
set_option maxHeartbeats 2000000
open Commons.Analysis.GaussianMeasure

private lemma inner_single_right' (v : E) (i : Fin n) : ⟪v, EuclideanSpace.single i 1⟫_ℝ = v i := by
  rw [real_inner_comm, show (v i) = v.ofLp i from rfl]
  simpa using EuclideanSpace.inner_single_left i 1 v

private noncomputable def Hfield (u : E → ℝ) : E → E := fun y => hessOp u y (grad u y)

private lemma differentiableAt_grad (u : E → ℝ) (hu : ContDiff ℝ 2 u) (x : E) :
    DifferentiableAt ℝ (grad u) x := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (m := 1) (by norm_num)
  have hc : DifferentiableAt ℝ (fderiv ℝ u) x := h1.contDiffAt.differentiableAt (by norm_num)
  let Tc : StrongDual ℝ E →L[ℝ] E := (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearMap
  have hg : grad u = Tc ∘ (fderiv ℝ u) := rfl
  rw [hg]; exact Tc.differentiableAt.comp x hc

private lemma fderiv_grad (φ : E → ℝ) (hφ : ContDiff ℝ 2 φ) (x : E) :
    fderiv ℝ (grad φ) x = hessOp φ x := by
  have hdiff : DifferentiableAt ℝ (fderiv ℝ φ) x :=
    ((hφ.fderiv_right (m := 1) (by norm_num)).contDiffAt).differentiableAt (by norm_num)
  have h1 : HasFDerivAt (fderiv ℝ φ) (fderiv ℝ (fderiv ℝ φ) x) x := hdiff.hasFDerivAt
  let Tc : StrongDual ℝ E →L[ℝ] E := (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearMap
  have h2 : HasFDerivAt (fun y : StrongDual ℝ E => (InnerProductSpace.toDual ℝ E).symm y) Tc
      (fderiv ℝ φ x) := ContinuousLinearMap.hasFDerivAt Tc
  have h3 := h2.comp x h1
  have hgrad : grad φ
      = (fun y : StrongDual ℝ E => (InnerProductSpace.toDual ℝ E).symm y) ∘ (fderiv ℝ φ) := rfl
  rw [hgrad, h3.fderiv]
  rfl

private lemma fderiv_Hfield (u : E → ℝ) (hu : ContDiff ℝ 3 u) (x : E) :
    fderiv ℝ (Hfield u) x
      = ((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearMap).comp
          ((fderiv ℝ (fderiv ℝ u) x).comp (hessOp u x)
            + (fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x).flip (grad u x)) := by
  have h2 : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ u)) :=
    (hu.fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)
  have hcd : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ u)) x :=
    h2.contDiffAt.differentiableAt (by norm_num)
  have hgd : DifferentiableAt ℝ (grad u) x := differentiableAt_grad u (hu.of_le (m := 2) (by norm_num)) x
  let Tc : StrongDual ℝ E →L[ℝ] E := (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearMap
  set β : E → StrongDual ℝ E := fun y => (fderiv ℝ (fderiv ℝ u) y) (grad u y) with hβ
  have hβd : DifferentiableAt ℝ β x := hcd.clm_apply hgd
  have hβder : fderiv ℝ β x
      = (fderiv ℝ (fderiv ℝ u) x).comp (fderiv ℝ (grad u) x)
        + (fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x).flip (grad u x) := by
    rw [hβ, fderiv_clm_apply hcd hgd]
  have heq : Hfield u = (fun z : StrongDual ℝ E => (InnerProductSpace.toDual ℝ E).symm z) ∘ β := by
    funext y
    simp only [Function.comp_apply, Hfield, hessOp, hβ]
    rfl
  have hTd : DifferentiableAt ℝ (fun z : StrongDual ℝ E => (InnerProductSpace.toDual ℝ E).symm z) (β x) :=
    Tc.differentiableAt
  rw [heq, fderiv_comp x hTd hβd, hβder]
  have hthis : fderiv ℝ (fun z : StrongDual ℝ E => (InnerProductSpace.toDual ℝ E).symm z) (β x) = Tc :=
    ContinuousLinearMap.fderiv Tc
  rw [hthis, fderiv_grad u (hu.of_le (by norm_num)) x]


private lemma third_symm (u : E → ℝ) (hu : ContDiff ℝ 3 u) (x a b γ : E) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x a b γ = fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x b a γ := by
  have h1 : ContDiff ℝ 2 (fderiv ℝ u) := hu.fderiv_right (m := 2) (by norm_num)
  have hs := h1.contDiffAt.isSymmSndFDerivAt (x := x) (by norm_num)
  have h := hs.eq a b
  exact DFunLike.congr_fun h γ


private lemma laplacian_eq_sum_psi (u : E → ℝ) (x : E) :
    Laplacian.laplacian u x
      = ∑ i : Fin n, (fderiv ℝ (fderiv ℝ u) x) (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) := by
  rw [Commons.Analysis.Calculus.FDeriv.laplacian_eq_sum_second_partials
        (EuclideanSpace.basisFun (Fin n) ℝ) u x]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [EuclideanSpace.basisFun_apply, bilinearIteratedFDerivTwo_eq_iteratedFDeriv,
      iteratedFDeriv_two_apply]
  simp

private lemma fderiv_secondPartial (u : E → ℝ) (hu : ContDiff ℝ 3 u) (i : Fin n) (x v : E) :
    fderiv ℝ (fun y => (fderiv ℝ (fderiv ℝ u) y) (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) x v
      = (fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x v) (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) := by
  have h2 : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ u)) :=
    (hu.fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)
  have hcd : DifferentiableAt ℝ (fun y => fderiv ℝ (fderiv ℝ u) y) x :=
    h2.contDiffAt.differentiableAt (by norm_num)
  have hFi' : fderiv ℝ (fun y => (fderiv ℝ (fderiv ℝ u) y) (EuclideanSpace.single i 1)) x
      = (fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x).flip (EuclideanSpace.single i 1) := by
    rw [fderiv_clm_apply (c := fun y => fderiv ℝ (fderiv ℝ u) y)
      (u := fun _ : E => EuclideanSpace.single i 1) hcd (differentiableAt_const _)]
    simp
  have hFid : DifferentiableAt ℝ (fun y => (fderiv ℝ (fderiv ℝ u) y) (EuclideanSpace.single i 1)) x :=
    hcd.clm_apply (differentiableAt_const _)
  have hψ := fderiv_clm_apply (c := fun y => (fderiv ℝ (fderiv ℝ u) y) (EuclideanSpace.single i 1))
    (u := fun _ : E => EuclideanSpace.single i 1) hFid (differentiableAt_const _)
  rw [hψ, hFi']
  simp

private lemma fderiv_laplacian_apply (u : E → ℝ) (hu : ContDiff ℝ 3 u) (x v : E) :
    fderiv ℝ (Laplacian.laplacian u) x v
      = ∑ i : Fin n, (fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x v) (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) := by
  have h2 : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ u)) :=
    (hu.fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)
  have hcd : DifferentiableAt ℝ (fun y => fderiv ℝ (fderiv ℝ u) y) x :=
    h2.contDiffAt.differentiableAt (by norm_num)
  have hdA : ∀ i : Fin n, DifferentiableAt ℝ
      (fun y => (fderiv ℝ (fderiv ℝ u) y) (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) x :=
    fun i => (hcd.clm_apply (differentiableAt_const _)).clm_apply (differentiableAt_const _)
  have hlapl : Laplacian.laplacian u = (∑ i : Fin n, fun y : E =>
      (fderiv ℝ (fderiv ℝ u) y) (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) := by
    funext y
    rw [Finset.sum_apply]
    exact laplacian_eq_sum_psi u y
  rw [hlapl, fderiv_sum (fun i _ => hdA i)]
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact fderiv_secondPartial u hu i x v


private lemma Tc_coord' (L : E →L[ℝ] (E →L[ℝ] ℝ)) (i : Fin n) :
    (((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearMap).comp L)
        (EuclideanSpace.single i 1) i
      = (L (EuclideanSpace.single i 1)) (EuclideanSpace.single i 1) := by
  rw [ContinuousLinearMap.comp_apply]
  change ((InnerProductSpace.toDual ℝ E).symm (L (EuclideanSpace.single i 1))) i
      = (L (EuclideanSpace.single i 1)) (EuclideanSpace.single i 1)
  rw [show (((InnerProductSpace.toDual ℝ E).symm (L (EuclideanSpace.single i 1))) i)
        = ⟪(InnerProductSpace.toDual ℝ E).symm (L (EuclideanSpace.single i 1)), EuclideanSpace.single i 1⟫_ℝ
      from (inner_single_right' _ _).symm]
  exact InnerProductSpace.toDual_symm_apply

private lemma hess_diag (u : E → ℝ) (hu : ContDiff ℝ 2 u) (x : E) (i : Fin n) :
    ((fderiv ℝ (fderiv ℝ u) x) (hessOp u x (EuclideanSpace.single i 1))) (EuclideanSpace.single i 1)
      = ∑ j : Fin n, (fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) ^ 2 := by
  rw [← hessOp_spec u x (hessOp u x (EuclideanSpace.single i 1)) (EuclideanSpace.single i 1)]
  rw [hessOp_symm u hu x (hessOp u x (EuclideanSpace.single i 1)) (EuclideanSpace.single i 1)]
  have h := OrthonormalBasis.sum_inner_mul_inner (EuclideanSpace.basisFun (Fin n) ℝ)
      (hessOp u x (EuclideanSpace.single i 1)) (hessOp u x (EuclideanSpace.single i 1))
  simp only [EuclideanSpace.basisFun_apply] at h
  rw [← h]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have e1 : ⟪(hessOp u x) (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ
      = (fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1)) (EuclideanSpace.single j 1) :=
    hessOp_spec u x _ _
  have e2 : ⟪EuclideanSpace.single j 1, (hessOp u x) (EuclideanSpace.single i 1)⟫_ℝ
      = (fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1)) (EuclideanSpace.single j 1) := by
    rw [real_inner_comm]; exact e1
  rw [e1, e2]; ring

private lemma mixed_sum (u : E → ℝ) (hu : ContDiff ℝ 3 u) (x : E) :
    (∑ i : Fin n, (fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x (EuclideanSpace.single i 1) (grad u x)) (EuclideanSpace.single i 1))
      = ⟪grad (fun y => Laplacian.laplacian u y) x, grad u x⟫_ℝ := by
  rw [grad_spec, fderiv_laplacian_apply u hu x (grad u x)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact third_symm u hu x (EuclideanSpace.single i 1) (grad u x) (EuclideanSpace.single i 1)

private lemma divHfield_eq (u : E → ℝ) (hu : ContDiff ℝ 3 u) (x : E) :
    (∑ i : Fin n, (fderiv ℝ (Hfield u) x (EuclideanSpace.single i 1)) i)
      = ⟪grad (fun y => Laplacian.laplacian u y) x, grad u x⟫_ℝ
        + ∑ i : Fin n, ∑ j : Fin n,
            (fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) ^ 2 := by
  have key : ∀ i : Fin n, (fderiv ℝ (Hfield u) x (EuclideanSpace.single i 1)) i
      = (∑ j : Fin n, (fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) ^ 2)
        + (fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x (EuclideanSpace.single i 1) (grad u x)) (EuclideanSpace.single i 1) := by
    intro i
    rw [fderiv_Hfield u hu x, Tc_coord']
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
    rw [hess_diag u (hu.of_le (m := 2) (by norm_num)) x i]
  rw [Finset.sum_congr rfl (fun i _ => key i), Finset.sum_add_distrib, mixed_sum u hu x]
  ring




private lemma opNorm_le_of_apply2 (g : E → ℝ) (hg : ContDiff ℝ 2 g) {C : ℝ} (hC : 0 ≤ C) {N : ℕ}
    (h : ∀ x v w : E, |fderiv ℝ (fderiv ℝ g) x v w| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ * ‖w‖) (x : E) :
    ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ C * (1 + ‖x‖) ^ N := by
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC (pow_nonneg (by positivity) _)) ?_
  intro v
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (mul_nonneg hC (pow_nonneg (by positivity) _)) (norm_nonneg v)) ?_
  intro w
  rw [Real.norm_eq_abs]
  exact h x v w

private lemma opNorm_le_of_apply1 (g : E → ℝ) (hg : ContDiff ℝ 1 g) {C : ℝ} (hC : 0 ≤ C) {N : ℕ}
    (h : ∀ x v : E, |fderiv ℝ g x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖) (x : E) :
    ‖fderiv ℝ g x‖ ≤ C * (1 + ‖x‖) ^ N := by
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC (pow_nonneg (by positivity) _)) ?_
  intro v
  rw [Real.norm_eq_abs]
  exact h x v


open Commons.Analysis.GaussianMeasure

/-- Bound on the operator norm of the Hessian operator from the diagonal bound (using
self-adjointness). -/
private lemma hessOp_norm_le (g : E → ℝ) (hg : ContDiff ℝ 2 g) {C : ℝ} (hC : 0 ≤ C) {N : ℕ}
    (h : ∀ x v : E, |fderiv ℝ (fderiv ℝ g) x v v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ^ 2) (x : E) :
    ‖hessOp g x‖ ≤ C * (1 + ‖x‖) ^ N := by
  have hsym : LinearMap.IsSymmetric (hessOp g x).toLinearMap :=
    fun v w => hessOp_symm g hg x v w
  rw [show ‖hessOp g x‖ = ⨆ v, |(hessOp g x).rayleighQuotient v| from
    ContinuousLinearMap.norm_eq_iSup_rayleighQuotient (T := hessOp g x) hsym]
  refine ciSup_le (fun v => ?_)
  have hv : (hessOp g x).rayleighQuotient v = fderiv ℝ (fderiv ℝ g) x v v / ‖v‖ ^ 2 := by
    rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply,
        hessOp_spec]
    simp
  rw [hv, abs_div]
  rw [show |‖v‖ ^ 2| = ‖v‖ ^ 2 from abs_of_nonneg (by positivity)]
  rcases eq_or_ne ‖v‖ 0 with hv0 | hv0
  · rw [hv0]
    simp only [norm_zero, pow_two, mul_zero, div_zero]
    exact mul_nonneg hC (pow_nonneg (by positivity) _)
  · rw [div_le_iff₀ (by positivity)]
    exact h x v


private lemma flip_bound3 (u : E → ℝ) {C : ℝ} (hC : 0 ≤ C) {N : ℕ}
    (h : ∀ x v w z : E, |fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x v w z| ≤ C * (1+‖x‖)^N * ‖v‖*‖w‖*‖z‖)
    (x g : E) :
    ‖(fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x).flip g‖ ≤ C * (1 + ‖x‖) ^ N * ‖g‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (mul_nonneg hC (pow_nonneg (by positivity) _)) (norm_nonneg g)) (fun v => ?_)
  rw [ContinuousLinearMap.flip_apply]
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (mul_nonneg (mul_nonneg hC (pow_nonneg (by positivity) _)) (norm_nonneg g)) (norm_nonneg v))
    (fun w => ?_)
  rw [Real.norm_eq_abs]
  calc |(fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x) v g w| ≤ C * (1+‖x‖)^N * ‖v‖ * ‖g‖ * ‖w‖ := h x v g w
    _ = (C * (1 + ‖x‖) ^ N * ‖g‖ * ‖v‖) * ‖w‖ := by ring

private lemma flip_bound2 (f : E → ℝ) (hf : ContDiff ℝ 2 f) {C : ℝ} (hC : 0 ≤ C) {N : ℕ}
    (h : ∀ x v : E, |fderiv ℝ (fderiv ℝ f) x v v| ≤ C * (1+‖x‖)^N * ‖v‖ ^ 2) (x g : E) :
    ‖(fderiv ℝ (fderiv ℝ f) x).flip g‖ ≤ C * (1 + ‖x‖) ^ N * ‖g‖ := by
  have hH := hessOp_norm_le f hf hC h x
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (mul_nonneg hC (pow_nonneg (by positivity) _)) (norm_nonneg g)) (fun v => ?_)
  rw [ContinuousLinearMap.flip_apply]
  have hv : (fderiv ℝ (fderiv ℝ f) x) v g = ⟪hessOp f x v, g⟫_ℝ := (hessOp_spec f x v g).symm
  rw [hv]
  calc ‖⟪hessOp f x v, g⟫_ℝ‖ ≤ ‖hessOp f x v‖ * ‖g‖ := norm_inner_le_norm _ _
    _ ≤ (‖hessOp f x‖ * ‖v‖) * ‖g‖ :=
        mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg g)
    _ ≤ ((C * (1 + ‖x‖) ^ N) * ‖v‖) * ‖g‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hH (norm_nonneg v)) (norm_nonneg g)
    _ = (C * (1 + ‖x‖) ^ N * ‖g‖) * ‖v‖ := by ring


private lemma fderiv_laplacian_norm_le (u : E → ℝ) (hu : ContDiff ℝ 3 u) {C : ℝ} (hC : 0 ≤ C) {N : ℕ}
    (h : ∀ x v w z : E, |fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x v w z| ≤ C * (1+‖x‖)^N * ‖v‖*‖w‖*‖z‖)
    (x : E) : ‖fderiv ℝ (fun y => Laplacian.laplacian u y) x‖ ≤ (n : ℝ) * C * (1 + ‖x‖) ^ N := by
  have hs : ∀ i : Fin n, ‖EuclideanSpace.single i (1:ℝ)‖ = 1 := by intro i; simp
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun v => ?_)
  rw [fderiv_laplacian_apply u hu x v]
  calc ‖∑ i : Fin n, (fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x v) (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)‖
      ≤ ∑ i : Fin n, ‖(fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x v) (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ i : Fin n, C * (1 + ‖x‖) ^ N * ‖v‖ := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        rw [Real.norm_eq_abs]
        simpa [hs i] using h x v (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)
    _ = (n : ℝ) * C * (1 + ‖x‖) ^ N * ‖v‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring


private lemma contDiff_laplacian (u : E → ℝ) (hu : ContDiff ℝ 3 u) :
    ContDiff ℝ 1 (fun y => Laplacian.laplacian u y) := by
  have h1u : ContDiff ℝ 2 (fderiv ℝ u) := hu.fderiv_right (m := 2) (by norm_num)
  have h2u : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ u)) := h1u.fderiv_right (m := 1) (by norm_num)
  have heq : (fun y => Laplacian.laplacian u y) = fun y => ∑ i : Fin n,
      (fderiv ℝ (fderiv ℝ u) y) (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) :=
    funext (fun y => laplacian_eq_sum_psi u y)
  rw [heq]
  exact ContDiff.sum (fun i _ => (h2u.clm_apply contDiff_const).clm_apply contDiff_const)

private lemma fderiv_Lu (f u : E → ℝ) (hf : ContDiff ℝ 2 f) (hu : ContDiff ℝ 3 u) (x : E) :
    fderiv ℝ (fun y => -Laplacian.laplacian u y + inner ℝ (grad f y) (grad u y)) x
      = -(fderiv ℝ (fun y => Laplacian.laplacian u y) x)
        + (fderiv ℝ f x).comp (hessOp u x)
        + (fderiv ℝ (fderiv ℝ f) x).flip (grad u x) := by
  have h1f : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (m := 1) (by norm_num)
  have hcd : DifferentiableAt ℝ (fderiv ℝ f) x := h1f.contDiffAt.differentiableAt (by norm_num)
  have h1u2 : ContDiff ℝ 2 (fderiv ℝ u) := hu.fderiv_right (m := 2) (by norm_num)
  have hgd : DifferentiableAt ℝ (grad u) x := by
    have hc : DifferentiableAt ℝ (fderiv ℝ u) x := h1u2.contDiffAt.differentiableAt (by norm_num)
    have hg : grad u = ((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearMap) ∘ (fderiv ℝ u) := rfl
    rw [hg]
    exact (ContinuousLinearMap.differentiableAt _).comp x hc
  have hcd2 : DifferentiableAt ℝ (fun y => (fderiv ℝ f y) (grad u y)) x :=
    hcd.clm_apply hgd
  have hcΔ : DifferentiableAt ℝ (fun y => -Laplacian.laplacian u y) x :=
    ((contDiff_laplacian u hu).contDiffAt.differentiableAt (by norm_num)).neg
  have heq : (fun y : E => -Laplacian.laplacian u y + inner ℝ (grad f y) (grad u y))
      = (fun y => -Laplacian.laplacian u y) + (fun y => (fderiv ℝ f y) (grad u y)) := by
    funext y; rw [grad_spec]; rfl
  have hneg : fderiv ℝ (fun y : E => -Laplacian.laplacian u y) x
      = -(fderiv ℝ (fun y : E => Laplacian.laplacian u y) x) := by
    have : (fun y : E => -Laplacian.laplacian u y) = -(fun y : E => Laplacian.laplacian u y) := rfl
    rw [this, fderiv_neg]
  rw [heq, fderiv_add hcΔ hcd2, hneg, fderiv_clm_apply hcd hgd]
  rw [fderiv_grad u (hu.of_le (m := 2) (by norm_num)) x]
  abel


open Commons.Analysis.MeasureTheory

/-- Growth bound for the sum-of-squares of the Hessian of `u`. -/
private lemma hess_sum_bound (u : E → ℝ) {Cu : ℝ} (hCu : 0 ≤ Cu) {Nu : ℕ}
    (h : ∀ x v w : E, |fderiv ℝ (fderiv ℝ u) x v w| ≤ Cu * (1+‖x‖)^Nu * ‖v‖ * ‖w‖) (x : E) :
    |∑ i : Fin n, ∑ j : Fin n,
      (fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) ^ 2|
      ≤ (n : ℝ) ^ 2 * Cu ^ 2 * (1 + ‖x‖) ^ (2 * Nu) := by
  have hs : ∀ i : Fin n, ‖EuclideanSpace.single i (1:ℝ)‖ = 1 := by intro i; simp
  rw [abs_of_nonneg (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _)))]
  have hterm : ∀ i j : Fin n,
      (fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) ^ 2
        ≤ Cu ^ 2 * (1 + ‖x‖) ^ (2 * Nu) := by
    intro i j
    have hb := h x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
    rw [hs i, hs j, mul_one, mul_one] at hb
    calc (fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) ^ 2
        = |fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ^ 2 := by rw [sq_abs]
      _ ≤ (Cu * (1 + ‖x‖) ^ Nu) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hb 2
      _ = Cu ^ 2 * (1 + ‖x‖) ^ (2 * Nu) := by rw [mul_pow, ← pow_mul, Nat.mul_comm Nu 2]
  calc (∑ i : Fin n, ∑ j : Fin n,
        (fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) ^ 2)
      ≤ ∑ i : Fin n, ∑ j : Fin n, Cu ^ 2 * (1 + ‖x‖) ^ (2 * Nu) :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hterm i j))
    _ = (n : ℝ) ^ 2 * Cu ^ 2 * (1 + ‖x‖) ^ (2 * Nu) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring


private lemma poly_add_le' {A B t : ℝ} {m n : ℕ} (ht : 1 ≤ t) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    A * t ^ m + B * t ^ n ≤ (A + B) * t ^ max m n := by
  have ht0 : 0 ≤ t := le_trans zero_le_one ht
  calc A * t ^ m + B * t ^ n ≤ A * t ^ max m n + B * t ^ max m n :=
        add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht (le_max_left _ _)) hA)
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht (le_max_right _ _)) hB)
    _ = (A + B) * t ^ max m n := by ring

private lemma poly_mul_le' {A B t : ℝ} {m n : ℕ} :
    (A * t ^ m) * (B * t ^ n) = (A * B) * t ^ (m + n) := by rw [pow_add]; ring

private lemma Δu_bound (u : E → ℝ) {Cu : ℝ} (hCu : 0 ≤ Cu) {Nu : ℕ}
    (h2 : ∀ x v w : E, |fderiv ℝ (fderiv ℝ u) x v w| ≤ Cu*(1+‖x‖)^Nu*‖v‖*‖w‖)
    (x : E) : |Laplacian.laplacian u x| ≤ (n : ℝ) * Cu * (1 + ‖x‖) ^ Nu := by
  rw [laplacian_eq_sum_psi u x]
  have hs : ∀ i : Fin n, ‖EuclideanSpace.single i (1:ℝ)‖ = 1 := by intro i; simp
  calc |∑ i : Fin n, (fderiv ℝ (fderiv ℝ u) x) (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)|
      ≤ ∑ i : Fin n, |(fderiv ℝ (fderiv ℝ u) x) (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin n, Cu * (1 + ‖x‖) ^ Nu := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        simpa [hs i] using (h2 x (EuclideanSpace.single i 1) (EuclideanSpace.single i 1))
    _ = (n : ℝ) * Cu * (1 + ‖x‖) ^ Nu := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring


private lemma integrable_poly_gauss {f Φ : E → ℝ} (hf : Continuous f)
    (hdec : ∃ c : ℝ, ∀ x : E, c + Real.pi * ‖x‖ ^ 2 ≤ f x)
    (hΦc : Continuous Φ) {C : ℝ} (hC : 0 ≤ C) {N : ℕ} (h : ∀ x, |Φ x| ≤ C * (1 + ‖x‖) ^ N) :
    Integrable (fun x : E => Φ x * Real.exp (-(f x))) := by
  obtain ⟨c, hc⟩ := hdec
  have hbound : ∀ x : E, ‖Φ x * Real.exp (-(f x))‖
      ≤ (C * Real.exp (-c)) * ((1 + ‖x‖) ^ N * Real.exp (-Real.pi * ‖x‖ ^ 2)) := by
    intro x
    have hxc : Real.exp (-(f x)) ≤ Real.exp (-c) * Real.exp (-Real.pi * ‖x‖ ^ 2) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith [hc x])
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc |Φ x| * Real.exp (-(f x)) ≤ (C * (1 + ‖x‖) ^ N) * (Real.exp (-c) * Real.exp (-Real.pi * ‖x‖ ^ 2)) :=
          mul_le_mul (h x) hxc (Real.exp_pos _).le (mul_nonneg hC (pow_nonneg (by positivity) _))
      _ = (C * Real.exp (-c)) * ((1 + ‖x‖) ^ N * Real.exp (-Real.pi * ‖x‖ ^ 2)) := by ring
  refine Integrable.mono'
    ((Commons.Measure.Integral.integrable_pow_mul_exp_neg_norm_sq Real.pi Real.pi_pos N).const_mul (C * Real.exp (-c)))
    (hΦc.aestronglyMeasurable.mul (Real.continuous_exp.comp hf.neg).aestronglyMeasurable) (Filter.Eventually.of_forall hbound)


private lemma coord_smul (a : ℝ) (v : E) (i : Fin n) : (a • v) i = a * v i := by
  rw [show ((a • v) i) = (a • v).ofLp i from rfl, show (v i) = v.ofLp i from rfl,
      PiLp.smul_apply, smul_eq_mul]

private lemma coord_add (v w : E) (i : Fin n) : (v + w) i = v i + w i := by
  rw [show ((v + w) i) = (v + w).ofLp i from rfl, show (v i) = v.ofLp i from rfl,
      show (w i) = w.ofLp i from rfl, PiLp.add_apply]

private lemma inner_single_left' (v : E) (i : Fin n) : ⟪EuclideanSpace.single i 1, v⟫_ℝ = v i := by
  rw [show (v i) = v.ofLp i from rfl]
  simpa using EuclideanSpace.inner_single_left i 1 v

private lemma sum_coord_mul (v w : E) : (∑ i : Fin n, (v i) * (w i)) = ⟪v, w⟫_ℝ := by
  have h := OrthonormalBasis.sum_inner_mul_inner (EuclideanSpace.basisFun (Fin n) ℝ) v w
  simp only [EuclideanSpace.basisFun_apply] at h
  rw [← h]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [inner_single_right', inner_single_left']

private lemma sum_hess_diag (ψ : E → ℝ) (x : E) :
    (∑ i : Fin n, ⟪(hessOp ψ x) (EuclideanSpace.single i 1), EuclideanSpace.single i 1⟫_ℝ)
      = Laplacian.laplacian ψ x := by
  rw [laplacian_eq_sum_psi ψ x]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hessOp_spec]

private lemma fderiv_smul_grad (φ ψ : E → ℝ) (x : E) (hφd : DifferentiableAt ℝ φ x)
    (hψ : ContDiff ℝ 2 ψ) :
    fderiv ℝ (fun y => φ y • grad ψ y) x
      = φ x • hessOp ψ x + (fderiv ℝ φ x).smulRight (grad ψ x) := by
  show fderiv ℝ (φ • grad ψ) x = φ x • hessOp ψ x + (fderiv ℝ φ x).smulRight (grad ψ x)
  rw [fderiv_smul (𝕜' := ℝ) hφd (differentiableAt_grad ψ hψ x), fderiv_grad ψ hψ x]

private lemma div_smul_grad (φ ψ : E → ℝ) (x : E) (hφd : DifferentiableAt ℝ φ x)
    (hψ : ContDiff ℝ 2 ψ) :
    (∑ i : Fin n, (fderiv ℝ (fun y => φ y • grad ψ y) x (EuclideanSpace.single i 1)) i)
      = ⟪grad φ x, grad ψ x⟫_ℝ + φ x * Laplacian.laplacian ψ x := by
  have key : ∀ i : Fin n,
      (fderiv ℝ (fun y => φ y • grad ψ y) x (EuclideanSpace.single i 1)) i
        = φ x * ⟪(hessOp ψ x) (EuclideanSpace.single i 1), EuclideanSpace.single i 1⟫_ℝ
          + (fderiv ℝ φ x (EuclideanSpace.single i 1)) * ⟪grad ψ x, EuclideanSpace.single i 1⟫_ℝ := by
    intro i
    rw [fderiv_smul_grad φ ψ x hφd hψ, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
        coord_add, coord_smul, coord_smul]
    rw [← inner_single_right' ((hessOp ψ x) (EuclideanSpace.single i 1)) i,
        ← inner_single_right' (grad ψ x) i]
  rw [Finset.sum_congr rfl (fun i _ => key i), Finset.sum_add_distrib]
  have h1 : (∑ i : Fin n, φ x * ⟪(hessOp ψ x) (EuclideanSpace.single i 1), EuclideanSpace.single i 1⟫_ℝ)
      = φ x * Laplacian.laplacian ψ x := by
    rw [← Finset.mul_sum, sum_hess_diag ψ x]
  have h2 : (∑ i : Fin n, (fderiv ℝ φ x (EuclideanSpace.single i 1)) * ⟪grad ψ x, EuclideanSpace.single i 1⟫_ℝ)
      = ⟪grad φ x, grad ψ x⟫_ℝ := by
    rw [← sum_coord_mul (grad φ x) (grad ψ x)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← grad_spec φ x (EuclideanSpace.single i 1),
        ← inner_single_right' (grad φ x) i, ← inner_single_right' (grad ψ x) i]
  rw [h1, h2, add_comm]

private theorem bochner_identity_smooth (f u : E → ℝ) (hf : ContDiff ℝ 2 f) (hu : ContDiff ℝ 3 u) (hdec : ∃ c : ℝ, ∀ x : E, c + Real.pi * ‖x‖ ^ 2 ≤ f x) (hgf : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x v : E, |fderiv ℝ f x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ∧ |fderiv ℝ (fderiv ℝ f) x v v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ^ 2) (hgu : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x v w z : E, |u x| ≤ C * (1 + ‖x‖) ^ N ∧ |fderiv ℝ u x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ∧ |fderiv ℝ (fderiv ℝ u) x v w| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ * ‖w‖ ∧ |fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x v w z| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ * ‖w‖ * ‖z‖) : (∫ x, (- Laplacian.laplacian u x + inner ℝ ((InnerProductSpace.toDual ℝ (E)).symm (fderiv ℝ f x)) ((InnerProductSpace.toDual ℝ (E)).symm (fderiv ℝ u x))) ^ 2 * Real.exp (-(f x))) = ∫ x, ((∑ i : Fin n, ∑ j : Fin n, ((fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1)) (EuclideanSpace.single j 1)) ^ 2) + (fderiv ℝ (fderiv ℝ f) x ((InnerProductSpace.toDual ℝ (E)).symm (fderiv ℝ u x)) ((InnerProductSpace.toDual ℝ (E)).symm (fderiv ℝ u x)))) * Real.exp (-(f x)) := by
  obtain ⟨Cf, hCf, Nf, hgf'⟩ := hgf
  obtain ⟨Cu, hCu, Nu, hgu'⟩ := hgu
  have hf1 : ContDiff ℝ 1 f := hf.of_le (m := 1) (by norm_num)
  have hfc : Continuous f := hf.continuous
  have hu2 : ContDiff ℝ 2 u := hu.of_le (m := 2) (by norm_num)
  have hu1 : ContDiff ℝ 1 u := hu.of_le (m := 1) (by norm_num)
  have h1u : ContDiff ℝ 2 (fderiv ℝ u) := hu.fderiv_right (m := 2) (by norm_num)
  have hgradcd : ContDiff ℝ 1 (grad u) := by
    have hg : grad u = (fun z : StrongDual ℝ E => (InnerProductSpace.toDual ℝ E).symm z) ∘ (fderiv ℝ u) := rfl
    rw [hg]
    exact ((InnerProductSpace.toDual ℝ E).symm.contDiff (n := 1)).comp (h1u.of_le (m := 1) (by norm_num))
  set φ : E → ℝ := fun y => -Laplacian.laplacian u y + inner ℝ (grad f y) (grad u y) with hφdef
  have hφcd : ContDiff ℝ 1 φ := by
    rw [hφdef]
    refine ((contDiff_laplacian u hu).neg).add ?_
    rw [show (fun y : E => inner ℝ (grad f y) (grad u y)) = fun y => (fderiv ℝ f y) (grad u y) by
      funext y; rw [grad_spec]]
    exact (hf.fderiv_right (m := 1) (by norm_num)).clm_apply hgradcd
  have hφd : ∀ x, DifferentiableAt ℝ φ x := fun x => hφcd.contDiffAt.differentiableAt (by norm_num)
  have DfB : ∀ x : E, ‖fderiv ℝ f x‖ ≤ Cf * (1 + ‖x‖) ^ Nf :=
    fun x => opNorm_le_of_apply1 f hf1 hCf (fun x v => (hgf' x v).1) x
  have hessfB : ∀ x : E, ‖hessOp f x‖ ≤ Cf * (1 + ‖x‖) ^ Nf :=
    fun x => hessOp_norm_le f hf hCf (fun x v => (hgf' x v).2) x
  have DuB : ∀ x : E, ‖fderiv ℝ u x‖ ≤ Cu * (1 + ‖x‖) ^ Nu :=
    fun x => opNorm_le_of_apply1 u hu1 hCu (fun x v => (hgu' x v 0 0).2.1) x
  have D2uB : ∀ x : E, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ Cu * (1 + ‖x‖) ^ Nu :=
    fun x => opNorm_le_of_apply2 u hu2 hCu (fun x v w => (hgu' x v w 0).2.2.1) x
  have hessuB : ∀ x : E, ‖hessOp u x‖ ≤ Cu * (1 + ‖x‖) ^ Nu := by
    intro x
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun v => ?_)
    rw [show hessOp u x v = (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (fderiv ℝ u) x v) from rfl,
        LinearIsometryEquiv.norm_map]
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun w => ?_)
    rw [Real.norm_eq_abs]
    exact (hgu' x v w 0).2.2.1
  have D3uB : ∀ x g : E, ‖(fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x).flip g‖ ≤ Cu * (1 + ‖x‖) ^ Nu * ‖g‖ :=
    fun x g => flip_bound3 u hCu (fun x v w z => (hgu' x v w z).2.2.2) x g
  have D2fB : ∀ x g : E, ‖(fderiv ℝ (fderiv ℝ f) x).flip g‖ ≤ Cf * (1 + ‖x‖) ^ Nf * ‖g‖ :=
    fun x g => flip_bound2 f hf hCf (fun x v => (hgf' x v).2) x g
  have ΔuB : ∀ x : E, |Laplacian.laplacian u x| ≤ (n : ℝ) * Cu * (1 + ‖x‖) ^ Nu :=
    fun x => Δu_bound u hCu (fun x v w => (hgu' x v w 0).2.2.1) x
  have DΔuB : ∀ x : E, ‖fderiv ℝ (fun y => Laplacian.laplacian u y) x‖ ≤ (n : ℝ) * Cu * (1 + ‖x‖) ^ Nu :=
    fun x => fderiv_laplacian_norm_le u hu hCu (fun x v w z => (hgu' x v w z).2.2.2) x
  have hpow1 : ∀ x : E, (1 : ℝ) ≤ 1 + ‖x‖ := fun x => le_add_of_nonneg_right (norm_nonneg x)
  have φB : ∀ x : E, |φ x| ≤ ((n : ℝ) * Cu + Cf * Cu) * (1 + ‖x‖) ^ (max Nu (Nf + Nu)) := by
    intro x
    have hp1 : |Laplacian.laplacian u x| ≤ ((n : ℝ) * Cu) * (1 + ‖x‖) ^ Nu := by
      simpa using ΔuB x
    have hp2 : |inner ℝ (grad f x) (grad u x)| ≤ (Cf * Cu) * (1 + ‖x‖) ^ (Nf + Nu) := by
      calc |inner ℝ (grad f x) (grad u x)| ≤ ‖grad f x‖ * ‖grad u x‖ := abs_real_inner_le_norm _ _
        _ ≤ (Cf * (1 + ‖x‖) ^ Nf) * (Cu * (1 + ‖x‖) ^ Nu) :=
            mul_le_mul (by rw [grad_norm_eq]; exact DfB x) (by rw [grad_norm_eq]; exact DuB x) (norm_nonneg _) (by positivity)
        _ = (Cf * Cu) * (1 + ‖x‖) ^ (Nf + Nu) := poly_mul_le'
    rw [hφdef]
    calc |(-Laplacian.laplacian u x) + inner ℝ (grad f x) (grad u x)|
        ≤ |Laplacian.laplacian u x| + |inner ℝ (grad f x) (grad u x)| := by
          calc |(-Laplacian.laplacian u x) + inner ℝ (grad f x) (grad u x)|
              ≤ |-(Laplacian.laplacian u x)| + |inner ℝ (grad f x) (grad u x)| := abs_add_le _ _
            _ = |Laplacian.laplacian u x| + |inner ℝ (grad f x) (grad u x)| := by rw [abs_neg]
      _ ≤ ((n : ℝ) * Cu) * (1 + ‖x‖) ^ Nu + (Cf * Cu) * (1 + ‖x‖) ^ (Nf + Nu) := add_le_add hp1 hp2
      _ ≤ ((n : ℝ) * Cu + Cf * Cu) * (1 + ‖x‖) ^ (max Nu (Nf + Nu)) :=
          poly_add_le' (hpow1 x) (by positivity) (by positivity)
  have DφB : ∀ x : E, ‖fderiv ℝ φ x‖ ≤ ((n : ℝ) * Cu + 2 * Cf * Cu) * (1 + ‖x‖) ^ (max Nu (Nf + Nu)) := by
    intro x
    rw [hφdef, fderiv_Lu f u hf hu x]
    have h1 : ‖-(fderiv ℝ (fun y => Laplacian.laplacian u y) x)‖ ≤ ((n : ℝ) * Cu) * (1 + ‖x‖) ^ Nu := by
      rw [norm_neg]; exact DΔuB x
    have h2 : ‖(fderiv ℝ f x).comp (hessOp u x)‖ ≤ (Cf * Cu) * (1 + ‖x‖) ^ (Nf + Nu) := by
      calc ‖(fderiv ℝ f x).comp (hessOp u x)‖ ≤ ‖fderiv ℝ f x‖ * ‖hessOp u x‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ (Cf * (1 + ‖x‖) ^ Nf) * (Cu * (1 + ‖x‖) ^ Nu) :=
            mul_le_mul (DfB x) (hessuB x) (norm_nonneg _) (by positivity)
        _ = (Cf * Cu) * (1 + ‖x‖) ^ (Nf + Nu) := poly_mul_le'
    have h3 : ‖(fderiv ℝ (fderiv ℝ f) x).flip (grad u x)‖ ≤ (Cf * Cu) * (1 + ‖x‖) ^ (Nf + Nu) := by
      calc ‖(fderiv ℝ (fderiv ℝ f) x).flip (grad u x)‖ ≤ Cf * (1 + ‖x‖) ^ Nf * ‖grad u x‖ := D2fB x (grad u x)
        _ = Cf * (1 + ‖x‖) ^ Nf * ‖fderiv ℝ u x‖ := by rw [grad_norm_eq]
        _ ≤ (Cf * (1 + ‖x‖) ^ Nf) * (Cu * (1 + ‖x‖) ^ Nu) :=
            mul_le_mul_of_nonneg_left (DuB x) (by positivity)
        _ = (Cf * Cu) * (1 + ‖x‖) ^ (Nf + Nu) := poly_mul_le'
    calc ‖-(fderiv ℝ (fun y => Laplacian.laplacian u y) x) + (fderiv ℝ f x).comp (hessOp u x)
            + (fderiv ℝ (fderiv ℝ f) x).flip (grad u x)‖
        ≤ ‖-(fderiv ℝ (fun y => Laplacian.laplacian u y) x) + (fderiv ℝ f x).comp (hessOp u x)‖
            + ‖(fderiv ℝ (fderiv ℝ f) x).flip (grad u x)‖ := norm_add_le _ _
      _ ≤ (‖-(fderiv ℝ (fun y => Laplacian.laplacian u y) x)‖ + ‖(fderiv ℝ f x).comp (hessOp u x)‖)
            + ‖(fderiv ℝ (fderiv ℝ f) x).flip (grad u x)‖ := add_le_add (norm_add_le _ _) le_rfl
      _ ≤ (((n : ℝ) * Cu) * (1 + ‖x‖) ^ Nu + (Cf * Cu) * (1 + ‖x‖) ^ (Nf + Nu))
            + (Cf * Cu) * (1 + ‖x‖) ^ (Nf + Nu) := add_le_add (add_le_add h1 h2) h3
      _ = ((n : ℝ) * Cu) * (1 + ‖x‖) ^ Nu + (2 * Cf * Cu) * (1 + ‖x‖) ^ (Nf + Nu) := by ring
      _ ≤ ((n : ℝ) * Cu + 2 * Cf * Cu) * (1 + ‖x‖) ^ (max Nu (Nf + Nu)) :=
          poly_add_le' (hpow1 x) (by positivity) (by positivity)
  -- W1 = phi • grad u
  have hW1 : ContDiff ℝ 1 (fun x : E => φ x • grad u x) := hφcd.smul hgradcd
  have hgW1 : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x : E,
      ‖(fun x => φ x • grad u x) x‖ ≤ C * (1 + ‖x‖) ^ N ∧
      ‖fderiv ℝ (fun x => φ x • grad u x) x‖ ≤ C * (1 + ‖x‖) ^ N := by
    refine ⟨2 * (((n : ℝ) * Cu + 2 * Cf * Cu) * Cu), by positivity,
      max Nu (Nf + Nu) + Nu, fun x => ⟨?_, ?_⟩⟩
    · have hsm : ‖φ x • grad u x‖ = |φ x| * ‖grad u x‖ := by rw [norm_smul, Real.norm_eq_abs]
      rw [hsm]
      calc |φ x| * ‖grad u x‖ ≤ (((n : ℝ) * Cu + Cf * Cu) * (1 + ‖x‖) ^ (max Nu (Nf + Nu)))
              * (Cu * (1 + ‖x‖) ^ Nu) := by
            refine mul_le_mul (φB x) ?_ (norm_nonneg _) (by positivity)
            rw [grad_norm_eq]; exact DuB x
        _ = (((n : ℝ) * Cu + Cf * Cu) * Cu) * (1 + ‖x‖) ^ (max Nu (Nf + Nu) + Nu) := poly_mul_le'
        _ ≤ 2 * (((n : ℝ) * Cu + 2 * Cf * Cu) * Cu) * (1 + ‖x‖) ^ (max Nu (Nf + Nu) + Nu) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            nlinarith [hCu, hCf, sq_nonneg Cu, mul_nonneg hCf hCu]
    · rw [fderiv_smul_grad φ u x (hφd x) hu2]
      have hsm : ‖φ x • hessOp u x + (fderiv ℝ φ x).smulRight (grad u x)‖
          ≤ |φ x| * ‖hessOp u x‖ + ‖fderiv ℝ φ x‖ * ‖grad u x‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, Real.norm_eq_abs, ContinuousLinearMap.norm_smulRight_apply]
      calc ‖φ x • hessOp u x + (fderiv ℝ φ x).smulRight (grad u x)‖
          ≤ |φ x| * ‖hessOp u x‖ + ‖fderiv ℝ φ x‖ * ‖grad u x‖ := hsm
        _ ≤ (((n : ℝ) * Cu + 2 * Cf * Cu) * (1 + ‖x‖) ^ (max Nu (Nf + Nu))) * (Cu * (1 + ‖x‖) ^ Nu)
              + (((n : ℝ) * Cu + 2 * Cf * Cu) * (1 + ‖x‖) ^ (max Nu (Nf + Nu))) * (Cu * (1 + ‖x‖) ^ Nu) := by
            refine add_le_add ?_ ?_
            · refine mul_le_mul ?_ ?_ (norm_nonneg _) (by positivity)
              · calc |φ x| ≤ ((n : ℝ) * Cu + Cf * Cu) * (1 + ‖x‖) ^ (max Nu (Nf + Nu)) := φB x
                  _ ≤ ((n : ℝ) * Cu + 2 * Cf * Cu) * (1 + ‖x‖) ^ (max Nu (Nf + Nu)) := by
                      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
                      nlinarith [hCf, hCu, mul_nonneg hCf hCu]
              · exact hessuB x
            · refine mul_le_mul (DφB x) ?_ (norm_nonneg _) (by positivity)
              rw [grad_norm_eq]; exact DuB x
        _ = (2 * (((n : ℝ) * Cu + 2 * Cf * Cu) * Cu)) * (1 + ‖x‖) ^ (max Nu (Nf + Nu) + Nu) := by
            ring
  have hA : (∫ x, (⟪grad φ x, grad u x⟫_ℝ + φ x * Laplacian.laplacian u x) * Real.exp (-(f x)))
      = ∫ x, φ x * ⟪grad f x, grad u x⟫_ℝ * Real.exp (-(f x)) := by
    have hwdg := Commons.Analysis.MeasureTheory.weighted_divergence_growth f (fun x => φ x • grad u x)
      hf1 hW1 hgW1 hdec ⟨Cf, hCf, Nf, fun x v => (hgf' x v).1⟩
    calc (∫ x, (⟪grad φ x, grad u x⟫_ℝ + φ x * Laplacian.laplacian u x) * Real.exp (-(f x)))
        = ∫ x, (∑ i : Fin n, (fderiv ℝ (fun y => φ y • grad u y) x (EuclideanSpace.single i 1)) i)
            * Real.exp (-(f x)) := by
          apply integral_congr_ae; filter_upwards with x
          rw [div_smul_grad φ u x (hφd x) hu2]
      _ = ∫ x, ⟪grad f x, (fun y => φ y • grad u y) x⟫_ℝ * Real.exp (-(f x)) := hwdg
      _ = ∫ x, φ x * ⟪grad f x, grad u x⟫_ℝ * Real.exp (-(f x)) := by
          apply integral_congr_ae; filter_upwards with x
          rw [real_inner_smul_right]
  -- W2 = Hfield u
  have hW2 : ContDiff ℝ 1 (Hfield u) := by
    have h3 : ContDiff ℝ 1 (fun y : E => fderiv ℝ (fderiv ℝ u) y) :=
      h1u.fderiv_right (m := 1) (by norm_num)
    have hg : Hfield u = (fun z : StrongDual ℝ E => (InnerProductSpace.toDual ℝ E).symm z)
        ∘ (fun y : E => (fderiv ℝ (fderiv ℝ u) y) (grad u y)) := rfl
    rw [hg]
    exact ((InnerProductSpace.toDual ℝ E).symm.contDiff (n := 1)).comp (h3.clm_apply hgradcd)
  have hgW2 : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x : E,
      ‖Hfield u x‖ ≤ C * (1 + ‖x‖) ^ N ∧ ‖fderiv ℝ (Hfield u) x‖ ≤ C * (1 + ‖x‖) ^ N := by
    refine ⟨2 * Cu ^ 2, by positivity, 2 * Nu, fun x => ⟨?_, ?_⟩⟩
    · rw [show Hfield u x = hessOp u x (grad u x) from rfl]
      calc ‖hessOp u x (grad u x)‖ ≤ ‖hessOp u x‖ * ‖grad u x‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ (Cu * (1 + ‖x‖) ^ Nu) * (Cu * (1 + ‖x‖) ^ Nu) :=
            mul_le_mul (hessuB x) (by rw [grad_norm_eq]; exact DuB x) (norm_nonneg _) (by positivity)
        _ = (Cu * (1 + ‖x‖) ^ Nu) ^ 2 := by ring
        _ = Cu ^ 2 * (1 + ‖x‖) ^ (2 * Nu) := by rw [mul_pow, ← pow_mul, Nat.mul_comm Nu 2]
        _ ≤ 2 * Cu ^ 2 * (1 + ‖x‖) ^ (2 * Nu) := by
            rw [show (2:ℝ) * Cu ^ 2 * (1 + ‖x‖) ^ (2 * Nu) = 2 * (Cu ^ 2 * (1 + ‖x‖) ^ (2 * Nu)) from by ring]
            exact le_mul_of_one_le_left (by positivity) (by norm_num)
    · rw [fderiv_Hfield u hu x]
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun v => ?_)
      rw [ContinuousLinearMap.comp_apply]
      change ‖(InnerProductSpace.toDual ℝ E).symm
          (((fderiv ℝ (fderiv ℝ u) x).comp (hessOp u x)
          + (fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x).flip (grad u x)) v)‖ ≤ _ * ‖v‖
      rw [LinearIsometryEquiv.norm_map, ContinuousLinearMap.add_apply]
      have hgux : ‖grad u x‖ ≤ Cu * (1 + ‖x‖) ^ Nu := by rw [grad_norm_eq]; exact DuB x
      have hv1 : ‖((fderiv ℝ (fderiv ℝ u) x).comp (hessOp u x)) v‖ ≤ Cu ^ 2 * (1 + ‖x‖) ^ (2 * Nu) * ‖v‖ := by
        rw [ContinuousLinearMap.comp_apply]
        calc ‖(fderiv ℝ (fderiv ℝ u) x) ((hessOp u x) v)‖ ≤ ‖fderiv ℝ (fderiv ℝ u) x‖ * ‖(hessOp u x) v‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ ≤ (Cu * (1 + ‖x‖) ^ Nu) * ((Cu * (1 + ‖x‖) ^ Nu) * ‖v‖) :=
              mul_le_mul (D2uB x)
                ((ContinuousLinearMap.le_opNorm (hessOp u x) v).trans
                  (mul_le_mul_of_nonneg_right (hessuB x) (norm_nonneg v))) (norm_nonneg _)
                (by positivity)
          _ = Cu ^ 2 * (1 + ‖x‖) ^ (2 * Nu) * ‖v‖ := by
              have hsq : Cu * (1 + ‖x‖) ^ Nu * (Cu * (1 + ‖x‖) ^ Nu) = Cu ^ 2 * (1 + ‖x‖) ^ (2 * Nu) := by
                rw [show Cu * (1+‖x‖)^Nu * (Cu*(1+‖x‖)^Nu) = (Cu*(1+‖x‖)^Nu)^2 from by ring,
                  mul_pow, ← pow_mul, Nat.mul_comm Nu 2]
              rw [show Cu * (1+‖x‖)^Nu * (Cu*(1+‖x‖)^Nu * ‖v‖)
                    = (Cu * (1+‖x‖)^Nu * (Cu*(1+‖x‖)^Nu)) * ‖v‖ from by ring, hsq]
      have hv2 : ‖((fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x).flip (grad u x)) v‖ ≤ Cu ^ 2 * (1 + ‖x‖) ^ (2 * Nu) * ‖v‖ := by
        rw [ContinuousLinearMap.flip_apply]
        refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun w => ?_)
        rw [Real.norm_eq_abs]
        calc |(fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x) v (grad u x) w|
            ≤ Cu * (1 + ‖x‖) ^ Nu * ‖v‖ * ‖grad u x‖ * ‖w‖ := (hgu' x v (grad u x) w).2.2.2
          _ ≤ (Cu ^ 2 * (1 + ‖x‖) ^ (2 * Nu) * ‖v‖) * ‖w‖ := by
              have hb : Cu * (1 + ‖x‖) ^ Nu * ‖v‖ * ‖grad u x‖ ≤ Cu * (1 + ‖x‖) ^ Nu * ‖v‖ * (Cu * (1 + ‖x‖) ^ Nu) :=
                mul_le_mul_of_nonneg_left hgux (by positivity)
              calc Cu * (1 + ‖x‖) ^ Nu * ‖v‖ * ‖grad u x‖ * ‖w‖
                  ≤ (Cu * (1 + ‖x‖) ^ Nu * ‖v‖ * (Cu * (1 + ‖x‖) ^ Nu)) * ‖w‖ :=
                    mul_le_mul_of_nonneg_right hb (norm_nonneg w)
                _ = (Cu ^ 2 * (1 + ‖x‖) ^ (2 * Nu) * ‖v‖) * ‖w‖ := by
                    have hsq2 : Cu * (1 + ‖x‖) ^ Nu * (Cu * (1 + ‖x‖) ^ Nu) = Cu ^ 2 * (1 + ‖x‖) ^ (2 * Nu) := by
                      rw [show Cu*(1+‖x‖)^Nu*(Cu*(1+‖x‖)^Nu) = (Cu*(1+‖x‖)^Nu)^2 from by ring,
                        mul_pow, ← pow_mul, Nat.mul_comm Nu 2]
                    rw [show Cu * (1+‖x‖)^Nu * ‖v‖ * (Cu*(1+‖x‖)^Nu) * ‖w‖
                          = (Cu * (1+‖x‖)^Nu * (Cu*(1+‖x‖)^Nu)) * ‖v‖ * ‖w‖ from by ring, hsq2]
      calc ‖((fderiv ℝ (fderiv ℝ u) x).comp (hessOp u x)) v
              + ((fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x).flip (grad u x)) v‖
          ≤ ‖((fderiv ℝ (fderiv ℝ u) x).comp (hessOp u x)) v‖
              + ‖((fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x).flip (grad u x)) v‖ := norm_add_le _ _
        _ ≤ Cu ^ 2 * (1 + ‖x‖) ^ (2 * Nu) * ‖v‖ + Cu ^ 2 * (1 + ‖x‖) ^ (2 * Nu) * ‖v‖ := add_le_add hv1 hv2
        _ = 2 * Cu ^ 2 * (1 + ‖x‖) ^ (2 * Nu) * ‖v‖ := by ring
  have hB : (∫ x, (⟪grad (fun y => Laplacian.laplacian u y) x, grad u x⟫_ℝ
        + ∑ i : Fin n, ∑ j : Fin n,
          (fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) ^ 2)
        * Real.exp (-(f x)))
      = ∫ x, ⟪grad f x, hessOp u x (grad u x)⟫_ℝ * Real.exp (-(f x)) := by
    have hwdg := Commons.Analysis.MeasureTheory.weighted_divergence_growth f (Hfield u)
      hf1 hW2 hgW2 hdec ⟨Cf, hCf, Nf, fun x v => (hgf' x v).1⟩
    calc (∫ x, (⟪grad (fun y => Laplacian.laplacian u y) x, grad u x⟫_ℝ
          + ∑ i : Fin n, ∑ j : Fin n,
            (fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) ^ 2)
          * Real.exp (-(f x)))
        = ∫ x, (∑ i : Fin n, (fderiv ℝ (Hfield u) x (EuclideanSpace.single i 1)) i)
            * Real.exp (-(f x)) := by
          apply integral_congr_ae; filter_upwards with x
          rw [divHfield_eq u hu x]
      _ = ∫ x, ⟪grad f x, Hfield u x⟫_ℝ * Real.exp (-(f x)) := hwdg
      _ = ∫ x, ⟪grad f x, hessOp u x (grad u x)⟫_ℝ * Real.exp (-(f x)) := rfl
  -- chain rule pointwise
  have hchain : ∀ x : E, ⟪grad φ x, grad u x⟫_ℝ
      = -⟪grad (fun y => Laplacian.laplacian u y) x, grad u x⟫_ℝ
        + (fderiv ℝ (fderiv ℝ f) x) (grad u x) (grad u x)
        + ⟪grad f x, hessOp u x (grad u x)⟫_ℝ := by
    intro x
    rw [hφdef, grad_spec, fderiv_Lu f u hf hu x]
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply, neg_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
    rw [grad_spec, grad_spec]
    ring


  have hgradφc : Continuous (grad φ) := by
    have h : Continuous (fderiv ℝ φ) := hφcd.continuous_fderiv (by norm_num)
    have h2 : grad φ = (fun z : StrongDual ℝ E => (InnerProductSpace.toDual ℝ E).symm z) ∘ (fderiv ℝ φ) := rfl
    rw [h2]
    exact ((InnerProductSpace.toDual ℝ E).symm.continuous).comp h
  have hΔuc : Continuous (fun y : E => Laplacian.laplacian u y) := (contDiff_laplacian u hu).continuous
  have hgradΔuc : Continuous (fun y : E => grad (fun z => Laplacian.laplacian u z) y) := by
    have h : Continuous (fderiv ℝ (fun y : E => Laplacian.laplacian u y)) :=
      (contDiff_laplacian u hu).continuous_fderiv (by norm_num)
    have h2 : grad (fun y : E => Laplacian.laplacian u y)
        = (fun z : StrongDual ℝ E => (InnerProductSpace.toDual ℝ E).symm z) ∘ (fderiv ℝ (fun y : E => Laplacian.laplacian u y)) := rfl
    rw [h2]
    exact ((InnerProductSpace.toDual ℝ E).symm.continuous).comp h
  have hhessu_c : Continuous (fun x : E => hessOp u x (grad u x)) := by
    have h3 : Continuous (fun y : E => fderiv ℝ (fderiv ℝ u) y) := h1u.continuous_fderiv (by norm_num)
    have h2 : (fun x : E => hessOp u x (grad u x))
        = (fun z : StrongDual ℝ E => (InnerProductSpace.toDual ℝ E).symm z) ∘ (fun y : E => (fderiv ℝ (fderiv ℝ u) y) (grad u y)) := rfl
    rw [h2]
    exact ((InnerProductSpace.toDual ℝ E).symm.continuous).comp (h3.clm_apply hgradcd.continuous)
  have hgradfc : Continuous (grad f) := by
    have h : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
    have h2 : grad f = (fun z : StrongDual ℝ E => (InnerProductSpace.toDual ℝ E).symm z) ∘ (fderiv ℝ f) := rfl
    rw [h2]
    exact ((InnerProductSpace.toDual ℝ E).symm.continuous).comp h
  have hhessf_c : Continuous (fun x : E => (fderiv ℝ (fderiv ℝ f) x) (grad u x) (grad u x)) :=
    (((hf.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)).clm_apply
      hgradcd.continuous).clm_apply hgradcd.continuous
  have hsum_c : Continuous (fun x : E => ∑ i : Fin n, ∑ j : Fin n,
      (fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) ^ 2) := by
    refine continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ => ?_))
    exact (((h1u.continuous_fderiv (by norm_num)).clm_apply continuous_const).clm_apply continuous_const).pow 2
  have hInta : Integrable (fun x : E => ⟪grad φ x, grad u x⟫_ℝ * Real.exp (-(f x))) := by
    refine integrable_poly_gauss hfc hdec (Continuous.inner hgradφc hgradcd.continuous)
      (C := ((n : ℝ) * Cu + 2 * Cf * Cu) * Cu) (N := max Nu (Nf + Nu) + Nu) (by positivity) (fun x => ?_)
    calc |⟪grad φ x, grad u x⟫_ℝ| ≤ ‖grad φ x‖ * ‖grad u x‖ := abs_real_inner_le_norm _ _
      _ ≤ (((n : ℝ) * Cu + 2 * Cf * Cu) * (1 + ‖x‖) ^ (max Nu (Nf + Nu)))
            * (Cu * (1 + ‖x‖) ^ Nu) := by
          refine mul_le_mul ?_ ?_ (norm_nonneg _) (by positivity)
          · rw [grad_norm_eq]; exact DφB x
          · rw [grad_norm_eq]; exact DuB x
      _ = (((n : ℝ) * Cu + 2 * Cf * Cu) * Cu) * (1 + ‖x‖) ^ (max Nu (Nf + Nu) + Nu) := poly_mul_le'
  have hIntb : Integrable (fun x : E => φ x * Laplacian.laplacian u x * Real.exp (-(f x))) := by
    refine integrable_poly_gauss hfc hdec (hφcd.continuous.mul hΔuc)
      (C := ((n : ℝ) * Cu + Cf * Cu) * ((n : ℝ) * Cu)) (N := max Nu (Nf + Nu) + Nu) (by positivity) (fun x => ?_)
    rw [abs_mul]
    calc |φ x| * |Laplacian.laplacian u x| ≤ (((n : ℝ) * Cu + Cf * Cu) * (1 + ‖x‖) ^ (max Nu (Nf + Nu)))
            * (((n : ℝ) * Cu) * (1 + ‖x‖) ^ Nu) :=
          mul_le_mul (φB x) (by simpa using ΔuB x) (abs_nonneg _) (by positivity)
      _ = (((n : ℝ) * Cu + Cf * Cu) * ((n : ℝ) * Cu)) * (1 + ‖x‖) ^ (max Nu (Nf + Nu) + Nu) := poly_mul_le'
  have hIntc : Integrable (fun x : E => φ x * ⟪grad f x, grad u x⟫_ℝ * Real.exp (-(f x))) := by
    refine integrable_poly_gauss hfc hdec ((hφcd.continuous.mul (Continuous.inner hgradfc hgradcd.continuous)))
      (C := ((n : ℝ) * Cu + Cf * Cu) * (Cf * Cu)) (N := max Nu (Nf + Nu) + (Nf + Nu)) (by positivity) (fun x => ?_)
    rw [abs_mul]
    calc |φ x| * |⟪grad f x, grad u x⟫_ℝ| ≤ (((n : ℝ) * Cu + Cf * Cu) * (1 + ‖x‖) ^ (max Nu (Nf + Nu)))
            * ((Cf * Cu) * (1 + ‖x‖) ^ (Nf + Nu)) := by
          refine mul_le_mul (φB x) ?_ (abs_nonneg _) (by positivity)
          calc |⟪grad f x, grad u x⟫_ℝ| ≤ ‖grad f x‖ * ‖grad u x‖ := abs_real_inner_le_norm _ _
            _ ≤ (Cf * (1 + ‖x‖) ^ Nf) * (Cu * (1 + ‖x‖) ^ Nu) :=
                mul_le_mul (by rw [grad_norm_eq]; exact DfB x) (by rw [grad_norm_eq]; exact DuB x) (norm_nonneg _) (by positivity)
            _ = (Cf * Cu) * (1 + ‖x‖) ^ (Nf + Nu) := poly_mul_le'
      _ = (((n : ℝ) * Cu + Cf * Cu) * (Cf * Cu)) * (1 + ‖x‖) ^ (max Nu (Nf + Nu) + (Nf + Nu)) := poly_mul_le'
  have hInte : Integrable (fun x : E => ⟪grad (fun y => Laplacian.laplacian u y) x, grad u x⟫_ℝ * Real.exp (-(f x))) := by
    refine integrable_poly_gauss hfc hdec (Continuous.inner hgradΔuc hgradcd.continuous)
      (C := ((n : ℝ) * Cu) * Cu) (N := Nu + Nu) (by positivity) (fun x => ?_)
    calc |⟪grad (fun y => Laplacian.laplacian u y) x, grad u x⟫_ℝ| ≤ ‖grad (fun y => Laplacian.laplacian u y) x‖ * ‖grad u x‖ := abs_real_inner_le_norm _ _
      _ ≤ (((n : ℝ) * Cu) * (1 + ‖x‖) ^ Nu)
            * (Cu * (1 + ‖x‖) ^ Nu) := by
          refine mul_le_mul ?_ ?_ (norm_nonneg _) (by positivity)
          · rw [grad_norm_eq]; exact DΔuB x
          · rw [grad_norm_eq]; exact DuB x
      _ = (((n : ℝ) * Cu) * Cu) * (1 + ‖x‖) ^ (Nu + Nu) := poly_mul_le'
  have hIntf : Integrable (fun x : E => (fderiv ℝ (fderiv ℝ f) x) (grad u x) (grad u x) * Real.exp (-(f x))) := by
    refine integrable_poly_gauss hfc hdec hhessf_c (C := Cf * Cu ^ 2) (N := Nf + 2 * Nu) (by positivity) (fun x => ?_)
    have hgf'' : ∀ x, (fderiv ℝ (fderiv ℝ f) x) (grad u x) (grad u x)
        = ⟪hessOp f x (grad u x), grad u x⟫_ℝ := fun x => (hessOp_spec f x (grad u x) (grad u x)).symm
    rw [hgf'']
    calc |⟪hessOp f x (grad u x), grad u x⟫_ℝ| ≤ ‖hessOp f x (grad u x)‖ * ‖grad u x‖ := abs_real_inner_le_norm _ _
      _ ≤ (Cf * (1 + ‖x‖) ^ Nf * ‖grad u x‖) * ‖grad u x‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          exact (ContinuousLinearMap.le_opNorm (hessOp f x) (grad u x)).trans
            (mul_le_mul_of_nonneg_right (hessfB x) (norm_nonneg _))
      _ ≤ (Cf * (1 + ‖x‖) ^ Nf * (Cu * (1 + ‖x‖) ^ Nu)) * (Cu * (1 + ‖x‖) ^ Nu) := by
          have hgu2 : ‖grad u x‖ ≤ Cu * (1 + ‖x‖) ^ Nu := by rw [grad_norm_eq]; exact DuB x
          exact mul_le_mul (mul_le_mul_of_nonneg_left hgu2 (by positivity)) hgu2 (norm_nonneg _) (by positivity)
      _ = (Cf * Cu ^ 2) * (1 + ‖x‖) ^ (Nf + 2 * Nu) := by
          rw [show (Cf * (1+‖x‖)^Nf * (Cu*(1+‖x‖)^Nu)) * (Cu*(1+‖x‖)^Nu)
                = (Cf * (Cu * Cu)) * ((1+‖x‖)^Nf * ((1+‖x‖)^Nu * (1+‖x‖)^Nu)) from by ring]
          rw [← pow_add, ← two_mul, ← pow_add]
          ring
  have hIntg : Integrable (fun x : E => ⟪grad f x, hessOp u x (grad u x)⟫_ℝ * Real.exp (-(f x))) := by
    refine integrable_poly_gauss hfc hdec (Continuous.inner hgradfc hhessu_c)
      (C := Cf * Cu ^ 2) (N := Nf + 2 * Nu) (by positivity) (fun x => ?_)
    have hgu_x : ∀ x : E, ‖grad u x‖ ≤ Cu * (1 + ‖x‖) ^ Nu := fun x => by rw [grad_norm_eq]; exact DuB x
    calc |⟪grad f x, hessOp u x (grad u x)⟫_ℝ| ≤ ‖grad f x‖ * ‖hessOp u x (grad u x)‖ := abs_real_inner_le_norm _ _
      _ ≤ (Cf * (1 + ‖x‖) ^ Nf)
            * (Cu * (1 + ‖x‖) ^ Nu * (Cu * (1 + ‖x‖) ^ Nu)) := by
          refine mul_le_mul (by rw [grad_norm_eq]; exact DfB x) ?_ (norm_nonneg _) (by positivity)
          calc ‖hessOp u x (grad u x)‖ ≤ ‖hessOp u x‖ * ‖grad u x‖ := ContinuousLinearMap.le_opNorm _ _
            _ ≤ (Cu * (1 + ‖x‖) ^ Nu) * (Cu * (1 + ‖x‖) ^ Nu) :=
                mul_le_mul (hessuB x) (hgu_x x) (norm_nonneg _) (by positivity)
      _ = (Cf * Cu ^ 2) * (1 + ‖x‖) ^ (Nf + 2 * Nu) := by
          rw [show Cf * (1+‖x‖)^Nf * (Cu*(1+‖x‖)^Nu * (Cu*(1+‖x‖)^Nu))
                = (Cf * (Cu * Cu)) * ((1+‖x‖)^Nf * ((1+‖x‖)^Nu * (1+‖x‖)^Nu)) from by ring]
          rw [← pow_add, ← two_mul, ← pow_add]
          ring
  have hInth : Integrable (fun x : E => (∑ i : Fin n, ∑ j : Fin n,
      (fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) ^ 2) * Real.exp (-(f x))) := by
    refine integrable_poly_gauss hfc hdec hsum_c (C := (n : ℝ) ^ 2 * Cu ^ 2) (N := 2 * Nu) (by positivity) (fun x => ?_)
    exact hess_sum_bound u hCu (fun x v w => (hgu' x v w 0).2.2.1) x
  have hIntEH : Integrable (fun x : E => (⟪grad (fun y => Laplacian.laplacian u y) x, grad u x⟫_ℝ
      + ∑ i : Fin n, ∑ j : Fin n,
        (fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) ^ 2)
      * Real.exp (-(f x))) := by
    refine (hInte.add hInth).congr ?_
    filter_upwards with x; simp only [Pi.add_apply]; ring
  have hIntG : Integrable (fun x : E => ((∑ i : Fin n, ∑ j : Fin n,
      (fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) ^ 2)
      + (fderiv ℝ (fderiv ℝ f) x) (grad u x) (grad u x)) * Real.exp (-(f x))) := by
    refine (hInth.add hIntf).congr ?_
    filter_upwards with x; simp only [Pi.add_apply]; ring
  have step1 : (∫ x, φ x ^ 2 * Real.exp (-(f x))) = ∫ x, ⟪grad φ x, grad u x⟫_ℝ * Real.exp (-(f x)) := by
    have hpw : ∀ x : E, φ x ^ 2 * Real.exp (-(f x))
        = φ x * ⟪grad f x, grad u x⟫_ℝ * Real.exp (-(f x))
          - φ x * Laplacian.laplacian u x * Real.exp (-(f x)) := by
      intro x
      have h1 : φ x = ⟪grad f x, grad u x⟫_ℝ - Laplacian.laplacian u x := by
        rw [hφdef]
        change -Laplacian.laplacian u x + ⟪grad f x, grad u x⟫_ℝ = ⟪grad f x, grad u x⟫_ℝ - Laplacian.laplacian u x
        rw [grad_spec]; ring
      rw [h1]; ring
    have hdist : (∫ x, (⟪grad φ x, grad u x⟫_ℝ + φ x * Laplacian.laplacian u x) * Real.exp (-(f x)))
        = (∫ x, ⟪grad φ x, grad u x⟫_ℝ * Real.exp (-(f x)))
          + (∫ x, φ x * Laplacian.laplacian u x * Real.exp (-(f x))) := by
      rw [show (∫ x, (⟪grad φ x, grad u x⟫_ℝ + φ x * Laplacian.laplacian u x) * Real.exp (-(f x)))
            = (∫ x, (fun x : E => ⟪grad φ x, grad u x⟫_ℝ * Real.exp (-(f x))) x
                + (fun x : E => φ x * Laplacian.laplacian u x * Real.exp (-(f x))) x) from by
        apply integral_congr_ae; filter_upwards with x; ring]
      exact integral_add hInta hIntb
    calc (∫ x, φ x ^ 2 * Real.exp (-(f x)))
        = ∫ x, (φ x * ⟪grad f x, grad u x⟫_ℝ * Real.exp (-(f x))
            - φ x * Laplacian.laplacian u x * Real.exp (-(f x))) :=
          integral_congr_ae (Filter.Eventually.of_forall hpw)
      _ = (∫ x, φ x * ⟪grad f x, grad u x⟫_ℝ * Real.exp (-(f x)))
            - (∫ x, φ x * Laplacian.laplacian u x * Real.exp (-(f x))) := integral_sub hIntc hIntb
      _ = (∫ x, (⟪grad φ x, grad u x⟫_ℝ + φ x * Laplacian.laplacian u x) * Real.exp (-(f x)))
            - (∫ x, φ x * Laplacian.laplacian u x * Real.exp (-(f x))) := by rw [← hA]
      _ = ((∫ x, ⟪grad φ x, grad u x⟫_ℝ * Real.exp (-(f x)))
            + (∫ x, φ x * Laplacian.laplacian u x * Real.exp (-(f x))))
            - (∫ x, φ x * Laplacian.laplacian u x * Real.exp (-(f x))) := by rw [hdist]
      _ = ∫ x, ⟪grad φ x, grad u x⟫_ℝ * Real.exp (-(f x)) := by ring
  have hkeyE : (∫ x, ⟪grad (fun y => Laplacian.laplacian u y) x, grad u x⟫_ℝ * Real.exp (-(f x)))
      = (∫ x, ⟪grad f x, hessOp u x (grad u x)⟫_ℝ * Real.exp (-(f x)))
        - (∫ x, (∑ i : Fin n, ∑ j : Fin n,
            (fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) ^ 2)
            * Real.exp (-(f x))) := by
    rw [← hB]
    have hE2 : (∫ x, (⟪grad (fun y => Laplacian.laplacian u y) x, grad u x⟫_ℝ
          + ∑ i : Fin n, ∑ j : Fin n,
            (fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) ^ 2)
          * Real.exp (-(f x)))
        = ∫ x, (fun x : E => ⟪grad (fun y => Laplacian.laplacian u y) x, grad u x⟫_ℝ * Real.exp (-(f x))) x
            + (fun x : E => (∑ i : Fin n, ∑ j : Fin n,
              (fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) ^ 2)
              * Real.exp (-(f x))) x := by
      apply integral_congr_ae; filter_upwards with x; ring
    rw [hE2, integral_add hInte hInth]
    ring
  have step2 : (∫ x, ⟪grad φ x, grad u x⟫_ℝ * Real.exp (-(f x)))
      = ∫ x, ((∑ i : Fin n, ∑ j : Fin n,
          (fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) ^ 2)
          + (fderiv ℝ (fderiv ℝ f) x) (grad u x) (grad u x)) * Real.exp (-(f x)) := by
    have hcr : ∀ x : E, ⟪grad φ x, grad u x⟫_ℝ * Real.exp (-(f x))
        = (-⟪grad (fun y => Laplacian.laplacian u y) x, grad u x⟫_ℝ
            + (fderiv ℝ (fderiv ℝ f) x) (grad u x) (grad u x)
            + ⟪grad f x, hessOp u x (grad u x)⟫_ℝ) * Real.exp (-(f x)) := by
      intro x; rw [hchain x]
    have hmidd : (∫ x, ⟪grad φ x, grad u x⟫_ℝ * Real.exp (-(f x)))
        = -(∫ x, ⟪grad (fun y => Laplacian.laplacian u y) x, grad u x⟫_ℝ * Real.exp (-(f x)))
          + (∫ x, (fderiv ℝ (fderiv ℝ f) x) (grad u x) (grad u x) * Real.exp (-(f x)))
          + (∫ x, ⟪grad f x, hessOp u x (grad u x)⟫_ℝ * Real.exp (-(f x))) := by
      rw [integral_congr_ae (Filter.Eventually.of_forall hcr)]
      have hI23 : (∫ x : E,
          (fun x : E => -(⟪grad (fun y => Laplacian.laplacian u y) x, grad u x⟫_ℝ * Real.exp (-(f x)))
              + (fderiv ℝ (fderiv ℝ f) x) (grad u x) (grad u x) * Real.exp (-(f x))) x
          + (fun x : E => ⟪grad f x, hessOp u x (grad u x)⟫_ℝ * Real.exp (-(f x))) x)
          = (∫ x : E, -(⟪grad (fun y => Laplacian.laplacian u y) x, grad u x⟫_ℝ * Real.exp (-(f x)))
              + (fderiv ℝ (fderiv ℝ f) x) (grad u x) (grad u x) * Real.exp (-(f x)))
            + (∫ x, ⟪grad f x, hessOp u x (grad u x)⟫_ℝ * Real.exp (-(f x))) :=
        integral_add (hInte.neg.add hIntf) hIntg
      rw [show (∫ x : E, (-⟪grad (fun y => Laplacian.laplacian u y) x, grad u x⟫_ℝ
              + (fderiv ℝ (fderiv ℝ f) x) (grad u x) (grad u x)
              + ⟪grad f x, hessOp u x (grad u x)⟫_ℝ) * Real.exp (-(f x)))
            = (∫ x : E,
                (fun x : E => -(⟪grad (fun y => Laplacian.laplacian u y) x, grad u x⟫_ℝ * Real.exp (-(f x)))
                    + (fderiv ℝ (fderiv ℝ f) x) (grad u x) (grad u x) * Real.exp (-(f x))) x
                + (fun x : E => ⟪grad f x, hessOp u x (grad u x)⟫_ℝ * Real.exp (-(f x))) x) from by
          apply integral_congr_ae; filter_upwards with x; ring]
      rw [hI23]
      have hI1 : (∫ x : E,
          (fun x : E => -(⟪grad (fun y => Laplacian.laplacian u y) x, grad u x⟫_ℝ * Real.exp (-(f x)))) x
          + (fun x : E => (fderiv ℝ (fderiv ℝ f) x) (grad u x) (grad u x) * Real.exp (-(f x))) x)
          = (∫ x : E, -(⟪grad (fun y => Laplacian.laplacian u y) x, grad u x⟫_ℝ * Real.exp (-(f x))))
            + (∫ x, (fderiv ℝ (fderiv ℝ f) x) (grad u x) (grad u x) * Real.exp (-(f x))) :=
        integral_add hInte.neg hIntf
      rw [hI1, integral_neg]
    have hG : (∫ x, ((∑ i : Fin n, ∑ j : Fin n,
          (fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) ^ 2)
          + (fderiv ℝ (fderiv ℝ f) x) (grad u x) (grad u x)) * Real.exp (-(f x)))
        = (∫ x, (∑ i : Fin n, ∑ j : Fin n,
            (fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) ^ 2)
            * Real.exp (-(f x)))
          + (∫ x, (fderiv ℝ (fderiv ℝ f) x) (grad u x) (grad u x) * Real.exp (-(f x))) := by
      rw [show (∫ x, ((∑ i : Fin n, ∑ j : Fin n,
            (fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) ^ 2)
            + (fderiv ℝ (fderiv ℝ f) x) (grad u x) (grad u x)) * Real.exp (-(f x)))
            = (∫ x : E, (fun x : E => (∑ i : Fin n, ∑ j : Fin n,
                (fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) ^ 2)
                * Real.exp (-(f x))) x
              + (fun x : E => (fderiv ℝ (fderiv ℝ f) x) (grad u x) (grad u x) * Real.exp (-(f x))) x) from by
          apply integral_congr_ae; filter_upwards with x; ring]
      exact integral_add hInth hIntf
    rw [hmidd, hkeyE, hG]; ring
  have hL : (∫ x, (- Laplacian.laplacian u x + inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x))
        ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x))) ^ 2 * Real.exp (-(f x)))
      = ∫ x, φ x ^ 2 * Real.exp (-(f x)) := by
    apply integral_congr_ae; filter_upwards with x
    have h1 : (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x) = grad f x := rfl
    have h2 : (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x) = grad u x := rfl
    rw [h1, h2, hφdef]
  have hR : (∫ x, ((∑ i : Fin n, ∑ j : Fin n,
        ((fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1)) (EuclideanSpace.single j 1)) ^ 2)
        + (fderiv ℝ (fderiv ℝ f) x) ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x))
          ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x))) * Real.exp (-(f x)))
      = ∫ x, ((∑ i : Fin n, ∑ j : Fin n,
          (fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) ^ 2)
          + (fderiv ℝ (fderiv ℝ f) x) (grad u x) (grad u x)) * Real.exp (-(f x)) := by
    apply integral_congr_ae; filter_upwards with x
    have h2 : (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x) = grad u x := rfl
    rw [h2]
  rw [hL, hR, step1, step2]

private lemma even_convex_min {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {g : F → ℝ}
    (hconv : ConvexOn ℝ Set.univ g) (he : ∀ x, g (-x) = g x) (x : F) : g 0 ≤ g x := by
  have h := hconv.2 (Set.mem_univ x) (Set.mem_univ (-x)) (by norm_num) (by norm_num)
    (by norm_num : ((1:ℝ)/2) + 1/2 = 1)
  have hx : ((1:ℝ)/2) • x + ((1:ℝ)/2) • (-x) = 0 := by module
  rw [hx, he x] at h
  simp only [smul_eq_mul] at h
  linarith

private lemma pi_mul_norm_sq_add_le {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (f : F → ℝ) (he : ∀ x, f (-x) = f x)
    (hconv : ConvexOn ℝ Set.univ (fun x => f x - Real.pi * ‖x‖ ^ 2)) (x : F) :
    Real.pi * ‖x‖ ^ 2 + f 0 ≤ f x := by
  have hge : ∀ y : F, (fun y => f y - Real.pi * ‖y‖ ^ 2) (-y)
      = (fun y => f y - Real.pi * ‖y‖ ^ 2) y := by
    intro y; simp only [he y, norm_neg]
  have hmin := even_convex_min hconv hge x
  simp only [norm_zero, pow_two, mul_zero, sub_zero] at hmin
  linarith

private theorem creation_energy_aux (f u : E → ℝ) (hf : ContDiff ℝ 2 f) (hfe : ∀ x, f (-x) = f x) (hH : ∀ x v : E, 2 * Real.pi * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) x v v) (hconv : ConvexOn ℝ Set.univ (fun x => f x - Real.pi * ‖x‖ ^ 2)) (hgf : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x v : E, |fderiv ℝ f x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ∧ |fderiv ℝ (fderiv ℝ f) x v v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ^ 2) (hu : ContDiff ℝ 3 u) (hueven : ∀ x, u (-x) = u x) (hgu : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x v w z : E, |u x| ≤ C * (1 + ‖x‖) ^ N ∧ |fderiv ℝ u x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ∧ |fderiv ℝ (fderiv ℝ u) x v w| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ * ‖w‖ ∧ |fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x v w z| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ * ‖w‖ * ‖z‖) : 4 * Real.pi * (∫ x, ‖fderiv ℝ u x‖ ^ 2 * Real.exp (-(f x))) ≤ (∫ x, (- Laplacian.laplacian u x + inner ℝ ((InnerProductSpace.toDual ℝ (E)).symm (fderiv ℝ f x)) ((InnerProductSpace.toDual ℝ (E)).symm (fderiv ℝ u x))) ^ 2 * Real.exp (-(f x))) := by
  have hdec : ∃ c : ℝ, ∀ x, c + Real.pi * ‖x‖ ^ 2 ≤ f x :=
    ⟨f 0, fun x => by linarith [pi_mul_norm_sq_add_le f hfe hconv x]⟩
  have hBoch := bochner_identity_smooth f u hf hu hdec hgf hgu
  have hebl := Commons.Analysis.GaussianMeasure.even_bl_hessian_energy f u hf hfe hH hconv hgf
    (hu.of_le (m := 2) (by norm_num)) hueven (by
      obtain ⟨C, hC, N, hN⟩ := hgu
      exact ⟨C, hC, N, fun x v w => ⟨(hN x 0 0 0).1, (hN x v 0 0).2.1, (hN x v w 0).2.2.1⟩⟩)
  obtain ⟨Cf, hCf, Nf, hgf'⟩ := hgf
  obtain ⟨Cu, hCu, Nu, hgu'⟩ := hgu
  have hDunorm : ∀ x : E, ‖fderiv ℝ u x‖ ≤ Cu * (1 + ‖x‖) ^ Nu := by
    intro x
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    rw [Real.norm_eq_abs]; exact (hgu' x v 0 0).2.1
  -- integrability of ‖fderiv u‖²·e^{-f}
  have hIntD : Integrable (fun x : E => ‖fderiv ℝ u x‖ ^ 2 * Real.exp (-(f x))) := by
    refine Commons.Analysis.GaussianMeasure.integrable_mul_exp_neg_stronglyConvex f (fun x => ‖fderiv ℝ u x‖ ^ 2) hf hconv ?_ (Cu ^ 2) (sq_nonneg Cu) (2 * Nu) ?_
    · exact (((hu.continuous_fderiv (by norm_num)).norm).pow 2)
    · intro x
      rw [abs_of_nonneg (sq_nonneg _)]
      calc ‖fderiv ℝ u x‖ ^ 2 ≤ (Cu * (1 + ‖x‖) ^ Nu) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hDunorm x) 2
        _ = Cu ^ 2 * (1 + ‖x‖) ^ (2 * Nu) := by rw [mul_pow, ← pow_mul, Nat.mul_comm]
  -- integrability of D²f(gu)(gu)·e^{-f}
  have hIntC : Integrable (fun x : E =>
      fderiv ℝ (fderiv ℝ f) x ((InnerProductSpace.toDual ℝ (E)).symm (fderiv ℝ u x)) ((InnerProductSpace.toDual ℝ (E)).symm (fderiv ℝ u x)) * Real.exp (-(f x))) := by
    set g : E → E :=
      fun x => (InnerProductSpace.toDual ℝ (E)).symm (fderiv ℝ u x) with hgdef
    have hgc : Continuous g := by
      rw [hgdef]
      exact ((InnerProductSpace.toDual ℝ (E)).symm.continuous.comp
        (hu.continuous_fderiv (by norm_num)))
    have hgn : ∀ x, ‖g x‖ ≤ Cu * (1 + ‖x‖) ^ Nu := fun x => by
      rw [hgdef, LinearIsometryEquiv.norm_map]; exact hDunorm x
    refine Commons.Analysis.GaussianMeasure.integrable_mul_exp_neg_stronglyConvex f (fun x =>
      fderiv ℝ (fderiv ℝ f) x (g x) (g x)) hf hconv ?_ (Cf * Cu ^ 2) (by positivity) (Nf + 2 * Nu) ?_
    · have hf1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (m := 1) (by norm_num)
      exact ((hf1.continuous_fderiv (by norm_num)).clm_apply hgc).clm_apply hgc
    · intro x
      have h2 : |fderiv ℝ (fderiv ℝ f) x (g x) (g x)| ≤ Cf * (1 + ‖x‖) ^ Nf * ‖g x‖ ^ 2 := by
        exact (hgf' x (g x)).2
      calc |fderiv ℝ (fderiv ℝ f) x (g x) (g x)|
          ≤ Cf * (1 + ‖x‖) ^ Nf * ‖g x‖ ^ 2 := h2
        _ ≤ Cf * (1 + ‖x‖) ^ Nf * (Cu * (1 + ‖x‖) ^ Nu) ^ 2 := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hCf (pow_nonneg (by positivity) _))
            exact pow_le_pow_left₀ (norm_nonneg _) (hgn x) 2
        _ = Cf * Cu ^ 2 * (1 + ‖x‖) ^ (Nf + 2 * Nu) := by
            rw [mul_pow, ← pow_mul, Nat.mul_comm Nu 2]
            rw [show Cf * (1 + ‖x‖) ^ Nf * (Cu ^ 2 * (1 + ‖x‖) ^ (2 * Nu))
                  = Cf * Cu ^ 2 * ((1 + ‖x‖) ^ Nf * (1 + ‖x‖) ^ (2 * Nu)) by ring]
            rw [← pow_add]
  -- continuity helpers
  have hu1 : ContDiff ℝ 2 (fderiv ℝ u) := hu.fderiv_right (m := 2) (by norm_num)
  have hD2c : Continuous (fun x : E => fderiv ℝ (fderiv ℝ u) x) :=
    hu1.continuous_fderiv (by norm_num)
  -- integrability of the sum-of-squares integrand
  have hIntB : Integrable (fun x : E =>
      (∑ i : Fin n, ∑ j : Fin n, ((fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1)) (EuclideanSpace.single j 1)) ^ 2) * Real.exp (-(f x))) := by
    refine Commons.Analysis.GaussianMeasure.integrable_mul_exp_neg_stronglyConvex f (fun x =>
      ∑ i : Fin n, ∑ j : Fin n, ((fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1)) (EuclideanSpace.single j 1)) ^ 2) hf hconv ?_ ((n : ℝ) ^ 2 * Cu ^ 2) (by positivity) (2 * Nu) ?_
    · refine continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ => ?_))
      exact (((hD2c.clm_apply continuous_const).clm_apply continuous_const).pow 2)
    · intro x
      rw [abs_of_nonneg (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _)))]
      have hterm : ∀ i j : Fin n, ((fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1)) (EuclideanSpace.single j 1)) ^ 2 ≤ Cu ^ 2 * (1 + ‖x‖) ^ (2 * Nu) := by
        intro i j
        have h := (hgu' x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) 0).2.2.1
        have h1 : ‖EuclideanSpace.single i (1:ℝ)‖ = 1 := by simp
        have h2 : ‖EuclideanSpace.single j (1:ℝ)‖ = 1 := by simp
        rw [h1, h2, mul_one, mul_one] at h
        calc ((fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1)) (EuclideanSpace.single j 1)) ^ 2
            = |(fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1)) (EuclideanSpace.single j 1)| ^ 2 := by rw [sq_abs]
          _ ≤ (Cu * (1 + ‖x‖) ^ Nu) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
          _ = Cu ^ 2 * (1 + ‖x‖) ^ (2 * Nu) := by rw [mul_pow, ← pow_mul, Nat.mul_comm Nu 2]
      calc (∑ i : Fin n, ∑ j : Fin n, ((fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1)) (EuclideanSpace.single j 1)) ^ 2)
          ≤ ∑ i : Fin n, ∑ j : Fin n, Cu ^ 2 * (1 + ‖x‖) ^ (2 * Nu) :=
            Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hterm i j))
        _ = (n : ℝ) ^ 2 * Cu ^ 2 * (1 + ‖x‖) ^ (2 * Nu) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring
  have hIntD' : Integrable (fun x : E =>
      2 * Real.pi * (‖fderiv ℝ u x‖ ^ 2 * Real.exp (-(f x)))) := hIntD.const_mul _
  have hpt : ∀ x : E,
      2 * Real.pi * (‖fderiv ℝ u x‖ ^ 2 * Real.exp (-(f x)))
        ≤ (fderiv ℝ (fderiv ℝ f) x ((InnerProductSpace.toDual ℝ (E)).symm (fderiv ℝ u x)) ((InnerProductSpace.toDual ℝ (E)).symm (fderiv ℝ u x))) * Real.exp (-(f x)) := by
    intro x
    have hh := hH x ((InnerProductSpace.toDual ℝ (E)).symm (fderiv ℝ u x))
    rw [LinearIsometryEquiv.norm_map] at hh
    have h2 : 2 * Real.pi * ‖fderiv ℝ u x‖ ^ 2 ≤
        fderiv ℝ (fderiv ℝ f) x ((InnerProductSpace.toDual ℝ (E)).symm (fderiv ℝ u x)) ((InnerProductSpace.toDual ℝ (E)).symm (fderiv ℝ u x)) := hh
    calc 2 * Real.pi * (‖fderiv ℝ u x‖ ^ 2 * Real.exp (-(f x)))
        = (2 * Real.pi * ‖fderiv ℝ u x‖ ^ 2) * Real.exp (-(f x)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
  have hmono : 2 * Real.pi * (∫ x, ‖fderiv ℝ u x‖ ^ 2 * Real.exp (-(f x)))
      ≤ ∫ x, (fderiv ℝ (fderiv ℝ f) x ((InnerProductSpace.toDual ℝ (E)).symm (fderiv ℝ u x)) ((InnerProductSpace.toDual ℝ (E)).symm (fderiv ℝ u x))) * Real.exp (-(f x)) := by
    rw [← integral_const_mul]
    exact integral_mono hIntD' hIntC hpt
  have hsplit : (∫ x, ((∑ i : Fin n, ∑ j : Fin n, ((fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1)) (EuclideanSpace.single j 1)) ^ 2) + (fderiv ℝ (fderiv ℝ f) x ((InnerProductSpace.toDual ℝ (E)).symm (fderiv ℝ u x)) ((InnerProductSpace.toDual ℝ (E)).symm (fderiv ℝ u x)))) * Real.exp (-(f x)))
      = (∫ x, (∑ i : Fin n, ∑ j : Fin n, ((fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1)) (EuclideanSpace.single j 1)) ^ 2) * Real.exp (-(f x)))
        + (∫ x, (fderiv ℝ (fderiv ℝ f) x ((InnerProductSpace.toDual ℝ (E)).symm (fderiv ℝ u x)) ((InnerProductSpace.toDual ℝ (E)).symm (fderiv ℝ u x))) * Real.exp (-(f x))) := by
    rw [show (fun x : E => ((∑ i : Fin n, ∑ j : Fin n, ((fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1)) (EuclideanSpace.single j 1)) ^ 2) + (fderiv ℝ (fderiv ℝ f) x ((InnerProductSpace.toDual ℝ (E)).symm (fderiv ℝ u x)) ((InnerProductSpace.toDual ℝ (E)).symm (fderiv ℝ u x)))) * Real.exp (-(f x)))
        = (fun x : E => (∑ i : Fin n, ∑ j : Fin n, ((fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1)) (EuclideanSpace.single j 1)) ^ 2) * Real.exp (-(f x)) + (fderiv ℝ (fderiv ℝ f) x ((InnerProductSpace.toDual ℝ (E)).symm (fderiv ℝ u x)) ((InnerProductSpace.toDual ℝ (E)).symm (fderiv ℝ u x))) * Real.exp (-(f x))) from funext (fun x => by ring)]
    exact integral_add hIntB hIntC
  have h1 : 4 * Real.pi * (∫ x, ‖fderiv ℝ u x‖ ^ 2 * Real.exp (-(f x)))
      = 2 * Real.pi * (∫ x, ‖fderiv ℝ u x‖ ^ 2 * Real.exp (-(f x)))
        + 2 * Real.pi * (∫ x, ‖fderiv ℝ u x‖ ^ 2 * Real.exp (-(f x))) := by ring
  have h4 : (∫ x, (- Laplacian.laplacian u x + inner ℝ ((InnerProductSpace.toDual ℝ (E)).symm (fderiv ℝ f x)) ((InnerProductSpace.toDual ℝ (E)).symm (fderiv ℝ u x))) ^ 2 * Real.exp (-(f x)))
      = (∫ x, (∑ i : Fin n, ∑ j : Fin n, ((fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1)) (EuclideanSpace.single j 1)) ^ 2) * Real.exp (-(f x)))
        + (∫ x, (fderiv ℝ (fderiv ℝ f) x ((InnerProductSpace.toDual ℝ (E)).symm (fderiv ℝ u x)) ((InnerProductSpace.toDual ℝ (E)).symm (fderiv ℝ u x))) * Real.exp (-(f x))) := hBoch.trans hsplit
  linarith [h1, hebl, hmono, h4]



theorem creation_energy_bound_even_smooth {n : ℕ} (f u : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 2 f) (hfe : ∀ x, f (-x) = f x) (hH : ∀ x v : EuclideanSpace ℝ (Fin n), 2 * Real.pi * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) x v v) (hconv : ConvexOn ℝ Set.univ (fun x => f x - Real.pi * ‖x‖ ^ 2)) (hgf : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x v : EuclideanSpace ℝ (Fin n), |fderiv ℝ f x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ∧ |fderiv ℝ (fderiv ℝ f) x v v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ^ 2) (hu : ContDiff ℝ 3 u) (hueven : ∀ x, u (-x) = u x) (hgu : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x v w z : EuclideanSpace ℝ (Fin n), |u x| ≤ C * (1 + ‖x‖) ^ N ∧ |fderiv ℝ u x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ∧ |fderiv ℝ (fderiv ℝ u) x v w| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ * ‖w‖ ∧ |fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x v w z| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ * ‖w‖ * ‖z‖) : 4 * Real.pi * (∫ x, ‖fderiv ℝ u x‖ ^ 2 * Real.exp (-(f x))) ≤ (∫ x, (- Laplacian.laplacian u x + inner ℝ ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ f x)) ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ u x))) ^ 2 * Real.exp (-(f x))) := by
  exact creation_energy_aux f u hf hfe hH hconv hgf hu hueven hgu

end Commons.Analysis.GaussianMeasure
