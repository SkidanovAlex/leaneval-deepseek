import Mathlib
import Submission.Work.ThomBordism.LeadChapter.TubeDetDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Lead chapter, tube determinant: the structural calculus of the block model

`Work.ThomBordism.LeadChapter.theta` is the affine block reparametrisation of the tube point
(`modelEuc` of the source point `srcOfSpatial k v`), and `thetaInv` its explicit inverse.  This file
collects the elementary calculus of that pair, which the determinant and inverse-function lemmas
consume:

* the collar cube coordinate of `srcOfSpatial k v` is `ptScalar (v i)`;
* the model point of `srcOfSpatial k v`, and the fact that `modelAffineInv` of it is the cube point
  (`modelAffineInv_modelPoint`) — the pointwise content of the inverse identity;
* the component formula for `theta`;
* `thetaInv_theta`: `thetaInv` is a left inverse of `theta`;
* the explicit composite form of `theta` (`theta_eq_comp`) and of its derivative (`dtheta_eq`).

No `sorry`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped Manifold ContDiff Topology
open CategoryTheory

namespace Work.ThomBordism.LeadChapter

open Work.PTGeometric

noncomputable section

variable {k : ℕ} {D : Work.ThomBordism.PontryaginThom.ThomTarget k} {ι : Type} [Fintype ι]
  {Fam : ι → Work.ThomBordism.Man8}

/-! ## The collar coordinates of `srcOfSpatial` -/

/-- The collar cube coordinate of `srcOfSpatial k v` is the cube chart of `v`. -/
theorem collPt_srcOfSpatial (v : EuclideanSpace ℝ (Fin (k + 8))) (m : Fin (k + 8)) :
    ((collPt k (srcOfSpatial k v) m : Set.Icc (0:ℝ) 1) : ℝ) = ptScalar (v.ofLp m) := by
  rw [collPt_apply, cubeCoord_apply_coe, ptScalar]
  rw [tail_srcCast_srcOfSpatial]

/-- The model point of `srcOfSpatial k v`, coordinatewise. -/
theorem modelPoint_srcOfSpatial (k₀ j₀ : ℕ) (v : EuclideanSpace ℝ (Fin (k + 8)))
    (m : Fin (k + 8)) :
    modelPoint k (cZero k) (cOne k) k₀ j₀ (srcOfSpatial k v) m
      = (if m = cZero k then (2:ℝ)^(k₀+1) * ptScalar (v.ofLp m) - 1
         else if m = cOne k then (2:ℝ)^(j₀+1) * ptScalar (v.ofLp m) - 1
         else ptScalar (v.ofLp m)) := by
  simp only [modelPoint, collPt_srcOfSpatial]
  by_cases hm0 : m = cZero k
  · subst hm0; simp
  · rw [if_neg hm0, if_neg hm0]
    by_cases hm1 : m = cOne k
    · subst hm1; simp
    · rw [if_neg hm1, if_neg hm1]

/-- **The pointwise inverse identity of the block model**: the explicit inverse `modelAffineInv`
applied to the model point of `srcOfSpatial k v` recovers the cube point. -/
theorem modelAffineInv_modelPoint (k₀ j₀ : ℕ) (v : EuclideanSpace ℝ (Fin (k + 8))) :
    modelAffineInv k k₀ j₀
        (fun i => modelPoint k (cZero k) (cOne k) k₀ j₀ (srcOfSpatial k v) (finKRInv k i))
      = ptCubeFun (k + 8) (euToPi (k + 8) v) := by
  funext m
  rw [modelAffineInv, ptCubeFun, euToPi_apply]
  by_cases hm0 : m = cZero k
  · subst hm0
    rw [if_pos rfl, finKRInv_finKR, modelPoint_srcOfSpatial (k₀ := k₀) (j₀ := j₀) v (cZero k),
      if_pos rfl]
    field_simp
    ring
  · rw [if_neg hm0]
    by_cases hm1 : m = cOne k
    · subst hm1
      rw [if_pos rfl, finKRInv_finKR, modelPoint_srcOfSpatial (k₀ := k₀) (j₀ := j₀) v (cOne k),
        if_neg (Ne.symm (cZero_ne_cOne k)), if_pos rfl]
      field_simp
      ring
    · rw [if_neg hm1, finKRInv_finKR, modelPoint_srcOfSpatial (k₀ := k₀) (j₀ := j₀) v m,
        if_neg hm0, if_neg hm1]

/-! ## The model point of `theta` -/

/-- The component formula for `theta`: reading the tube point of `theta G m k₀ j₀ v` back through
the affine chart `2 R (· - 1/2)` gives the model point of the source. -/
theorem euToPi_theta_apply (G : GenuineTubeGeometry k D ι Fam) (m k₀ j₀ : ℕ) (hR : 0 < G.R)
    (v : EuclideanSpace ℝ (Fin (k + 8))) (i : Fin (8 + k)) :
    euToPi (8 + k) (theta G m k₀ j₀ v) i / (2 * G.R) + 1/2
      = modelPoint k (cZero k) (cOne k) k₀ j₀ (srcOfSpatial k v) (finKRInv k i) := by
  rw [euToPi_apply]
  show ((theta G m k₀ j₀ v).ofLp i) / (2 * G.R) + 1/2 = _
  rw [show theta G m k₀ j₀ v
      = eucOfReal (8 + k) G.R (fun l => modelPoint k (cZero k) (cOne k) k₀ j₀
          (srcOfSpatial k v) (finKRInv k l)) from rfl]
  rw [eucOfReal_apply]
  have hR' : (2 * G.R) ≠ 0 := by positivity
  field_simp
  ring

/-! ## The inverse identity -/

/-- **`thetaInv` is a left inverse of `theta`** (the first conjunct of `thetaInvAux`). -/
theorem thetaInv_theta (G : GenuineTubeGeometry k D ι Fam) (m k₀ j₀ : ℕ) (hR : 0 < G.R)
    (v : EuclideanSpace ℝ (Fin (k + 8))) :
    thetaInv G m k₀ j₀ (theta G m k₀ j₀ v) = v := by
  rw [thetaInv]
  have h1 : (fun i => euToPi (8 + k) (theta G m k₀ j₀ v) i / (2 * G.R) + 1 / 2)
      = (fun i => modelPoint k (cZero k) (cOne k) k₀ j₀ (srcOfSpatial k v) (finKRInv k i)) := by
    funext i
    exact euToPi_theta_apply G m k₀ j₀ hR v i
  rw [h1, modelAffineInv_modelPoint, ptCubeInvFun_ptCubeFun]
  have hpi : (piToEucl (k + 8)).symm = euToPi (k + 8) := by
    ext x i
    rfl
  rw [← hpi]
  exact ContinuousLinearEquiv.apply_symm_apply (piToEucl (k + 8)) v

/-! ## `modelAffineInv` is affine -/

/-- The linear part of the affine map `modelAffineInv`. -/
def modelAffineInvLin (k k₀ j₀ : ℕ) :
    (Fin (8 + k) → ℝ) →L[ℝ] (Fin (k + 8) → ℝ) :=
  ContinuousLinearMap.pi (fun m : Fin (k + 8) =>
    if m = cZero k then ((2:ℝ)^(k₀+1))⁻¹ • ContinuousLinearMap.proj (finKR k (cZero k))
    else if m = cOne k then ((2:ℝ)^(j₀+1))⁻¹ • ContinuousLinearMap.proj (finKR k (cOne k))
    else ContinuousLinearMap.proj (finKR k m))

/-- The constant part of the affine map `modelAffineInv`. -/
def modelAffineInvConst (k k₀ j₀ : ℕ) : Fin (k + 8) → ℝ :=
  fun m => if m = cZero k then (1:ℝ)/2^(k₀+1)
    else if m = cOne k then 1/2^(j₀+1) else 0

theorem modelAffineInv_apply_eq (k k₀ j₀ : ℕ) (w : Fin (8 + k) → ℝ) (m : Fin (k + 8)) :
    modelAffineInv k k₀ j₀ w m = modelAffineInvLin k k₀ j₀ w m + modelAffineInvConst k k₀ j₀ m := by
  rw [modelAffineInv, modelAffineInvLin, modelAffineInvConst, ContinuousLinearMap.pi_apply]
  by_cases hm0 : m = cZero k
  · subst hm0
    rw [if_pos rfl, if_pos rfl, if_pos rfl]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
    field_simp
  · rw [if_neg hm0, if_neg hm0, if_neg hm0]
    by_cases hm1 : m = cOne k
    · subst hm1
      rw [if_pos rfl, if_pos rfl, if_pos rfl]
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
      field_simp
    · rw [if_neg hm1, if_neg hm1, if_neg hm1]
      simp only [ContinuousLinearMap.proj_apply]
      ring

/-- `modelAffineInv` is affine, with linear part `modelAffineInvLin`. -/
theorem hasFDerivAt_modelAffineInv (k k₀ j₀ : ℕ) (w : Fin (8 + k) → ℝ) :
    HasFDerivAt (modelAffineInv k k₀ j₀) (modelAffineInvLin k k₀ j₀) w := by
  have h : HasFDerivAt (fun w : Fin (8 + k) → ℝ => modelAffineInvLin k k₀ j₀ w
      + modelAffineInvConst k k₀ j₀) (modelAffineInvLin k k₀ j₀) w :=
    (modelAffineInvLin k k₀ j₀).hasFDerivAt.add_const _
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)
  exact funext fun m => modelAffineInv_apply_eq k k₀ j₀ w m

/-! ## The explicit composite form of `theta` and its derivative -/

/-- **`theta` is the explicit composite** `piToEucl ∘ shiftScale ∘ modelAffine ∘ ptCubeFun ∘
euToPi` (the collar reindexing `cubeLin ∘ srcOfSpatial` is the identity). -/
theorem theta_eq_comp (G : GenuineTubeGeometry k D ι Fam) (m k₀ j₀ : ℕ) :
    theta G m k₀ j₀ = fun v => piToEucl (8 + k) (shiftScale (8 + k) G.R
        (modelAffine k k₀ j₀ (ptCubeFun (k + 8) (euToPi (k + 8) v)))) := by
  funext v
  show modelEuc G (cZero k) (cOne k) k₀ j₀ (srcOfSpatial k v) = _
  rw [modelEuc_eq_comp]
  simp only [Function.comp_apply]
  rw [show cubeLin k (srcOfSpatial k v) = v from tail_srcCast_srcOfSpatial k v]
  rfl

/-- The explicit derivative of `theta`. -/
def dthetaLin (G : GenuineTubeGeometry k D ι Fam) (k₀ j₀ : ℕ)
    (v : EuclideanSpace ℝ (Fin (k + 8))) :
    EuclideanSpace ℝ (Fin (k + 8)) →L[ℝ] EuclideanSpace ℝ (Fin (8 + k)) :=
  ((piToEucl (8 + k)).toContinuousLinearMap).comp
    (((2 * G.R) • (1 : (Fin (8 + k) → ℝ) →L[ℝ] (Fin (8 + k) → ℝ))).comp
      ((modelLin k k₀ j₀).comp
        ((fderiv ℝ (ptCubeFun (k + 8)) (euToPi (k + 8) v)).comp (euToPi (k + 8)))))

/-- The derivative of the explicit composite form of `theta`. -/
theorem hasFDerivAt_thetaComp (G : GenuineTubeGeometry k D ι Fam) (k₀ j₀ : ℕ)
    (v : EuclideanSpace ℝ (Fin (k + 8))) :
    HasFDerivAt (fun v => piToEucl (8 + k) (shiftScale (8 + k) G.R
        (modelAffine k k₀ j₀ (ptCubeFun (k + 8) (euToPi (k + 8) v)))))
      (dthetaLin G k₀ j₀ v) v := by
  have h1 : HasFDerivAt (⇑(euToPi (k + 8))) (euToPi (k + 8)) v :=
    (euToPi (k + 8)).hasFDerivAt
  have h2 : HasFDerivAt (ptCubeFun (k + 8))
      (fderiv ℝ (ptCubeFun (k + 8)) (euToPi (k + 8) v)) (euToPi (k + 8) v) :=
    (differentiableAt_ptCubeFun (k + 8) _).hasFDerivAt
  have h3 : HasFDerivAt (modelAffine k k₀ j₀) (modelLin k k₀ j₀)
      (ptCubeFun (k + 8) (euToPi (k + 8) v)) := hasFDerivAt_modelAffine k k₀ j₀ _
  have h4 : HasFDerivAt (shiftScale (8 + k) G.R)
      ((2 * G.R) • (1 : (Fin (8 + k) → ℝ) →L[ℝ] (Fin (8 + k) → ℝ)))
      (modelAffine k k₀ j₀ (ptCubeFun (k + 8) (euToPi (k + 8) v))) :=
    hasFDerivAt_shiftScale (8 + k) G.R _
  have h5 : HasFDerivAt (⇑(piToEucl (8 + k))) ((piToEucl (8 + k)).toContinuousLinearMap)
      (shiftScale (8 + k) G.R (modelAffine k k₀ j₀ (ptCubeFun (k + 8) (euToPi (k + 8) v)))) :=
    (piToEucl (8 + k)).hasFDerivAt
  have h21 : HasFDerivAt (fun w : EuclideanSpace ℝ (Fin (k + 8)) =>
        ptCubeFun (k + 8) (euToPi (k + 8) w))
      ((fderiv ℝ (ptCubeFun (k + 8)) (euToPi (k + 8) v)).comp (euToPi (k + 8))) v :=
    HasFDerivAt.comp (x := v) (g := ptCubeFun (k + 8)) h2 h1
  have h31 : HasFDerivAt (fun w : EuclideanSpace ℝ (Fin (k + 8)) =>
        modelAffine k k₀ j₀ (ptCubeFun (k + 8) (euToPi (k + 8) w)))
      ((modelLin k k₀ j₀).comp
        ((fderiv ℝ (ptCubeFun (k + 8)) (euToPi (k + 8) v)).comp (euToPi (k + 8)))) v :=
    HasFDerivAt.comp (x := v) (g := modelAffine k k₀ j₀) h3 h21
  have h41 : HasFDerivAt (fun w : EuclideanSpace ℝ (Fin (k + 8)) =>
        shiftScale (8 + k) G.R (modelAffine k k₀ j₀ (ptCubeFun (k + 8) (euToPi (k + 8) w))))
      (((2 * G.R) • (1 : (Fin (8 + k) → ℝ) →L[ℝ] (Fin (8 + k) → ℝ))).comp
        ((modelLin k k₀ j₀).comp
          ((fderiv ℝ (ptCubeFun (k + 8)) (euToPi (k + 8) v)).comp (euToPi (k + 8))))) v :=
    HasFDerivAt.comp (x := v) (g := shiftScale (8 + k) G.R) h4 h31
  have h51 : HasFDerivAt (fun w : EuclideanSpace ℝ (Fin (k + 8)) =>
        piToEucl (8 + k) (shiftScale (8 + k) G.R
          (modelAffine k k₀ j₀ (ptCubeFun (k + 8) (euToPi (k + 8) w)))))
      (((piToEucl (8 + k)).toContinuousLinearMap).comp
        (((2 * G.R) • (1 : (Fin (8 + k) → ℝ) →L[ℝ] (Fin (8 + k) → ℝ))).comp
          ((modelLin k k₀ j₀).comp
            ((fderiv ℝ (ptCubeFun (k + 8)) (euToPi (k + 8) v)).comp (euToPi (k + 8)))))) v :=
    HasFDerivAt.comp (x := v) (g := piToEucl (8 + k)) h5 h41
  exact h51

/-- The explicit derivative of `theta`. -/
theorem dtheta_eq (G : GenuineTubeGeometry k D ι Fam) (m k₀ j₀ : ℕ)
    (v : EuclideanSpace ℝ (Fin (k + 8))) :
    dtheta G m k₀ j₀ v = dthetaLin G k₀ j₀ v := by
  rw [dtheta, theta_eq_comp]
  exact (hasFDerivAt_thetaComp G k₀ j₀ v).fderiv

/-- `theta` is differentiable everywhere. -/
theorem hasFDerivAt_theta (G : GenuineTubeGeometry k D ι Fam) (m k₀ j₀ : ℕ)
    (v : EuclideanSpace ℝ (Fin (k + 8))) :
    HasFDerivAt (theta G m k₀ j₀) (dtheta G m k₀ j₀ v) v := by
  rw [theta_eq_comp, dtheta_eq]
  exact hasFDerivAt_thetaComp G k₀ j₀ v

/-- `theta` is differentiable everywhere. -/
theorem differentiableAt_theta (G : GenuineTubeGeometry k D ι Fam) (m k₀ j₀ : ℕ)
    (v : EuclideanSpace ℝ (Fin (k + 8))) :
    DifferentiableAt ℝ (theta G m k₀ j₀) v :=
  (hasFDerivAt_theta G m k₀ j₀ v).differentiableAt

/-! ## A left inverse of a square continuous linear map is a two-sided inverse -/

/-- A left inverse of a continuous linear map between Euclidean spaces of equal dimension is a
two-sided inverse. -/
theorem comp_eq_one_of_comp_eq_one
    (A : EuclideanSpace ℝ (Fin (k + 8)) →L[ℝ] EuclideanSpace ℝ (Fin (8 + k)))
    (B : EuclideanSpace ℝ (Fin (8 + k)) →L[ℝ] EuclideanSpace ℝ (Fin (k + 8)))
    (hBA : B.comp A = 1) : A.comp B = 1 := by
  have hinj : Function.Injective
      (A : EuclideanSpace ℝ (Fin (k + 8)) → EuclideanSpace ℝ (Fin (8 + k))) := by
    intro x y hxy
    have hx : B (A x) = x := by simpa using DFunLike.congr_fun hBA x
    have hy : B (A y) = y := by simpa using DFunLike.congr_fun hBA y
    rw [← hx, hxy]
    exact hy
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin (k + 8)))
      = Module.finrank ℝ (EuclideanSpace ℝ (Fin (8 + k))) := by
    rw [finrank_euclideanSpace, finrank_euclideanSpace, Fintype.card_fin, Fintype.card_fin]
    omega
  have hsurj : Function.Surjective
      (A : EuclideanSpace ℝ (Fin (k + 8)) → EuclideanSpace ℝ (Fin (8 + k))) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := A.toLinearMap) hfr).mp hinj
  apply ContinuousLinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := hsurj y
  have hx : B (A x) = x := by simpa using DFunLike.congr_fun hBA x
  show A (B (A x)) = A x
  rw [hx]

/-! ## Differentiability of `thetaInv` at the points of the image of `theta` -/

/-- **`thetaInv` is differentiable at `theta G m k₀ j₀ v`**: the inner affine chart lands on the cube
point `ptCubeFun (euToPi v)`, where `ptCubeInvFun` is differentiable. -/
theorem thetaAux_differentiableAt_thetaInv (G : GenuineTubeGeometry k D ι Fam) (m k₀ j₀ : ℕ)
    (hR : 0 < G.R) (v : EuclideanSpace ℝ (Fin (k + 8))) :
    DifferentiableAt ℝ (thetaInv G m k₀ j₀) (theta G m k₀ j₀ v) := by
  have hR' : (2 * G.R) ≠ 0 := by positivity
  let w : Fin (8 + k) → ℝ := fun i => euToPi (8 + k) (theta G m k₀ j₀ v) i / (2 * G.R) + 1/2
  let W : EuclideanSpace ℝ (Fin (8 + k)) →L[ℝ] (Fin (8 + k) → ℝ) :=
    ((2 * G.R)⁻¹) • (euToPi (8 + k))
  let W' : (Fin (k + 8) → ℝ) →L[ℝ] (Fin (k + 8) → ℝ) :=
    ContinuousLinearMap.pi fun i : Fin (k + 8) =>
      fderiv ℝ ptScalarInv (ptCubeFun (k + 8) (euToPi (k + 8) v) i) ∘SL
        ContinuousLinearMap.proj i
  have hw : modelAffineInv k k₀ j₀ w = ptCubeFun (k + 8) (euToPi (k + 8) v) := by
    have h1 : w = (fun i => modelPoint k (cZero k) (cOne k) k₀ j₀ (srcOfSpatial k v)
        (finKRInv k i)) := by
      funext i
      exact euToPi_theta_apply G m k₀ j₀ hR v i
    rw [h1, modelAffineInv_modelPoint]
  have hA : HasFDerivAt (fun u : EuclideanSpace ℝ (Fin (8 + k)) =>
        fun i => euToPi (8 + k) u i / (2 * G.R) + 1/2) W (theta G m k₀ j₀ v) := by
    refine ((((2 * G.R)⁻¹) • (euToPi (8 + k))).hasFDerivAt.add_const
      (fun _ : Fin (8 + k) => (1:ℝ)/2)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun u => ?_)
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have hB : HasFDerivAt (modelAffineInv k k₀ j₀) (modelAffineInvLin k k₀ j₀) w :=
    hasFDerivAt_modelAffineInv k k₀ j₀ w
  have hBA : HasFDerivAt (fun u : EuclideanSpace ℝ (Fin (8 + k)) =>
        modelAffineInv k k₀ j₀ (fun i => euToPi (8 + k) u i / (2 * G.R) + 1/2))
      ((modelAffineInvLin k k₀ j₀).comp W) (theta G m k₀ j₀ v) :=
    HasFDerivAt.comp (x := theta G m k₀ j₀ v) (g := modelAffineInv k k₀ j₀) hB hA
  have hC : HasFDerivAt (ptCubeInvFun (k + 8)) W' (modelAffineInv k k₀ j₀ w) := by
    rw [hw]
    exact hasFDerivAt_ptCubeInvFun (k + 8) (euToPi (k + 8) v)
  have hCBA : HasFDerivAt (fun u : EuclideanSpace ℝ (Fin (8 + k)) =>
        ptCubeInvFun (k + 8) (modelAffineInv k k₀ j₀
          (fun i => euToPi (8 + k) u i / (2 * G.R) + 1/2)))
      (W'.comp ((modelAffineInvLin k k₀ j₀).comp W)) (theta G m k₀ j₀ v) :=
    HasFDerivAt.comp (x := theta G m k₀ j₀ v) (g := ptCubeInvFun (k + 8)) hC hBA
  have hfinal : HasFDerivAt (fun u : EuclideanSpace ℝ (Fin (8 + k)) =>
        piToEucl (k + 8) (ptCubeInvFun (k + 8) (modelAffineInv k k₀ j₀
          (fun i => euToPi (8 + k) u i / (2 * G.R) + 1/2))))
      (((piToEucl (k + 8)).toContinuousLinearMap).comp
        (W'.comp ((modelAffineInvLin k k₀ j₀).comp W))) (theta G m k₀ j₀ v) :=
    HasFDerivAt.comp (x := theta G m k₀ j₀ v) (g := piToEucl (k + 8))
      (piToEucl (k + 8)).hasFDerivAt hCBA
  have hdiff : DifferentiableAt ℝ (fun u : EuclideanSpace ℝ (Fin (8 + k)) =>
        piToEucl (k + 8) (ptCubeInvFun (k + 8) (modelAffineInv k k₀ j₀
          (fun i => euToPi (8 + k) u i / (2 * G.R) + 1/2)))) (theta G m k₀ j₀ v) :=
    hfinal.differentiableAt
  refine hdiff.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
  rfl

/-! ## The determinant of the tube endomorphism -/

section Det

/-- The affine scale attached to the `i`-th coordinate of the model point. -/
def thetaScale (k k₀ j₀ : ℕ) (i : Fin (k + 8)) : ℝ :=
  if i = cZero k then (2:ℝ)^(k₀+1) else if i = cOne k then (2:ℝ)^(j₀+1) else 1

/-- The scalar profile of the `i`-th coordinate of the tube model read through `reEKInv`. -/
def thetaProfile (G : GenuineTubeGeometry k D ι Fam) (k₀ j₀ : ℕ) (i : Fin (k + 8)) (s : ℝ) : ℝ :=
  2 * G.R * ((if i = cZero k then (2:ℝ)^(k₀+1) * ptScalar s - 1
              else if i = cOne k then (2:ℝ)^(j₀+1) * ptScalar s - 1
              else ptScalar s) - 1/2)

theorem thetaProfile_apply (G : GenuineTubeGeometry k D ι Fam) (k₀ j₀ : ℕ) (i : Fin (k + 8))
    (s : ℝ) :
    thetaProfile G k₀ j₀ i s
      = 2 * G.R * ((if i = cZero k then (2:ℝ)^(k₀+1) * ptScalar s - 1
          else if i = cOne k then (2:ℝ)^(j₀+1) * ptScalar s - 1
          else ptScalar s) - 1/2) := rfl

/-- The derivative of `ptScalar` is `1/(2 (1+s²)^{3/2})`. -/
theorem hasDerivAt_ptScalar (s : ℝ) :
    HasDerivAt ptScalar (1 / (2 * Real.sqrt (1 + s^2)^3)) s := by
  have hinner : HasDerivAt (fun z : ℝ => 1 + z^2) (2*s) s := by
    have h' := (hasDerivAt_const (x := s) (1:ℝ)).add (hasDerivAt_pow 2 s)
    have h'' : HasDerivAt (fun z : ℝ => 1 + z^2) (0 + (2:ℝ) * s ^ (2 - 1)) s :=
      h'.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => rfl)
    exact h''.congr_deriv (by norm_num)
  have hsqrt : HasDerivAt (fun z : ℝ => Real.sqrt (1 + z^2)) (s / Real.sqrt (1 + s^2)) s := by
    have h := (Real.hasDerivAt_sqrt (x := 1 + s^2) (by positivity)).comp s hinner
    refine h.congr_deriv ?_
    field_simp
  have hdiv : HasDerivAt (fun z : ℝ => z / Real.sqrt (1 + z^2))
      ((1 * Real.sqrt (1 + s^2) - s * (s / Real.sqrt (1 + s^2))) / (Real.sqrt (1 + s^2))^2) s :=
    (hasDerivAt_id s).div hsqrt (by positivity)
  have h3 : HasDerivAt (fun z : ℝ => 1 + z / Real.sqrt (1 + z^2))
      (0 + (1 * Real.sqrt (1 + s^2) - s * (s / Real.sqrt (1 + s^2)))
        / (Real.sqrt (1 + s^2))^2) s :=
    (hasDerivAt_const (x := s) (1:ℝ)).add hdiv
  have h4 : HasDerivAt (fun x : ℝ => (1 + x / Real.sqrt (1 + x^2))/2)
      ((0 + (1 * Real.sqrt (1 + s^2) - s * (s / Real.sqrt (1 + s^2)))
        / (Real.sqrt (1 + s^2))^2)/2) s :=
    h3.div_const 2
  refine (h4.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)).congr_deriv ?_
  · rfl
  · field_simp
    rw [Real.sq_sqrt (by positivity)]
    ring

theorem deriv_ptScalar_pos (s : ℝ) : 0 < deriv ptScalar s := by
  rw [(hasDerivAt_ptScalar s).deriv]
  positivity

/-- The derivative of the scalar profile. -/
theorem hasDerivAt_thetaProfile (G : GenuineTubeGeometry k D ι Fam) (k₀ j₀ : ℕ)
    (i : Fin (k + 8)) (s : ℝ) :
    HasDerivAt (thetaProfile G k₀ j₀ i) (2 * G.R * thetaScale k k₀ j₀ i * deriv ptScalar s) s := by
  have hfun : thetaProfile G k₀ j₀ i
      = (fun s => 2 * G.R * ((if i = cZero k then (2:ℝ)^(k₀+1) * ptScalar s - 1
          else if i = cOne k then (2:ℝ)^(j₀+1) * ptScalar s - 1
          else ptScalar s) - 1/2)) := by
    funext s
    rw [thetaProfile_apply]
  rw [hfun]
  by_cases h0 : i = cZero k
  · simp only [thetaScale, if_pos h0]
    have h := (((hasDerivAt_ptScalar s).const_mul ((2:ℝ)^(k₀+1))).add_const (-1)).add_const (-(1/2))
    have h2 := h.const_mul (2 * G.R)
    refine h2.congr_deriv ?_
    rw [(hasDerivAt_ptScalar s).deriv]
    ring
  · simp only [if_neg h0]
    by_cases h1 : i = cOne k
    · simp only [thetaScale, if_neg h0, if_pos h1]
      have h := (((hasDerivAt_ptScalar s).const_mul ((2:ℝ)^(j₀+1))).add_const (-1)).add_const (-(1/2))
      have h2 := h.const_mul (2 * G.R)
      refine h2.congr_deriv ?_
      rw [(hasDerivAt_ptScalar s).deriv]
      ring
    · simp only [thetaScale, if_neg h0, if_neg h1]
      have h := ((hasDerivAt_ptScalar s).add_const (-(1/2)))
      have h2 := h.const_mul (2 * G.R)
      refine h2.congr_deriv ?_
      rw [(hasDerivAt_ptScalar s).deriv]
      ring

/-- The scalar profile is strictly increasing in its argument. -/
theorem deriv_thetaProfile_pos (G : GenuineTubeGeometry k D ι Fam) (hR : 0 < G.R) (k₀ j₀ : ℕ)
    (i : Fin (k + 8)) (s : ℝ) : 0 < deriv (thetaProfile G k₀ j₀ i) s := by
  rw [(hasDerivAt_thetaProfile G k₀ j₀ i s).deriv]
  have h2 : 0 < 2 * G.R := by linarith
  have h4 : 0 < thetaScale k k₀ j₀ i := by
    rw [thetaScale]
    by_cases h0 : i = cZero k
    · rw [if_pos h0]; positivity
    · rw [if_neg h0]
      by_cases h1 : i = cOne k
      · rw [if_pos h1]; positivity
      · rw [if_neg h1]; norm_num
  have h5 : 0 < deriv ptScalar s := deriv_ptScalar_pos s
  exact mul_pos (mul_pos h2 h4) h5

/-- The coordinatewise map of the tube model. -/
def thetaMap (G : GenuineTubeGeometry k D ι Fam) (k₀ j₀ : ℕ) :
    (Fin (k + 8) → ℝ) → (Fin (k + 8) → ℝ) :=
  fun x i => thetaProfile G k₀ j₀ i (x i)

/-- The derivative of `thetaMap`. -/
def thetaMapDeriv (G : GenuineTubeGeometry k D ι Fam) (k₀ j₀ : ℕ) (x : Fin (k + 8) → ℝ) :
    (Fin (k + 8) → ℝ) →L[ℝ] (Fin (k + 8) → ℝ) :=
  ContinuousLinearMap.pi fun i => (fderiv ℝ (thetaProfile G k₀ j₀ i) (x i)).comp
    (ContinuousLinearMap.proj i)

theorem hasFDerivAt_thetaMap (G : GenuineTubeGeometry k D ι Fam) (k₀ j₀ : ℕ)
    (x : Fin (k + 8) → ℝ) :
    HasFDerivAt (thetaMap G k₀ j₀) (thetaMapDeriv G k₀ j₀ x) x := by
  refine hasFDerivAt_pi.mpr (fun i => ?_)
  exact (((hasDerivAt_thetaProfile G k₀ j₀ i (x i)).differentiableAt).hasFDerivAt).comp x
    (((ContinuousLinearMap.proj i) : (Fin (k + 8) → ℝ) →L[ℝ] ℝ)).hasFDerivAt

/-- The determinant of `thetaMapDeriv`. -/
theorem det_thetaMapDeriv (G : GenuineTubeGeometry k D ι Fam) (k₀ j₀ : ℕ)
    (x : Fin (k + 8) → ℝ) :
    LinearMap.det (thetaMapDeriv G k₀ j₀ x).toLinearMap
      = ∏ i, deriv (thetaProfile G k₀ j₀ i) (x i) := by
  rw [← LinearMap.det_toMatrix']
  have hmat : LinearMap.toMatrix' ((thetaMapDeriv G k₀ j₀ x).toLinearMap)
      = Matrix.diagonal (fun i => deriv (thetaProfile G k₀ j₀ i) (x i)) := by
    ext i j
    by_cases h : i = j
    · subst h
      simp [LinearMap.toMatrix'_apply, thetaMapDeriv, ContinuousLinearMap.coe_pi]
    · simp [LinearMap.toMatrix'_apply, thetaMapDeriv, ContinuousLinearMap.coe_pi, h]
  rw [hmat, Matrix.det_diagonal]

/-- Conjugating a continuous linear endomorphism by a continuous linear equivalence does not change
the determinant. -/
theorem det_conj_clm {M N : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup N] [NormedSpace ℝ N] (e : M ≃L[ℝ] N) (f : M →L[ℝ] M) :
    LinearMap.det (((e : M →L[ℝ] N).toLinearMap).comp
        ((f.toLinearMap).comp ((e.symm : N →L[ℝ] M).toLinearMap)))
      = LinearMap.det f.toLinearMap := by
  rw [← LinearMap.det_conj (f := f.toLinearMap) (e := e.toLinearEquiv)]
  congr 1

/-- The `i`-th coordinate of `reEKInv`. -/
theorem reEKInv_apply (k : ℕ) (u : EuclideanSpace ℝ (Fin (8 + k))) (i : Fin (k + 8)) :
    (reEKInv k u).ofLp i = u.ofLp (finKR k i) := by
  have h : ((ContinuousLinearMap.pi fun i =>
        (ContinuousLinearMap.proj (finKR k i)).comp (euToPi (8 + k))) u)
      = (fun i => u.ofLp (finKR k i)) := by
    funext i
    rw [ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply, euToPi_apply]
  rw [reEKInv, ContinuousLinearMap.comp_apply, h]
  rfl

/-- The coordinates of `piToEucl`. -/
theorem piToEucl_ofLp (n : ℕ) (w : Fin n → ℝ) (i : Fin n) :
    (piToEucl n w).ofLp i = w i := rfl

/-- `reEKInv` of `theta` is the coordinatewise profile map of the cube coordinates. -/
theorem reEKInv_theta_eq (G : GenuineTubeGeometry k D ι Fam) (m k₀ j₀ : ℕ)
    (v : EuclideanSpace ℝ (Fin (k + 8))) :
    reEKInv k (theta G m k₀ j₀ v)
      = piToEucl (k + 8) (thetaMap G k₀ j₀ (euToPi (k + 8) v)) := by
  ext i
  rw [reEKInv_apply, piToEucl_ofLp]
  change (theta G m k₀ j₀ v).ofLp (finKR k i)
    = thetaProfile G k₀ j₀ i ((euToPi (k + 8) v) i)
  rw [thetaProfile, euToPi_apply]
  show (theta G m k₀ j₀ v).ofLp (finKR k i)
    = 2 * G.R * ((if i = cZero k then (2:ℝ)^(k₀+1) * ptScalar (v.ofLp i) - 1
        else if i = cOne k then (2:ℝ)^(j₀+1) * ptScalar (v.ofLp i) - 1
        else ptScalar (v.ofLp i)) - 1/2)
  rw [show theta G m k₀ j₀ v
      = eucOfReal (8 + k) G.R (fun l => modelPoint k (cZero k) (cOne k) k₀ j₀
          (srcOfSpatial k v) (finKRInv k l)) from rfl]
  rw [eucOfReal_apply, finKRInv_finKR, modelPoint_srcOfSpatial]

/-- `dthetaEndo` is the derivative of `reEKInv ∘ theta`. -/
theorem dthetaEndo_eq_fderiv (G : GenuineTubeGeometry k D ι Fam) (m k₀ j₀ : ℕ)
    (v : EuclideanSpace ℝ (Fin (k + 8))) :
    dthetaEndo G m k₀ j₀ v = fderiv ℝ (fun v => reEKInv k (theta G m k₀ j₀ v)) v := by
  have h : HasFDerivAt (fun v => reEKInv k (theta G m k₀ j₀ v))
      ((reEKInv k).comp (dtheta G m k₀ j₀ v)) v :=
    ((reEKInv k).hasFDerivAt.comp v (hasFDerivAt_theta G m k₀ j₀ v)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun x => rfl)
  rw [h.fderiv]
  rfl

/-- **The Jacobian of the tube block model is positive** (the last conjunct of `thetaInvAux`). -/
theorem thetaAux_det_dthetaEndo_pos (G : GenuineTubeGeometry k D ι Fam) (m k₀ j₀ : ℕ)
    (hR : 0 < G.R) (v : EuclideanSpace ℝ (Fin (k + 8))) :
    0 < LinearMap.det (dthetaEndo G m k₀ j₀ v).toLinearMap := by
  rw [dthetaEndo_eq_fderiv]
  rw [show (fun v => reEKInv k (theta G m k₀ j₀ v))
      = (fun v => piToEucl (k + 8) (thetaMap G k₀ j₀ (euToPi (k + 8) v))) from
    funext fun v => reEKInv_theta_eq G m k₀ j₀ v]
  have h1 : HasFDerivAt (⇑(euToPi (k + 8))) (euToPi (k + 8)) v :=
    (euToPi (k + 8)).hasFDerivAt
  have h2 : HasFDerivAt (thetaMap G k₀ j₀) (thetaMapDeriv G k₀ j₀ (euToPi (k + 8) v))
      (euToPi (k + 8) v) := hasFDerivAt_thetaMap G k₀ j₀ _
  have h3 : HasFDerivAt (⇑(piToEucl (k + 8))) ((piToEucl (k + 8)).toContinuousLinearMap)
      (thetaMap G k₀ j₀ (euToPi (k + 8) v)) := (piToEucl (k + 8)).hasFDerivAt
  have h21 : HasFDerivAt (fun v => thetaMap G k₀ j₀ (euToPi (k + 8) v))
      ((thetaMapDeriv G k₀ j₀ (euToPi (k + 8) v)).comp (euToPi (k + 8))) v :=
    HasFDerivAt.comp (x := v) (g := thetaMap G k₀ j₀) h2 h1
  have h321 : HasFDerivAt (fun v => piToEucl (k + 8) (thetaMap G k₀ j₀ (euToPi (k + 8) v)))
      (((piToEucl (k + 8)).toContinuousLinearMap).comp
        ((thetaMapDeriv G k₀ j₀ (euToPi (k + 8) v)).comp (euToPi (k + 8)))) v :=
    HasFDerivAt.comp (x := v) (g := piToEucl (k + 8)) h3 h21
  rw [h321.fderiv]
  simp only [ContinuousLinearMap.toLinearMap_comp]
  rw [show (euToPi (k + 8)).toLinearMap
      = (((piToEucl (k + 8)).symm : EuclideanSpace ℝ (Fin (k + 8)) →L[ℝ]
          (Fin (k + 8) → ℝ)).toLinearMap) from by
    ext x i
    rfl]
  rw [det_conj_clm (e := piToEucl (k + 8))
    (f := thetaMapDeriv G k₀ j₀ (euToPi (k + 8) v))]
  rw [det_thetaMapDeriv]
  exact Finset.prod_pos (fun i _ => deriv_thetaProfile_pos G hR k₀ j₀ i (euToPi (k + 8) v i))

end Det

end

end Work.ThomBordism.LeadChapter
