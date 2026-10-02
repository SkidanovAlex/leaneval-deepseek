import Mathlib
import Submission.Work.PTGeometric.SourceNull
import Submission.Work.PTGeometric.SourceFamily
import Submission.Work.PTGeometric.ConcreteCollapse
import Submission.Work.PTGeometric.TubeAmbient
import Submission.Work.Tubular.Transversality
import Submission.Work.Tubular.TubeTransversalityOfChart
import Submission.Work.PTGeometric.flatCoordModel
import Submission.Work.PTGeometric.genLoopListConcat_eq_block
import Submission.Work.PTGeometric.isSubmersionAt_normalCoord_comp
import Submission.Work.PTGeometric.isSubmersionAt_of_boundary_linearization

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.PTGeometric

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter

noncomputable section

open Work.ThomBordism
open Work.ThomBordism.PontryaginThom

variable {k : ℕ} {D : ThomTarget k} {ι : Type} [Fintype ι] {Fam : ι → Man8}

/-! ## The scalar cube chart and its (local) inverse -/

def ptScalar (s : ℝ) : ℝ := (1 + s / Real.sqrt (1 + s ^ 2)) / 2

def ptScalarInv (t : ℝ) : ℝ := (2 * t - 1) / Real.sqrt (1 - (2 * t - 1) ^ 2)

theorem ptScalar_two_mul_sub_one (s : ℝ) :
    2 * ptScalar s - 1 = s / Real.sqrt (1 + s ^ 2) := by
  simp only [ptScalar]; field_simp; ring

theorem ptScalar_sq_lt_one (s : ℝ) : (2 * ptScalar s - 1) ^ 2 < 1 := by
  have h1 : |s| < Real.sqrt (1 + s ^ 2) := by
    rw [Real.lt_sqrt (abs_nonneg s), sq_abs]
    linarith
  have h2 : 0 < Real.sqrt (1 + s ^ 2) := Real.sqrt_pos.mpr (by positivity)
  rw [ptScalar_two_mul_sub_one, div_pow, div_lt_one (by positivity)]
  have h3 := Real.sq_sqrt (show (0 : ℝ) ≤ 1 + s ^ 2 by positivity)
  nlinarith [h1, h2, sq_nonneg s, h3, sq_abs s]

theorem ptScalarInv_ptScalar (s : ℝ) : ptScalarInv (ptScalar s) = s := by
  have hsq : Real.sqrt (1 + s ^ 2) ^ 2 = 1 + s ^ 2 := Real.sq_sqrt (by positivity)
  have h4 : 1 - (s / Real.sqrt (1 + s ^ 2)) ^ 2 = (1 / Real.sqrt (1 + s ^ 2)) ^ 2 := by
    field_simp
    nlinarith [hsq]
  rw [ptScalarInv, ptScalar_two_mul_sub_one, h4, Real.sqrt_sq_eq_abs,
    abs_of_pos (by positivity)]
  field_simp

theorem differentiableAt_ptScalar (s : ℝ) : DifferentiableAt ℝ ptScalar s := by
  have h1 : DifferentiableAt ℝ (fun t : ℝ => Real.sqrt (1 + t ^ 2)) s := by
    refine DifferentiableAt.sqrt ?_ ?_
    · fun_prop
    · positivity
  have h2 : DifferentiableAt ℝ (fun t : ℝ => 1 + t / Real.sqrt (1 + t ^ 2)) s :=
    (differentiableAt_const (c := (1 : ℝ))).add
      (differentiableAt_id.div h1 (by positivity))
  have h3 : DifferentiableAt ℝ ptScalar s := h2.div_const 2
  exact h3

theorem differentiableAt_ptScalarInv (t : ℝ) (ht : (2 * t - 1) ^ 2 < 1) :
    DifferentiableAt ℝ ptScalarInv t := by
  have hne : 1 - (2 * t - 1) ^ 2 ≠ 0 := by nlinarith
  have h1 : DifferentiableAt ℝ (fun t : ℝ => 2 * t - 1) t := by fun_prop
  have h2 : DifferentiableAt ℝ (fun t : ℝ => Real.sqrt (1 - (2 * t - 1) ^ 2)) t := by
    refine DifferentiableAt.sqrt ?_ ?_
    · fun_prop
    · exact hne
  have h3 : DifferentiableAt ℝ ptScalarInv t :=
    h1.div h2 (ne_of_gt (Real.sqrt_pos.mpr (by linarith)))
  exact h3

/-! ## The coordinatewise cube chart on `Fin n → ℝ` -/

def ptCubeFun (n : ℕ) (v : Fin n → ℝ) : Fin n → ℝ := fun i => ptScalar (v i)

def ptCubeInvFun (n : ℕ) (w : Fin n → ℝ) : Fin n → ℝ := fun i => ptScalarInv (w i)

theorem ptCubeInvFun_ptCubeFun (n : ℕ) (v : Fin n → ℝ) :
    ptCubeInvFun n (ptCubeFun n v) = v := by
  funext i; exact ptScalarInv_ptScalar (v i)

theorem proj_comp_pi {ι ι' : Type*} [Fintype ι'] (f : ι → (ι' → ℝ) →L[ℝ] ℝ) (i : ι) :
    (ContinuousLinearMap.proj (R := ℝ) i).comp (ContinuousLinearMap.pi f) = f i := by
  ext v; simp

theorem hasFDerivAt_proj {n : ℕ} (i : Fin n) (v : Fin n → ℝ) :
    HasFDerivAt (fun x : Fin n → ℝ => x i) (ContinuousLinearMap.proj (R := ℝ) i) v := by
  have hfun : (⇑(ContinuousLinearMap.proj (R := ℝ) i) : (Fin n → ℝ) → ℝ) = fun x => x i := by
    funext x; simp
  have h := (ContinuousLinearMap.proj (R := ℝ) i : (Fin n → ℝ) →L[ℝ] ℝ).hasFDerivAt (x := v)
  rw [hfun] at h
  exact h

theorem hasFDerivAt_ptCubeFun (n : ℕ) (v : Fin n → ℝ) :
    HasFDerivAt (ptCubeFun n)
      (ContinuousLinearMap.pi (fun i => (fderiv ℝ ptScalar (v i)).comp
        (ContinuousLinearMap.proj (R := ℝ) i))) v := by
  refine hasFDerivAt_pi'' fun i => ?_
  rw [proj_comp_pi]
  exact ((differentiableAt_ptScalar (v i)).hasFDerivAt).comp v (hasFDerivAt_proj i v)

theorem differentiableAt_ptCubeFun (n : ℕ) (v : Fin n → ℝ) :
    DifferentiableAt ℝ (ptCubeFun n) v :=
  (hasFDerivAt_ptCubeFun n v).differentiableAt

theorem hasFDerivAt_ptCubeInvFun (n : ℕ) (v : Fin n → ℝ) :
    HasFDerivAt (ptCubeInvFun n)
      (ContinuousLinearMap.pi (fun i => (fderiv ℝ ptScalarInv (ptCubeFun n v i)).comp
        (ContinuousLinearMap.proj (R := ℝ) i))) (ptCubeFun n v) := by
  refine hasFDerivAt_pi'' fun i => ?_
  rw [proj_comp_pi]
  exact ((differentiableAt_ptScalarInv (ptCubeFun n v i)
    (ptScalar_sq_lt_one (v i))).hasFDerivAt).comp (ptCubeFun n v) (hasFDerivAt_proj i _)

theorem fderiv_ptCubeFun_surjective (n : ℕ) (v : Fin n → ℝ) :
    Function.Surjective (fderiv ℝ (ptCubeFun n) v) := by
  have h1 : DifferentiableAt ℝ (ptCubeFun n) v := differentiableAt_ptCubeFun n v
  have h2 : DifferentiableAt ℝ (ptCubeInvFun n) (ptCubeFun n v) :=
    (hasFDerivAt_ptCubeInvFun n v).differentiableAt
  have hcomp : (fderiv ℝ (ptCubeInvFun n) (ptCubeFun n v)).comp
      (fderiv ℝ (ptCubeFun n) v) = ContinuousLinearMap.id ℝ (Fin n → ℝ) := by
    rw [← fderiv_comp (𝕜 := ℝ) v h2 h1,
      show ptCubeInvFun n ∘ ptCubeFun n = id from funext (ptCubeInvFun_ptCubeFun n),
      fderiv_id]
  have hinj : Function.Injective (fderiv ℝ (ptCubeFun n) v) := by
    refine Function.LeftInverse.injective
      (g := ⇑(fderiv ℝ (ptCubeInvFun n) (ptCubeFun n v))) fun x => ?_
    have h := congrArg (fun T : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) => T x) hcomp
    simpa using h
  exact (LinearMap.injective_iff_surjective.mp hinj)

/-! ## The reindexing equivalence `Euc n → (Fin n → ℝ)` -/

def euToPi (n : ℕ) : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin n → ℝ) :=
  (EuclideanSpace.equiv (Fin n) ℝ).toContinuousLinearMap

theorem euToPi_apply (n : ℕ) (z : EuclideanSpace ℝ (Fin n)) : euToPi n z = fun i => z i := rfl

theorem euToPi_surjective (n : ℕ) : Function.Surjective (euToPi n) := by
  intro w
  exact ⟨(EuclideanSpace.equiv (Fin n) ℝ).symm w, rfl⟩

/-! ## The affine model of the block reparametrisation -/

def modelCoeff (k : ℕ) (k₀ j₀ : ℕ) (l : Fin (8 + k)) : (Fin (k + 8) → ℝ) →L[ℝ] ℝ :=
  if finKRInv k l = cZero k then (2 : ℝ) ^ (k₀ + 1) • ContinuousLinearMap.proj (R := ℝ) (cZero k)
  else if finKRInv k l = cOne k then (2 : ℝ) ^ (j₀ + 1) • ContinuousLinearMap.proj (R := ℝ) (cOne k)
  else ContinuousLinearMap.proj (R := ℝ) (finKRInv k l)

def modelLin (k : ℕ) (k₀ j₀ : ℕ) : (Fin (k + 8) → ℝ) →L[ℝ] (Fin (8 + k) → ℝ) :=
  ContinuousLinearMap.pi (modelCoeff k k₀ j₀)

def modelAffine (k : ℕ) (k₀ j₀ : ℕ) (v : Fin (k + 8) → ℝ) : Fin (8 + k) → ℝ :=
  fun l => if finKRInv k l = cZero k then (2 : ℝ) ^ (k₀ + 1) * v (cZero k) - 1
    else if finKRInv k l = cOne k then (2 : ℝ) ^ (j₀ + 1) * v (cOne k) - 1
    else v (finKRInv k l)

theorem modelPoint_eq_modelAffine (k₀ j₀ : ℕ)
    (y : EuclideanSpace ℝ (Fin ((8 + k) + 1))) (l : Fin (8 + k)) :
    modelPoint k (cZero k) (cOne k) k₀ j₀ y (finKRInv k l)
      = modelAffine k k₀ j₀ (fun m => ((collPt k y m : Set.Icc (0 : ℝ) 1) : ℝ)) l := rfl

theorem hasFDerivAt_modelCoeff (k k₀ j₀ : ℕ) (l : Fin (8 + k)) (v : Fin (k + 8) → ℝ) :
    HasFDerivAt (fun w : Fin (k + 8) → ℝ => modelAffine k k₀ j₀ w l)
      (modelCoeff k k₀ j₀ l) v := by
  by_cases h0 : finKRInv k l = cZero k
  · have hf : (fun w : Fin (k + 8) → ℝ => modelAffine k k₀ j₀ w l)
        = fun w => (2 : ℝ) ^ (k₀ + 1) * w (cZero k) - 1 := by
      funext w; simp only [modelAffine, if_pos h0]
    have hd : modelCoeff k k₀ j₀ l
        = (2 : ℝ) ^ (k₀ + 1) • ContinuousLinearMap.proj (R := ℝ) (cZero k) := by
      simp only [modelCoeff, if_pos h0]
    rw [hf, hd]
    exact ((hasFDerivAt_proj (cZero k) v).const_mul ((2 : ℝ) ^ (k₀ + 1))).sub_const 1
  · by_cases h1 : finKRInv k l = cOne k
    · have hne : (cOne k = cZero k) = False := eq_false (Ne.symm (cZero_ne_cOne k))
      have hf : (fun w : Fin (k + 8) → ℝ => modelAffine k k₀ j₀ w l)
          = fun w => (2 : ℝ) ^ (j₀ + 1) * w (cOne k) - 1 := by
        funext w; simp only [modelAffine, h1, hne, if_false, if_true]
      have hd : modelCoeff k k₀ j₀ l
          = (2 : ℝ) ^ (j₀ + 1) • ContinuousLinearMap.proj (R := ℝ) (cOne k) := by
        simp only [modelCoeff, h1, hne, if_false, if_true]
      rw [hf, hd]
      exact ((hasFDerivAt_proj (cOne k) v).const_mul ((2 : ℝ) ^ (j₀ + 1))).sub_const 1
    · have hf : (fun w : Fin (k + 8) → ℝ => modelAffine k k₀ j₀ w l)
          = fun w => w (finKRInv k l) := by
        funext w; simp only [modelAffine, h0, h1, if_false]
      have hd : modelCoeff k k₀ j₀ l = ContinuousLinearMap.proj (R := ℝ) (finKRInv k l) := by
        simp only [modelCoeff, h0, h1, if_false]
      rw [hf, hd]
      exact hasFDerivAt_proj (finKRInv k l) v

theorem hasFDerivAt_modelAffine (k k₀ j₀ : ℕ) (v : Fin (k + 8) → ℝ) :
    HasFDerivAt (modelAffine k k₀ j₀) (modelLin k k₀ j₀) v := by
  refine hasFDerivAt_pi'' (Φ' := modelLin k k₀ j₀) fun l => ?_
  rw [show (ContinuousLinearMap.proj (R := ℝ) l).comp (modelLin k k₀ j₀)
      = modelCoeff k k₀ j₀ l from by rw [modelLin, proj_comp_pi]]
  exact hasFDerivAt_modelCoeff k k₀ j₀ l v

theorem modelLin_surjective (k k₀ j₀ : ℕ) : Function.Surjective (modelLin k k₀ j₀) := by
  intro w
  refine ⟨fun m => if m = cZero k then w (finKR k (cZero k)) / 2 ^ (k₀ + 1)
      else if m = cOne k then w (finKR k (cOne k)) / 2 ^ (j₀ + 1)
      else w (finKR k m), ?_⟩
  funext l
  rw [show modelLin k k₀ j₀ (fun m => if m = cZero k then w (finKR k (cZero k)) / 2 ^ (k₀ + 1)
        else if m = cOne k then w (finKR k (cOne k)) / 2 ^ (j₀ + 1)
        else w (finKR k m)) l
      = modelCoeff k k₀ j₀ l (fun m => if m = cZero k then w (finKR k (cZero k)) / 2 ^ (k₀ + 1)
        else if m = cOne k then w (finKR k (cOne k)) / 2 ^ (j₀ + 1)
        else w (finKR k m)) from by rw [modelLin, ContinuousLinearMap.pi_apply]]
  by_cases h0 : finKRInv k l = cZero k
  · have hf : finKR k (cZero k) = l := by rw [← h0, finKR_finKRInv]
    have hd : modelCoeff k k₀ j₀ l
        = (2 : ℝ) ^ (k₀ + 1) • ContinuousLinearMap.proj (R := ℝ) (cZero k) := by
      simp only [modelCoeff, if_pos h0]
    rw [hd, hf]
    simp only [h0, if_true, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
    field_simp
  · by_cases h1 : finKRInv k l = cOne k
    · have hf : finKR k (cOne k) = l := by rw [← h1, finKR_finKRInv]
      have hne : (cOne k = cZero k) = False := eq_false (Ne.symm (cZero_ne_cOne k))
      have hd : modelCoeff k k₀ j₀ l
          = (2 : ℝ) ^ (j₀ + 1) • ContinuousLinearMap.proj (R := ℝ) (cOne k) := by
        simp only [modelCoeff, h1, hne, if_false, if_true]
      rw [hd, hf]
      simp only [h0, h1, hne, if_false, if_true, smul_apply, ContinuousLinearMap.proj_apply,
        smul_eq_mul]
      field_simp
    · have hf : finKR k (finKRInv k l) = l := finKR_finKRInv k l
      have hd : modelCoeff k k₀ j₀ l = ContinuousLinearMap.proj (R := ℝ) (finKRInv k l) := by
        simp only [modelCoeff, h0, h1, if_false]
      rw [hd]
      simp only [ContinuousLinearMap.proj_apply, h0, h1, if_false, finKR_finKRInv]

/-! ## The affine cube-to-box map -/

def shiftScale (N : ℕ) (R : ℝ) (v : Fin N → ℝ) : Fin N → ℝ := fun i => 2 * R * (v i - 1 / 2)

theorem hasFDerivAt_shiftScale (N : ℕ) (R : ℝ) (v : Fin N → ℝ) :
    HasFDerivAt (shiftScale N R) ((2 * R) • (1 : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ))) v := by
  have hfun : shiftScale N R = fun x : Fin N → ℝ => (2 * R) • x - (fun _ : Fin N => R) := by
    funext x i
    simp only [shiftScale, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hfun]
  simpa using ((2 * R) • (1 : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ))).hasFDerivAt.sub_const
    (fun _ : Fin N => R)

theorem funToEuc_surjective (n : ℕ) : Function.Surjective (funToEuc n) := by
  intro w
  exact ⟨(Work.Tubular.funToEuc n).symm w, (Work.Tubular.funToEuc n).apply_symm_apply w⟩

theorem surjective_clm_comp {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {A : Y →L[ℝ] Z} {B : X →L[ℝ] Y}
    (hA : Function.Surjective A) (hB : Function.Surjective B) :
    Function.Surjective (A.comp B) := by
  intro z
  obtain ⟨y, rfl⟩ := hA z
  obtain ⟨x, rfl⟩ := hB y
  exact ⟨x, by simp⟩

/-! ## The linear reindexing `L` -/

def cubeLin (k : ℕ) : EuclideanSpace ℝ (Fin ((8 + k) + 1)) →L[ℝ]
    EuclideanSpace ℝ (Fin (k + 8)) :=
  (tailCLM (k + 8)).comp (srcCast k)

theorem srcCast_srcCastInv (k : ℕ) (x : EuclideanSpace ℝ (Fin ((k + 8) + 1))) :
    srcCast k (srcCastInv k x) = x := by
  ext i
  rw [srcCast_apply, srcCastInv_apply, Fin.cast_cast]
  exact congrArg (fun j : Fin ((k + 8) + 1) => x.ofLp j) (Fin.ext (by simp [Fin.cast]))

theorem cubeLin_surjective (k : ℕ) : Function.Surjective (cubeLin k) := by
  intro w
  refine ⟨srcCastInv k (consCLM (k + 8) (0, w)), ?_⟩
  show tailCLM (k + 8) (srcCast k (srcCastInv k (consCLM (k + 8) (0, w)))) = w
  rw [srcCast_srcCastInv, tailCLM_consCLM]

theorem cubeLin_single_zero (k : ℕ) :
    cubeLin k (PiLp.single 2 (0 : Fin ((8 + k) + 1)) 1) = 0 := by
  ext m
  show tailCLM (k + 8) (srcCast k (PiLp.single 2 (0 : Fin ((8 + k) + 1)) 1)) m = 0
  rw [tailCLM_apply, srcCast_apply, PiLp.single_apply]
  split_ifs with h
  · exact absurd h (by simp)
  · rfl

/-! ## The factorization of `modelEuc` -/

theorem modelEuc_eq_comp (G : GenuineTubeGeometry k D ι Fam) (k₀ j₀ : ℕ) :
    modelEuc G (cZero k) (cOne k) k₀ j₀
      = (⇑(funToEuc (8 + k))) ∘ (shiftScale (8 + k) G.R) ∘ (modelAffine k k₀ j₀)
        ∘ (ptCubeFun (k + 8)) ∘ (⇑(euToPi (k + 8))) ∘ (⇑(cubeLin k)) := by
  funext y
  rfl

/-! ## The chain rule and its consequences -/

def modelChain (G : GenuineTubeGeometry k D ι Fam) (k₀ j₀ : ℕ)
    (y : EuclideanSpace ℝ (Fin ((8 + k) + 1))) :
    EuclideanSpace ℝ (Fin ((8 + k) + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (8 + k)) :=
  ((funToEuc (8 + k)).toContinuousLinearMap).comp
    (((2 * G.R) • (1 : (Fin (8 + k) → ℝ) →L[ℝ] (Fin (8 + k) → ℝ))).comp
      ((modelLin k k₀ j₀).comp
        ((fderiv ℝ (ptCubeFun (k + 8)) (euToPi (k + 8) (cubeLin k y))).comp
          ((euToPi (k + 8)).comp (cubeLin k)))))

theorem hasFDerivAt_modelEuc (G : GenuineTubeGeometry k D ι Fam) (k₀ j₀ : ℕ)
    (y : EuclideanSpace ℝ (Fin ((8 + k) + 1))) :
    HasFDerivAt (modelEuc G (cZero k) (cOne k) k₀ j₀) (modelChain G k₀ j₀ y) y := by
  rw [modelEuc_eq_comp (G := G) k₀ j₀]
  rw [modelChain]
  have h1 : HasFDerivAt (⇑(cubeLin k)) (cubeLin k) y := (cubeLin k).hasFDerivAt
  have h2 : HasFDerivAt (⇑(euToPi (k + 8))) (euToPi (k + 8)) (cubeLin k y) :=
    (euToPi (k + 8)).hasFDerivAt
  have h3 : HasFDerivAt (ptCubeFun (k + 8))
      (fderiv ℝ (ptCubeFun (k + 8)) (euToPi (k + 8) (cubeLin k y)))
      (euToPi (k + 8) (cubeLin k y)) :=
    (differentiableAt_ptCubeFun (k + 8) _).hasFDerivAt
  have h4 : HasFDerivAt (modelAffine k k₀ j₀) (modelLin k k₀ j₀)
      (ptCubeFun (k + 8) (euToPi (k + 8) (cubeLin k y))) :=
    hasFDerivAt_modelAffine k k₀ j₀ _
  have h5 : HasFDerivAt (shiftScale (8 + k) G.R)
      ((2 * G.R) • (1 : (Fin (8 + k) → ℝ) →L[ℝ] (Fin (8 + k) → ℝ)))
      (modelAffine k k₀ j₀ (ptCubeFun (k + 8) (euToPi (k + 8) (cubeLin k y)))) :=
    hasFDerivAt_shiftScale (8 + k) G.R _
  have h6 : HasFDerivAt (⇑(funToEuc (8 + k))) ((funToEuc (8 + k)).toContinuousLinearMap)
      (shiftScale (8 + k) G.R
        (modelAffine k k₀ j₀ (ptCubeFun (k + 8) (euToPi (k + 8) (cubeLin k y))))) :=
    (funToEuc (8 + k)).hasFDerivAt
  exact h6.comp y (h5.comp y (h4.comp y (h3.comp y (h2.comp y h1))))

theorem fderiv_modelEuc_surjective (G : GenuineTubeGeometry k D ι Fam) (k₀ j₀ : ℕ)
    (hR : G.R ≠ 0) (y : EuclideanSpace ℝ (Fin ((8 + k) + 1))) :
    Function.Surjective (fderiv ℝ (modelEuc G (cZero k) (cOne k) k₀ j₀) y) := by
  rw [(hasFDerivAt_modelEuc G k₀ j₀ y).fderiv, modelChain]
  refine surjective_clm_comp (funToEuc_surjective (8 + k)) ?_
  refine surjective_clm_comp ?_ ?_
  · intro w
    refine ⟨(2 * G.R)⁻¹ • w, ?_⟩
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply]
    exact smul_inv_smul₀ (mul_ne_zero two_ne_zero hR) w
  · refine surjective_clm_comp (modelLin_surjective k k₀ j₀) ?_
    refine surjective_clm_comp
      (fderiv_ptCubeFun_surjective (k + 8) (euToPi (k + 8) (cubeLin k y))) ?_
    exact surjective_clm_comp (euToPi_surjective (k + 8)) (cubeLin_surjective k)

theorem fderiv_modelEuc_single_zero (G : GenuineTubeGeometry k D ι Fam) (k₀ j₀ : ℕ)
    (y : EuclideanSpace ℝ (Fin ((8 + k) + 1))) :
    fderiv ℝ (modelEuc G (cZero k) (cOne k) k₀ j₀) y
        (PiLp.single 2 (0 : Fin ((8 + k) + 1)) 1) = 0 := by
  rw [(hasFDerivAt_modelEuc G k₀ j₀ y).fderiv, modelChain]
  simp only [ContinuousLinearMap.comp_apply, cubeLin_single_zero, map_zero]

/-! ## The tube radius is positive -/

theorem tube_radius_pos (G : GenuineTubeGeometry k D ι Fam) (i : ι) : 0 < G.R := by
  obtain ⟨x⟩ := G.nonempty i
  have hmem : (G.emb i).e x ∈ (G.chart i).U := (G.chart i).zero_mem_U x
  have h := G.hbox i ((G.emb i).e x) hmem ⟨0, by omega⟩
  exact lt_of_le_of_lt (abs_nonneg _) h


/-! ## The block data at a point of the core -/

theorem exists_block_data (G : GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1)
    (y₀ : EuclideanSpace ℝ (Fin ((8 + k) + 1))) (hy₀ : y₀ 0 = 0)
    (hc : flatSourceHomotopy8 (k := k)
        (familySource (D := D) (Fam := Fam) G m hpow).H
        (familySource (D := D) (Fam := Fam) G m hpow).φ y₀ ∈ G.core) :
    ∃ (k₀ j₀ : ℕ) (hj : j₀ < Fintype.card ι) (iχ : ι),
      iχ = (Fintype.equivFin ι).symm ⟨j₀, hj⟩ ∧ k₀ < m ∧
      (1 < 2 ^ (k₀ + 1) * ((collPt k y₀ (cZero k) : Set.Icc (0 : ℝ) 1) : ℝ)) ∧
      (2 ^ k₀ * ((collPt k y₀ (cZero k) : Set.Icc (0 : ℝ) 1) : ℝ) < 1) ∧
      (1 < 2 ^ (j₀ + 1) * ((collPt k y₀ (cOne k) : Set.Icc (0 : ℝ) 1) : ℝ)) ∧
      (2 ^ j₀ * ((collPt k y₀ (cOne k) : Set.Icc (0 : ℝ) 1) : ℝ) < 1) ∧
      modelEuc G (cZero k) (cOne k) k₀ j₀ y₀ ∈ (G.chart iχ).openTube ∧
      (∃ z : (Fam iχ).pt, modelEuc G (cZero k) (cOne k) k₀ j₀ y₀ = (G.emb iχ).e z) := by
  classical
  have hne : flatSourceHomotopy8 (k := k)
      (familySource (D := D) (Fam := Fam) G m hpow).H
      (familySource (D := D) (Fam := Fam) G m hpow).φ y₀ ≠ D.t₀ :=
    fun h => G.t0_notMem_core (h ▸ hc)
  have hcollar : flatSourceHomotopy8 (k := k)
      (familySource (D := D) (Fam := Fam) G m hpow).H
      (familySource (D := D) (Fam := Fam) G m hpow).φ y₀
      = alphaFamily (D := D) (Fam := Fam) G m (collPt k y₀) :=
    flatSourceHomotopy8_eq_collapse (k := k)
      (familySource (D := D) (Fam := Fam) G m hpow).H
      (familySource (D := D) (Fam := Fam) G m hpow).φ
      (alphaFamily (D := D) (Fam := Fam) G m)
      (familySource (D := D) (Fam := Fam) G m hpow).collar (by rw [hy₀]; norm_num)
  have hα : genLoopListConcat (cZero k)
      (List.ofFn (fun _ : Fin m => blockInner (D := D) (Fam := Fam) G)) (collPt k y₀) ≠ D.t₀ :=
    fun h => hne (hcollar.trans h)
  obtain ⟨k₀, hk₀', hξlo, hξhi⟩ := exists_block_interval (cZero k)
    (List.ofFn (fun _ : Fin m => blockInner (D := D) (Fam := Fam) G)) (collPt k y₀) hα
  have hk₀ : k₀ < m := by rwa [List.length_ofFn] at hk₀'
  have hget1 : (List.ofFn (fun _ : Fin m => blockInner (D := D) (Fam := Fam) G))[k₀]
      = blockInner (D := D) (Fam := Fam) G := get_ofFn_eq _ _ hk₀'
  have hpt1 : blockPt (cZero k) k₀ (collPt k y₀) hξlo hξhi = outerPt k (cZero k) k₀ y₀ :=
    blockPt_eq_upd (cZero k) k₀ (collPt k y₀) hξlo hξhi
  have houterval : alphaFamily (D := D) (Fam := Fam) G m (collPt k y₀)
      = blockInner (D := D) (Fam := Fam) G (outerPt k (cZero k) k₀ y₀) := by
    rw [show alphaFamily (D := D) (Fam := Fam) G m
        = genLoopListConcat (cZero k) (List.ofFn (fun _ : Fin m =>
            blockInner (D := D) (Fam := Fam) G)) from rfl,
      genLoopListConcat_eq_block (cZero k) _ (collPt k y₀) k₀ hk₀' hξlo hξhi, hget1, hpt1]
  have hbi : blockInner (D := D) (Fam := Fam) G (outerPt k (cZero k) k₀ y₀) ≠ D.t₀ :=
    fun h => hα (houterval.trans h)
  have hbi' : genLoopListConcat (cOne k) (List.ofFn (blockLoop (D := D) (Fam := Fam) G))
      (outerPt k (cZero k) k₀ y₀) ≠ D.t₀ := hbi
  obtain ⟨j₀, hj₀', hηlo', hηhi'⟩ := exists_block_interval (cOne k)
    (List.ofFn (blockLoop (D := D) (Fam := Fam) G)) (outerPt k (cZero k) k₀ y₀) hbi'
  have hj₀ : j₀ < Fintype.card ι := by rwa [List.length_ofFn] at hj₀'
  have hηlo : 1 < 2 ^ (j₀ + 1) * ((collPt k y₀ (cOne k) : Set.Icc (0 : ℝ) 1) : ℝ) := by
    rw [← outerPt_apply_cOne k₀ y₀]; exact hηlo'
  have hηhi : 2 ^ j₀ * ((collPt k y₀ (cOne k) : Set.Icc (0 : ℝ) 1) : ℝ) < 1 := by
    rw [← outerPt_apply_cOne k₀ y₀]; exact hηhi'
  set iχ := (Fintype.equivFin ι).symm ⟨j₀, hj₀⟩ with hiχ
  have hblock₀ : alphaFamily (D := D) (Fam := Fam) G m (collPt k y₀)
      = (G.rep iχ).collapse (clipPt k (cZero k) (cOne k) k₀ j₀ y₀) :=
    alphaFamily_eq_collapse_of_block (G := G) m k₀ j₀ hk₀ hj₀ y₀ hξlo hξhi hηlo hηhi
  have hrep₀ : (G.rep iχ).collapse (clipPt k (cZero k) (cOne k) k₀ j₀ y₀) ≠ D.t₀ :=
    fun h => hα (hblock₀.trans h)
  have htube₀ : modelEuc G (cZero k) (cOne k) k₀ j₀ y₀ ∈ (G.chart iχ).openTube := by
    have h1 : (G.rep iχ).collapse
        (fun j => (reIdx k (clipPt k (cZero k) (cOne k) k₀ j₀ y₀)) (finKR k j)) ≠ D.t₀ := by
      rw [reIdx_comp_finKR k (clipPt k (cZero k) (cOne k) k₀ j₀ y₀)]
      exact hrep₀
    have h2 : Work.Tubular.alphaV (G.chart iχ) G.hR (G.hbox iχ) D.t₀ (G.J iχ) (G.hJ iχ)
        (G.g iχ) (G.hg iχ) (reIdx k (clipPt k (cZero k) (cOne k) k₀ j₀ y₀)) ≠ D.t₀ := by
      rw [← G.isGeom iχ (reIdx k (clipPt k (cZero k) (cOne k) k₀ j₀ y₀))]
      exact h1
    have hmem := mem_openTube_of_alphaV_ne (G.chart iχ) G.hR (G.hbox iχ) D.t₀ (G.J iχ) (G.hJ iχ)
      (G.g iχ) (G.hg iχ) (t := reIdx k (clipPt k (cZero k) (cOne k) k₀ j₀ y₀)) h2
    rw [modelEuc_eq_cubeToEuc G (cZero_ne_cOne k) k₀ j₀ y₀ hξlo hξhi hηlo hηhi]
    exact hmem
  have hz : ∃ z : (Fam iχ).pt, modelEuc G (cZero k) (cOne k) k₀ j₀ y₀ = (G.emb iχ).e z := by
    have hval : flatSourceHomotopy8 (k := k)
        (familySource (D := D) (Fam := Fam) G m hpow).H
        (familySource (D := D) (Fam := Fam) G m hpow).φ y₀
        = Work.Tubular.alphaV (G.chart iχ) G.hR (G.hbox iχ) D.t₀ (G.J iχ) (G.hJ iχ)
            (G.g iχ) (G.hg iχ) (reIdx k (clipPt k (cZero k) (cOne k) k₀ j₀ y₀)) := by
      rw [hcollar, hblock₀]
      have h := G.isGeom iχ (reIdx k (clipPt k (cZero k) (cOne k) k₀ j₀ y₀))
      rw [reIdx_comp_finKR k (clipPt k (cZero k) (cOne k) k₀ j₀ y₀)] at h
      exact h
    have hcore : Work.Tubular.alphaV (G.chart iχ) G.hR (G.hbox iχ) D.t₀ (G.J iχ) (G.hJ iχ)
        (G.g iχ) (G.hg iχ) (reIdx k (clipPt k (cZero k) (cOne k) k₀ j₀ y₀)) ∈ G.core :=
      hval ▸ hc
    have hrange := (G.zero iχ (reIdx k (clipPt k (cZero k) (cOne k) k₀ j₀ y₀))).mp hcore
    rw [← modelEuc_eq_cubeToEuc G (cZero_ne_cOne k) k₀ j₀ y₀ hξlo hξhi hηlo hηhi] at hrange
    obtain ⟨z, hz⟩ := hrange
    exact ⟨z, hz.symm⟩
  exact ⟨k₀, j₀, hj₀, iχ, rfl, hk₀, hξlo, hξhi, hηlo, hηhi, htube₀, hz⟩


theorem exists_model_submersion_at_mem_core {k : ℕ}
    {D : Work.ThomBordism.PontryaginThom.ThomTarget k} {ι : Type} [Fintype ι]
    {Fam : ι → Work.ThomBordism.Man8}
    (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, Work.PTGeometric.tubeAlpha (G.rep i)) ^ m = 1)
    (y₀ : EuclideanSpace ℝ (Fin ((8 + k) + 1))) (hy₀ : y₀ 0 = 0)
    (hc : Work.PTGeometric.flatSourceHomotopy8 (k := k)
        (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).H
        (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).φ y₀ ∈ G.core) :
    ∃ (i : ι) (z : (Fam i).pt)
      (ℓ : Work.Tubular.Euc (8 + k) →L[ℝ] EuclideanSpace ℝ (Fin k))
      (W : Set (EuclideanSpace ℝ (Fin ((8 + k) + 1))))
      (p : EuclideanSpace ℝ (Fin ((8 + k) + 1)) → Work.Tubular.Euc (8 + k)),
      IsOpen W ∧ y₀ ∈ W ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) p W ∧
      (∀ y ∈ W, p y ∈ (G.chart i).openTube) ∧
      p y₀ = (G.emb i).e z ∧
      (∀ z' ∈ Work.Tubular.normalSpace (G.emb i) z, ℓ z' = 0 → z' = 0) ∧
      Function.Surjective (fderiv ℝ p y₀) ∧
      fderiv ℝ p y₀ (PiLp.single 2 (0 : Fin ((8 + k) + 1)) 1) = 0 ∧
      Manifold.IsSubmersionAt (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k))) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun u : EuclideanHalfSpace ((8 + k) + 1) =>
          ℓ (Work.PTGeometric.tubeNormalCoord (G.emb i) (G.chart i) (p u.1)))
        ⟨y₀, le_of_eq hy₀.symm⟩ ∧
      (∀ y ∈ W, ∀ (h : Work.PTGeometric.flatSourceHomotopy8 (k := k)
          (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).H
          (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).φ y ≠ D.t₀),
        G.coord ⟨Work.PTGeometric.flatSourceHomotopy8 (k := k)
            (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).H
            (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).φ y, h⟩ =
          (padEndEuc k G.mU G.hmU (Work.PTGeometric.tubeNormalProj (G.emb i) (G.chart i) (p y)),
           padEuc k G.mU G.hmU
            (Work.PTGeometric.tubeNormalCoord (G.emb i) (G.chart i) (p y)))) := by
  classical
  obtain ⟨k₀, j₀, hj₀, iχ, hiχ, hk₀, hξlo, hξhi, hηlo, hηhi, htube₀, z, hzy₀⟩ :=
    exists_block_data (G := G) m hpow y₀ hy₀ hc
  have hR : G.R ≠ 0 := ne_of_gt (tube_radius_pos (G := G) iχ)
  let ν : Submodule ℝ (Work.Tubular.Euc (8 + k)) := Work.Tubular.normalSpace (G.emb iχ) z
  have hfr : Module.finrank ℝ ν = k := by
    rw [show ν = Work.Tubular.normalSpace (G.emb iχ) z from rfl,
      Work.Tubular.finrank_normalSpace]
    omega
  let eL : ν ≃L[ℝ] EuclideanSpace ℝ (Fin k) :=
    ContinuousLinearEquiv.ofFinrankEq (𝕜 := ℝ) (E := ν) (F := EuclideanSpace ℝ (Fin k))
      (by rw [hfr, finrank_euclideanSpace_fin])
  let ℓ : Work.Tubular.Euc (8 + k) →L[ℝ] EuclideanSpace ℝ (Fin k) :=
    eL.toContinuousLinearMap.comp ν.orthogonalProjectionOnto
  let p : EuclideanSpace ℝ (Fin ((8 + k) + 1)) → Work.Tubular.Euc (8 + k) :=
    modelEuc G (cZero k) (cOne k) k₀ j₀
  refine ⟨iχ, z, ℓ, localSet G k₀ j₀ iχ, p, ?_⟩
  have hpz : p y₀ = (G.emb iχ).e z := hzy₀
  have hWopen : IsOpen (localSet G k₀ j₀ iχ) := isOpen_localSet G k₀ j₀ iχ
  have hy₀W : y₀ ∈ localSet G k₀ j₀ iχ :=
    ⟨by rw [hy₀]; norm_num, hξlo, hξhi, hηlo, hηhi, htube₀⟩
  have hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) p (localSet G k₀ j₀ iχ) :=
    (contMDiff_iff_contDiff.mp (contMDiff_modelEuc G (cZero k) (cOne k) k₀ j₀)).contDiffOn.mono
      (fun _ _ => trivial)
  have htubeW : ∀ y ∈ localSet G k₀ j₀ iχ, p y ∈ (G.chart iχ).openTube :=
    fun y hy => hy.2.2.2.2.2
  have hrange : (fderiv ℝ (Work.PTGeometric.tubeNormalCoord (G.emb iχ) (G.chart iχ))
      (p y₀)).toLinearMap.range = ν := by
    have h := (Work.Tubular.TubeTransversalityOfChart (G.emb iχ) (G.chart iχ)).mfderiv_range z
    rw [← hzy₀] at h
    rwa [mfderiv_eq_fderiv] at h
  refine ⟨hWopen, hy₀W, hsm, htubeW, hpz, ?_, ?_, ?_, ?_, ?_⟩
  · -- the kernel of `ℓ` meets the normal space trivially
    intro z' hz' hz'0
    have h1 : ℓ z' = eL.toContinuousLinearMap ⟨z', hz'⟩ := by
      rw [show ℓ z' = eL.toContinuousLinearMap (ν.orthogonalProjectionOnto z') from rfl,
        Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ⟨z', hz'⟩]
    rw [h1] at hz'0
    have h2 : eL ⟨z', hz'⟩ = 0 := hz'0
    have h3 : (⟨z', hz'⟩ : ν) = 0 := LinearEquiv.map_eq_zero_iff eL.toLinearEquiv |>.1 h2
    simpa using congrArg Subtype.val h3
  · exact fderiv_modelEuc_surjective (G := G) k₀ j₀ hR y₀
  · exact fderiv_modelEuc_single_zero (G := G) k₀ j₀ y₀
  · -- the submersion at the boundary point
    have hnc0 : Work.PTGeometric.tubeNormalCoord (G.emb iχ) (G.chart iχ) (p y₀) = 0 := by
      rw [hpz]
      exact (Work.Tubular.normalCoord_eq_zero_iff (G.emb iχ) (G.chart iχ)
        ((G.chart iχ).mem_openTube z)).mpr ⟨z, rfl⟩
    have hmem_p : p y₀ ∈ (G.chart iχ).openTube := by
      rw [hpz]; exact (G.chart iχ).mem_openTube z
    have hnc_sm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (Work.PTGeometric.tubeNormalCoord (G.emb iχ) (G.chart iχ)) (G.chart iχ).openTube :=
      contMDiffOn_iff_contDiffOn.mp (contMDiffOn_tubeNormalCoord (G.emb iχ) (G.chart iχ))
    have hd_nc : DifferentiableAt ℝ
        (Work.PTGeometric.tubeNormalCoord (G.emb iχ) (G.chart iχ)) (p y₀) :=
      (hnc_sm.contDiffAt ((G.chart iχ).openTube_isOpen.mem_nhds hmem_p)).differentiableAt
        (by simp)
    have hd_p : DifferentiableAt ℝ p y₀ :=
      (hasFDerivAt_modelEuc G k₀ j₀ y₀).differentiableAt
    have hderiv : fderiv ℝ (fun w : EuclideanSpace ℝ (Fin ((8 + k) + 1)) =>
          ℓ (Work.PTGeometric.tubeNormalCoord (G.emb iχ) (G.chart iχ) (p w))) y₀
        = ℓ.comp ((fderiv ℝ (Work.PTGeometric.tubeNormalCoord (G.emb iχ) (G.chart iχ))
            (p y₀)).comp (fderiv ℝ p y₀)) := by
      have h1 : HasFDerivAt (Work.PTGeometric.tubeNormalCoord (G.emb iχ) (G.chart iχ))
          (fderiv ℝ (Work.PTGeometric.tubeNormalCoord (G.emb iχ) (G.chart iχ)) (p y₀))
          (p y₀) := hd_nc.hasFDerivAt
      have h2 : HasFDerivAt p (fderiv ℝ p y₀) y₀ := hd_p.hasFDerivAt
      have h3 : HasFDerivAt (fun w => Work.PTGeometric.tubeNormalCoord (G.emb iχ) (G.chart iχ)
          (p w)) ((fderiv ℝ (Work.PTGeometric.tubeNormalCoord (G.emb iχ) (G.chart iχ))
          (p y₀)).comp (fderiv ℝ p y₀)) y₀ := h1.comp y₀ h2
      have h4 : HasFDerivAt (fun w => ℓ (Work.PTGeometric.tubeNormalCoord (G.emb iχ)
          (G.chart iχ) (p w)))
          (ℓ.comp ((fderiv ℝ (Work.PTGeometric.tubeNormalCoord (G.emb iχ) (G.chart iχ))
            (p y₀)).comp (fderiv ℝ p y₀))) y₀ :=
        (ContinuousLinearMap.hasFDerivAt ℓ).comp y₀ h3
      exact h4.fderiv
    have hsurj_p : Function.Surjective (fderiv ℝ p y₀) :=
      fderiv_modelEuc_surjective (G := G) k₀ j₀ hR y₀
    have htime_p : fderiv ℝ p y₀ (PiLp.single 2 (0 : Fin ((8 + k) + 1)) 1) = 0 :=
      fderiv_modelEuc_single_zero (G := G) k₀ j₀ y₀
    have hsurj : Function.Surjective (fderiv ℝ (fun w : EuclideanSpace ℝ (Fin ((8 + k) + 1)) =>
        ℓ (Work.PTGeometric.tubeNormalCoord (G.emb iχ) (G.chart iχ) (p w))) y₀) := by
      rw [hderiv]
      intro w
      have hm : ((eL.symm w : ν) : Work.Tubular.Euc (8 + k)) ∈
          (fderiv ℝ (Work.PTGeometric.tubeNormalCoord (G.emb iχ) (G.chart iχ))
            (p y₀)).toLinearMap.range := by
        rw [hrange]
        exact (eL.symm w).2
      obtain ⟨u, hu⟩ := LinearMap.mem_range.mp hm
      obtain ⟨v, hv⟩ := hsurj_p u
      refine ⟨v, ?_⟩
      simp only [ContinuousLinearMap.comp_apply]
      have hv' : (fderiv ℝ p y₀) v = u := hv
      have hu' : (fderiv ℝ (Work.PTGeometric.tubeNormalCoord (G.emb iχ) (G.chart iχ))
          (p y₀)) u = ((eL.symm w : ν) : Work.Tubular.Euc (8 + k)) := hu
      rw [hv', hu']
      show eL.toContinuousLinearMap (ν.orthogonalProjectionOnto
        ((eL.symm w : ν) : Work.Tubular.Euc (8 + k))) = w
      rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (eL.symm w)]
      exact eL.apply_symm_apply w
    have hnorm : ∃ v : EuclideanSpace ℝ (Fin ((8 + k) + 1)),
        (fderiv ℝ (fun w : EuclideanSpace ℝ (Fin ((8 + k) + 1)) =>
          ℓ (Work.PTGeometric.tubeNormalCoord (G.emb iχ) (G.chart iχ) (p w))) y₀) v = 0 ∧
          v 0 ≠ 0 := by
      refine ⟨PiLp.single 2 (0 : Fin ((8 + k) + 1)) 1, ?_, ?_⟩
      · rw [hderiv]
        simp only [ContinuousLinearMap.comp_apply]
        have htime_p' : (fderiv ℝ p y₀) (PiLp.single 2 (0 : Fin ((8 + k) + 1)) 1) = 0 :=
          htime_p
        rw [htime_p', map_zero, map_zero]
      · rw [show (PiLp.single 2 (0 : Fin ((8 + k) + 1)) 1 :
              EuclideanSpace ℝ (Fin ((8 + k) + 1))) 0 = 1 from by
            rw [PiLp.single_apply, if_pos rfl]]
        norm_num
    have hf0 : (fun u : EuclideanHalfSpace ((8 + k) + 1) =>
        ℓ (Work.PTGeometric.tubeNormalCoord (G.emb iχ) (G.chart iχ) (p u.1)))
        ⟨y₀, le_of_eq hy₀.symm⟩ = 0 := by
      show ℓ (Work.PTGeometric.tubeNormalCoord (G.emb iχ) (G.chart iχ) (p y₀)) = 0
      rw [hnc0, map_zero]
    have hgg0 : ℓ (Work.PTGeometric.tubeNormalCoord (G.emb iχ) (G.chart iχ) (p y₀)) = 0 := by
      rw [hnc0, map_zero]
    have hext_apply : ∀ u : EuclideanHalfSpace ((8 + k) + 1),
        (OpenPartialHomeomorph.refl (EuclideanHalfSpace ((8 + k) + 1))).extend
          (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)) u = u.1 := by
      intro u
      rw [OpenPartialHomeomorph.extend_coe]
      rfl
    have hagree : (fun u : EuclideanHalfSpace ((8 + k) + 1) =>
        ℓ (Work.PTGeometric.tubeNormalCoord (G.emb iχ) (G.chart iχ) (p u.1)))
        =ᶠ[𝓝 (⟨y₀, le_of_eq hy₀.symm⟩ : EuclideanHalfSpace ((8 + k) + 1))]
        (fun y => ℓ (Work.PTGeometric.tubeNormalCoord (G.emb iχ) (G.chart iχ)
          (p ((OpenPartialHomeomorph.refl (EuclideanHalfSpace ((8 + k) + 1))).extend
            (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)) y)))) :=
      Filter.EventuallyEq.of_eq (funext fun u => by rw [hext_apply u])
    have hg : ∃ U ∈ 𝓝 (y₀ : EuclideanSpace ℝ (Fin ((8 + k) + 1))),
        ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun w => ℓ (Work.PTGeometric.tubeNormalCoord (G.emb iχ) (G.chart iχ) (p w))) U := by
      refine ⟨localSet G k₀ j₀ iχ ∩ p ⁻¹' (G.chart iχ).openTube, ?_, ?_⟩
      · exact Filter.inter_mem (hWopen.mem_nhds hy₀W)
          (hd_p.continuousAt.preimage_mem_nhds ((G.chart iχ).openTube_isOpen.mem_nhds hmem_p))
      · have houter : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
            (fun w => ℓ (Work.PTGeometric.tubeNormalCoord (G.emb iχ) (G.chart iχ) w))
            (G.chart iχ).openTube :=
          (show ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ℓ Set.univ from
            (ContinuousLinearMap.contDiff ℓ).contDiffOn).comp
            (contMDiffOn_iff_contDiffOn.mp
              (contMDiffOn_tubeNormalCoord (G.emb iχ) (G.chart iχ)))
            (fun _ _ => trivial)
        refine ContDiffOn.comp (s := localSet G k₀ j₀ iχ ∩ p ⁻¹' (G.chart iχ).openTube)
          (t := (G.chart iχ).openTube)
          (g := fun w => ℓ (Work.PTGeometric.tubeNormalCoord (G.emb iχ) (G.chart iχ) w))
          (f := p) houter ?_ ?_
        · exact hsm.mono Set.inter_subset_left
        · exact fun y hy => hy.2
    exact Work.PTGeometric.isSubmersionAt_of_boundary_linearization
      (N := (8 + k) + 1)
      (M := EuclideanHalfSpace ((8 + k) + 1))
      (e := OpenPartialHomeomorph.refl (EuclideanHalfSpace ((8 + k) + 1)))
      (StructureGroupoid.id_mem_maximalAtlas (contDiffGroupoid ((⊤ : ℕ∞) : WithTop ℕ∞)
        (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))))
      (mem_univ _) hg hf0 hgg0 hagree hsurj hnorm
  · -- the coordinate identity on `localSet`
    intro y hy h
    have hblock : alphaFamily (D := D) (Fam := Fam) G m (collPt k y)
        = (G.rep iχ).collapse (clipPt k (cZero k) (cOne k) k₀ j₀ y) := by
      rw [hiχ]
      exact alphaFamily_eq_collapse_of_block (G := G) m k₀ j₀ hk₀ hj₀ y hy.2.1 hy.2.2.1
        hy.2.2.2.1 hy.2.2.2.2.1
    exact coord_eq_model (G := G) hpow k₀ j₀ iχ y hy.1 hy.2.2.2.2.2 hblock hy.2.1 hy.2.2.1
      hy.2.2.2.1 hy.2.2.2.2.1 h

end

end Work.PTGeometric
