import Mathlib
import Submission.Work.ThomBordism.LeadChapter.TubeDetDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `Work.ThomBordism.LeadChapter.det_dthetaEndo_pos`

The block model `theta G m k₀ j₀ : ℝ^{k+8} → ℝ^{8+k}` of the collar chart is, in the source
coordinates, the reindexing `reEK k` of a *coordinatewise* map

  `diagMap v j = 2 R (A_j · ptScalar (v j) + B_j)`,

where `ptScalar t = (1 + t/√(1+t²))/2` is the scalar cube chart, `A_j = 2^{k₀+1}` on the outer
concatenation coordinate, `2^{j₀+1}` on the inner one, and `1` elsewhere.  Hence the derivative of
`theta` is the reindexing of a diagonal endomorphism with strictly positive diagonal
`2 R A_j · ptScalar'(v j)`, and since the reindexing has determinant `1`, the composed
endomorphism `dthetaEndo = reEKInv ∘ dtheta` has positive determinant.

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

/-! ## The block coefficients -/

/-- The coefficient of the model point in the coordinate `j`: `2^{k₀+1}` on the outer
concatenation coordinate `cZero k`, `2^{j₀+1}` on the inner one `cOne k`, and `1` elsewhere. -/
def blockA (k k₀ j₀ : ℕ) (j : Fin (k + 8)) : ℝ :=
  if j = cZero k then (2 : ℝ) ^ (k₀ + 1) else if j = cOne k then (2 : ℝ) ^ (j₀ + 1) else 1

/-- The constant part of the affine realisation of the block point in the coordinate `j`. -/
def blockB (k : ℕ) (j : Fin (k + 8)) : ℝ :=
  if j = cZero k ∨ j = cOne k then -(3 / 2) else -(1 / 2)

theorem blockA_cZero (k k₀ j₀ : ℕ) : blockA k k₀ j₀ (cZero k) = (2 : ℝ) ^ (k₀ + 1) := by
  rw [blockA, if_pos rfl]

theorem blockA_cOne (k k₀ j₀ : ℕ) : blockA k k₀ j₀ (cOne k) = (2 : ℝ) ^ (j₀ + 1) := by
  rw [blockA, if_neg (Ne.symm (cZero_ne_cOne k)), if_pos rfl]

theorem blockA_other {k k₀ j₀ : ℕ} {m : Fin (k + 8)} (h0 : m ≠ cZero k) (h1 : m ≠ cOne k) :
    blockA k k₀ j₀ m = 1 := by
  rw [blockA, if_neg h0, if_neg h1]

theorem blockB_cZero (k : ℕ) : blockB k (cZero k) = -(3 / 2) := by
  rw [blockB, if_pos (Or.inl rfl)]

theorem blockB_cOne (k : ℕ) : blockB k (cOne k) = -(3 / 2) := by
  rw [blockB, if_pos (Or.inr rfl)]

theorem blockB_other {k : ℕ} {m : Fin (k + 8)} (h0 : m ≠ cZero k) (h1 : m ≠ cOne k) :
    blockB k m = -(1 / 2) := by
  rw [blockB, if_neg (fun h => h.elim h0 h1)]

theorem blockA_pos (k k₀ j₀ : ℕ) (j : Fin (k + 8)) : 0 < blockA k k₀ j₀ j := by
  rw [blockA]
  split_ifs <;> positivity

/-! ## The coordinatewise model and its derivative -/

/-- The coordinatewise model: the `j`-th coordinate is the affine image of the scalar cube chart. -/
def diagPsi (G : GenuineTubeGeometry k D ι Fam) (k₀ j₀ : ℕ) (w : Fin (k + 8) → ℝ) :
    Fin (k + 8) → ℝ :=
  fun j => 2 * G.R * (blockA k k₀ j₀ j * ptScalar (w j) + blockB k j)

theorem diagPsi_eq (G : GenuineTubeGeometry k D ι Fam) (k₀ j₀ : ℕ) (w : Fin (k + 8) → ℝ) :
    diagPsi G k₀ j₀ w =
      fun j => 2 * G.R * (blockA k k₀ j₀ j * ptScalar (w j) + blockB k j) :=
  rfl

/-- The block model read in the source coordinates: `reEKInv ∘ theta`. -/
def diagMap (G : GenuineTubeGeometry k D ι Fam) (k₀ j₀ : ℕ)
    (v : EuclideanSpace ℝ (Fin (k + 8))) : EuclideanSpace ℝ (Fin (k + 8)) :=
  piToEucl (k + 8) (diagPsi G k₀ j₀ (euclToPi (k + 8) v))

/-- The diagonal endomorphism of `(Fin n → ℝ)` with diagonal `c`. -/
def diagCLM {n : ℕ} (c : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi
    (fun j => c j • (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ))

/-- The derivative of the block model, as an endomorphism of the source coordinates. -/
def diagEndo (G : GenuineTubeGeometry k D ι Fam) (k₀ j₀ : ℕ)
    (v : EuclideanSpace ℝ (Fin (k + 8))) :
    EuclideanSpace ℝ (Fin (k + 8)) →L[ℝ] EuclideanSpace ℝ (Fin (k + 8)) :=
  (piToEucl (k + 8)).toContinuousLinearMap.comp
    ((diagCLM (fun j => 2 * G.R * (blockA k k₀ j₀ j * deriv ptScalar (v j)))).comp
      (euclToPi (k + 8)).toContinuousLinearMap)

/-! ## The scalar cube chart -/

theorem hasDerivAt_ptScalar (t : ℝ) :
    HasDerivAt ptScalar (1 / (2 * (Real.sqrt (1 + t ^ 2)) ^ 3)) t := by
  have hs : 0 < Real.sqrt (1 + t ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hq : HasDerivAt (fun u : ℝ => 1 + u ^ 2) (2 * t) t := by
    simpa using ((hasDerivAt_id t).pow 2).const_add 1
  have h1 : HasDerivAt (fun u : ℝ => Real.sqrt (1 + u ^ 2)) (t / Real.sqrt (1 + t ^ 2)) t := by
    have h := hq.sqrt (by positivity : (1 : ℝ) + t ^ 2 ≠ 0)
    rw [show (2 * t) / (2 * Real.sqrt (1 + t ^ 2)) = t / Real.sqrt (1 + t ^ 2) by
      rw [mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]] at h
    exact h
  have h2 : HasDerivAt (fun u : ℝ => u / Real.sqrt (1 + u ^ 2))
      ((1 * Real.sqrt (1 + t ^ 2) - t * (t / Real.sqrt (1 + t ^ 2))) /
        (Real.sqrt (1 + t ^ 2)) ^ 2) t :=
    (hasDerivAt_id t).div h1 (ne_of_gt hs)
  have h3 : HasDerivAt (fun u : ℝ => (1 + u / Real.sqrt (1 + u ^ 2)) / 2)
      (((1 * Real.sqrt (1 + t ^ 2) - t * (t / Real.sqrt (1 + t ^ 2))) /
        (Real.sqrt (1 + t ^ 2)) ^ 2) / 2) t :=
    (h2.const_add 1).div_const 2
  have hfun : (fun u : ℝ => (1 + u / Real.sqrt (1 + u ^ 2)) / 2) = ptScalar := rfl
  have hval : ((1 * Real.sqrt (1 + t ^ 2) - t * (t / Real.sqrt (1 + t ^ 2))) /
        (Real.sqrt (1 + t ^ 2)) ^ 2) / 2 = 1 / (2 * (Real.sqrt (1 + t ^ 2)) ^ 3) := by
    have hsq : Real.sqrt (1 + t ^ 2) ^ 2 = 1 + t ^ 2 := Real.sq_sqrt (by positivity)
    field_simp
    rw [hsq]
    ring
  rw [hfun, hval] at h3
  exact h3

theorem deriv_ptScalar_eq (t : ℝ) :
    deriv ptScalar t = 1 / (2 * (Real.sqrt (1 + t ^ 2)) ^ 3) :=
  (hasDerivAt_ptScalar t).deriv

theorem deriv_ptScalar_pos (t : ℝ) : 0 < deriv ptScalar t := by
  rw [deriv_ptScalar_eq]
  positivity

/-! ## The source coordinates of the block point -/

theorem collPt_srcOfSpatial (k : ℕ) (v : EuclideanSpace ℝ (Fin (k + 8))) (m : Fin (k + 8)) :
    ((collPt k (srcOfSpatial k v) m : Set.Icc (0 : ℝ) 1) : ℝ) = ptScalar (v m) := by
  rw [collPt_apply, tail_srcCast_srcOfSpatial]
  rfl

theorem modelPoint_eq (k : ℕ) (k₀ j₀ : ℕ)
    (v : EuclideanSpace ℝ (Fin (k + 8))) (m : Fin (k + 8)) :
    modelPoint k (cZero k) (cOne k) k₀ j₀ (srcOfSpatial k v) m - 1 / 2
      = blockA k k₀ j₀ m * ptScalar (v m) + blockB k m := by
  simp only [modelPoint_apply, collPt_srcOfSpatial]
  by_cases h0 : m = cZero k
  · rw [if_pos h0, h0, blockA_cZero, blockB_cZero]; ring
  · rw [if_neg h0]
    by_cases h1 : m = cOne k
    · rw [if_pos h1, h1, blockA_cOne, blockB_cOne]; ring
    · rw [if_neg h1, blockA_other h0 h1, blockB_other h0 h1]; ring

/-! ## `theta` as the reindexing of the coordinatewise model -/

theorem eucOfReal_eq_piToEucl (N : ℕ) (R : ℝ) (v : Fin N → ℝ) :
    eucOfReal N R v = piToEucl N (fun i => 2 * R * (v i - 1 / 2)) := rfl

theorem euToPi_piToEucl (n : ℕ) (x : Fin n → ℝ) : euToPi n ((piToEucl n) x) = x :=
  ContinuousLinearEquiv.apply_symm_apply _ _

theorem euclToPi_piToEucl (n : ℕ) (x : Fin n → ℝ) : euclToPi n ((piToEucl n) x) = x :=
  ContinuousLinearEquiv.apply_symm_apply _ _

theorem theta_eq (G : GenuineTubeGeometry k D ι Fam) (m k₀ j₀ : ℕ)
    (v : EuclideanSpace ℝ (Fin (k + 8))) :
    theta G m k₀ j₀ v = reEK k (diagMap G k₀ j₀ v) := by
  rw [theta, modelEuc, eucOfReal_eq_piToEucl, reEK, diagMap, diagPsi_eq]
  apply (euclToPi (8 + k)).injective
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply]
  funext l
  simp only [ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply]
  rw [modelPoint_eq, euToPi_piToEucl]
  rfl

/-! ## `reEKInv` is a left inverse of `reEK` -/

theorem reEKInv_reEK (k : ℕ) (x : EuclideanSpace ℝ (Fin (k + 8))) :
    reEKInv k (reEK k x) = x := by
  rw [reEK, reEKInv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  apply (euclToPi (k + 8)).injective
  rw [euclToPi_piToEucl]
  funext i
  simp only [ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, euToPi_piToEucl, finKRInv_finKR]
  rfl

/-! ## The derivative of the coordinatewise model -/

theorem hasFDerivAt_diagPsi (G : GenuineTubeGeometry k D ι Fam) (k₀ j₀ : ℕ)
    (w : Fin (k + 8) → ℝ) :
    HasFDerivAt (diagPsi G k₀ j₀)
      (diagCLM (fun j => 2 * G.R * (blockA k k₀ j₀ j * deriv ptScalar (w j)))) w := by
  show HasFDerivAt (fun w j => 2 * G.R * (blockA k k₀ j₀ j * ptScalar (w j) + blockB k j))
    (ContinuousLinearMap.pi (fun j =>
      (2 * G.R * (blockA k k₀ j₀ j * deriv ptScalar (w j))) •
        (ContinuousLinearMap.proj j : (Fin (k + 8) → ℝ) →L[ℝ] ℝ))) w
  rw [hasFDerivAt_pi]
  intro j
  have hder : HasDerivAt (fun t : ℝ => 2 * G.R * (blockA k k₀ j₀ j * ptScalar t + blockB k j))
      (2 * G.R * (blockA k k₀ j₀ j * deriv ptScalar (w j))) (w j) := by
    have h1 : HasDerivAt ptScalar (deriv ptScalar (w j)) (w j) :=
      (differentiableAt_ptScalar (w j)).hasDerivAt
    have h2 : HasDerivAt (fun y : ℝ => blockA k k₀ j₀ j * ptScalar y + blockB k j)
        (blockA k k₀ j₀ j * deriv ptScalar (w j)) (w j) :=
      (h1.const_mul (blockA k k₀ j₀ j)).add_const (blockB k j)
    have h3 := h2.const_mul (2 * G.R)
    simpa only [mul_assoc] using h3
  have hcomp := hder.hasFDerivAt.comp w (hasFDerivAt_proj j w)
  have hkey : (ContinuousLinearMap.toSpanSingleton ℝ
        (2 * G.R * (blockA k k₀ j₀ j * deriv ptScalar (w j)))).comp
        (ContinuousLinearMap.proj j : (Fin (k + 8) → ℝ) →L[ℝ] ℝ)
      = (2 * G.R * (blockA k k₀ j₀ j * deriv ptScalar (w j))) •
        (ContinuousLinearMap.proj j : (Fin (k + 8) → ℝ) →L[ℝ] ℝ) := by
    ext y
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      smul_apply, smul_eq_mul]
    ring
  rw [hkey] at hcomp
  exact hcomp

theorem hasFDerivAt_diagMap (G : GenuineTubeGeometry k D ι Fam) (k₀ j₀ : ℕ)
    (v : EuclideanSpace ℝ (Fin (k + 8))) :
    HasFDerivAt (diagMap G k₀ j₀) (diagEndo G k₀ j₀ v) v := by
  have h1 : HasFDerivAt (fun v : EuclideanSpace ℝ (Fin (k + 8)) =>
        diagPsi G k₀ j₀ (euclToPi (k + 8) v))
      ((diagCLM (fun j =>
         2 * G.R * (blockA k k₀ j₀ j * deriv ptScalar ((euclToPi (k + 8) v) j)))).comp
        (euclToPi (k + 8)).toContinuousLinearMap) v :=
    (hasFDerivAt_diagPsi G k₀ j₀ (euclToPi (k + 8) v)).comp v
      (euclToPi (k + 8)).hasFDerivAt
  exact (piToEucl (k + 8)).hasFDerivAt.comp v h1

/-! ## `dthetaEndo` is the derivative of the coordinatewise model -/

theorem dthetaEndo_eq_diagEndo (G : GenuineTubeGeometry k D ι Fam) (m k₀ j₀ : ℕ)
    (v : EuclideanSpace ℝ (Fin (k + 8))) :
    dthetaEndo G m k₀ j₀ v = diagEndo G k₀ j₀ v := by
  have hth : (fun v => reEK k (diagMap G k₀ j₀ v)) = theta G m k₀ j₀ :=
    funext fun v => (theta_eq G m k₀ j₀ v).symm
  have hcompId : (reEKInv k).comp (reEK k) =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (k + 8))) :=
    ContinuousLinearMap.ext fun x => reEKInv_reEK k x
  have hdtheta : HasFDerivAt (theta G m k₀ j₀) ((reEK k).comp (diagEndo G k₀ j₀ v)) v := by
    rw [← hth]
    exact (reEK k).hasFDerivAt.comp v (hasFDerivAt_diagMap G k₀ j₀ v)
  have hfderiv : dtheta G m k₀ j₀ v = (reEK k).comp (diagEndo G k₀ j₀ v) := by
    rw [dtheta]
    exact hdtheta.fderiv
  calc dthetaEndo G m k₀ j₀ v
      = (reEKInv k).comp (dtheta G m k₀ j₀ v) := rfl
    _ = (reEKInv k).comp ((reEK k).comp (diagEndo G k₀ j₀ v)) := by rw [hfderiv]
    _ = ((reEKInv k).comp (reEK k)).comp (diagEndo G k₀ j₀ v) := by
          rw [ContinuousLinearMap.comp_assoc]
    _ = (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (k + 8)))).comp
          (diagEndo G k₀ j₀ v) := by rw [hcompId]
    _ = diagEndo G k₀ j₀ v := ContinuousLinearMap.id_comp _

/-! ## The determinant of the diagonal endomorphism -/

theorem det_diagCLM {n : ℕ} (c : Fin n → ℝ) :
    LinearMap.det (diagCLM c).toLinearMap = ∏ j, c j := by
  have hM : LinearMap.toMatrix' ((diagCLM c).toLinearMap) = Matrix.diagonal c := by
    ext i j
    rw [LinearMap.toMatrix'_apply]
    simp only [diagCLM]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  have hD : (diagCLM c).toLinearMap = Matrix.toLin' (Matrix.diagonal c) := by
    rw [← hM, Matrix.toLin'_toMatrix']
  rw [hD, LinearMap.det_toLin', Matrix.det_diagonal]

theorem det_diagEndo_pos (G : GenuineTubeGeometry k D ι Fam) (k₀ j₀ : ℕ) (hR : 0 < G.R)
    (v : EuclideanSpace ℝ (Fin (k + 8))) :
    0 < LinearMap.det (diagEndo G k₀ j₀ v).toLinearMap := by
  set c : Fin (k + 8) → ℝ := fun j => 2 * G.R * (blockA k k₀ j₀ j * deriv ptScalar (v j)) with hc
  set e : (Fin (k + 8) → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (k + 8)) :=
    (piToEucl (k + 8)).toLinearEquiv with he
  have hX : (diagEndo G k₀ j₀ v).toLinearMap
      = (e : (Fin (k + 8) → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin (k + 8))) ∘ₗ
          (diagCLM c).toLinearMap ∘ₗ
          (e.symm : EuclideanSpace ℝ (Fin (k + 8)) →ₗ[ℝ] (Fin (k + 8) → ℝ)) := by
    rw [diagEndo, hc, he]
    simp only [ContinuousLinearMap.toLinearMap_comp]
    rfl
  rw [hX, LinearMap.det_conj (diagCLM c).toLinearMap e, det_diagCLM]
  apply Finset.prod_pos
  intro j _
  rw [hc]
  exact mul_pos (mul_pos (by norm_num) hR)
    (mul_pos (blockA_pos k k₀ j₀ j) (deriv_ptScalar_pos (v j)))

/-! ## The target -/

theorem det_dthetaEndo_pos {k : ℕ} {D : Work.ThomBordism.PontryaginThom.ThomTarget k} {ι : Type}
    [Fintype ι] {Fam : ι → Work.ThomBordism.Man8}
    (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam) (m k₀ j₀ : ℕ) (hR : 0 < G.R)
    (v : EuclideanSpace ℝ (Fin (k + 8))) :
    0 < LinearMap.det (Work.ThomBordism.LeadChapter.dthetaEndo G m k₀ j₀ v).toLinearMap := by
  rw [dthetaEndo_eq_diagEndo]
  exact det_diagEndo_pos G k₀ j₀ hR v

end

end Work.ThomBordism.LeadChapter
