import Mathlib
import Submission.Work.ThomBordism.Grassmann.Grassmannian
import Submission.Work.PTGeometric.RieszProj.Defs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-!
# The orthogonal projection onto the plane of a frame

Vocabulary for `Work.PTGeometric.exists_projOfPlane`.  For a (not necessarily orthonormal)
frame `f : Fin k → ℝ^{k+m}`:

* `frameMat f` is the `(k+m) × k` coordinate matrix of the frame;
* `projMat f = frameMat f * (frameMat f)ᵀ` is the matrix of the orthogonal projection onto the
  plane of the frame when `f` is orthonormal;
* `frameProj f = matLin (projMat f)` is that projection as a continuous linear endomorphism.

The point of the *matrix* description (as opposed to a submodule description) is that
`f ↦ frameProj f` is manifestly continuous, which is what makes the descended map on the oriented
Grassmannian continuous.  The main facts proved here, for an orthonormal frame `f`:

* `frameProj_apply` : `frameProj f w = ∑ j, ⟪f j, w⟫ • f j`;
* `frameProj_fixed_iff` : `frameProj f w = w ↔ w ∈ span ℝ (range f)`;
* `frameProj_mem_Gr` : `frameProj f ∈ Gr (k+m) k`;
* `frameProj_soActFun` : the projection is invariant under the `SO(k)`-action on frames;
* `continuous_frameProj` : `f ↦ frameProj f` is continuous.
-/

namespace Work.PTGeometric

open scoped Topology Matrix
open Work.ThomBordism.Grassmann

noncomputable section

variable {k m : ℕ}

/-! ## Definitions -/

/-- The **coordinate matrix** of a frame: the `(r,j)` entry is the `r`-th coordinate of the `j`-th
vector of the frame. -/
def frameMat (f : Fin k → Amb (k + m)) : Matrix (Fin (k + m)) (Fin k) ℝ :=
  fun r j => EuclideanSpace.proj r (f j)

/-- `A Aᵀ`, for `A = frameMat f` the coordinate matrix of a frame; the matrix of the orthogonal
projection onto the plane of the frame when the frame is orthonormal. -/
def projMat (f : Fin k → Amb (k + m)) : Matrix (Fin (k + m)) (Fin (k + m)) ℝ :=
  frameMat f * (frameMat f)ᵀ

/-- **The orthogonal projection onto the plane of a frame**, as a continuous linear endomorphism
of the ambient space. -/
def frameProj (f : Fin k → Amb (k + m)) : Amb (k + m) →L[ℝ] Amb (k + m) :=
  matLin (projMat f)

/-! ## Elementary computations -/

/-- The real inner product on `ℝⁿ` is the sum of the products of the coordinates. -/
theorem inner_eq_sum_proj {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) :
    inner ℝ x y = ∑ i, EuclideanSpace.proj i y * EuclideanSpace.proj i x := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, Pi.star_apply, star_trivial, EuclideanSpace.coe_proj]

/-- The entries of `mulVec`. -/
theorem mulVec_apply_sum {l m : ℕ} (M : Matrix (Fin l) (Fin m) ℝ) (v : Fin m → ℝ)
    (i : Fin l) : M.mulVec v i = ∑ j, M i j * v j := rfl

/-- The frame matrix acts on coefficients by the coordinate map of the frame. -/
theorem frameMat_mulVec_eq_coeffMap (f : Fin k → Amb (k + m))
    (u : Fin k → ℝ) : (frameMat f).mulVec u = coeffMap f u := by
  funext r
  rw [mulVec_apply_sum, coeffMap_apply]
  exact Finset.sum_congr rfl fun j _ => by rw [frameMat]; ring

/-- The transpose of the frame matrix reads the inner products with the vectors of the frame. -/
theorem frameMat_transpose_mulVec (f : Fin k → Amb (k + m))
    (w : Amb (k + m)) (j : Fin k) :
    ((frameMat f)ᵀ.mulVec w.ofLp) j = inner ℝ (f j) w := by
  have h1 : ((frameMat f)ᵀ.mulVec w.ofLp) j = ∑ r, frameMat f r j * w.ofLp r := by
    rw [mulVec_apply_sum]
    exact Finset.sum_congr rfl fun r _ => by rw [Matrix.transpose_apply]
  rw [h1, inner_eq_sum_proj]
  refine Finset.sum_congr rfl fun r _ => ?_
  show frameMat f r j * w.ofLp r = EuclideanSpace.proj r w * EuclideanSpace.proj r (f j)
  rw [frameMat]
  simp only [EuclideanSpace.coe_proj]
  ring

/-- **The orthogonal projection onto the plane of the frame**, in the form of a sum. -/
theorem frameProj_apply (f : Fin k → Amb (k + m)) (w : Amb (k + m)) :
    frameProj f w = ∑ j, (inner ℝ (f j) w) • f j := by
  rw [frameProj, matLin_apply]
  apply WithLp.ofLp_injective
  rw [WithLp.ofLp_toLp, projMat, ← Matrix.mulVec_mulVec]
  have h2 : (frameMat f)ᵀ.mulVec w.ofLp = fun j => inner ℝ (f j) w := by
    funext j; exact frameMat_transpose_mulVec f w j
  rw [h2, frameMat_mulVec_eq_coeffMap]
  funext r
  rw [WithLp.ofLp_sum, Finset.sum_apply, coeffMap_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, EuclideanSpace.coe_proj]

/-! ## Orthonormality -/

/-- The transpose of an orthonormal frame matrix is its left inverse. -/
theorem frameMat_transpose_mul {f : Fin k → Amb (k + m)}
    (hf : Orthonormal ℝ f) : (frameMat f)ᵀ * frameMat f = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hinner : (∑ r, (frameMat f)ᵀ i r * frameMat f r j) = inner ℝ (f i) (f j) := by
    rw [inner_eq_sum_proj]
    refine Finset.sum_congr rfl fun r _ => ?_
    show (frameMat f)ᵀ i r * frameMat f r j
      = EuclideanSpace.proj r (f j) * EuclideanSpace.proj r (f i)
    rw [Matrix.transpose_apply, mul_comm]
    rfl
  rw [hinner, orthonormal_iff_ite] at *
  exact hf i j

/-! ## The projection fixes the plane, and only the plane -/

/-- The projection lands in the plane of the frame. -/
theorem frameProj_mem_span {f : Fin k → Amb (k + m)} (x : Amb (k + m)) :
    frameProj f x ∈ Submodule.span ℝ (Set.range f) := by
  rw [frameProj_apply]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

/-- The projection fixes the vectors of the frame. -/
theorem frameProj_fixes {f : Fin k → Amb (k + m)}
    (hf : Orthonormal ℝ f) (i : Fin k) : frameProj f (f i) = f i := by
  rw [frameProj_apply]
  rw [orthonormal_iff_ite] at hf
  rw [Finset.sum_eq_single i]
  · rw [hf i i, if_pos rfl, one_smul]
  · intro j _ hji
    rw [hf j i, if_neg hji, zero_smul]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- **The fixed points of the projection are exactly the plane of the frame**. -/
theorem frameProj_fixed_iff {f : Fin k → Amb (k + m)}
    (hf : Orthonormal ℝ f) (w : Amb (k + m)) :
    frameProj f w = w ↔ w ∈ Submodule.span ℝ (Set.range f) := by
  constructor
  · intro h
    rw [← h]
    exact frameProj_mem_span w
  · intro hw
    refine Submodule.span_induction (p := fun z _ => frameProj f z = z) ?_ ?_ ?_ ?_ hw
    · rintro - ⟨i, rfl⟩; exact frameProj_fixes hf i
    · simp
    · intro a b _ _ ha hb; rw [map_add, ha, hb]
    · intro c a _ ha; rw [map_smul, ha]

/-- The range of the projection is the plane of the frame. -/
theorem frameProj_range {f : Fin k → Amb (k + m)} (hf : Orthonormal ℝ f) :
    LinearMap.range ((frameProj f) : Amb (k + m) →ₗ[ℝ] Amb (k + m)) =
      Submodule.span ℝ (Set.range f) := by
  ext w
  constructor
  · rintro ⟨u, rfl⟩
    exact frameProj_mem_span u
  · intro hw
    exact ⟨w, (frameProj_fixed_iff hf w).mpr hw⟩

/-- The projection is self-adjoint. -/
theorem frameProj_inner_eq (f : Fin k → Amb (k + m)) (x y : Amb (k + m)) :
    inner ℝ (frameProj f x) y = inner ℝ x (frameProj f y) := by
  rw [frameProj_apply, frameProj_apply, sum_inner, inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_left, inner_smul_right, real_inner_comm (f j) x]
  simp only [starRingEnd_apply, star_trivial]
  ring

/-- The projection is self-adjoint, as an operator identity. -/
theorem frameProj_adjoint (f : Fin k → Amb (k + m)) :
    ContinuousLinearMap.adjoint (frameProj f) = frameProj f :=
  ((ContinuousLinearMap.eq_adjoint_iff _ _).mpr fun x y => frameProj_inner_eq f x y).symm

/-- The projection is idempotent. -/
theorem frameProj_mul_self {f : Fin k → Amb (k + m)} (hf : Orthonormal ℝ f) :
    frameProj f * frameProj f = frameProj f := by
  refine ContinuousLinearMap.ext fun x => ?_
  show frameProj f (frameProj f x) = frameProj f x
  exact (frameProj_fixed_iff hf _).mpr (frameProj_mem_span x)

/-- **The projection of an orthonormal frame is a rank-`k` orthogonal projection.** -/
theorem frameProj_mem_Gr {f : Fin k → Amb (k + m)} (hf : Orthonormal ℝ f) :
    frameProj f ∈ Gr (k + m) k := by
  have htrace : LinearMap.trace ℝ (Amb (k + m)) (frameProj f) = (k : ℝ) := by
    have hIsIdem : IsIdempotentElem ((frameProj f) : Amb (k + m) →ₗ[ℝ] Amb (k + m)) := by
      rw [IsIdempotentElem]
      refine LinearMap.ext fun x => ?_
      show frameProj f (frameProj f x) = frameProj f x
      exact (frameProj_fixed_iff hf _).mpr (frameProj_mem_span x)
    have hIsProj : LinearMap.IsProj
        (LinearMap.range ((frameProj f) : Amb (k + m) →ₗ[ℝ] Amb (k + m)))
        ((frameProj f) : Amb (k + m) →ₗ[ℝ] Amb (k + m)) :=
      (LinearMap.isProj_range_iff_isIdempotentElem _).mpr hIsIdem
    have hfin : Module.finrank ℝ
        (LinearMap.range ((frameProj f) : Amb (k + m) →ₗ[ℝ] Amb (k + m))) = k := by
      rw [frameProj_range hf, finrank_span_eq_card hf.linearIndependent, Fintype.card_fin]
    rw [hIsProj.trace, hfin]
  exact ⟨frameProj_adjoint f, frameProj_mul_self hf, htrace⟩

/-! ## Continuity in the frame -/

/-- The coordinate matrix of a frame depends continuously on the frame. -/
theorem continuous_frameMat :
    Continuous (fun f : Stiefel k m => frameMat f.1) := by
  refine continuous_matrix fun r j => ?_
  exact (EuclideanSpace.proj r).continuous.comp ((continuous_apply j).comp continuous_subtype_val)

/-- The matrix of the projection depends continuously on the frame. -/
theorem continuous_projMat :
    Continuous (fun f : Stiefel k m => projMat f.1) :=
  continuous_frameMat.matrix_mul continuous_frameMat.matrix_transpose

/-- **The projection depends continuously on the frame.** -/
theorem continuous_frameProj : Continuous (fun f : Stiefel k m => frameProj f.1) :=
  continuous_matLin.comp continuous_projMat

/-! ## Invariance under the `SO(k)`-action on frames -/

/-- The `SO(k)`-action on frames preserves the span. -/
theorem span_soActFun_eq (A : SOk k) (f : Fin k → Amb (k + m)) :
    Submodule.span ℝ (Set.range (soActFun A.1 f)) = Submodule.span ℝ (Set.range f) := by
  refine le_antisymm ?_ ?_
  · refine Submodule.span_le.mpr ?_
    rintro - ⟨j, rfl⟩
    rw [soActFun]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨i, rfl⟩)
  · have hAA : ∀ i l : Fin k, (∑ j : Fin k, A.1 i j * A.1 l j) = if i = l then 1 else 0 := by
      intro i l
      have h := congrFun (congrFun A.2.mul_transpose_self i) l
      simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using h
    have hback : ∀ i : Fin k, f i = ∑ j : Fin k, A.1 i j • soActFun A.1 f j := by
      intro i
      have h1 : (∑ j : Fin k, A.1 i j • soActFun A.1 f j)
          = ∑ j : Fin k, ∑ l : Fin k, (A.1 i j * A.1 l j) • f l := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [soActFun, Finset.smul_sum]
        exact Finset.sum_congr rfl (fun l _ => by rw [mul_smul])
      have h2 : (∑ j : Fin k, ∑ l : Fin k, (A.1 i j * A.1 l j) • f l)
          = ∑ l : Fin k, (∑ j : Fin k, A.1 i j * A.1 l j) • f l := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun l _ => (Finset.sum_smul).symm)
      have h3 : (∑ l : Fin k, (∑ j : Fin k, A.1 i j * A.1 l j) • f l) = f i := by
        rw [Finset.sum_eq_single i]
        · rw [hAA i i, if_pos rfl, one_smul]
        · intro l _ hl
          rw [hAA i l, if_neg (fun hc => hl hc.symm), zero_smul]
        · intro h; exact absurd (Finset.mem_univ i) h
      rw [h1, h2, h3]
    refine Submodule.span_le.mpr ?_
    rintro - ⟨i, rfl⟩
    rw [hback i]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

/-- The coordinate matrix of the transformed frame. -/
theorem frameMat_soActFun (f : Fin k → Amb (k + m)) (A : Matrix (Fin k) (Fin k) ℝ) :
    frameMat (soActFun A f) = frameMat f * A := by
  ext r j
  rw [frameMat, soActFun, Matrix.mul_apply]
  simp only [map_sum, map_smul]
  exact Finset.sum_congr rfl fun l _ => by rw [frameMat, smul_eq_mul, mul_comm]

/-- **The projection is invariant under the `SO(k)`-action on frames.** -/
theorem frameProj_soActFun (f : Fin k → Amb (k + m)) (A : SOk k) :
    frameProj (soActFun A.1 f) = frameProj f := by
  show matLin (projMat (soActFun A.1 f)) = matLin (projMat f)
  congr 1
  simp only [projMat, frameMat_soActFun, Matrix.transpose_mul]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (A.1) (A.1ᵀ) (frameMat f)ᵀ, A.2.mul_transpose_self,
    Matrix.one_mul]

end

end Work.PTGeometric
