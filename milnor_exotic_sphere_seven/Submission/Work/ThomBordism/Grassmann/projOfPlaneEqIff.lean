import Mathlib
import Submission.Work.ThomBordism.gaussTubeData

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

open scoped Matrix

namespace Work.ThomBordism.Grassmann

open Work.PTGeometric

/-- **Two orthonormal frames with the same orthogonal projection differ by an element of `SO(k)`.**
The projection onto the span remembers the span but forgets the orientation: the transition matrix
of the two frames is `A i j = ⟪f i, g j⟫`, it satisfies `Aᵀ A = 1`, and `g = A · f`. -/
theorem frameProj_eq_iff_soActFun {k m : ℕ} (f g : Stiefel k m)
    (h : frameProj f.1 = frameProj g.1) :
    ∃ A : Matrix (Fin k) (Fin k) ℝ,
      Aᵀ * A = 1 ∧ (g.1 = soActFun A f.1) ∧
        (A.det = 1 ∨ A.det = -1) := by
  let A : Matrix (Fin k) (Fin k) ℝ := fun j i => inner ℝ (f.1 j) (g.1 i)
  have hg : g.1 = soActFun A f.1 := by
    funext i
    have h1 : frameProj f.1 (g.1 i) = g.1 i := by
      rw [h, frameProj_fixes g.2 i]
    rw [← h1, frameProj_apply]
    rfl
  have hAorth : Aᵀ * A = 1 := by
    have h1 : (frameMat g.1)ᵀ * frameMat g.1 = 1 := frameMat_transpose_mul g.2
    rw [hg, frameMat_soActFun, Matrix.transpose_mul] at h1
    rw [Matrix.mul_assoc Aᵀ (frameMat f.1)ᵀ (frameMat f.1 * A)] at h1
    rw [← Matrix.mul_assoc (frameMat f.1)ᵀ (frameMat f.1) A] at h1
    rw [← Matrix.mul_assoc Aᵀ ((frameMat f.1)ᵀ * frameMat f.1) A] at h1
    rw [frameMat_transpose_mul f.2, Matrix.mul_one] at h1
    exact h1
  have hdet : A.det * A.det = 1 := by
    have h2 : (Aᵀ * A).det = (1 : Matrix (Fin k) (Fin k) ℝ).det := congrArg Matrix.det hAorth
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h2
    exact h2
  exact ⟨A, hAorth, hg, mul_self_eq_one_iff.mp hdet⟩

/-- **The projection onto the plane determines the oriented plane up to the orientation flip.** -/
theorem eq_or_flip_of_frameProj_eq {k m : ℕ} (f g : Stiefel k m)
    (h : frameProj f.1 = frameProj g.1) :
    (Quotient.mk'' f : OG k m) = Quotient.mk'' g ∨
      (Quotient.mk'' f : OG k m) = ogFlip k m (Quotient.mk'' g) := by
  obtain ⟨A, hAorth, hg, hdet⟩ := frameProj_eq_iff_soActFun f g h
  rcases hdet with hdet1 | hdetm1
  · left
    exact Quotient.sound ⟨⟨A, hAorth, hdet1⟩, Subtype.ext hg⟩
  · right
    have hk : 0 < k := by
      by_contra hk
      have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
      subst hk0
      rw [Matrix.det_fin_zero] at hdetm1
      norm_num at hdetm1
    have hB : IsSO (A * flipMat k) := by
      constructor
      · rw [Matrix.transpose_mul, flipMat_transpose]
        rw [Matrix.mul_assoc (flipMat k) Aᵀ (A * flipMat k)]
        rw [← Matrix.mul_assoc Aᵀ A (flipMat k)]
        rw [hAorth, Matrix.one_mul, flipMat_mul_self]
      · rw [Matrix.det_mul, hdetm1, Work.ThomBordism.Signs.CoordFlip.flipMat_det hk]
        norm_num
    have hfun : soActFun (A * flipMat k) f.1 = soActFun (flipMat k) g.1 := by
      rw [hg, soActFun_comp]
    have h1 : (Quotient.mk'' f : OG k m) =
        (Quotient.mk'' (⟨soActFun (A * flipMat k) f.1,
          orthonormal_soActFun hB.1 f.2⟩ : Stiefel k m) : OG k m) :=
      Quotient.sound ⟨⟨A * flipMat k, hB⟩, Subtype.ext rfl⟩
    have h2 : (Quotient.mk'' (⟨soActFun (A * flipMat k) f.1,
          orthonormal_soActFun hB.1 f.2⟩ : Stiefel k m) : OG k m) =
        (Quotient.mk'' (⟨soActFun (flipMat k) g.1,
          orthonormal_soActFun (flipMat_transpose_mul k) g.2⟩ : Stiefel k m) : OG k m) := by
      apply congrArg (fun x : Stiefel k m => (Quotient.mk'' x : OG k m))
      exact Subtype.ext hfun
    rw [h1, h2, ogFlip_mk g]

theorem projOfPlaneEqIff (k m : ℕ) (P Q : Work.ThomBordism.Grassmann.OG k m) :
    Work.PTGeometric.projOfPlane k m P = Work.PTGeometric.projOfPlane k m Q ↔
      P = Q ∨ P = Work.ThomBordism.Grassmann.ogFlip k m Q := by
  constructor
  · intro h
    obtain ⟨f, rfl⟩ := Quotient.exists_rep P
    obtain ⟨g, rfl⟩ := Quotient.exists_rep Q
    rw [Work.PTGeometric.projOfPlane_mk, Work.PTGeometric.projOfPlane_mk] at h
    exact eq_or_flip_of_frameProj_eq f g h
  · rintro (h | h)
    · rw [h]
    · rw [h, projOfPlane_ogFlip]

end Work.ThomBordism.Grassmann
