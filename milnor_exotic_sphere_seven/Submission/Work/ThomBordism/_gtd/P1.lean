import Mathlib
import Submission.Work.ThomBordism.Grassmann.InclDefs
import Submission.Work.ThomBordism.Grassmann.GrassmannianTopology
import Submission.Work.ThomBordism.Grassmann.Model
import Submission.Work.ThomBordism.Grassmann.Oriented
import Submission.Work.PTGeometric.exists_projOfPlane

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped Topology

namespace Work.ThomBordism.Grassmann

open Work.PTGeometric

noncomputable section

variable {k m : ℕ}

/-- The orientation-reversing diagonal matrix `diag(-1,1,…,1)`. -/
def flipMat (k : ℕ) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.diagonal fun a : Fin k => if (a : ℕ) = 0 then (-1 : ℝ) else 1

theorem flipMat_transpose (k : ℕ) : (flipMat k).transpose = flipMat k := by
  ext a b
  simp only [Matrix.transpose_apply, flipMat, Matrix.diagonal_apply]
  by_cases h : a = b
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h)]

theorem flipMat_mul_self (k : ℕ) : flipMat k * flipMat k = 1 := by
  rw [flipMat, Matrix.diagonal_mul_diagonal]
  have hfun : (fun a : Fin k => (if (a : ℕ) = 0 then (-1 : ℝ) else 1)
      * (if (a : ℕ) = 0 then (-1 : ℝ) else 1)) = fun _ => (1 : ℝ) := by
    funext a
    by_cases h : (a : ℕ) = 0 <;> simp [h]
  rw [hfun, Matrix.diagonal_one]

theorem flipMat_transpose_mul (k : ℕ) : (flipMat k).transpose * flipMat k = 1 := by
  rw [flipMat_transpose, flipMat_mul_self]

theorem flipMat_mul_transpose (k : ℕ) : flipMat k * (flipMat k).transpose = 1 := by
  rw [flipMat_transpose, flipMat_mul_self]

theorem isSO_conj_flipMat {A : Matrix (Fin k) (Fin k) ℝ} (hA : IsSO A) :
    IsSO (flipMat k * A * flipMat k) := by
  constructor
  · have h1 : (flipMat k * A * flipMat k).transpose = flipMat k * A.transpose * flipMat k := by
      rw [Matrix.transpose_mul, Matrix.transpose_mul, flipMat_transpose, Matrix.mul_assoc]
    rw [h1]
    calc flipMat k * A.transpose * flipMat k * (flipMat k * A * flipMat k)
        = flipMat k * A.transpose * (flipMat k * flipMat k) * A * flipMat k := by noncomm_ring
      _ = flipMat k * A.transpose * A * flipMat k := by
          rw [flipMat_mul_self, Matrix.mul_one]
      _ = flipMat k * (A.transpose * A) * flipMat k := by noncomm_ring
      _ = 1 := by rw [hA.1, Matrix.mul_one, flipMat_mul_self]
  · rw [Matrix.det_mul, Matrix.det_mul, hA.2]
    have hdet : (flipMat k).det * (flipMat k).det = 1 := by
      have h := congrArg Matrix.det (flipMat_transpose_mul k)
      rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
    calc (flipMat k).det * 1 * (flipMat k).det = (flipMat k).det * (flipMat k).det := by ring
      _ = 1 := hdet

/-- **The orientation reversal of the oriented Grassmannian**: right-multiplication of frames by
`diag(-1,1,…,1)`.  It preserves the underlying plane and reverses its orientation. -/
def ogFlip (k m : ℕ) : OG k m → OG k m :=
  Quotient.lift
    (fun f : Stiefel k m =>
      Quotient.mk'' (⟨soActFun (flipMat k) f.1,
        orthonormal_soActFun (flipMat_transpose_mul k) f.2⟩ : Stiefel k m))
    (fun f g hfg => by
      obtain ⟨A, rfl⟩ := hfg
      refine Quotient.sound ⟨⟨flipMat k * A.1 * flipMat k, isSO_conj_flipMat A.2⟩, ?_⟩
      apply Subtype.ext
      simp only [SOk.act]
      have hM : (A.1 * flipMat k : Matrix (Fin k) (Fin k) ℝ)
          = flipMat k * (flipMat k * A.1 * flipMat k) := by
        calc A.1 * flipMat k = (1 : Matrix (Fin k) (Fin k) ℝ) * A.1 * flipMat k := by
              rw [Matrix.one_mul]
          _ = (flipMat k * flipMat k) * A.1 * flipMat k := by rw [flipMat_mul_self]
          _ = flipMat k * (flipMat k * A.1 * flipMat k) := by noncomm_ring
      rw [soActFun_comp (flipMat k) A.1 f.1,
        soActFun_comp (flipMat k * A.1 * flipMat k) (flipMat k) f.1]
      exact congrArg (fun M => soActFun M f.1) hM)

theorem ogFlip_mk (f : Stiefel k m) :
    ogFlip k m (Quotient.mk (grassmannSetoid k m) f) =
      Quotient.mk (grassmannSetoid k m) (⟨soActFun (flipMat k) f.1,
        orthonormal_soActFun (flipMat_transpose_mul k) f.2⟩ : Stiefel k m) :=
  rfl

theorem continuous_ogFlip (k m : ℕ) : Continuous (ogFlip k m) := by
  refine (isQuotientMap_quotient_mk'.continuous_iff).mpr ?_
  show Continuous fun f : Stiefel k m => ogFlip k m (Quotient.mk (grassmannSetoid k m) f)
  have h : (fun f : Stiefel k m => ogFlip k m (Quotient.mk (grassmannSetoid k m) f))
      = fun f : Stiefel k m =>
          Quotient.mk (grassmannSetoid k m) (⟨soActFun (flipMat k) f.1,
            orthonormal_soActFun (flipMat_transpose_mul k) f.2⟩ : Stiefel k m) := by
    funext f; rw [ogFlip_mk]
  rw [h]
  refine continuous_quotient_mk'.comp (Continuous.subtype_mk ?_ _)
  exact (continuous_soActFun.comp (Continuous.prodMk continuous_const
    continuous_subtype_val))

/-- The orientation reversal as a continuous map. -/
def ogFlipCM (k m : ℕ) : C(OG k m, OG k m) := ⟨ogFlip k m, continuous_ogFlip k m⟩

@[simp] theorem ogFlipCM_apply (k m : ℕ) (x : OG k m) : ogFlipCM k m x = ogFlip k m x := rfl

theorem ogFlip_idem (k m : ℕ) (x : OG k m) : ogFlip k m (ogFlip k m x) = x := by
  obtain ⟨f, rfl⟩ := Quotient.exists_rep x
  rw [ogFlip_mk, ogFlip_mk]
  refine Quotient.sound ⟨⟨1, IsSO.one⟩, ?_⟩
  apply Subtype.ext
  simp only [SOk.act, soActFun_comp, flipMat_mul_self, soActFun_one]

theorem frameProj_flipMat (f : Fin k → Amb (k + m)) :
    frameProj (soActFun (flipMat k) f) = frameProj f := by
  show matLin (frameMat (soActFun (flipMat k) f) * (frameMat (soActFun (flipMat k) f)).transpose)
    = matLin (frameMat f * (frameMat f).transpose)
  congr 1
  rw [frameMat_soActFun, Matrix.transpose_mul,
    Matrix.mul_assoc, ← Matrix.mul_assoc (flipMat k) (flipMat k).transpose (frameMat f).transpose,
    flipMat_mul_transpose, Matrix.one_mul]

theorem projOfPlane_ogFlip (k m : ℕ) (x : OG k m) :
    projOfPlane k m (ogFlip k m x) = projOfPlane k m x := by
  obtain ⟨f, rfl⟩ := Quotient.exists_rep x
  rw [ogFlip_mk, projOfPlane_mk, projOfPlane_mk]
  exact frameProj_flipMat f.1

end

end Work.ThomBordism.Grassmann
