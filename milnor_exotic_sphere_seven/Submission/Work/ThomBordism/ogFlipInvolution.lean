import Mathlib
import Submission.Work.ThomBordism._gtd.P1

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# THOM: the orientation flip of the oriented Grassmannian is an involution

`Work.ThomBordism.Grassmann.ogFlip` reverses the orientation of an oriented plane (right
multiplication of frames by `flipMat k = diag(-1, 1, …, 1)`).  This file records that it is an
involution, together with the immediate corollaries (injectivity, surjectivity, bijectivity).

## Why this matters for the last mile (session 48)

The field `Work.PTGeometric.GenuineTubeGeometry.tie` is, per piece, the **disjunction**

    gauss(·) = padGaussFunM E ND mU hmU (foot)  ∨  gauss(·) = ogFlip (padGaussFunM E ND mU hmU (foot))

(`Work.PTGeometric.TiedGaussNormal`), and the two disjuncts *can be swapped*: if `gauss` satisfies
`tie` then so does `ogFlip ∘ gauss`, because the flipped disjunct becomes the other one — which is
exactly this involution.  So `tie` alone does not pin the branch, and (with `padGaussFunM_eq_of_normalData`,
which makes the plane's *orientation* the only datum in play) the branch is free per piece unless a
further field (the project lead's round-45 `pulledThom_gauss`) ties it.  This is the session-48
finding recorded in `NOTE_SESSION48.md` §4; the filling of the lead's field needs this involution.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped Topology

namespace Work.ThomBordism.Grassmann

open Work.TangentClasses

noncomputable section

variable {k m : ℕ}

/-- The involution on representatives. -/
theorem ogFlip_ogFlip_aux (k m : ℕ) (f : Stiefel k m) :
    ogFlip k m (ogFlip k m (Quotient.mk (grassmannSetoid k m) f)) =
      Quotient.mk (grassmannSetoid k m) f := by
  set g : Stiefel k m :=
    ⟨soActFun (flipMat k) f.1, orthonormal_soActFun (flipMat_transpose_mul k) f.2⟩ with hg
  have h1 : ogFlip k m (Quotient.mk (grassmannSetoid k m) f)
      = Quotient.mk (grassmannSetoid k m) g := ogFlip_mk f
  have h2 : ogFlip k m (Quotient.mk (grassmannSetoid k m) g)
      = Quotient.mk (grassmannSetoid k m)
          ⟨soActFun (flipMat k) g.1,
            orthonormal_soActFun (flipMat_transpose_mul k) g.2⟩ := ogFlip_mk g
  rw [h1, h2]
  congr 1
  apply Subtype.ext
  show soActFun (flipMat k) (soActFun (flipMat k) f.1) = f.1
  rw [soActFun_comp, flipMat_mul_self, soActFun_one]

/-- **The orientation flip of the oriented Grassmannian is an involution.** -/
theorem ogFlip_ogFlip (k m : ℕ) (P : OG k m) : ogFlip k m (ogFlip k m P) = P := by
  refine Quotient.inductionOn P ?_
  intro f
  exact ogFlip_ogFlip_aux k m f

/-- **`ogFlip` is an involution** (function form). -/
theorem ogFlip_involutive (k m : ℕ) : Function.Involutive (ogFlip k m) :=
  fun P => ogFlip_ogFlip k m P

theorem ogFlip_injective (k m : ℕ) : Function.Injective (ogFlip k m) :=
  (ogFlip_involutive k m).injective

theorem ogFlip_surjective (k m : ℕ) : Function.Surjective (ogFlip k m) :=
  (ogFlip_involutive k m).surjective

theorem ogFlip_bijective (k m : ℕ) : Function.Bijective (ogFlip k m) :=
  (ogFlip_involutive k m).bijective

/-- **The continuous flip is an involution.** -/
@[simp] theorem ogFlipCM_ogFlipCM (k m : ℕ) (P : OG k m) :
    ogFlipCM k m (ogFlipCM k m P) = P :=
  ogFlip_ogFlip k m P

end

end Work.ThomBordism.Grassmann
