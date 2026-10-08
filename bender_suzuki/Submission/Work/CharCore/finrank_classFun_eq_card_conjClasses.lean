import Mathlib
import Submission.Work.CharCore.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The dimension of the space of class functions

The class functions on a finite group `G` are exactly the functions that are constant on
conjugacy classes, so the space `classFunSubmodule G` of class functions is linearly
equivalent to the space `ConjClasses G → ℂ` of all complex valued functions on the set of
conjugacy classes.  Consequently its dimension is the number of conjugacy classes.

Main result: `Work.CharCore.finrank_classFun_eq_card_conjClasses`.
-/

noncomputable section

open Classical

namespace Work.CharCore

variable {G : Type*} [Group G] [Fintype G]

/-- A class function evaluated at a conjugacy class: descend the function to the quotient
`ConjClasses G`. -/
def classFunDescend (f : classFunSubmodule G) : ConjClasses G → ℂ :=
  Quotient.lift (f : G → ℂ) fun a b hab => by
    obtain ⟨c, hc⟩ := isConj_iff.mp hab
    rw [← hc]
    exact (f.2 a c).symm

/-- The value of the descended class function on the class of `g` is `f g`. -/
@[simp] theorem classFunDescend_mk (f : classFunSubmodule G) (g : G) :
    classFunDescend f (ConjClasses.mk g) = (f : G → ℂ) g := rfl

/-- Descending to conjugacy classes is `ℂ`-linear. -/
def classFunDescendLin : classFunSubmodule G →ₗ[ℂ] (ConjClasses G → ℂ) where
  toFun := classFunDescend
  map_add' f g := by
    funext x
    refine Quotient.inductionOn x ?_
    intro a
    rfl
  map_smul' c f := by
    funext x
    refine Quotient.inductionOn x ?_
    intro a
    rfl

/-- The class function obtained by pulling back a function on conjugacy classes. -/
def classFunLift (F : ConjClasses G → ℂ) : classFunSubmodule G where
  val := fun g => F (ConjClasses.mk g)
  property := fun g h => by
    have hc : IsConj (h * g * h⁻¹) g := (isConj_iff.mpr ⟨h, rfl⟩).symm
    exact congrArg F (ConjClasses.mk_eq_mk_iff_isConj.mpr hc)

/-- Pulling back a function on conjugacy classes is `ℂ`-linear. -/
def classFunLiftLin : (ConjClasses G → ℂ) →ₗ[ℂ] classFunSubmodule G where
  toFun := classFunLift
  map_add' F F' := by ext g; simp [classFunLift]
  map_smul' c F := by ext g; simp [classFunLift]

/-- **The space of class functions on `G` is the space of functions on the conjugacy classes
of `G`.** -/
def classFunEquiv : classFunSubmodule G ≃ₗ[ℂ] (ConjClasses G → ℂ) where
  toLinearMap := classFunDescendLin
  invFun := classFunLift
  left_inv f := by
    ext g
    rfl
  right_inv F := by
    funext x
    refine Quotient.inductionOn x ?_
    intro a
    rfl

theorem finrank_classFun_eq_card_conjClasses {G : Type*} [Group G] [Fintype G] :
    Module.finrank ℂ (classFunSubmodule G) = Nat.card (ConjClasses G) := by
  classical
  rw [LinearEquiv.finrank_eq (classFunEquiv (G := G)), Module.finrank_fintype_fun_eq_card,
    Nat.card_eq_fintype_card]

end Work.CharCore
