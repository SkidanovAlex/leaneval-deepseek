import Mathlib
import Submission.Work.Serre.serreE0OfRange
import Submission.Work.Serre.hZeroOfPiZero

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The augmentation `H₀(X;ℚ) → H₀(*;ℚ)` vanishes when `π₀(X)` is a point

`Work.Serre.serreE0OfRange` reduces rational acyclicity (`SerreE0`) to two inputs, and the degree-`0`
input is exactly the statement proved here: if `π₀(X, x₀)` is a subsingleton then the augmentation
`Work.Serre.ratHomologyMap (Work.Serre.toPoint X) 0 : H₀(X;ℚ) → H₀(*;ℚ)` is an isomorphism.

Mathematically this is `H₀(X;ℚ) = ℚ[π₀ X]`: a space with one path component has `H₀(X;ℚ) ≅ ℚ`, and
`H₀(*;ℚ) ≅ ℚ`, and the augmentation is that identification.

Formally the work is all in `Submission/Work/Serre/hZeroOfPiZero.lean`, where Mathlib's
`TopCat.singularHomology₀Iso` (identifying `H₀` with the coproduct of copies of `ℚ` indexed by
`ZerothHomotopy`) is made functorial in the space, giving

`hZeroOfPiZero : IsIso (ratHomologyMap f 0)` for any `f : C(X,Y)` inducing a bijection on `π₀` at
every base point (and `X` nonempty).

What is left here is the passage from "`π₀(X,x₀)` is a point" to "`π₀(X,x)` is a point for every
base point `x`, and `π₀(*, f x)` is a point", i.e. the translation between the `ZerothHomotopy`
quotient and Mathlib's cube-based `HomotopyGroup (Fin 0) - x` via
`HomotopyGroup.pi0EquivZerothHomotopy`.  Then any map whose source and target are subsingletons is
bijective.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace Work.Serre

noncomputable section

/-- If `π₀(X, x₀)` is a subsingleton then so is `ZerothHomotopy X` (the set of path components). -/
private theorem zerothHomotopy_subsingleton_of_pi0 (X : Type) [TopologicalSpace X] (x₀ : X)
    (h : Subsingleton (HomotopyGroup (Fin 0) X x₀)) : Subsingleton (ZerothHomotopy X) :=
  ⟨fun _ _ => (HomotopyGroup.pi0EquivZerothHomotopy (x := x₀)).symm.injective (h.elim _ _)⟩

/-- If `ZerothHomotopy X` is a subsingleton then `π₀(X, x)` is a subsingleton at every base point. -/
private theorem pi0_subsingleton_of_zerothHomotopy {X : Type} [TopologicalSpace X]
    (h : Subsingleton (ZerothHomotopy X)) (x : X) :
    Subsingleton (HomotopyGroup (Fin 0) X x) :=
  ⟨fun _ _ => (HomotopyGroup.pi0EquivZerothHomotopy (x := x)).injective (h.elim _ _)⟩

/-- `π₀` of a one-point space is a point. -/
private theorem pi0_subsingleton_punit (y : PUnit) :
    Subsingleton (HomotopyGroup (Fin 0) PUnit y) := by
  have h : Subsingleton (ZerothHomotopy PUnit) :=
    inferInstanceAs (Subsingleton (Quotient (pathSetoid PUnit)))
  exact ⟨fun _ _ => (HomotopyGroup.pi0EquivZerothHomotopy (x := y)).injective (h.elim _ _)⟩

/-- **The degree-`0` augmentation is an isomorphism when `π₀(X)` is a point.**

`H₀(-;ℚ)` is the free `ℚ`-module on `π₀`, so this is the statement `H₀(X;ℚ) ≅ ℚ` for a
path-connected `X`.  It is the degree-`0` input of `Work.Serre.serreE0_of_range`. -/
theorem serreAugmentationZero (X : Type) [TopologicalSpace X] (x₀ : X)
    (h : Subsingleton (HomotopyGroup (Fin 0) X x₀)) :
    CategoryTheory.IsIso (Work.Serre.ratHomologyMap (Work.Serre.toPoint X) 0) := by
  haveI : Nonempty X := ⟨x₀⟩
  haveI hZ : Subsingleton (ZerothHomotopy X) := zerothHomotopy_subsingleton_of_pi0 X x₀ h
  refine hZeroOfPiZero (toPoint X) (fun x => ?_)
  haveI hx : Subsingleton (HomotopyGroup (Fin 0) X x) :=
    pi0_subsingleton_of_zerothHomotopy hZ x
  haveI hy : Subsingleton (HomotopyGroup (Fin 0) PUnit (toPoint X x)) :=
    pi0_subsingleton_punit _
  exact ⟨fun a b _ => Subsingleton.elim a b,
    fun y => ⟨(HomotopyGroup.pi0EquivZerothHomotopy (x := x)).symm (ZerothHomotopy.mk x),
      Subsingleton.elim _ _⟩⟩

end

end Work.Serre
