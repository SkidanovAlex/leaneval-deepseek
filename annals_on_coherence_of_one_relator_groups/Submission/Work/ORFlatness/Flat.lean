/-
# Flatness and `Tor₁`-vanishing for modules over a noncommutative ring

`Mathlib`'s `Module.Flat` is only available over commutative rings.  For the
formalisation of Jaikin-Zapirain--Linton we need flatness of a left module over an
arbitrary ring `R` (there: the group algebra `K[G]`), and the low-dimensional fact that
flatness is equivalent to the vanishing of `Tor₁` against all right modules.  Everything
is phrased in terms of the balanced tensor product `Work.ORFlatness.BalTensor` from
`Submission.Work.ORFlatness.Tensor`.

`Tor₁^{R}(X, N) = 0` is expressed, for a right `R`-module `X` and a left `R`-module `N`,
by the standard dimension criterion: some (equivalently: every) projective presentation
`0 → K → P → X → 0` of `X` has `K ⊗[R] N → P ⊗[R] N` injective.  We call this
`Tor1Vanishes R X N`.
-/
import Submission.Work.ORFlatness.Tensor

set_option autoImplicit false
set_option maxHeartbeats 1000000

open TensorProduct MulOpposite

universe u

namespace Work.ORFlatness

variable (R : Type u) [Ring R]

/-- A left `R`-module `M` is **left flat** if tensoring on the right by `M` (balanced
tensor product over `R`) preserves injective maps of right `R`-modules. -/
def LeftFlat (M : Type u) [AddCommGroup M] [Module R M] : Prop :=
  ∀ {X Y : Type u} [AddCommGroup X] [Module Rᵐᵒᵖ X] [AddCommGroup Y] [Module Rᵐᵒᵖ Y]
    (f : X →ₗ[Rᵐᵒᵖ] Y), Function.Injective f →
    Function.Injective (BalTensor.map R f (LinearMap.id : M →ₗ[R] M))

/-- A right `R`-module `X` is **right flat** if tensoring on the left by `X` preserves
injective maps of left `R`-modules. -/
def RightFlat (X : Type u) [AddCommGroup X] [Module Rᵐᵒᵖ X] : Prop :=
  ∀ {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (g : M →ₗ[R] N), Function.Injective g →
    Function.Injective (BalTensor.map R (LinearMap.id : X →ₗ[Rᵐᵒᵖ] X) g)

/-- A projective presentation of a right `R`-module: a surjection onto `X` from a
projective right `R`-module. -/
structure ProjPres (X : Type u) [AddCommGroup X] [Module Rᵐᵒᵖ X] where
  /-- the covering projective module -/
  P : Type u
  [addCommGroup : AddCommGroup P]
  [module : Module Rᵐᵒᵖ P]
  [projective : Module.Projective Rᵐᵒᵖ P]
  /-- the covering map -/
  π : P →ₗ[Rᵐᵒᵖ] X
  /-- the covering map is surjective -/
  surj : Function.Surjective π

attribute [instance] ProjPres.addCommGroup ProjPres.module ProjPres.projective

/-- The kernel of a projective presentation, as a right `R`-module. -/
abbrev ProjPres.K {X : Type u} [AddCommGroup X] [Module Rᵐᵒᵖ X] (P : ProjPres R X) :
    Submodule Rᵐᵒᵖ P.P := LinearMap.ker P.π

/-- `Tor1Vanishes R X N` is the statement `Tor₁^{R}(X, N) = 0`, for a right `R`-module
`X` and a left `R`-module `N`: there is a projective presentation `0 → K → P → X → 0`
of `X` for which `K ⊗[R] N → P ⊗[R] N` is injective. -/
def Tor1Vanishes (X : Type u) [AddCommGroup X] [Module Rᵐᵒᵖ X]
    (N : Type u) [AddCommGroup N] [Module R N] : Prop :=
  ∃ P : ProjPres R X, Function.Injective
    (BalTensor.map R (Submodule.subtype P.K) (LinearMap.id : N →ₗ[R] N))

end Work.ORFlatness
