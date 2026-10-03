/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `Tor` over a noncommutative ring

For a ring `R`, a right `R`-module `M` and a left `R`-module `N`, we define
`Tor R n M N = Tor_n^R(M, N)` as the `n`-th left derived functor of the right exact functor
`N ↦ M ⊠[R] N`.  Everything is carried out in the category of `ℤ`-modules, since the balanced
tensor product of a right module and a left module over a noncommutative ring is only an abelian
group.

## Main definitions

* `Work.ORHomAlg.tensorLeftFunctor R M : ModuleCat R ⥤ ModuleCat ℤ`;
* `Work.ORHomAlg.Tor R n M N`.
-/
module

public import Submission.Work.ORHomAlg.Map
public import Mathlib.CategoryTheory.Abelian.LeftDerived
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution

@[expose] public section

namespace Work.ORHomAlg

open CategoryTheory

universe u

variable {R : Type u} [Ring R]

instance instSmallSelfRing : Small.{u} R := ⟨⟨R, ⟨Equiv.refl R⟩⟩⟩

/-- The functor `M ⊠[R] -` from left `R`-modules to abelian groups. -/
noncomputable def tensorLeftFunctor (M : Type u) [AddCommGroup M] [Module Rᵐᵒᵖ M] :
    ModuleCat.{u} R ⥤ ModuleCat.{u} ℤ where
  obj N := ModuleCat.of ℤ (BalancedTensor R M N)
  map g := ModuleCat.ofHom (BalancedTensor.lTensor (M := M) g.hom).toIntLinearMap
  map_id X := by
    apply ModuleCat.hom_ext
    show (BalancedTensor.lTensor (M := M) (LinearMap.id : ↑X →ₗ[R] ↑X)).toIntLinearMap = _
    rw [BalancedTensor.lTensor_id]
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    show (BalancedTensor.lTensor (M := M) ((f ≫ g).hom)).toIntLinearMap = _
    rw [show (f ≫ g).hom = g.hom.comp f.hom from rfl]
    rw [BalancedTensor.lTensor_comp]
    rfl

instance tensorLeftFunctor_additive (M : Type u) [AddCommGroup M] [Module Rᵐᵒᵖ M] :
    (tensorLeftFunctor (R := R) M).Additive where
  map_add {X Y f g} := by
    apply ModuleCat.hom_ext
    show (BalancedTensor.lTensor (M := M) ((f + g).hom)).toIntLinearMap = _
    rw [show (f + g).hom = f.hom + g.hom from rfl, BalancedTensor.lTensor_add]
    rfl

/-- `Tor_n^R(M, N)`, the `n`-th left derived functor of `N ↦ M ⊠[R] N`. -/
noncomputable def Tor (n : ℕ) (M : Type u) [AddCommGroup M] [Module Rᵐᵒᵖ M]
    (N : Type u) [AddCommGroup N] [Module R N] : Type u :=
  ((tensorLeftFunctor (R := R) M).leftDerived n).obj (ModuleCat.of R N)

namespace Tor

variable {n : ℕ}
variable {M : Type u} [AddCommGroup M] [Module Rᵐᵒᵖ M]
variable {N : Type u} [AddCommGroup N] [Module R N]

noncomputable instance instAddCommGroup : AddCommGroup (Tor (R := R) n M N) :=
  inferInstanceAs (AddCommGroup
    (((tensorLeftFunctor (R := R) M).leftDerived n).obj (ModuleCat.of R N)))

noncomputable instance instModule : Module ℤ (Tor (R := R) n M N) :=
  inferInstanceAs (Module ℤ
    (((tensorLeftFunctor (R := R) M).leftDerived n).obj (ModuleCat.of R N)))

/-- `Tor_n^R(M, N)` vanishes in positive degrees when `N` is projective. -/
noncomputable instance subsingleton_succ [Module.Projective R N] (n : ℕ) :
    Subsingleton (Tor (R := R) (n + 1) M N) :=
  ModuleCat.subsingleton_of_isZero
    (Functor.isZero_leftDerived_obj_projective_succ (tensorLeftFunctor (R := R) M) n
      (ModuleCat.of R N))

end Tor

end Work.ORHomAlg
