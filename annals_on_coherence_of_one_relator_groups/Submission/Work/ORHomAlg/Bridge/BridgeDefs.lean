/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Bridging `Work.ORCoherence.Tor` and `Work.ORHomAlg.Tor`

The `ORCoherence` chapter defines `Tor_n^R(S, M)` as a left derived functor landing in
`S`-modules, while the `ORHomAlg` chapter defines `Tor_n^R(M, N)` as a left derived functor
landing in `ℤ`-modules (abelian groups).  This file contains the definitions used to compare
the two: the forgetful functor `ModuleCat S ⥤ ModuleCat ℤ` which keeps the underlying
additive group together with its canonical `ℤ`-module structure.

Using this functor rather than `ModuleCat.restrictScalars (Int.castRingHom S)` keeps the
`ℤ`-module structure *definitionally* the canonical one (`AddCommGroup.intModule`), which is
what appears in the statement of the comparison theorem.
-/
import Mathlib
import Submission.Work.ORHomAlg.Tor
import Submission.Work.ORCoherence.Defs
import Submission.Work.ORCoherence.Tor

set_option autoImplicit false

namespace Work.ORHomAlg.Bridge

universe u

open CategoryTheory

/-- The forgetful functor from left `S`-modules to abelian groups (i.e. `ℤ`-modules): it keeps
the underlying additive group together with its canonical `ℤ`-module structure. -/
noncomputable def forgetInt (S : Type u) [Ring S] : ModuleCat.{u} S ⥤ ModuleCat.{u} ℤ where
  obj M := ModuleCat.of ℤ M
  map φ := ModuleCat.ofHom φ.hom.toAddMonoidHom.toIntLinearMap
  map_id M := by
    apply ModuleCat.hom_ext
    exact LinearMap.ext fun x => rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    exact LinearMap.ext fun x => rfl

@[simp]
theorem forgetInt_obj (S : Type u) [Ring S] (M : ModuleCat.{u} S) :
    (forgetInt S).obj M = ModuleCat.of ℤ (M : Type u) := rfl

@[simp]
theorem forgetInt_map_hom (S : Type u) [Ring S] {M N : ModuleCat.{u} S} (φ : M ⟶ N) :
    ((forgetInt S).map φ).hom = φ.hom.toAddMonoidHom.toIntLinearMap := rfl

instance forgetInt_additive (S : Type u) [Ring S] : (forgetInt S).Additive where
  map_add {X Y f g} := by
    apply ModuleCat.hom_ext
    show (f + g).hom.toAddMonoidHom.toIntLinearMap =
      f.hom.toAddMonoidHom.toIntLinearMap + g.hom.toAddMonoidHom.toIntLinearMap
    ext x
    simp

end Work.ORHomAlg.Bridge
