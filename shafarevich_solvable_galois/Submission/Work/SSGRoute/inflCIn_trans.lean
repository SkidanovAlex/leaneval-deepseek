import Mathlib
import Submission.Work.SSGRoute.PTDefsOmega
import Submission.Work.SSGRoute.inflTrivIn_trans
import Submission.Work.SSGRoute.phi1_classIncl_compat
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Transitivity of the level inflation maps `Work.SSGRoute.PTExt.inflCIn`

Inflation of `Ext`-cohomology of the idèle class groups along an inclusion of levels `L ≤ L'`
inside a fixed algebraic closure `Ω ⊇ K` is the map
`inflCIn h = extHMap (galRes k L L') (classIncl k L L')` (`PTDefsOmega`).  This file proves that
these maps are *transitive*, i.e. that inflating `y ∈ Hⁿ(Gal(L/k), C_L)` first to `L'` and then to
`L''` is inflating along the composite inclusion `L ≤ L''`:

`inflCIn h₂ (inflCIn h₁ y) = inflCIn (h₁.trans h₂) y`.

Equivalently, this is the `map_map` axiom for the level system of the colimit step of
`Work.SSGRoute.phi1_mono_step_in` in the *non-trivial* coefficient system `L ↦ Hⁿ(Gal(L/k), C_L)`
(the trivial-coefficient companion is `Work.SSGRoute.inflTrivIn_trans`).

## The two obstructions

* **The group homomorphisms.**  `galRes k L L'' : Gal(L''/k) →* Gal(L/k)` is only *propositionally*
  equal to the composite `(galRes k L L').comp (galRes k L' L'')`
  (`IsScalarTower.AlgEquiv.restrictNormalHom_comp`), so the two presentations of the coefficient
  module `res C_L` at the top level are distinct objects of `Rep` (related by `resResHom`).  This is
  handled by `extHMap_congr_hom`, which transports `extHMap` along an equality of group
  homomorphisms, using agreement of the coefficient maps on the common carrier.
* **The coefficient maps.**  `classIncl k L L'` and `classIncl k L' L''` compose to
  `classIncl k L L''` (`Work.SSGRoute.classIncl_compat_apply`), so the two-step composite
  `Rep.resMap (galRes k L' L'') (classIncl k L L') ≫ classIncl k L' L''` is the coefficient map of
  the composite presentation of `inflCIn (h₁.trans h₂)`.

The composite of the two steps is `Work.SSGRoute.extHMap_comp_aux`
(`Submission/Work/SSGRoute/inflTrivIn_trans.lean`).
-/

open CategoryTheory

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module

set_option linter.style.haveILetI false

namespace Work.SSGRoute

open SSGRoute.PTExt

/-- **`extHMap` only depends on the presentation of the group homomorphism.**  If `f` and `f'` are
group homomorphisms which are propositionally equal, and the coefficient maps `ι : res f A ⟶ B`
and `ι' : res f' A ⟶ B` agree on the common carrier of the two coefficient modules, then the
induced maps on `Ext`-cohomology coincide.

(For `f : H →* G`, `res f A` has the same underlying type as `A`, so "agreeing on the common
carrier" makes sense; the two coefficient modules differ only by the group action.) -/
theorem extHMap_congr_hom {H G : Type} [Group H] [Group G]
    {A : Rep.{0} SSGRoute.PTExt.Coeff G} {B : Rep.{0} SSGRoute.PTExt.Coeff H}
    {f f' : H →* G} (hff : f = f') (ι : Rep.res f A ⟶ B) (ι' : Rep.res f' A ⟶ B)
    (hι : ∀ z : ↥(Rep.res f A), (Rep.Hom.hom ι) z = (Rep.Hom.hom ι') z) {n : ℕ}
    (y : SSGRoute.PTExt.extH A n) :
    SSGRoute.PTExt.extHMap f ι y = SSGRoute.PTExt.extHMap f' ι' y := by
  subst hff
  have h : ι = ι' := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro z
    exact hι z
  rw [h]

set_option maxHeartbeats 1000000 in
/-- **Transitivity of the level inflation maps `inflCIn`**: inflating `y ∈ Hⁿ(Gal(L/k), C_L)`
first to the level `L'` and then to `L''` is inflating along the composite inclusion `L ≤ L''`. -/
theorem inflCIn_trans {k K Ω : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [Field Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    {L L' L'' : IntermediateField K Ω} [NumberField L] [NumberField L'] [NumberField L'']
    [FiniteDimensional k L] [FiniteDimensional k L'] [FiniteDimensional k L'']
    [IsGalois k L] [IsGalois k L'] [IsGalois k L''] (h₁ : L ≤ L') (h₂ : L' ≤ L'')
    {n : ℕ} (y : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) n) :
    SSGRoute.PTExt.inflCIn (k := k) h₂ (SSGRoute.PTExt.inflCIn (k := k) h₁ y)
      = SSGRoute.PTExt.inflCIn (k := k) (h₁.trans h₂) y := by
  -- the three algebra structures on `↥L`, `↥L'`, `↥L''` induced by the inclusions, and the
  -- corresponding scalar towers
  letI : Algebra ↥L ↥L' := (IntermediateField.inclusion h₁).toAlgebra
  letI : Algebra ↥L ↥L'' := (IntermediateField.inclusion (h₁.trans h₂)).toAlgebra
  letI : Algebra ↥L' ↥L'' := (IntermediateField.inclusion h₂).toAlgebra
  haveI : IsScalarTower k ↥L ↥L' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower k ↥L ↥L'' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower k ↥L' ↥L'' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower ↥L ↥L' ↥L'' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  -- the middle extension `↥L''/↥L'` is again finite and Galois (needed by
  -- `classIncl_compat_apply`)
  haveI hfdmid : FiniteDimensional ↥L' ↥L'' := FiniteDimensional.right k ↥L' ↥L''
  haveI hgalmid : IsGalois ↥L' ↥L'' := IsGalois.tower_top_of_isGalois k ↥L' ↥L''
  -- restriction of the Galois group is compatible with the tower
  have hgal : (SSGRoute.PTExt.galRes k ↥L ↥L'' : (↥L'' ≃ₐ[k] ↥L'') →* (↥L ≃ₐ[k] ↥L))
      = (SSGRoute.PTExt.galRes k ↥L ↥L').comp (SSGRoute.PTExt.galRes k ↥L' ↥L'') :=
    IsScalarTower.AlgEquiv.restrictNormalHom_comp k ↥L ↥L' ↥L''
  -- the two coefficient maps at the composite level agree on the common carrier
  have hι : ∀ z : ↥(SSGRoute.PTExt.classesK k ↥L),
      (Rep.Hom.hom (Rep.resMap (SSGRoute.PTExt.galRes k ↥L' ↥L'')
          (SSGRoute.PTExt.classIncl k ↥L ↥L') ≫ SSGRoute.PTExt.classIncl k ↥L' ↥L'')) z
        = (Rep.Hom.hom (SSGRoute.PTExt.classIncl k ↥L ↥L'')) z := by
    intro z
    exact classIncl_compat_apply (k := k) (K := ↥L) (L := ↥L') (L₂ := ↥L'') z
  unfold SSGRoute.PTExt.inflCIn SSGRoute.PTExt.inflC
  exact (extHMap_comp_aux (SSGRoute.PTExt.galRes k ↥L ↥L') (SSGRoute.PTExt.galRes k ↥L' ↥L'')
      (SSGRoute.PTExt.classIncl k ↥L ↥L') (SSGRoute.PTExt.classIncl k ↥L' ↥L'')
      (Rep.resMap (SSGRoute.PTExt.galRes k ↥L' ↥L'') (SSGRoute.PTExt.classIncl k ↥L ↥L')
        ≫ SSGRoute.PTExt.classIncl k ↥L' ↥L'') rfl y).trans
    (extHMap_congr_hom hgal.symm
      (Rep.resMap (SSGRoute.PTExt.galRes k ↥L' ↥L'') (SSGRoute.PTExt.classIncl k ↥L ↥L')
        ≫ SSGRoute.PTExt.classIncl k ↥L' ↥L'')
      (SSGRoute.PTExt.classIncl k ↥L ↥L'') hι y)

end Work.SSGRoute
