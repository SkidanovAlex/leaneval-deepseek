import Mathlib.Tactic.Have
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Submission.Work.SSGRoute.PTDefsOmega
import Submission.Work.SSGRoute.extHMap_id
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The level inflation `inflHIn` is the identity at `le_refl`

`SSGRoute.PTExt.inflHIn h` is the inflation of `Hⁿ(Gal(L/k), M) → Hⁿ(Gal(L'/k), M)`
(`L ≤ L'`) defined in `PTDefsOmega` as `inflHLevel`, i.e. as the change-of-group map
`extHMap (AlgEquiv.restrictNormalHom L) (resResHom M)`.  We prove that at `h = le_refl L`
it is the identity.  This is the `map_self` axiom for the directed system of levels used in the
colimit step of `Work.SSGRoute.phi1_mono_step_in`.

The mathematical content is that both pieces of data degenerate:

* `AlgEquiv.restrictNormalHom (K₁ := ↥L) (E := ↥L)` is the identity of `Gal(L/k)`
  (`AlgEquiv.restrictNormalHom_id`), and
* the canonical comparison `resResHom M : Rep.res (restrictNormalHom ↥L) (Rep.res (restrictNormalHom K) M)
  ⟶ Rep.res (restrictNormalHom K) M` is `eqToHom` of the self-equality `Rep.res (id) A = A` of
  representations.

Abstract form of the second point (`extHMap_eqToHom_id`): if `f = MonoidHom.id G` and
`hres : Rep.res f A = A`, then `extHMap f (eqToHom hres)` is the identity on `Hⁿ(G, A)`.  After
`subst`ing `f`, the morphism `eqToHom hres` is `𝟙 A` by `eqToHom_refl` (which holds for *any* proof
of `X = X`), and `extHMap` at the identity group homomorphism with the identity coefficient
morphism is the identity (`Work.SSGRoute.extHMap_id`).
-/

set_option maxHeartbeats 400000

namespace Work.SSGRoute

open CategoryTheory

/-- **Abstract form of `inflHIn_refl`.**  If `f : G →* G` is the identity and `hres` exhibits
`Rep.res f A` as `A`, then the change-of-group map `extHMap f (eqToHom hres)` is the identity on
`Hⁿ(G, A)`. -/
theorem extHMap_eqToHom_id {G : Type} [Group G] {A : Rep.{0} SSGRoute.PTExt.Coeff G} {n : ℕ}
    (f : G →* G) (hf : f = MonoidHom.id G) (hres : Rep.res f A = A)
    (y : SSGRoute.PTExt.extH A n) :
    SSGRoute.PTExt.extHMap f (CategoryTheory.eqToHom hres) y = y := by
  subst hf
  have hid : CategoryTheory.eqToHom hres = 𝟙 A := CategoryTheory.eqToHom_refl A hres
  rw [hid]
  exact Work.SSGRoute.extHMap_id y

theorem inflHIn_refl {k K Ω : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K] [Field Ω] [Algebra K Ω] [Algebra k Ω]
    [IsScalarTower k K Ω]
    {L : IntermediateField K Ω} [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    {M : Rep SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)} {n : ℕ}
    (y : SSGRoute.PTExt.extH (Rep.res (SSGRoute.PTExt.galRes k K L) M) n) :
    SSGRoute.PTExt.inflHIn (k := k) (K := K) (le_refl L) y = y := by
  unfold SSGRoute.PTExt.inflHIn SSGRoute.PTExt.inflHLevel
  have hf : AlgEquiv.restrictNormalHom (K₁ := ↥L) (E := ↥L) = MonoidHom.id (↥L ≃ₐ[k] ↥L) :=
    AlgEquiv.restrictNormalHom_id k ↥L
  have hres : Rep.res (AlgEquiv.restrictNormalHom (K₁ := ↥L) (E := ↥L))
      (Rep.res (SSGRoute.PTExt.galRes k K ↥L) M) = Rep.res (SSGRoute.PTExt.galRes k K ↥L) M := by
    rw [hf]
    exact Rep.res_id _
  have hι : SSGRoute.PTExt.resResHom (L := ↥L) (L' := ↥L) M
      = CategoryTheory.eqToHom hres := by
    unfold SSGRoute.PTExt.resResHom
    exact congrArg CategoryTheory.eqToHom (Subsingleton.elim _ _)
  have hgoal : SSGRoute.PTExt.extHMap (AlgEquiv.restrictNormalHom (K₁ := ↥L) (E := ↥L))
      (SSGRoute.PTExt.resResHom (L := ↥L) (L' := ↥L) M) y = y := by
    rw [hι]
    exact extHMap_eqToHom_id (f := AlgEquiv.restrictNormalHom (K₁ := ↥L) (E := ↥L)) hf hres y
  exact hgoal

end Work.SSGRoute
