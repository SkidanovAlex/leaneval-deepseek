import Mathlib
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `H⁰`-slot coefficient map `1 ↦ a` for an arbitrary `Coeff`-representation

`SSGRoute.Phi1.powHomCls` (`phi1_defs.lean`) is the map `ℤ → C_L`, `1 ↦ a`, attached to a
`Gal(L/k)`-fixed element of the idèle class group.  The cyclic norm criterion (`E7b`'s CFT input at
a local level, and its global analogue `E3`) needs the same construction for an *arbitrary*
`Coeff`-linear `G`-representation `A`; that is `powHomRep` below.
-/

namespace Work.SSGRoute

open CategoryTheory
open SSGRoute.PTExt

-- The canonical `ULift` instances compete with the module structure stored in a representation
-- (`Rep.hV2`); demote them, as in `module_free_ulift_int.lean` and `E2_STATUS.md`.
attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module
attribute [local instance 1] ULift.module ULift.smulLeft ULift.mulAction ULift.smulZeroClass
attribute [local instance 1] ULift.distribSMul ULift.distribMulAction ULift.smulWithZero
attribute [local instance 1] ULift.mulActionWithZero

noncomputable section

/-- **The `H⁰`-slot of the cup product for an arbitrary representation**: for a `G`-fixed element
`a` of `A : Rep Coeff G`, the `G`-linear map `ℤ → A`, `n ↦ n • a`. -/
def powHomRep {G : Type} [Group G] {A : Rep SSGRoute.PTExt.Coeff G} (a : A)
    (hafix : ∀ σ : G, A.ρ σ a = a) : SSGRoute.PTExt.unitRep G ⟶ A :=
  Rep.ofHom
    { toLinearMap :=
        { toFun := fun n => n • a
          map_add' := fun m n => by
            show (m + n) • a = m • a + n • a
            exact add_smul m n a
          map_smul' := fun c n => by
            show (c • n) • a = (RingHom.id SSGRoute.PTExt.Coeff) c • (n • a)
            rw [smul_eq_mul, RingHom.id_apply]
            exact (smul_smul c n a).symm }
      isIntertwining' := fun σ => by
        rw [Rep.trivial_ρ]
        apply LinearMap.ext
        intro n
        show (n • a : A) = A.ρ σ (n • a)
        rw [map_smul, hafix σ] }

@[simp] lemma powHomRep_apply {G : Type} [Group G] {A : Rep SSGRoute.PTExt.Coeff G} (a : A)
    (hafix : ∀ σ : G, A.ρ σ a = a) (n : SSGRoute.PTExt.Coeff) :
    (Rep.Hom.hom (powHomRep a hafix)) n = n • a := rfl

end

end Work.SSGRoute
