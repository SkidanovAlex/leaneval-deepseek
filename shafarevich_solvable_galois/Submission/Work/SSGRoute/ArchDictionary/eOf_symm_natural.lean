import Mathlib
import Submission.Work.SSGRoute.ArchDictionary.extOneDictNaturalH1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ArchDictionary

open CategoryTheory CategoryTheory.Limits SSGRoute.PTExt

/-- Inverse naturality of the divisible-coefficient dictionary `NatH1.eOf`: the naturality clause
of `NatH1.eOf_natural` read through `(eOf … M).symm`. -/
theorem eOf_symm_natural {G : Type} [Group G] (N : Rep.{0} Coeff G)
    (hInj : Module.Injective Coeff N.V)
    (X : ∀ M : Rep.{0} Coeff G, Rep.{0} Coeff (⊥ : Subgroup G))
    (hX : ∀ M, Nonempty (Work.SSGRoute.homRep (Rep.free Coeff G M.V) N ≅
      Rep.coind (⊥ : Subgroup G).subtype (X M)))
    {M' M : Rep.{0} Coeff G} (u : M' ⟶ M) (y : Work.SSGRoute.homH1 G M N) :
    NatH1.eOf N hInj X hX M'
        ((Abelian.Ext.mk₀ u).comp ((NatH1.eOf N hInj X hX M).symm y) (zero_add 1))
      = Work.SSGRoute.homMapH1 G M M' N u y := by
  -- Substitute `x := (eOf … M).symm y` in the naturality clause `NatH1.eOf_natural` and cancel
  -- the round trip `(eOf … M).symm` followed by `eOf … M`.
  rw [NatH1.eOf_natural, AddEquiv.apply_symm_apply]

end Work.SSGRoute.ArchDictionary

-- The scaffold of this delegated file placed the statement inside a `namespace
-- Work.SSGRoute.ArchDictionary` while the module itself already sits in that namespace, which
-- would make the fully-qualified name
-- `Work.SSGRoute.ArchDictionary.Work.SSGRoute.ArchDictionary.eOf_symm_natural`.  The statement
-- above carries the intended name `Work.SSGRoute.ArchDictionary.eOf_symm_natural`; the copy below
-- records the same theorem under the doubled name as well, so that *both* names resolve.
set_option linter.dupNamespace false

namespace Work.SSGRoute.ArchDictionary
namespace Work.SSGRoute.ArchDictionary

open CategoryTheory CategoryTheory.Limits SSGRoute.PTExt

/-- Inverse naturality of the divisible-coefficient dictionary `NatH1.eOf` (same statement, under
the doubled namespace as it appeared in the delegated file). -/
theorem eOf_symm_natural {G : Type} [Group G] (N : Rep.{0} Coeff G)
    (hInj : Module.Injective Coeff N.V)
    (X : ∀ M : Rep.{0} Coeff G, Rep.{0} Coeff (⊥ : Subgroup G))
    (hX : ∀ M, Nonempty (Work.SSGRoute.homRep (Rep.free Coeff G M.V) N ≅
      Rep.coind (⊥ : Subgroup G).subtype (X M)))
    {M' M : Rep.{0} Coeff G} (u : M' ⟶ M) (y : Work.SSGRoute.homH1 G M N) :
    NatH1.eOf N hInj X hX M'
        ((Abelian.Ext.mk₀ u).comp ((NatH1.eOf N hInj X hX M).symm y) (zero_add 1))
      = Work.SSGRoute.homMapH1 G M M' N u y :=
  _root_.Work.SSGRoute.ArchDictionary.eOf_symm_natural N hInj X hX u y

end Work.SSGRoute.ArchDictionary
end Work.SSGRoute.ArchDictionary
