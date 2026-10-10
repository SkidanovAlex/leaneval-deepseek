import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.Normal.Defs
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.Reconstruct

/-- **The restriction of a Galois automorphism fixing an intermediate field is trivial.**  Let
`L ≤ M` be intermediate fields of `K'/K` with `L/K` normal, and let the algebra structure
`↥L → ↥M` be an arbitrary one.  If `ρ ∈ Gal(M/K)` acts trivially on `L` (i.e. fixes every element
of the image of `algebraMap ↥L ↥M`), then its restriction `ρ|_L ∈ Gal(L/K)` is the identity.

Indeed, `AlgEquiv.restrictNormal_commutes` computes the action of the restriction on the image of
`algebraMap ↥L ↥M`: for `x : ↥L`,
`algebraMap ↥L ↥M (ρ|_L x) = ρ (algebraMap ↥L ↥M x) = algebraMap ↥L ↥M x`.  Since `↥L` is a
field and `↥M` is nontrivial, `algebraMap ↥L ↥M` is injective (any ring homomorphism out of a
field into a nontrivial ring is), so `ρ|_L x = x` for all `x`, i.e. `ρ|_L = 1`.  No finiteness or
Galois-theoretic hypothesis beyond normality of `L/K` is needed. -/
theorem restrictNormalHom_eq_one_of_commutes {K K' : Type*} [Field K] [Field K'] [Algebra K K']
    (L M : IntermediateField K K') [Normal K L] [Algebra ↥L ↥M] [IsScalarTower K ↥L ↥M]
    {ρ : Gal(↥M/K)}
    (h : ∀ x : ↥L, ρ (algebraMap ↥L ↥M x) = algebraMap ↥L ↥M x) :
    AlgEquiv.restrictNormalHom (F := K) (K₁ := ↥M) L ρ = 1 := by
  apply AlgEquiv.ext
  intro x
  -- it suffices to test after applying the injective map `algebraMap ↥L ↥M`
  refine (algebraMap ↥L ↥M).injective ?_
  -- `restrictNormalHom` is `restrictNormal`, and `restrictNormal_commutes` identifies the two
  change (algebraMap ↥L ↥M) ((ρ.restrictNormal ↥L) x) =
    (algebraMap ↥L ↥M) ((1 : ↥L ≃ₐ[K] ↥L) x)
  rw [AlgEquiv.restrictNormal_commutes, AlgEquiv.one_apply, h x]

end NK.Reconstruct
