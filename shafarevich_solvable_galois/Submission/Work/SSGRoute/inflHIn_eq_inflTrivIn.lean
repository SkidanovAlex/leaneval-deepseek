import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Submission.Work.SSGRoute.PTDefsOmega

/-!
# `inflHIn` agrees with `inflTrivIn` on the trivial module

For finite Galois levels `k ⊆ K ⊆ L ⊆ L' ≤ Ω`, inflating a class
`y ∈ H^n(Gal(L/k), res_{Gal(L/k)} M)` along the level inclusion `L ≤ L'` never uses any feature
of a *general* coefficient module `M` beyond the underlying abelian group: it is the change of
group `extHMap (galRes k L L')` followed by the canonical transport `resResHom M`, a morphism
that acts as the **identity** on the underlying module.

Consequently, for the trivial module `M = Coeff[p]` (`Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p)`)
the level inflation `inflHIn` coincides with the trivial-coefficient inflation `inflTrivIn`,
whose coefficient map is `trivResInv (galRes k L L') (ZMod p)` — again the identity on the
underlying module.

The content is therefore purely formal: after unfolding both definitions the two sides are
`extHMap f ι y` with the *same* `f = galRes k L L'` and the same `y`, and it remains to compare
the two coefficient morphisms, which both act as the identity
(`Work.SSGRoute.resResHom_triv`, proved from `Work.SSGRoute.Rep.eqToHom_hom_apply`).
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open CategoryTheory

namespace Work.SSGRoute

open SSGRoute.PTExt

/-- **`eqToHom` in `Rep k G` acts by transport along the underlying-type equality.** -/
theorem Rep.eqToHom_hom_apply_triv {k G : Type*} [Semiring k] [Monoid G] {A B : Rep k G}
    (h : A = B) (y : A.V) :
    (Rep.Hom.hom (CategoryTheory.eqToHom h)) y = (h ▸ y : B.V) := by
  cases h
  rfl

section ResResHomTriv

variable {k K Ω : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K] [Field Ω] [Algebra K Ω] [Algebra k Ω]
  [IsScalarTower k K Ω] {L L' : IntermediateField K Ω} [NumberField L] [NumberField L']
  [FiniteDimensional k L] [FiniteDimensional k L'] [IsGalois k L] [IsGalois k L']
  [Algebra ↥L ↥L'] [IsScalarTower k ↥L ↥L'] [IsScalarTower K ↥L ↥L']

/-- **The canonical transport `resResHom` acts as the identity on elements.**  The two
representations have the same underlying type, so the transport underlying `eqToHom` is a
transport along a self-equality of a type (compare `Work.SSGRoute.resResHom_hom_apply`). -/
theorem resResHom_hom_apply_triv (M : Rep Coeff (K ≃ₐ[k] K))
    (y : ↥(Rep.res (galRes k ↥L ↥L') (Rep.res (galRes k K ↥L) M))) :
    (Rep.Hom.hom (resResHom (k := k) (K := K) (L := ↥L) (L' := ↥L') M)) y = y := by
  rw [resResHom, Rep.eqToHom_hom_apply_triv]
  exact eq_of_heq (rec_heq_of_heq _ (HEq.refl y))

/-- **On the trivial module the canonical transport is the identity morphism**: for
`M = Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p)` the two presentations of the `Gal(L'/k)`-module
`ZMod p` (via `res_{Gal(L'/k)} (res_{Gal(L/k)} M)` and via `res_{Gal(L'/k)} M`) coincide, and both
`resResHom M` and `trivResInv (galRes k L L') (ZMod p)` act as the identity. -/
theorem resResHom_triv (p : ℕ) :
    resResHom (k := k) (K := K) (L := ↥L) (L' := ↥L') (Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p))
      = trivResInv (galRes k ↥L ↥L') (ZMod p) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  rw [show (Rep.Hom.hom (resResHom (k := k) (K := K) (L := ↥L) (L' := ↥L')
        (Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p)))).toLinearMap = LinearMap.id from by
      apply LinearMap.ext
      intro v
      exact resResHom_hom_apply_triv _ v]
  rfl

end ResResHomTriv

/-- **Level inflation of a trivial module.**  For `y ∈ H^n(Gal(L/k), res M)` with the trivial
coefficient module `M = ZMod p`, inflating `y` to the level `L' ≥ L` (as `inflHIn` does) is the
same as inflating the `Gal(L/k)`-module `ZMod p` to `Gal(L'/k)` (as `inflTrivIn` does). -/
theorem inflHIn_eq_inflTrivIn {k K Ω : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K] [Field Ω] [Algebra K Ω] [Algebra k Ω]
    [IsScalarTower k K Ω] (p : ℕ)
    {L L' : IntermediateField K Ω} [NumberField L] [NumberField L'] [FiniteDimensional k L]
    [FiniteDimensional k L'] [IsGalois k L] [IsGalois k L'] (h : L ≤ L') {n : ℕ}
    (y : SSGRoute.PTExt.extH (Rep.res (SSGRoute.PTExt.galRes k K L)
      (Rep.trivial SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) (ZMod p))) n) :
    SSGRoute.PTExt.inflHIn (k := k) (K := K) h y
      = SSGRoute.PTExt.inflTrivIn (k := k) h (ZMod p) y := by
  -- the level inclusion, as an algebra structure together with the two scalar towers
  letI : Algebra ↥L ↥L' := (IntermediateField.inclusion h).toAlgebra
  haveI : IsScalarTower k ↥L ↥L' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower K ↥L ↥L' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  -- unfold both inflation maps: they are `extHMap (galRes k L L')` with coefficient maps
  -- `resResHom` (for `inflHIn`) and `trivResInv` (for `inflTrivIn`)
  simp only [SSGRoute.PTExt.inflHIn, SSGRoute.PTExt.inflTrivIn, SSGRoute.PTExt.inflHLevel,
    SSGRoute.PTExt.inflTriv]
  -- on the trivial module the two coefficient morphisms agree
  rw [show SSGRoute.PTExt.resResHom (k := k) (K := K) (L := ↥L) (L' := ↥L')
        (Rep.trivial SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) (ZMod p))
      = SSGRoute.PTExt.trivResInv (SSGRoute.PTExt.galRes k ↥L ↥L') (ZMod p) from
    resResHom_triv (k := k) (K := K) (L := L) (L' := L') p]
  rfl

end Work.SSGRoute
