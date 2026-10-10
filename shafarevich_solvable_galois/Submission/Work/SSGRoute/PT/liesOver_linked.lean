import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Submission.Work.SSGRoute.E9c.TransportDefs
import Submission.Work.SSGRoute.InvAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace Work.SSGRoute.PT

/-- The linked places of one embedding form a tower.  For `K ≤ L` finite Galois over `k` inside `Ω`
and any embedding `φ : Ω →+* ℂ`, the infinite place `mk (φ|_L)` of `L` lies over `mk (φ|_K)`.

Route.  `φ|_L ∘ algebraMap K L = φ|_K` (scalar tower `K → L → Ω`), so the restriction of
`mk (φ|_L)` to `K` is `mk (φ|_K)` (`NumberField.InfinitePlace.comap_mk`); unfold `Place.LiesOver`
for infinite places. -/
theorem liesOver_linked (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K L : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [NumberField ↥K] [FiniteDimensional k L] [IsGalois k L] [NumberField ↥L]
    [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω] (φ : Ω →+* ℂ) :
    NK.GlobalCFT.Place.LiesOver
      (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk (φ.comp (algebraMap (↥L) Ω))))
      (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk (φ.comp (algebraMap (↥K) Ω)))) := by
  -- The two restricted embeddings agree on `K`: `φ|_L ∘ (K → L) = φ|_K` by the scalar tower.
  have hcomp : (φ.comp (algebraMap (↥L) Ω)).comp (algebraMap (↥K) (↥L)) =
      φ.comp (algebraMap (↥K) Ω) := by
    ext x
    simp only [RingHom.comp_apply]
    rw [IsScalarTower.algebraMap_apply ↥K ↥L Ω x]
  -- Hence `φ|_L` lies over `φ|_K` as complex embeddings, which gives the `AbsoluteValue`
  -- `LiesOver` relation on `mk` (Mathlib's instance in `NumberField.InfinitePlace.LiesOver`).
  haveI : FaithfulSMul ↥K ↥L :=
    (faithfulSMul_iff_algebraMap_injective ↥K ↥L).mpr (algebraMap ↥K ↥L).injective
  haveI : NumberField.ComplexEmbedding.LiesOver (φ.comp (algebraMap (↥L) Ω))
      (φ.comp (algebraMap (↥K) Ω)) := ⟨hcomp⟩
  -- Unfold `Place.LiesOver` at infinite places and apply the corresponding Mathlib instance.
  exact NK.GlobalCFT.Place.liesOver_ofInfinite
    (inferInstance : AbsoluteValue.LiesOver
      (NumberField.InfinitePlace.mk (φ.comp (algebraMap (↥L) Ω))).1
      (NumberField.InfinitePlace.mk (φ.comp (algebraMap (↥K) Ω))).1)

end Work.SSGRoute.PT
