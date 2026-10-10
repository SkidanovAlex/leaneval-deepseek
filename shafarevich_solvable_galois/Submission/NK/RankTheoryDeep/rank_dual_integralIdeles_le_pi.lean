import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import Submission.NK.RankTheoryDeep.IdeleRankDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The integral idèles sit inside `∏_v 𝒪_vˣ`: the rank inequality on the duals

This file proves the lemma requested by the idèle-side rank assembly,

`NK.RankTheoryDeep.rank_dual_integralIdeles_le_pi`,

i.e.

`rank_{ℤ_ℓ} Hom_cts(𝕀_int K, ℤ_ℓ) ≤ rank_{ℤ_ℓ} Hom_cts(∏_v 𝒪_vˣ, ℤ_ℓ)`,

for every number field `K` and every prime `ℓ`.

## The mathematics

The idèles which are units at every finite place (`NK.GlobalCFT.Idele.integralIdeles K`) are the
idèles all of whose *componentwise* membership conditions hold at *every* place, so that the
restricted-product condition defining `𝕀[K]` is automatic for them.  Hence the componentwise
map

`𝕀_int K → ∏_v 𝒪_vˣ,   x ↦ (x_v)_v`

(`NK.GlobalCFT.Place.localUnits K v = ⊤` at an archimedean place) is an isomorphism of
topological groups; concretely it is the structure map of the restricted product
(`RestrictedProduct.structureMap`), whose range is exactly `𝕀_int K`
(`RestrictedProduct.range_structureMap`), and it is continuous by
`RestrictedProduct.isEmbedding_structureMap`.

Contravariance of the continuous dual turns this into a *surjection* of `ℤ_ℓ`-modules in the
opposite direction, `Hom_cts(∏_v 𝒪_vˣ, ℤ_ℓ) ↠ Hom_cts(𝕀_int K, ℤ_ℓ)`
(`NK.Reconstruct.dualMap_injective_of_surjective` is the injectivity of the dual of a
surjection, applied to the inverse direction), and an injective linear map never decreases
`Module.rank` (`LinearMap.rank_le_of_injective`).

The content of the lemma is therefore the local structure of the idèles — the archimedean places
carry no restriction — plus the general facts about restricted products; no arithmetic input is
used (in particular no input at all about the ℓ-adic structure of the local unit groups, which is
carried separately by `NK.RankTheoryDeep.LocalUnitDualRankInput`).
-/

open NK.GlobalCFT

namespace NK.RankTheoryDeep

universe u

/-- The structure map of the restricted product, as a group homomorphism
`∏_v 𝒪_vˣ →* 𝕀_int K` from the product of the local unit groups onto the idèles which are units
at every finite place.  At an archimedean place `𝒪_vˣ = K_vˣ`, so the restricted product condition
holds at *every* place and there is no finiteness to check. -/
noncomputable def integralIdelesStructureMap (K : Type u) [Field K] [NumberField K] :
    ((∀ v : Place K, ↥(Place.localUnits K v)) →* ↥(Idele.integralIdeles K)) where
  toFun y :=
    ⟨RestrictedProduct.structureMap (fun v : Place K => (Place.localField K v)ˣ)
      (fun v => Place.localUnits K v) Filter.cofinite y,
      (Idele.mem_integralIdeles).mpr fun v _ => (y v).2⟩
  map_one' := by
    apply Subtype.ext
    apply RestrictedProduct.ext
    intro v
    rfl
  map_mul' := by
    intro x y
    apply Subtype.ext
    apply RestrictedProduct.ext
    intro v
    rfl

theorem integralIdelesStructureMap_apply (K : Type u) [Field K] [NumberField K]
    (y : ∀ v : Place K, ↥(Place.localUnits K v)) (v : Place K) :
    (integralIdelesStructureMap K y : Idele K) v = y v := rfl

/-- **The componentwise map `∏_v 𝒪_vˣ → 𝕀_int K` is surjective**: an idèle which is a unit at
every finite place is determined by, and determined by, its components, each of which lies in the
corresponding local unit group.  At a finite place this is the defining property of
`𝕀_int K`; at an archimedean place there is nothing to prove
(`Place.localUnits K v = ⊤`). -/
theorem integralIdelesStructureMap_surjective (K : Type u) [Field K] [NumberField K] :
    Function.Surjective (integralIdelesStructureMap K) := by
  intro x
  refine ⟨fun v => ⟨x.1 v, ?_⟩, ?_⟩
  · rcases v with w | q
    · exact Place.mem_localUnits_ofInfinite
    · exact (Idele.mem_integralIdeles.mp x.2) (Place.ofFinite q) (Place.isFinite_ofFinite q)
  · apply Subtype.ext
    apply RestrictedProduct.ext
    intro v
    rfl

/-- **The componentwise map `∏_v 𝒪_vˣ → 𝕀_int K` is continuous**: it is the structure map of the
restricted product, and the latter is an embedding of `∏_v 𝒪_vˣ` into it
(`RestrictedProduct.isEmbedding_structureMap`), hence continuous.  (This is the point where the
fact that the archimedean places are unrestricted in the restricted product is used: the map is
the identity on components, and the restricted product topology is the inductive limit of the
product topologies along cofinite sets.) -/
theorem continuous_integralIdelesStructureMap (K : Type u) [Field K] [NumberField K] :
    Continuous (integralIdelesStructureMap K) :=
  Continuous.subtype_mk (RestrictedProduct.isEmbedding_structureMap.continuous)
    fun y => (Idele.mem_integralIdeles).mpr fun v _ => (y v).2

/-- **The integral idèles are no larger than `∏_v 𝒪_vˣ` for the continuous dual**: the `ℤ_ℓ`-rank
of `Hom_cts(𝕀_int K, ℤ_ℓ)` is at most the `ℤ_ℓ`-rank of `Hom_cts(∏_v 𝒪_vˣ, ℤ_ℓ)`.

The componentwise identification `𝕀_int K ≅ ∏_v 𝒪_vˣ` (`integralIdelesStructureMap`) is a
surjective continuous group homomorphism, so its dual is an injective `ℤ_ℓ`-linear map in the
opposite direction, and `Module.rank` does not decrease along injections
(`LinearMap.rank_le_of_injective`). -/
theorem rank_dual_integralIdeles_le_pi (K : Type u) [Field K] [NumberField K] {ℓ : ℕ}
    [Fact ℓ.Prime] :
    Module.rank (PadicInt ℓ)
        (NK.Reconstruct.Dual (↥(NK.GlobalCFT.Idele.integralIdeles K)) ℓ)
      ≤ Module.rank (PadicInt ℓ)
          (NK.Reconstruct.Dual (∀ v : NK.GlobalCFT.Place K,
            ↥(NK.GlobalCFT.Place.localUnits K v)) ℓ) := by
  have hcont : Continuous (integralIdelesStructureMap K) :=
    continuous_integralIdelesStructureMap K
  have hinj : Function.Injective (NK.Reconstruct.dualMap ℓ (integralIdelesStructureMap K) hcont) :=
    NK.Reconstruct.dualMap_injective_of_surjective ℓ (integralIdelesStructureMap K) hcont
      (integralIdelesStructureMap_surjective K)
  let Φ : NK.Reconstruct.Dual (↥(NK.GlobalCFT.Idele.integralIdeles K)) ℓ →ₗ[PadicInt ℓ]
      NK.Reconstruct.Dual (∀ v : NK.GlobalCFT.Place K,
        ↥(NK.GlobalCFT.Place.localUnits K v)) ℓ :=
    { toFun := NK.Reconstruct.dualMap ℓ (integralIdelesStructureMap K) hcont
      map_add' := fun f g => NK.Reconstruct.dualMap_add ℓ (integralIdelesStructureMap K) hcont f g
      map_smul' := by
        intro a f
        apply Subtype.ext
        apply AddMonoidHom.ext
        intro x
        simp [NK.Reconstruct.dualMap_apply, smul_dual_apply] }
  exact LinearMap.rank_le_of_injective Φ hinj

end NK.RankTheoryDeep
