import Mathlib
import Submission.Work.RelatorRank.ProP

/-!
# `Work.ShaBound.isProPGroup_two_maximalProP`

**Namespace** `Work.ShaBound`; module `Submission.Work.ShaBound.isProPGroup_two_maximalProP`.

The Galois group of a maximal pro-`2` extension `Omega/F` of a field `F` is a pro-`2` group in the
sense of `Work.RelatorRank.IsProPGroup`: every open normal subgroup has a `2`-group quotient.

The only input is that every *finite dimensional Galois* intermediate field `L` of `Omega/F` has
`IsPGroup 2 (Gal(L/F))`.  The topology enters through the Krull topology: an open normal `U`
contains the fixing subgroup `Gal(Omega/L)` of some finite Galois intermediate field `L`, and
`Gal(Omega/F) / Gal(Omega/L) ≅ Gal(L/F)` is a `2`-group; the quotient by the larger subgroup `U`
is a quotient of that.

The proof is the intermediate-field form of the general lemma
`Work.ShaBound.isProPGroup_of_forall_finiteGalois_isPGroup` of
`Submission.Work.ShaBound.isProPGroup_two_galK`; it is restated here for convenience so that this
module is self-contained.
-/

set_option linter.style.haveILetI false
set_option autoImplicit false

open scoped Topology

namespace Work.ShaBound

universe u v

/-- **A Galois group all of whose finite Galois subextensions have `p`-group Galois group is a
pro-`p` group.**  (Intermediate-field form.)

If `K/F` is Galois and every finite dimensional Galois intermediate field `L` has
`IsPGroup p (Gal(L/F))`, then `Gal(K/F) = K ≃ₐ[F] K` is a pro-`p` group: for every open normal
subgroup `U`, the finite group `Gal(K/F) ⧸ U` is a `p`-group.

The base field `F` is a variable on purpose: over `F = ℚ` the carrier of an
`IntermediateField ℚ K` carries two competing, only propositionally equal, `ℚ`-algebra structures,
which make such statements fail to elaborate when written directly over `ℚ`. -/
theorem isProPGroup_of_forall_intermediateField_isPGroup {F : Type u} {K : Type v} [Field F]
    [Field K] [Algebra F K] [IsGalois F K] {p : ℕ}
    (hpro : ∀ (L : IntermediateField F K), FiniteDimensional F L → IsGalois F L →
      IsPGroup p (L ≃ₐ[F] L)) :
    Work.RelatorRank.IsProPGroup p (K ≃ₐ[F] K) := by
  intro U
  haveI hnormK : Normal F K := IsGalois.to_normal
  -- `U` is open, hence a neighbourhood of `1`: it contains the fixing subgroup of a finite Galois
  -- subextension of `K/F`.
  have hmem : (U : Set (K ≃ₐ[F] K)) ∈ 𝓝 1 := U.isOpen.mem_nhds U.one_mem
  obtain ⟨L, hL⟩ :=
    (InfiniteGalois.krullTopology_mem_nhds_one_iff_of_isGalois (k := F) (K := K)
      (U : Set (K ≃ₐ[F] K))).mp hmem
  -- `L` as an intermediate field, with its finiteness and Galois-ness as instances
  set E : IntermediateField F K := L.toIntermediateField with hE
  haveI hfdE : FiniteDimensional F ↥E := by rw [hE]; exact L.finiteDimensional
  haveI hgalE : IsGalois F ↥E := by rw [hE]; exact L.isGalois
  haveI hnormE : Normal F ↥E := IsGalois.to_normal
  -- the restriction map `Gal(K/F) →* Gal(L/F)`, with kernel `L.fixingSubgroup`
  let ρ : (K ≃ₐ[F] K) →* (↥E ≃ₐ[F] ↥E) := AlgEquiv.restrictNormalHom (F := F) (K₁ := K) ↥E
  have hρker : ρ.ker = L.fixingSubgroup := by
    rw [← IntermediateField.restrictNormalHom_ker E]
  have hsurj : Function.Surjective ρ :=
    AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := ↥E) K
  -- `Gal(L/F)` is a `p`-group by hypothesis
  have hpgE : IsPGroup p (↥E ≃ₐ[F] ↥E) := hpro E hfdE hgalE
  -- so the quotient of `Gal(K/F)` by the kernel of the restriction is a `p`-group ...
  have hpgKer : IsPGroup p ((K ≃ₐ[F] K) ⧸ ρ.ker) :=
    hpgE.of_equiv (QuotientGroup.quotientKerEquivOfSurjective ρ hsurj).symm
  -- ... and `Γ ⧸ U` is a quotient of `Γ ⧸ L.fixingSubgroup`, since `L.fixingSubgroup ≤ U`
  have hleker : ρ.ker ≤ (U : Subgroup (K ≃ₐ[F] K)) := by
    rw [hρker]; exact hL
  have hsurj2 : Function.Surjective (QuotientGroup.map ρ.ker (U : Subgroup (K ≃ₐ[F] K))
      (MonoidHom.id (K ≃ₐ[F] K)) (by simpa using hleker)) := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (U : Subgroup (K ≃ₐ[F] K)) y
    exact ⟨QuotientGroup.mk' ρ.ker g, by rw [QuotientGroup.map_mk']; rfl⟩
  exact hpgKer.of_surjective _ hsurj2

/-- The Galois group of a maximal pro-`2` extension of a field `F` is a pro-`2` group: every open normal subgroup has a `2`-group quotient. -/
theorem isProPGroup_two_maximalProP (F : Type) [Field F] (Omega : Type) [Field Omega]
    [Algebra F Omega] [Algebra.IsAlgebraic F Omega] [IsGalois F Omega]
    (h : ∀ (L : IntermediateField F Omega), FiniteDimensional F L → IsGalois F L →
      IsPGroup 2 (L ≃ₐ[F] L)) :
    Work.RelatorRank.IsProPGroup 2 (Omega ≃ₐ[F] Omega) :=
  isProPGroup_of_forall_intermediateField_isPGroup h

end Work.ShaBound
