import Mathlib
import Submission.Work.SSGRoute.PTembedding.kbdDefs
import Submission.NK.LocalReciprocityLubinTate.Target
import Submission.NK.NUV2.kernelCondition_all
import Submission.NK.LocalAnabelian.All
import Submission.NK.LocalAnabelian.GaloisCorrespondence.numIndexClosedSubgroups_eq_natCard_finrank_eq
import Submission.Work.SSGRoute.finite_homs_of_finite_galoisFields
import Submission.Work.SSGRoute.finite_powClass_localField
import Submission.Work.SSGRoute.finite_localField_homs
import Submission.Work.SSGRoute.PTembedding.natCard_isDegPLevel_eq_indexP_subgroups
import Submission.Work.SSGRoute.PTembedding.natCard_galoisExtensions_maxAbelian
import Submission.Work.SSGRoute.PTembedding.natCard_lcHoms_eq_degreeP
import Submission.Work.SSGRoute.PTembedding.mul_natCard_indexP_subgroups
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Pointwise

namespace Work.SSGRoute.PTembedding


section Helpers

/-- The `p`-th powers lie in every subgroup of index `p`. -/
lemma powMonoidHom_range_le_of_index (G : Type*) [CommGroup G] {p : ℕ} (M : Subgroup G)
    (hM : M.index = p) : (powMonoidHom p : G →* G).range ≤ M := by
  intro x hx
  rw [MonoidHom.mem_range] at hx
  obtain ⟨y, rfl⟩ := hx
  rw [← hM]
  exact Subgroup.pow_index_mem M y

/-- If the `p`-th power quotient of an abelian group is finite, then the group has only
finitely many subgroups of index `p`. -/
lemma finite_indexP_subgroups_of_finite_quot (G : Type*) [CommGroup G] (p : ℕ)
    [Finite (G ⧸ (powMonoidHom p : G →* G).range)] :
    Finite {M : Subgroup G // M.index = p} := by
  have key : ∀ M : {M : Subgroup G // M.index = p},
      M.1 = (M.1.map (QuotientGroup.mk' (powMonoidHom p : G →* G).range)).comap
        (QuotientGroup.mk' (powMonoidHom p : G →* G).range) := by
    intro M
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk',
      sup_eq_left.mpr (powMonoidHom_range_le_of_index G M.1 M.2)]
  refine Finite.of_injective
    (fun M : {M : Subgroup G // M.index = p} =>
      (M.1.map (QuotientGroup.mk' (powMonoidHom p : G →* G).range) : Subgroup _))
    ?_
  intro M₁ M₂ h
  have h' : Subgroup.map (QuotientGroup.mk' ((powMonoidHom p : G →* G).range)) M₁.1
      = Subgroup.map (QuotientGroup.mk' ((powMonoidHom p : G →* G).range)) M₂.1 := h
  have h₁ := key M₁
  have h₂ := key M₂
  rw [h'] at h₁
  exact Subtype.ext (h₁.trans h₂.symm)

end Helpers

section Finiteness

variable {K F' : Type*} [Field K] [Field F'] [Algebra K F']

/-- A group homomorphism with open kernel into a group is locally constant (for the discrete
topology on the target, when the target is viewed as a topological group). -/
lemma isLocallyConstant_of_isOpen_ker {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {A : Type*} [Group A] (χ : G →* A) (h : IsOpen (χ.ker : Set G)) :
    IsLocallyConstant χ := by
  rw [IsLocallyConstant.iff_isOpen_fiber]
  intro y
  by_cases hy : ∃ x, χ x = y
  · obtain ⟨x, hx⟩ := hy
    have h1 : χ ⁻¹' {y} = x • (χ.ker : Set G) := by
      ext z
      rw [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_smul_set]
      constructor
      · intro hz
        refine ⟨x⁻¹ * z, ?_, ?_⟩
        · show χ (x⁻¹ * z) = 1
          rw [map_mul, map_inv, hz, hx, inv_mul_cancel]
        · show x * (x⁻¹ * z) = z
          group
      · rintro ⟨k, hk, hkz⟩
        rw [← hkz, smul_eq_mul, map_mul, MonoidHom.mem_ker.mp hk, mul_one, hx]
    rw [h1]
    exact h.leftCoset x
  · have hempty : χ ⁻¹' {y} = ∅ := by
      rw [← Set.not_nonempty_iff_eq_empty]
      rintro ⟨x, hx⟩
      exact hy ⟨x, hx⟩
    rw [hempty]
    exact isOpen_empty

end Finiteness

section FiniteExtensions

variable {K F' : Type*} [Field K] [Field F'] [Algebra K F'] [IsSepClosure K F']

/-- **Every degree-`p` Galois subextension carries a nontrivial locally constant character whose
kernel is its fixing subgroup.** -/
lemma exists_lcHoms_ker_eq_fixingSubgroup (p : ℕ) [Fact p.Prime]
    {L : IntermediateField K F'} (hgal : IsGalois K L) (hdeg : Module.finrank K L = p) :
    ∃ χ : ↥(Work.SSGRoute.lcHoms p (F' ≃ₐ[K] F')), χ.1 ≠ 1 ∧
      χ.1.ker = L.fixingSubgroup := by
  haveI : FiniteDimensional K ↥L :=
    FiniteDimensional.of_finrank_pos (by rw [hdeg]; exact (Fact.out : p.Prime).pos)
  haveI : Normal K ↥L := hgal.to_normal
  have hsurj : Function.Surjective (AlgEquiv.restrictNormalHom (F := K) (K₁ := F') ↥L) :=
    AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := ↥L) F'
  have hcard : Nat.card (↥L ≃ₐ[K] ↥L) = p := by
    rw [IsGalois.card_aut_eq_finrank K ↥L, hdeg]
  haveI hNz : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let φ : (↥L ≃ₐ[K] ↥L) ≃* Multiplicative (ZMod p) :=
    mulEquivOfPrimeCardEq hcard (Work.SSGRoute.natCard_multiplicative_zmod p)
  have hker : (φ.toMonoidHom.comp (AlgEquiv.restrictNormalHom (F := K) (K₁ := F') ↥L)).ker
      = L.fixingSubgroup := by
    rw [MonoidHom.ker_comp_of_injective (AlgEquiv.restrictNormalHom (F := K) (K₁ := F') ↥L)
      φ.toMonoidHom φ.injective]
    change (AlgEquiv.restrictNormalHom (F := K) (K₁ := F') ↥L).ker = L.fixingSubgroup
    exact IntermediateField.restrictNormalHom_ker L
  have hlg : IsLocallyConstant
      (φ.toMonoidHom.comp (AlgEquiv.restrictNormalHom (F := K) (K₁ := F') ↥L)) := by
    refine isLocallyConstant_of_isOpen_ker _ ?_
    rw [hker]
    exact IntermediateField.fixingSubgroup_isOpen L
  refine ⟨⟨_, hlg⟩, ?_, hker⟩
  intro h1
  have hker_top : L.fixingSubgroup = ⊤ := by
    rw [← hker,
      show φ.toMonoidHom.comp (AlgEquiv.restrictNormalHom (F := K) (K₁ := F') ↥L) = 1 from h1,
      MonoidHom.ker_one]
  have h1' : Module.finrank K ↥L = 1 := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index (F := K) F' L, hker_top,
      Subgroup.index_top]
  have h2 : p ≤ 1 := by rw [← hdeg, h1']
  exact absurd h2 (by have := (Fact.out : p.Prime).two_le; omega)

/-- **Finitely many locally constant characters imply finitely many degree-`p` Galois
subextensions.** -/
theorem finite_degreeP_extensions_of_finite_lcHoms (p : ℕ) [Fact p.Prime]
    [Finite ↥(Work.SSGRoute.lcHoms p (F' ≃ₐ[K] F'))] :
    Finite {L : IntermediateField K F' // IsGalois K L ∧ Module.finrank K L = p} := by
  classical
  let cls : {L : IntermediateField K F' // IsGalois K L ∧ Module.finrank K L = p} →
      ↥(Work.SSGRoute.lcHoms p (F' ≃ₐ[K] F')) := fun L =>
    Classical.choose (exists_lcHoms_ker_eq_fixingSubgroup (K := K) (F' := F') p L.2.1 L.2.2)
  have hcls : ∀ L, (cls L).1.ker = L.1.fixingSubgroup := fun L =>
    (Classical.choose_spec
      (exists_lcHoms_ker_eq_fixingSubgroup (K := K) (F' := F') p L.2.1 L.2.2)).2
  refine Finite.of_injective cls ?_
  intro L₁ L₂ h
  have hk : (L₁.1).fixingSubgroup = (L₂.1).fixingSubgroup := by
    rw [← hcls L₁, ← hcls L₂, h]
  exact Subtype.ext (by
    rw [← InfiniteGalois.fixedField_fixingSubgroup L₁.1,
      ← InfiniteGalois.fixedField_fixingSubgroup L₂.1, hk])

end FiniteExtensions


section Main

open scoped Classical Pointwise

/-- **The locally constant characters of the local absolute Galois group are the units mod `p`-th
powers.**  For a number field `k`, an algebraic closure `Ω`, a finite place `A` of `Ω` and a prime
`p`: the continuous characters `Gal(k̄_𝔭/k_𝔭) → 𝔽_p` of the local absolute Galois group at `A` are
as numerous as `k_𝔭ˣ ⧸ (k_𝔭ˣ)^p`.

This is local Kummer theory / local Tate duality in the form needed by the local base case: both
sides are counted by the index-`p` subgroups of `k_𝔭ˣ` — the characters through their open
kernels, the unit quotient through the classification of the abelian extensions of degree `p` of
the completion by their norm groups. -/
theorem lcHoms_localUnits
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    Nat.card ↥(Work.SSGRoute.lcHoms p (Work.SSGRoute.PTembedding.localGalOf k A hA))
      = Nat.card ((Work.SSGRoute.PTembedding.localFieldOf k A hA)ˣ ⧸
          ((powMonoidHom p : (Work.SSGRoute.PTembedding.localFieldOf k A hA)ˣ →*
            (Work.SSGRoute.PTembedding.localFieldOf k A hA)ˣ).range)) := by
  classical
  -- the prime of `k` below the place `A`, and the completion `κ = k_𝔭`
  let Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k) :=
    Submission.NeukirchUchida.primeOf A hA
  have hκ : Work.SSGRoute.PTembedding.localFieldOf k A hA = Q.adicCompletion k := rfl
  have hκc : Work.SSGRoute.PTembedding.localClosureOf k A hA
      = SeparableClosure (Q.adicCompletion k) := rfl
  have hgal : Work.SSGRoute.PTembedding.localGalOf k A hA
      = (SeparableClosure (Q.adicCompletion k) ≃ₐ[Q.adicCompletion k]
          SeparableClosure (Q.adicCompletion k)) := rfl
  -- the local reciprocity datum at `A`
  let D : NK.LocalCFT.ArtinReciprocity (Q.adicCompletion k) (SeparableClosure (Q.adicCompletion k)) :=
    (NK.LocalReciprocityLubinTate.artinReciprocity_adicCompletion Q
      (NK.NUV2.kernelCondition_all k Q).some).some
  -- characteristic zero and the finiteness of the `p`-th power class group of `κ`
  haveI hcz : CharZero (Q.adicCompletion k) :=
    Commons.NumberTheory.NumberField.charZero_adicCompletion Q
  haveI hKum : Finite ((Q.adicCompletion k)ˣ ⧸
      (powMonoidHom p : (Q.adicCompletion k)ˣ →* (Q.adicCompletion k)ˣ).range) :=
    Work.SSGRoute.finite_powClass_localField (Q.adicCompletion k) p (Fact.out : p.Prime)
  haveI hFinM : Finite {M : Subgroup (Q.adicCompletion k)ˣ // M.index = p} :=
    finite_indexP_subgroups_of_finite_quot _ p
  -- finiteness of the locally constant characters (from the workspace)
  haveI hFinHoms : Finite {χ : Gal(SeparableClosure (Q.adicCompletion k) / (Q.adicCompletion k)) →*
      Multiplicative (ZMod p) //
        IsOpen (χ.ker : Set (Gal(SeparableClosure (Q.adicCompletion k) / (Q.adicCompletion k))))} :=
    Work.SSGRoute.finite_localField_homs k Q p (ZMod p)
  haveI hFinLc : Finite ↥(Work.SSGRoute.lcHoms p (SeparableClosure (Q.adicCompletion k) ≃ₐ[
      Q.adicCompletion k] SeparableClosure (Q.adicCompletion k))) := by
    refine Finite.of_injective
      (fun χ : ↥(Work.SSGRoute.lcHoms p (SeparableClosure (Q.adicCompletion k) ≃ₐ[
          Q.adicCompletion k] SeparableClosure (Q.adicCompletion k))) =>
        (⟨χ.1, ?_⟩ : {χ : Gal(SeparableClosure (Q.adicCompletion k) / (Q.adicCompletion k)) →*
          Multiplicative (ZMod p) //
            IsOpen (χ.ker : Set (Gal(SeparableClosure (Q.adicCompletion k) /
              (Q.adicCompletion k))))})) ?_
    · show IsOpen ((χ.1).ker : Set (Gal(SeparableClosure (Q.adicCompletion k) /
        (Q.adicCompletion k))))
      exact χ.2.isOpen_fiber 1
    · intro a b h
      refine Subtype.ext ?_
      have hz := congrArg (fun z : {ψ : Gal(SeparableClosure (Q.adicCompletion k) /
          (Q.adicCompletion k)) →* Multiplicative (ZMod p) //
          IsOpen (ψ.ker : Set (Gal(SeparableClosure (Q.adicCompletion k) /
            (Q.adicCompletion k))))} =>
        (z : Gal(SeparableClosure (Q.adicCompletion k) / (Q.adicCompletion k)) →*
          Multiplicative (ZMod p))) h
      simpa using hz
  -- hence finiteness of the degree-`p` extensions
  haveI hFinB : Finite {L : IntermediateField (Q.adicCompletion k)
      (SeparableClosure (Q.adicCompletion k)) //
        IsGalois (Q.adicCompletion k) L ∧
          Module.finrank (Q.adicCompletion k) L = p} :=
    finite_degreeP_extensions_of_finite_lcHoms (K := Q.adicCompletion k)
      (F' := SeparableClosure (Q.adicCompletion k)) p
  -- the character count and the count of the extensions
  have hA' : Nat.card ↥(Work.SSGRoute.lcHoms p
        (SeparableClosure (Q.adicCompletion k) ≃ₐ[Q.adicCompletion k]
          SeparableClosure (Q.adicCompletion k)))
      = 1 + (p - 1) * Nat.card {L : IntermediateField (Q.adicCompletion k)
          (SeparableClosure (Q.adicCompletion k)) //
            IsGalois (Q.adicCompletion k) L ∧
              Module.finrank (Q.adicCompletion k) L = p} :=
    natCard_lcHoms_eq_degreeP (K := Q.adicCompletion k)
      (F' := SeparableClosure (Q.adicCompletion k)) p hFinB
  -- the reduction of the extensions inside `κ̄` to the levels of `κ^{ab}`
  have hB : Nat.card {L : IntermediateField (Q.adicCompletion k)
        (SeparableClosure (Q.adicCompletion k)) //
          IsGalois (Q.adicCompletion k) L ∧
            Module.finrank (Q.adicCompletion k) L = p}
      = Nat.card {L : IntermediateField (Q.adicCompletion k)
          ↥(NK.LocalReciprocity.maxAbelianSubext (Q.adicCompletion k)
            (SeparableClosure (Q.adicCompletion k))) //
          IsGalois (Q.adicCompletion k) ↥L ∧
            Module.finrank (Q.adicCompletion k) ↥L = p} :=
    natCard_galoisExtensions_maxAbelian (F := Q.adicCompletion k)
      (F' := SeparableClosure (Q.adicCompletion k)) p
  -- the classification of the degree-`p` levels by the index-`p` subgroups of the units
  have hC : Nat.card {L : IntermediateField (Q.adicCompletion k)
        ↥(NK.LocalReciprocity.maxAbelianSubext (Q.adicCompletion k)
          (SeparableClosure (Q.adicCompletion k))) //
        IsGalois (Q.adicCompletion k) ↥L ∧
          Module.finrank (Q.adicCompletion k) ↥L = p}
      = Nat.card {M : Subgroup (Q.adicCompletion k)ˣ // M.index = p} := by
    exact natCard_isDegPLevel_eq_indexP_subgroups (F := Q.adicCompletion k)
      (F' := SeparableClosure (Q.adicCompletion k)) D
  -- the count of the index-`p` subgroups by the `p`-th power quotient
  have hD : (p - 1) * Nat.card {M : Subgroup (Q.adicCompletion k)ˣ // M.index = p}
      = Nat.card ((Q.adicCompletion k)ˣ ⧸
          (powMonoidHom p : (Q.adicCompletion k)ˣ →* (Q.adicCompletion k)ˣ).range) - 1 :=
    mul_natCard_indexP_subgroups p (Q.adicCompletion k)ˣ
  have hSpos : 1 ≤ Nat.card ((Q.adicCompletion k)ˣ ⧸
      (powMonoidHom p : (Q.adicCompletion k)ˣ →* (Q.adicCompletion k)ˣ).range) :=
    Nat.one_le_iff_ne_zero.mpr (Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩)
  change Nat.card ↥(Work.SSGRoute.lcHoms p (SeparableClosure (Q.adicCompletion k) ≃ₐ[
      Q.adicCompletion k] SeparableClosure (Q.adicCompletion k)))
    = Nat.card ((Q.adicCompletion k)ˣ ⧸
        (powMonoidHom p : (Q.adicCompletion k)ˣ →* (Q.adicCompletion k)ˣ).range)
  calc Nat.card ↥(Work.SSGRoute.lcHoms p
        (SeparableClosure (Q.adicCompletion k) ≃ₐ[Q.adicCompletion k]
          SeparableClosure (Q.adicCompletion k)))
      = 1 + (p - 1) * Nat.card {L : IntermediateField (Q.adicCompletion k)
          (SeparableClosure (Q.adicCompletion k)) //
            IsGalois (Q.adicCompletion k) L ∧
              Module.finrank (Q.adicCompletion k) L = p} := hA'
    _ = 1 + (p - 1) * Nat.card {M : Subgroup (Q.adicCompletion k)ˣ // M.index = p} := by
        rw [hB, hC]
    _ = 1 + (Nat.card ((Q.adicCompletion k)ˣ ⧸
          (powMonoidHom p : (Q.adicCompletion k)ˣ →* (Q.adicCompletion k)ˣ).range) - 1) := by
        rw [hD]
    _ = Nat.card ((Q.adicCompletion k)ˣ ⧸
          (powMonoidHom p : (Q.adicCompletion k)ˣ →* (Q.adicCompletion k)ˣ).range) :=
        Nat.add_sub_cancel' hSpos

end Main

end Work.SSGRoute.PTembedding
