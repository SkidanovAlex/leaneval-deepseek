import Mathlib
import Submission.Vdw.BlockAction
import Submission.Vdw.BlockPolyAction
import Submission.Vdw.BlockPolyL
import Submission.Vdw.GaloisRamification
import Submission.Commons.FieldTheory.Galois.finrank_mul_card_fixingSubgroup_eq_card_algEquiv

open Polynomial
open scoped Pointwise

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# The degree of the block field is the number of blocks

For an irreducible `p : ℚ[X]`, a block `B` of the naive Galois action on the
`s = p.natDegree` roots, `k = B.card` and `m` the number of blocks (the size of
the translate orbit of `B`), the field of definition

`L = blockField p hsep B = ℚ(coeffs of the block polynomial of B)`

has degree `m` over `ℚ`.

The proof is the cardinality computation
`[L:ℚ]·|stab| = |Gal(E/ℚ)| = |H| = |orbit|·|stab|`, where `H` is the image of
`galFinHomN` and `stab` the stabilizer of `B` in `H`.

Axioms: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw

noncomputable section

/-- **The naive permutation representation is faithful.** -/
theorem galFinHomN_injective (p : ℚ[X]) (hsep : p.Separable) :
    Function.Injective (galFinHomN p hsep) := by
  letI : Fact ((p.map (algebraMap ℚ p.SplittingField)).Splits) :=
    ⟨Polynomial.SplittingField.splits p⟩
  intro σ τ h
  refine galFinHom_injective p hsep ?_
  have hσ : galFinHom p hsep σ
      = conjPerm p hsep * galFinHomN p hsep σ * (conjPerm p hsep)⁻¹ :=
    galFinHom_conj p hsep σ
  have hτ : galFinHom p hsep τ
      = conjPerm p hsep * galFinHomN p hsep τ * (conjPerm p hsep)⁻¹ :=
    galFinHom_conj p hsep τ
  rw [hσ, hτ, h]

/-- **The block stabilizer** of `B`, as a subgroup of the image group
`H = (galFinHomN p hsep).range`. -/
abbrev blockStabilizer (p : ℚ[X]) (hsep : p.Separable) (B : Finset (Fin p.natDegree)) :
    Subgroup (↥((galFinHomN p hsep).range)) :=
  MulAction.stabilizer (↥((galFinHomN p hsep).range)) (↑B : Set (Fin p.natDegree))

lemma mem_blockStabilizer_iff (p : ℚ[X]) (hsep : p.Separable) (B : Finset (Fin p.natDegree))
    (x : ↥((galFinHomN p hsep).range)) :
    x ∈ blockStabilizer p hsep B ↔ (x : Equiv.Perm (Fin p.natDegree))
      '' (↑B : Set (Fin p.natDegree)) = ↑B := by
  rw [blockStabilizer, MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    have h' : (x : Equiv.Perm (Fin p.natDegree)) • (↑B : Set (Fin p.natDegree)) = ↑B := h
    rwa [show (x : Equiv.Perm (Fin p.natDegree)) • (↑B : Set (Fin p.natDegree))
      = (x : Equiv.Perm (Fin p.natDegree)) '' (↑B : Set (Fin p.natDegree)) from rfl] at h'
  · intro h
    show (x : Equiv.Perm (Fin p.natDegree)) • (↑B : Set (Fin p.natDegree)) = ↑B
    rw [show (x : Equiv.Perm (Fin p.natDegree)) • (↑B : Set (Fin p.natDegree))
      = (x : Equiv.Perm (Fin p.natDegree)) '' (↑B : Set (Fin p.natDegree)) from rfl, h]

/-- **The Galois group of the splitting field over the block field is the block
stabilizer.**  The two subgroups (one of `Gal(E/ℚ)`, one of the image group
`H = (galFinHomN p hsep).range`) are identified through the bijection
`galFinHomN`. -/
noncomputable def fixingSubgroupEquivBlockStabilizer (p : ℚ[X]) (hsep : p.Separable)
    (B : Finset (Fin p.natDegree)) :
    (↥(blockField p hsep B).fixingSubgroup) ≃ (↥(blockStabilizer p hsep B)) where
  toFun σ := ⟨⟨galFinHomN p hsep σ.1, ⟨σ.1, rfl⟩⟩, by
    refine MulAction.mem_stabilizer_iff.mpr ?_
    show (⟨galFinHomN p hsep σ.1, ⟨σ.1, rfl⟩⟩ : ↥((galFinHomN p hsep).range))
        • (↑B : Set (Fin p.natDegree)) = ↑B
    have hσ : (blockPoly p hsep B).map σ.1.toRingHom = blockPoly p hsep B :=
      (mem_blockField_fixingSubgroup_iffN p hsep B σ.1).mpr σ.2
    have him : B.image (galFinHomN p hsep σ.1) = B :=
      (blockPoly_mapN_eq_iff p hsep σ.1 B).mp hσ
    rw [show (⟨galFinHomN p hsep σ.1, ⟨σ.1, rfl⟩⟩ : ↥((galFinHomN p hsep).range))
        • (↑B : Set (Fin p.natDegree))
        = galFinHomN p hsep σ.1 '' (↑B : Set (Fin p.natDegree)) from rfl]
    rw [← Finset.coe_image, him]⟩
  invFun x := ⟨Classical.choose (MonoidHom.mem_range.mp x.1.2), by
    have hσ : galFinHomN p hsep (Classical.choose (MonoidHom.mem_range.mp x.1.2)) = x.1.1 :=
      Classical.choose_spec (MonoidHom.mem_range.mp x.1.2)
    have hx : x.1.1 '' (↑B : Set (Fin p.natDegree)) = ↑B :=
      (mem_blockStabilizer_iff p hsep B x.1).mp x.2
    have him : galFinHomN p hsep (Classical.choose (MonoidHom.mem_range.mp x.1.2)) '' (↑B : Set
        (Fin p.natDegree)) = ↑B := by rw [hσ]; exact hx
    have him2 : B.image (galFinHomN p hsep (Classical.choose (MonoidHom.mem_range.mp x.1.2))) = B := by
      apply Finset.coe_injective
      rw [Finset.coe_image, him]
    exact (mem_blockField_fixingSubgroup_iffN p hsep B _).mp
      ((blockPoly_mapN_eq_iff p hsep _ B).mpr him2)⟩
  left_inv σ := by
    apply Subtype.ext
    apply galFinHomN_injective p hsep
    exact Classical.choose_spec (MonoidHom.mem_range.mp (⟨σ.1, rfl⟩ :
      galFinHomN p hsep σ.1 ∈ (galFinHomN p hsep).range))
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    exact Classical.choose_spec (MonoidHom.mem_range.mp x.1.2)

/-- **The cardinality form** of the Galois-group/stabilizer identification. -/
theorem fixingSubgroup_card_eq_blockStabilizer_card (p : ℚ[X]) (hsep : p.Separable)
    (B : Finset (Fin p.natDegree)) :
    Nat.card (↥(blockField p hsep B).fixingSubgroup)
      = Nat.card (↥(blockStabilizer p hsep B)) :=
  Nat.card_congr (fixingSubgroupEquivBlockStabilizer p hsep B)

/-- **The order of the image group equals the order of the Galois group.** -/
theorem card_range_galFinHomN (p : ℚ[X]) (hsep : p.Separable) :
    Nat.card (↥((galFinHomN p hsep).range))
      = Nat.card (p.SplittingField ≃ₐ[ℚ] p.SplittingField) := by
  have hinj : Function.Injective (galFinHomN p hsep) := galFinHomN_injective p hsep
  exact (Nat.card_congr (Equiv.ofInjective (galFinHomN p hsep) hinj)).symm.trans rfl

/-- **The degree of the block field is the number of blocks.** -/
theorem finrank_blockField_eq_card_orbit (p : ℚ[X]) [Fact (Irreducible p)] (hsep : p.Separable)
    {B : Finset (Fin p.natDegree)}
    (hB : MulAction.IsBlock ((galFinHomN p hsep).range) (↑B : Set (Fin p.natDegree))) :
    Module.finrank ℚ ↥(blockField p hsep B)
      = (MulAction.orbit (↥((galFinHomN p hsep).range)) (↑B : Set (Fin p.natDegree))).ncard := by
  classical
  haveI : IsGalois ℚ p.SplittingField := spl_galois p
  haveI : Fintype (↥((galFinHomN p hsep).range)) := Fintype.ofFinite _
  haveI : Finite (↥(MulAction.stabilizer (↥((galFinHomN p hsep).range))
      (↑B : Set (Fin p.natDegree)))) := Subtype.finite
  haveI : Fintype (↥(MulAction.stabilizer (↥((galFinHomN p hsep).range))
      (↑B : Set (Fin p.natDegree)))) := Fintype.ofFinite _
  haveI : Fintype ↥(MulAction.orbit (↥((galFinHomN p hsep).range)) (↑B : Set (Fin p.natDegree))) :=
    Set.Finite.fintype (Set.toFinite _)
  haveI : Nonempty (↥(blockStabilizer p hsep B)) :=
    ⟨1, MulAction.mem_stabilizer_iff.mpr (one_smul _ _)⟩
  -- the two cardinality identities
  have h1 := Commons.FieldTheory.Galois.finrank_mul_card_fixingSubgroup_eq_card_algEquiv
    (p.SplittingField) (blockField p hsep B)
  have hfix := fixingSubgroup_card_eq_blockStabilizer_card p hsep B
  have hcardH := card_range_galFinHomN p hsep
  have h2 := MulAction.card_orbit_mul_card_stabilizer_eq_card_group
    (↥((galFinHomN p hsep).range)) (B : Set (Fin p.natDegree))
  have h2n : (MulAction.orbit (↥((galFinHomN p hsep).range)) (↑B : Set (Fin p.natDegree))).ncard
        * Nat.card (↥(blockStabilizer p hsep B))
      = Nat.card (↥((galFinHomN p hsep).range)) := by
    rw [← Nat.card_coe_set_eq (MulAction.orbit (↥((galFinHomN p hsep).range))
        (↑B : Set (Fin p.natDegree))), Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Nat.card_eq_fintype_card]
    exact h2
  have h3 : Module.finrank ℚ ↥(blockField p hsep B) * Nat.card (↥(blockStabilizer p hsep B))
      = (MulAction.orbit (↥((galFinHomN p hsep).range)) (↑B : Set (Fin p.natDegree))).ncard
        * Nat.card (↥(blockStabilizer p hsep B)) :=
    (hfix ▸ h1).trans (hcardH.symm.trans h2n.symm)
  exact Nat.mul_right_cancel (Nat.card_pos) h3

end

end Submission.Vdw
