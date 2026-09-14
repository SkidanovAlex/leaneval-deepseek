import Mathlib
import Submission.Vdw.BlockRank
import Submission.Vdw.BlockPolyComplex
import Submission.Commons.FieldTheory.Galois.algHom_fieldRange_eq_adjoin_image
import Submission.Commons.NumberTheory.NumberField.card_algHom_eq_finrank

open Polynomial
open scoped Pointwise

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-!
# The structural dictionary, set-indexed: block polynomial, orbit and the norm

This module reformulates the block dictionary of `BlockPoly`/`BlockPolyL` in a
form indexed by *sets* of roots (the natural index of the Galois action and of
`MulAction.orbit`), and proves the two facts the imprimitive counting needs:

* `blkEmbedOrbit` — the bijection between the translate orbit of a block `B`
  and the complex embeddings of the field of definition
  `L = blockField p hsep B`;
* **`normIdentity`** — the block system product over the *embeddings*:
  `∏_{χ : L →ₐ[ℚ] ℂ} χ(P_L) = p.map (algebraMap ℚ ℂ)`, i.e. `p` is recovered
  from the block polynomial and its field of definition.

Axioms: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw

noncomputable section

/-- The `Finset` of elements of a set of `Fin n`. -/
def setFin {n : ℕ} (B : Set (Fin n)) : Finset (Fin n) := by
  classical exact Finset.univ.filter (· ∈ B)

lemma mem_setFin {n : ℕ} {B : Set (Fin n)} {i : Fin n} : i ∈ setFin B ↔ i ∈ B := by
  classical simp [setFin]

lemma coe_setFin {n : ℕ} (B : Set (Fin n)) : ((setFin B : Finset (Fin n)) : Set (Fin n)) = B := by
  ext i; simp [setFin]

lemma setFin_injective {n : ℕ} : Function.Injective (setFin : Set (Fin n) → Finset (Fin n)) :=
  fun A B h => by rw [← coe_setFin A, ← coe_setFin B, h]

lemma setFin_card {n : ℕ} (B : Set (Fin n)) : (setFin B).card = B.ncard := by
  rw [← Set.ncard_coe_finset (setFin B), coe_setFin]

@[simp] lemma setFin_image {n : ℕ} (B : Set (Fin n)) (f : Fin n → Fin n) :
    setFin (f '' B) = (setFin B).image f := by
  classical
  ext i
  rw [mem_setFin, Finset.mem_image]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, by rwa [mem_setFin], rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, by rwa [mem_setFin] at hj, rfl⟩

variable (p : ℚ[X]) (hsep : p.Separable)

/-- The image group `H = (galFinHomN p hsep).range`. -/
abbrev galImg : Subgroup (Equiv.Perm (Fin p.natDegree)) := (galFinHomN p hsep).range

/-- The translate orbit of a block. -/
def blkOrbit (B : Set (Fin p.natDegree)) : Set (Set (Fin p.natDegree)) :=
  MulAction.orbit (↥(galImg p hsep)) B

/-- The orbit as a finite set. -/
def orbitF (B : Set (Fin p.natDegree)) : Finset (Set (Fin p.natDegree)) := by
  classical exact Finset.univ.image (fun g : ↥(galImg p hsep) => g • B)

lemma mem_orbitF {B C : Set (Fin p.natDegree)} :
    C ∈ orbitF p hsep B ↔ ∃ g : ↥(galImg p hsep), g • B = C := by
  classical
  rw [orbitF, Finset.mem_image]
  constructor
  · rintro ⟨g, -, hg⟩; exact ⟨g, hg⟩
  · rintro ⟨g, hg⟩; exact ⟨g, Finset.mem_univ g, hg⟩

lemma coe_orbitF (B : Set (Fin p.natDegree)) :
    ((orbitF p hsep B : Finset (Set (Fin p.natDegree))) : Set (Set (Fin p.natDegree)))
      = blkOrbit p hsep B := by
  ext C
  rw [Finset.mem_coe, mem_orbitF, blkOrbit, MulAction.mem_orbit_iff]

lemma orbitF_card (B : Set (Fin p.natDegree)) :
    (orbitF p hsep B).card = (blkOrbit p hsep B).ncard := by
  rw [← Set.ncard_coe_finset (orbitF p hsep B), coe_orbitF]

/-- The block polynomial of a *set* of roots. -/
abbrev spoly (B : Set (Fin p.natDegree)) : p.SplittingField[X] := blockPoly p hsep (setFin B)

/-- The field of definition of a *set* of roots. -/
abbrev sfield (B : Set (Fin p.natDegree)) : IntermediateField ℚ p.SplittingField :=
  blockField p hsep (setFin B)

/-- The block polynomial over its field of definition. -/
abbrev spolyL (B : Set (Fin p.natDegree)) : (↥(sfield p hsep B))[X] :=
  blockPolyL p hsep (setFin B)

lemma spoly_monic (B : Set (Fin p.natDegree)) : (spoly p hsep B).Monic :=
  blockPoly_monic p hsep (setFin B)

lemma spoly_natDegree (B : Set (Fin p.natDegree)) :
    (spoly p hsep B).natDegree = B.ncard := by
  rw [spoly, blockPoly_natDegree, setFin_card]

lemma spolyL_map_val (B : Set (Fin p.natDegree)) :
    (spolyL p hsep B).map (algebraMap ↥(sfield p hsep B) p.SplittingField)
      = spoly p hsep B :=
  blockPolyL_map_val p hsep (setFin B)

/-- **The Galois action on the block polynomial** (set indexing). -/
lemma spoly_map_galN (σ : p.Gal) (B : Set (Fin p.natDegree)) :
    (spoly p hsep B).map σ.toRingHom
      = spoly p hsep (galFinHomN p hsep σ '' B) := by
  rw [spoly, spoly, blockPoly_map_galN, setFin_image]

lemma spoly_map_eq_iff (σ : p.Gal) (B : Set (Fin p.natDegree)) :
    (spoly p hsep B).map σ.toRingHom = spoly p hsep B
      ↔ galFinHomN p hsep σ '' B = B := by
  rw [spoly_map_galN p hsep σ B]
  exact ⟨fun h => setFin_injective (blockPoly_injective p hsep h), fun h => by rw [h]⟩

/-- **The stabilizer of the block is the Galois group over the field of
definition** (set indexing). -/
lemma mem_sfield_fixingSubgroup_iffN (B : Set (Fin p.natDegree)) (σ : p.Gal) :
    ((spoly p hsep B).map σ.toRingHom = spoly p hsep B)
      ↔ σ ∈ (sfield p hsep B).fixingSubgroup :=
  mem_blockField_fixingSubgroup_iffN p hsep (setFin B) σ

/-! ## The block system product -/

/-- The translate orbit is a block system. -/
lemma isBlockSystem_blkOrbit {B : Set (Fin p.natDegree)}
    [MulAction.IsPretransitive (↥(galImg p hsep)) (Fin p.natDegree)]
    (hB : MulAction.IsBlock (↥(galImg p hsep)) B) (hne : B.Nonempty) :
    Setoid.IsPartition (blkOrbit p hsep B) :=
  (MulAction.IsBlock.isBlockSystem (G := ↥(galImg p hsep)) hB hne).1

lemma blkOrbit_finite (B : Set (Fin p.natDegree)) : (blkOrbit p hsep B).Finite :=
  (Set.finite_range (fun g : ↥(galImg p hsep) => g • B)).subset (by
    rintro C ⟨g, rfl⟩; exact ⟨g, rfl⟩)

lemma blkOrbit_eq_range (B : Set (Fin p.natDegree)) :
    blkOrbit p hsep B = Set.range (fun g : ↥(galImg p hsep) => g • B) := rfl

/-- **The block system product** (set indexing): `p` is the product of the block
polynomials over the translate orbit of `B`. -/
theorem spoly_factors (hmonic : p.Monic) {B : Set (Fin p.natDegree)}
    [MulAction.IsPretransitive (↥(galImg p hsep)) (Fin p.natDegree)]
    (hB : MulAction.IsBlock (↥(galImg p hsep)) B) (hne : B.Nonempty) :
    p.map (algebraMap ℚ p.SplittingField) = ∏ C : ↥(orbitF p hsep B), spoly p hsep C.1 := by
  classical
  have hpart := isBlockSystem_blkOrbit p hsep hB hne
  have hfin : (blkOrbit p hsep B).Finite := blkOrbit_finite p hsep B
  have hmain := Commons.Data.Finset.prod_eq_prod_of_isPartition hpart hfin
    (fun i : Fin p.natDegree => (X - C (rootOf p hsep i)))
  have hmap : p.map (algebraMap ℚ p.SplittingField)
      = ∏ a : Fin p.natDegree, (X - C (rootOf p hsep a)) :=
    map_eq_prod_rootOf p hmonic hsep
  have hcoe : (↑hfin.toFinset : Set (Set (Fin p.natDegree)))
      = (↑(orbitF p hsep B) : Set (Set (Fin p.natDegree))) := by
    rw [Set.Finite.coe_toFinset, coe_orbitF]
  have hstep : (∏ C ∈ hfin.toFinset, ∏ a ∈
        (Set.Finite.toFinset (Set.toFinite (C : Set (Fin p.natDegree)))),
          (Polynomial.X - Polynomial.C (rootOf p hsep a)))
      = ∏ C ∈ orbitF p hsep B, spoly p hsep C := by
    refine Finset.prod_congr (Finset.coe_injective hcoe) (fun C _ => ?_)
    have h1 : (Set.Finite.toFinset (Set.toFinite (C : Set (Fin p.natDegree)))) = setFin C := by
      apply Finset.coe_injective
      rw [Set.Finite.coe_toFinset, coe_setFin]
    rw [h1]
    rfl
  rw [hmap, hmain, hstep]
  exact (Finset.prod_coe_sort (orbitF p hsep B) (fun C => spoly p hsep C)).symm

/-! ## The bijection between the orbit and the complex embeddings -/

/-- The lift of an element of the image group to the Galois group. -/
noncomputable abbrev galLift (g : ↥(galImg p hsep)) : p.Gal :=
  Classical.choose (MonoidHom.mem_range.mp g.2)

lemma galFinHomN_galLift (g : ↥(galImg p hsep)) :
    galFinHomN p hsep (galLift p hsep g) = g.1 :=
  Classical.choose_spec (MonoidHom.mem_range.mp g.2)

/-- The translate of the block by an element of the image group, in terms of
its lift. -/
lemma galLift_smul (g : ↥(galImg p hsep)) (B : Set (Fin p.natDegree)) :
    g • B = galFinHomN p hsep (galLift p hsep g) '' B := by
  rw [galFinHomN_galLift p hsep g]
  rfl

/-- The coefficients of the block polynomial lie in the field of definition. -/
lemma spoly_coeff_mem (B : Set (Fin p.natDegree)) (i : ℕ) :
    (spoly p hsep B).coeff i ∈ sfield p hsep B :=
  blockPoly_coeff_mem p hsep (setFin B) i

/-- The coefficient of `spolyL`, as an element of the field of definition. -/
lemma spolyL_coeff_val (B : Set (Fin p.natDegree)) (i : ℕ) :
    ((spolyL p hsep B).coeff i : p.SplittingField) = (spoly p hsep B).coeff i :=
  congrArg Subtype.val (blockPolyL_coeff p hsep (setFin B) i)

/-- The inclusion of the block field, applied to a coefficient of the block
polynomial. -/
lemma sfield_val_coeff (B : Set (Fin p.natDegree)) (i : ℕ) :
    (sfield p hsep B).val ((spolyL p hsep B).coeff i) = (spoly p hsep B).coeff i :=
  spolyL_coeff_val p hsep B i

/-- **The embedding of the block field attached to an element of the orbit**:
the restriction of a lift of the orbit representative to the block field,
followed by `ι`. -/
noncomputable def blkEmbedOrbit (ι : p.SplittingField →ₐ[ℚ] ℂ) (B : Set (Fin p.natDegree))
    (C : ↥(orbitF p hsep B)) : ↥(sfield p hsep B) →ₐ[ℚ] ℂ :=
  ι.comp ((galLift p hsep (Classical.choose ((mem_orbitF p hsep).mp C.2))).toAlgHom.comp
    (sfield p hsep B).val)

lemma blkEmbedOrbit_apply (ι : p.SplittingField →ₐ[ℚ] ℂ) (B : Set (Fin p.natDegree))
    (C : ↥(orbitF p hsep B)) (x : ↥(sfield p hsep B)) :
    blkEmbedOrbit p hsep ι B C x
      = ι (galLift p hsep (Classical.choose ((mem_orbitF p hsep).mp C.2))
          ((sfield p hsep B).val x)) := rfl


/-- **Injectivity of the orbit-to-embedding map.** -/
lemma blkEmbedOrbit_injective (ι : p.SplittingField →ₐ[ℚ] ℂ) (B : Set (Fin p.natDegree)) :
    Function.Injective (blkEmbedOrbit p hsep ι B) := by
  intro C C' hCC
  have hg : (Classical.choose ((mem_orbitF p hsep).mp C.2) : ↥(galImg p hsep)) • B = C.1 :=
    Classical.choose_spec ((mem_orbitF p hsep).mp C.2)
  have hg' : (Classical.choose ((mem_orbitF p hsep).mp C'.2) : ↥(galImg p hsep)) • B = C'.1 :=
    Classical.choose_spec ((mem_orbitF p hsep).mp C'.2)
  have hσ : galFinHomN p hsep (galLift p hsep (Classical.choose ((mem_orbitF p hsep).mp C.2)))
      = (Classical.choose ((mem_orbitF p hsep).mp C.2)).1 := galFinHomN_galLift p hsep _
  have hσ' : galFinHomN p hsep (galLift p hsep (Classical.choose ((mem_orbitF p hsep).mp C'.2)))
      = (Classical.choose ((mem_orbitF p hsep).mp C'.2)).1 := galFinHomN_galLift p hsep _
  have hpoly : (spoly p hsep B).map
        (galLift p hsep (Classical.choose ((mem_orbitF p hsep).mp C.2))).toRingHom
      = (spoly p hsep B).map
        (galLift p hsep (Classical.choose ((mem_orbitF p hsep).mp C'.2))).toRingHom := by
    ext i
    rw [Polynomial.coeff_map, Polynomial.coeff_map]
    have hx := congrArg (fun f : ↥(sfield p hsep B) →ₐ[ℚ] ℂ =>
      f ⟨(spoly p hsep B).coeff i, spoly_coeff_mem p hsep B i⟩) hCC
    rw [blkEmbedOrbit_apply, blkEmbedOrbit_apply] at hx
    exact RingHom.injective (ι.toRingHom) hx
  have hset : galFinHomN p hsep (galLift p hsep (Classical.choose ((mem_orbitF p hsep).mp C.2))) '' B
      = galFinHomN p hsep (galLift p hsep (Classical.choose ((mem_orbitF p hsep).mp C'.2))) '' B := by
    have := hpoly
    rw [spoly_map_galN p hsep _ B, spoly_map_galN p hsep _ B] at this
    exact setFin_injective (blockPoly_injective p hsep this)
  have hset' : (Classical.choose ((mem_orbitF p hsep).mp C.2) : ↥(galImg p hsep)) • B
      = (Classical.choose ((mem_orbitF p hsep).mp C'.2) : ↥(galImg p hsep)) • B := by
    rw [galLift_smul p hsep _ B, galLift_smul p hsep _ B, hset]
  apply Subtype.ext
  rw [← hg, ← hg', hset']

/-- The block polynomial over the field of definition, mapped to the splitting
field and then by a Galois element. -/
lemma spolyL_map_algHom (B : Set (Fin p.natDegree)) (σ : p.Gal) :
    (spolyL p hsep B).map (σ.toAlgHom.comp (sfield p hsep B).val).toRingHom
      = (spoly p hsep B).map σ.toRingHom := by
  have hcomp : (σ.toAlgHom.comp (sfield p hsep B).val).toRingHom
      = σ.toRingHom.comp (algebraMap (↥(sfield p hsep B)) p.SplittingField) := rfl
  rw [hcomp, ← Polynomial.map_map, spolyL_map_val]

/-- **The key identity**: the complex block polynomial attached to an orbit
element is the image of the block polynomial over its field of definition. -/
lemma blkEmbedOrbit_map_spolyL (ι : p.SplittingField →ₐ[ℚ] ℂ) (B : Set (Fin p.natDegree))
    (C : ↥(orbitF p hsep B)) :
    (spolyL p hsep B).map (blkEmbedOrbit p hsep ι B C).toRingHom
      = (spoly p hsep C.1).map ι.toRingHom := by
  have hg := Classical.choose_spec ((mem_orbitF p hsep).mp C.2)
  have hσsmul : galFinHomN p hsep (galLift p hsep (Classical.choose ((mem_orbitF p hsep).mp C.2)))
      '' B = C.1 := by
    rw [← galLift_smul p hsep _ B, hg]
  have hp : (spoly p hsep B).map
      (galLift p hsep (Classical.choose ((mem_orbitF p hsep).mp C.2))).toRingHom
      = spoly p hsep C.1 := by
    rw [spoly_map_galN p hsep _ B, hσsmul]
  ext i
  rw [Polynomial.coeff_map, Polynomial.coeff_map]
  change (blkEmbedOrbit p hsep ι B C) ((spolyL p hsep B).coeff i)
      = ι ((spoly p hsep C.1).coeff i)
  rw [blkEmbedOrbit_apply, sfield_val_coeff, ← hp, Polynomial.coeff_map]
  rfl

lemma blkOrbit_setFin (B : Set (Fin p.natDegree)) :
    blkOrbit p hsep B
      = MulAction.orbit (↥(galImg p hsep)) (↑(setFin B) : Set (Fin p.natDegree)) := by
  rw [blkOrbit, coe_setFin]

/-- The cardinality of the orbit is the degree of the block field. -/
theorem card_orbitF_eq_finrank [Fact (Irreducible p)] (B : Set (Fin p.natDegree))
    (hB : MulAction.IsBlock (↥(galImg p hsep)) B) :
    (orbitF p hsep B).card = Module.finrank ℚ ↥(sfield p hsep B) := by
  have hB' : MulAction.IsBlock (↥(galImg p hsep)) (↑(setFin B) : Set (Fin p.natDegree)) := by
    rwa [coe_setFin]
  rw [orbitF_card, blkOrbit_setFin,
    ← finrank_blockField_eq_card_orbit p hsep (B := setFin B) hB']

/-- The cardinality of the orbit is the number of complex embeddings of the
block field. -/
theorem card_orbitF_eq_card_algHom [Fact (Irreducible p)] (B : Set (Fin p.natDegree))
    (hB : MulAction.IsBlock (↥(galImg p hsep)) B) :
    Fintype.card ↥(orbitF p hsep B)
      = Fintype.card (↥(sfield p hsep B) →ₐ[ℚ] ℂ) := by
  rw [Fintype.card_coe, card_orbitF_eq_finrank p hsep B hB,
    Commons.NumberTheory.NumberField.card_algHom_eq_finrank]

/-- **The orbit-to-embedding map is a bijection** (injectivity plus the
cardinality computation). -/
theorem blkEmbedOrbit_bijective [Fact (Irreducible p)] (ι : p.SplittingField →ₐ[ℚ] ℂ)
    (B : Set (Fin p.natDegree)) (hB : MulAction.IsBlock (↥(galImg p hsep)) B) :
    Function.Bijective (blkEmbedOrbit p hsep ι B) :=
  (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨blkEmbedOrbit_injective p hsep ι B, card_orbitF_eq_card_algHom p hsep B hB⟩

/-- **The norm identity for the imprimitive slice.**  For an irreducible
`p : ℚ[X]` with a block `B` of the naive Galois action, `p` is the product of
the conjugates of the block polynomial over its field of definition `L`:

`∏_{ψ : L →ₐ[ℚ] ℂ} ψ(P_L) = p.map (algebraMap ℚ ℂ)`.

In particular `p` is determined by the block polynomial `P_L` (over `L`), hence
by its `|B|` coefficients. -/
theorem normIdentity [Fact (Irreducible p)] (hmonic : p.Monic) {B : Set (Fin p.natDegree)}
    [MulAction.IsPretransitive (↥(galImg p hsep)) (Fin p.natDegree)]
    (hB : MulAction.IsBlock (↥(galImg p hsep)) B) (hne : B.Nonempty)
    (ι : p.SplittingField →ₐ[ℚ] ℂ) :
    (∏ ψ : (↥(sfield p hsep B) →ₐ[ℚ] ℂ), (spolyL p hsep B).map ψ.toRingHom)
      = p.map (algebraMap ℚ ℂ) := by
  have hkb := blkEmbedOrbit_bijective p hsep ι B hB
  have hkey := Fintype.prod_bijective (blkEmbedOrbit p hsep ι B) hkb
      (fun C : ↥(orbitF p hsep B) => (spoly p hsep C.1).map ι.toRingHom)
      (fun ψ : (↥(sfield p hsep B) →ₐ[ℚ] ℂ) => (spolyL p hsep B).map ψ.toRingHom)
      (fun C => (blkEmbedOrbit_map_spolyL p hsep ι B C).symm)
  have hf := spoly_factors p hsep hmonic hB hne
  rw [← hkey, ← Polynomial.map_prod, ← hf, Polynomial.map_map]
  have hcomp : ι.toRingHom.comp (algebraMap ℚ p.SplittingField) = algebraMap ℚ ℂ := by
    rw [AlgHom.toRingHom_eq_coe]
    exact AlgHom.comp_algebraMap ι
  rw [hcomp]

end

end Submission.Vdw
