import Mathlib
import Submission.Vdw.BlockPoly
import Submission.Vdw.GaloisRamification
import Submission.Commons.FieldTheory.Galois.finrank_mul_card_fixingSubgroup_eq_card_algEquiv

open Polynomial
open scoped Pointwise

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# The structural dictionary of the imprimitive slice, I: roots and the
Galois action on block polynomials

For an irreducible `p : ℚ[X]` with splitting field `E = p.SplittingField` and a
block `B` of the natural Galois action on the `n = natDegree p` roots
(`rootFinEquiv`, `galFinHom`), `BlockPoly.blockPoly p hsep B` is the monic
degree-`|B|` polynomial over `E` whose roots are the roots indexed by `B`.

This module proves the first layer of the dictionary:

* `map_roots_eq` — the roots of `p` in `E` are exactly the indexed roots
  `rootOf p hsep i`, `i : Fin p.natDegree`;
* `map_eq_prod_rootOf` — the full factorisation
  `p.map (algebraMap ℚ E) = ∏ i, (X - C (rootOf p hsep i))`;
* `roots_blockPoly` — the roots of `blockPoly B` are the indexed roots of `B`;
* `blockPoly_injective` — `B ↦ blockPoly B` is injective (the roots determine
  the block);
* `gal_apply_rootOf` — `σ (rootOf i) = rootOf (galFinHom σ i)`;
* `blockPoly_map_gal` — **the Galois action on block polynomials**:
  `(blockPoly B).map σ.toRingHom = blockPoly (B.image (galFinHom σ))`.

Axioms: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw

noncomputable section

variable {p : ℚ[X]}

/-- **The roots of `p` in its splitting field are the indexed roots.**  The
root multiset of `p` (mapped into `E = p.SplittingField`) is the enumeration
`rootOf p hsep`. -/
lemma map_roots_eq (p : ℚ[X]) (hsep : p.Separable) :
    (p.map (algebraMap ℚ p.SplittingField)).roots =
      (Finset.univ.val.map (rootOf p hsep) : Multiset p.SplittingField) := by
  classical
  haveI : Fact ((p.map (algebraMap ℚ p.SplittingField)).Splits) :=
    ⟨Polynomial.SplittingField.splits p⟩
  have h1 : (p.map (algebraMap ℚ p.SplittingField)).roots.Nodup :=
    Polynomial.nodup_roots hsep.map
  have h2 : (Finset.univ.val.map (rootOf p hsep) : Multiset p.SplittingField).Nodup :=
    Multiset.Nodup.map (rootOf_injective p hsep) Finset.univ.nodup
  rw [(Multiset.Nodup.ext h1 h2)]
  intro x
  rw [Multiset.mem_map]
  constructor
  · intro hx
    have hx' : x ∈ p.rootSet p.SplittingField := by
      rw [Polynomial.rootSet_def, Polynomial.aroots_def, Finset.mem_coe,
        Multiset.mem_toFinset]
      exact hx
    obtain ⟨i, hi⟩ := (rootFinEquiv p hsep).symm.surjective ⟨x, hx'⟩
    refine ⟨i, Finset.mem_univ i, ?_⟩
    have hc := congrArg Subtype.val hi
    rw [rootOf]
    exact hc
  · rintro ⟨i, -, hi⟩
    have hmem : rootOf p hsep i ∈ p.rootSet p.SplittingField :=
      ((rootFinEquiv p hsep).symm i).2
    rw [Polynomial.rootSet_def, Polynomial.aroots_def, Finset.mem_coe,
      Multiset.mem_toFinset] at hmem
    rw [← hi]
    exact hmem

/-- **The full root factorisation of `p` in its splitting field.** -/
theorem map_eq_prod_rootOf (p : ℚ[X]) (hmonic : p.Monic) (hsep : p.Separable) :
    p.map (algebraMap ℚ p.SplittingField) =
      ∏ i : Fin p.natDegree, (X - C (rootOf p hsep i)) := by
  haveI : Fact ((p.map (algebraMap ℚ p.SplittingField)).Splits) :=
    ⟨Polynomial.SplittingField.splits p⟩
  have h := Polynomial.Splits.eq_prod_roots_of_monic (Polynomial.SplittingField.splits p)
    (hmonic.map (algebraMap ℚ p.SplittingField))
  calc p.map (algebraMap ℚ p.SplittingField)
      = ((p.map (algebraMap ℚ p.SplittingField)).roots.map (fun x => X - C x)).prod := h
    _ = ((Finset.univ.val.map (rootOf p hsep)).map (fun x => X - C x)).prod := by
        rw [map_roots_eq p hsep]
    _ = ∏ i : Fin p.natDegree, (X - C (rootOf p hsep i)) := by
        rw [Multiset.map_map, ← Finset.prod_eq_multiset_prod]
        rfl

/-- **The roots of the block polynomial.** -/
lemma roots_blockPoly (p : ℚ[X]) (hsep : p.Separable) (B : Finset (Fin p.natDegree)) :
    (blockPoly p hsep B).roots = B.val.map (rootOf p hsep) := by
  have hne : (∏ i ∈ B, (X - C (rootOf p hsep i)) : p.SplittingField[X]) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => X_sub_C_ne_zero _)
  rw [blockPoly, Polynomial.roots_prod _ _ hne]
  simp [Polynomial.roots_X_sub_C]

/-- **The block polynomial determines the block.** -/
lemma blockPoly_injective (p : ℚ[X]) (hsep : p.Separable) :
    Function.Injective (blockPoly p hsep) := by
  intro B B' h
  have hr : B.val.map (rootOf p hsep) = B'.val.map (rootOf p hsep) := by
    rw [← roots_blockPoly p hsep B, ← roots_blockPoly p hsep B', h]
  apply Finset.ext
  intro x
  have hm := congrArg (fun m : Multiset p.SplittingField => rootOf p hsep x ∈ m) hr
  simp only [Multiset.mem_map] at hm
  constructor
  · intro hx
    obtain ⟨a, ha, hax⟩ := hm.mp ⟨x, hx, rfl⟩
    rwa [rootOf_injective p hsep hax] at ha
  · intro hx
    obtain ⟨a, ha, hax⟩ := hm.mpr ⟨x, hx, rfl⟩
    rwa [rootOf_injective p hsep hax] at ha

/-- **The root indexing is Galois-equivariant**: `σ` applied to the `i`-th root
is the `galFinHom σ i`-th root.  (Reduced to the coercion lemma
`coe_galActionHom_self` for the permutation representation.) -/
lemma gal_apply_rootOf (p : ℚ[X]) (hsep : p.Separable) (σ : p.Gal)
    (hbridge : ∀ x : p.rootSet p.SplittingField,
        ((galRootPerm p σ x : p.rootSet p.SplittingField) : p.SplittingField)
          = σ (x : p.SplittingField))
    (i : Fin p.natDegree) :
    σ (rootOf p hsep i) = rootOf p hsep (galFinHom p hsep σ i) := by
  have h := galRootPerm_symm_rootOf p hsep σ i
  have h1 := hbridge ((rootFinEquiv p hsep).symm i)
  change σ (((rootFinEquiv p hsep).symm i : p.rootSet p.SplittingField) : p.SplittingField)
      = ((rootFinEquiv p hsep).symm (galFinHom p hsep σ i) : p.SplittingField)
  rw [← h1]
  exact congrArg Subtype.val h

/-- **The Galois action on the block polynomial**: the translate of the block
polynomial of `B` by `σ` is the block polynomial of the translate
`galFinHom σ '' B`. -/
lemma blockPoly_map_gal (p : ℚ[X]) (hsep : p.Separable) (σ : p.Gal)
    (hbridge : ∀ x : p.rootSet p.SplittingField,
        ((galRootPerm p σ x : p.rootSet p.SplittingField) : p.SplittingField)
          = σ (x : p.SplittingField))
    (B : Finset (Fin p.natDegree)) :
    (blockPoly p hsep B).map σ.toRingHom
      = blockPoly p hsep (B.image (galFinHom p hsep σ)) := by
  have hroot : ∀ i : Fin p.natDegree,
      σ (rootOf p hsep i) = rootOf p hsep (galFinHom p hsep σ i) :=
    fun i => gal_apply_rootOf p hsep σ hbridge i
  have h1 : ∀ i : Fin p.natDegree,
      (X - C (rootOf p hsep i)).map σ.toRingHom
        = X - C (rootOf p hsep (galFinHom p hsep σ i)) := by
    intro i
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    exact congrArg (fun y => X - C y) (hroot i)
  rw [blockPoly, blockPoly, Polynomial.map_prod]
  simp only [h1]
  rw [Finset.prod_image]
  intro x _ y _ hxy
  exact (galFinHom p hsep σ).injective hxy

/-- **The stabilizer of a block polynomial.**  A Galois element fixes the block
polynomial of `B` (coefficientwise) if and only if it preserves `B`. -/
lemma blockPoly_map_gal_eq_iff (p : ℚ[X]) (hsep : p.Separable) (σ : p.Gal)
    (hbridge : ∀ x : p.rootSet p.SplittingField,
        ((galRootPerm p σ x : p.rootSet p.SplittingField) : p.SplittingField)
          = σ (x : p.SplittingField))
    (B : Finset (Fin p.natDegree)) :
    (blockPoly p hsep B).map σ.toRingHom = blockPoly p hsep B
      ↔ B.image (galFinHom p hsep σ) = B := by
  rw [blockPoly_map_gal p hsep σ hbridge B]
  exact ⟨fun h => blockPoly_injective p hsep h, fun h => by rw [h]⟩

/-- The field of definition of the block `B`: the subfield of the splitting
field generated by the coefficients of the block polynomial. -/
def blockField (p : ℚ[X]) (hsep : p.Separable) (B : Finset (Fin p.natDegree)) :
    IntermediateField ℚ p.SplittingField :=
  IntermediateField.adjoin ℚ (Set.range fun i : Fin p.natDegree => (blockPoly p hsep B).coeff i)

/-- **The stabilizer of the block is the Galois group of the splitting field over
the field of definition.**  A Galois element fixes the block polynomial `B`
coefficientwise if and only if it fixes the field of definition pointwise. -/
lemma mem_blockField_fixingSubgroup_iff (p : ℚ[X]) (hsep : p.Separable)
    (B : Finset (Fin p.natDegree)) (σ : p.Gal)
    (hbridge : ∀ x : p.rootSet p.SplittingField,
        ((galRootPerm p σ x : p.rootSet p.SplittingField) : p.SplittingField)
          = σ (x : p.SplittingField)) :
    ((blockPoly p hsep B).map σ.toRingHom = blockPoly p hsep B)
      ↔ σ ∈ (blockField p hsep B).fixingSubgroup := by
  classical
  constructor
  · intro h
    refine (IntermediateField.mem_fixingSubgroup_iff (K := blockField p hsep B) σ).mpr ?_
    intro x hx
    have hc : ∀ i : Fin p.natDegree, σ ((blockPoly p hsep B).coeff i)
        = (blockPoly p hsep B).coeff i := by
      intro i
      have h1 := congrArg (fun Q : p.SplittingField[X] => Q.coeff (i : ℕ)) h
      rw [Polynomial.coeff_map] at h1
      exact h1
    have hle : IntermediateField.adjoin ℚ
        (Set.range fun i : Fin p.natDegree => (blockPoly p hsep B).coeff i)
        ≤ IntermediateField.fixedField (Subgroup.zpowers σ) := by
      refine IntermediateField.adjoin_le_iff.mpr ?_
      rintro y ⟨i, rfl⟩
      refine (IntermediateField.mem_fixedField_iff (H := Subgroup.zpowers σ) _).mpr ?_
      intro f hf
      have hmem : σ ∈ MulAction.stabilizer p.Gal ((blockPoly p hsep B).coeff i) := by
        rw [MulAction.mem_stabilizer_iff]
        exact hc i
      have hz : (f : p.Gal) ∈ MulAction.stabilizer p.Gal ((blockPoly p hsep B).coeff i) :=
        Subgroup.zpowers_le.mpr hmem hf
      have hz' : (f : p.Gal) • ((blockPoly p hsep B).coeff i) = ((blockPoly p hsep B).coeff i) :=
        MulAction.mem_stabilizer_iff.mp hz
      exact hz'
    exact ((IntermediateField.mem_fixedField_iff (H := Subgroup.zpowers σ) x).mp (hle hx)) σ
      (Subgroup.mem_zpowers σ)
  · intro h
    have hx : ∀ y ∈ blockField p hsep B, σ y = y :=
      (IntermediateField.mem_fixingSubgroup_iff (K := blockField p hsep B) σ).mp h
    ext i
    rw [Polynomial.coeff_map]
    have hcard : B.card ≤ p.natDegree := by
      simpa using Finset.card_le_univ B
    by_cases hi : i < p.natDegree
    · exact hx _ (IntermediateField.subset_adjoin ℚ (Set.range fun j : Fin p.natDegree =>
        (blockPoly p hsep B).coeff j)
        (Set.mem_range_self (⟨i, hi⟩ : Fin p.natDegree)))
    · push Not at hi
      have hnd : (blockPoly p hsep B).natDegree ≤ i :=
        le_trans (by rw [blockPoly_natDegree]; exact hcard) hi
      rcases lt_or_eq_of_le hnd with hlt | heq
      · have h0 : (blockPoly p hsep B).coeff i = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt hlt
        rw [h0, map_zero]
      · have h1 : (blockPoly p hsep B).coeff i = 1 := by
          rw [← heq, Polynomial.coeff_natDegree,
            (blockPoly_monic p hsep B).leadingCoeff]
        rw [h1, map_one]

/-! ## The degree of the field of definition (next step)

The remaining dictionary statement is

`Module.finrank ℚ ↥(blockField p hsep B) = m`,   `m := #(orbit of B)`,

which follows from

* `Commons.FieldTheory.Galois.finrank_mul_card_fixingSubgroup_eq_card_algEquiv`:
  `finrank ℚ ↥L * Nat.card (L.fixingSubgroup) = Nat.card (E ≃ₐ[ℚ] E)`;
* the orbit-stabiliser theorem in the image group `H = (galFinHom p hsep).range`
  (`MulAction.card_orbit_mul_card_stabilizer_eq_card_group`);
* `hstab` — the identification of `(blockField p hsep B).fixingSubgroup` with
  the block stabiliser, which is `mem_blockField_fixingSubgroup_iff` together
  with `blockPoly_map_gal_eq_iff`;
* `Nat.card ↥H = Nat.card p.Gal` (`galFinHom_injective`).

The proof is a cardinality computation: from
`finrank * |fixL| = |G| = |H| = |orbit| * |stab|` and `|fixL| = |stab|`
one concludes `finrank = |orbit|`.  It is a pure plumbing exercise (the
coercions of `Subgroup` subtypes have to be normalised with
`Subgroup.coe_subtype`/`Subtype.coe_mk`); the statement and the reduction are
recorded here rather than completed.

The definition of `m` used in the imprimitive slice is
`(MulAction.orbit (irrGalFinHom f).range B).ncard` (see
`ImprimitiveBlock.imprimitiveBad_has_block`), and `|orbit H B| = |orbit G B|`.
-/

end

end Submission.Vdw
