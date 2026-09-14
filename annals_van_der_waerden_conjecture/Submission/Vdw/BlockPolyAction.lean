import Mathlib
import Submission.Vdw.BlockAction
import Submission.Vdw.BlockPolyGalois

open Polynomial
open scoped Pointwise

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# The structural dictionary of the imprimitive slice, for the naive action

This module transfers the block-polynomial dictionary
(`Submission.Vdw.BlockPolyGalois`) from Mathlib's conjugated Galois action to
the naive action `galFinHomN` of `Submission.Vdw.BlockAction`, so that no
`hbridge` hypothesis is needed:

* `blockPoly_map_galN` — `σ • P_B = P_{σ • B}`;
* `blockPoly_mapN_eq_iff` — the coefficientwise stabilizer is the setwise one;
* `mem_blockField_fixingSubgroup_iffN` — the stabilizer is the fixing subgroup
  of the block field `L`;
* `blockPolyL` — the block polynomial with coefficients in `L`, and
* `blockPoly_factors` — the product over the full block system,
  `p.map (algebraMap ℚ E) = ∏_{blocks} P_C`.

Axioms: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw

noncomputable section

/-! ## The Galois action on block polynomials -/

/-- **The Galois action on the block polynomial** (naive action): the translate
of the block polynomial of `B` by `σ` is the block polynomial of the translate
`galFinHomN σ '' B`. -/
lemma blockPoly_map_galN (p : ℚ[X]) (hsep : p.Separable) (σ : p.Gal)
    (B : Finset (Fin p.natDegree)) :
    (blockPoly p hsep B).map σ.toRingHom
      = blockPoly p hsep (B.image (galFinHomN p hsep σ)) := by
  have hroot : ∀ i : Fin p.natDegree,
      σ (rootOf p hsep i) = rootOf p hsep (galFinHomN p hsep σ i) :=
    fun i => gal_apply_rootOfN p hsep σ i
  have h1 : ∀ i : Fin p.natDegree,
      (X - C (rootOf p hsep i)).map σ.toRingHom
        = X - C (rootOf p hsep (galFinHomN p hsep σ i)) := by
    intro i
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    exact congrArg (fun y => X - C y) (hroot i)
  rw [blockPoly, blockPoly, Polynomial.map_prod]
  simp only [h1]
  rw [Finset.prod_image]
  intro x _ y _ hxy
  exact (galFinHomN p hsep σ).injective hxy

/-- **The stabilizer of a block polynomial** (naive action): a Galois element
fixes the block polynomial of `B` (coefficientwise) if and only if it preserves
`B`. -/
lemma blockPoly_mapN_eq_iff (p : ℚ[X]) (hsep : p.Separable) (σ : p.Gal)
    (B : Finset (Fin p.natDegree)) :
    (blockPoly p hsep B).map σ.toRingHom = blockPoly p hsep B
      ↔ B.image (galFinHomN p hsep σ) = B := by
  rw [blockPoly_map_galN p hsep σ B]
  exact ⟨fun h => blockPoly_injective p hsep h, fun h => by rw [h]⟩

/-- **The stabilizer of the block is the Galois group of the splitting field
over the field of definition** (naive action). -/
lemma mem_blockField_fixingSubgroup_iffN (p : ℚ[X]) (hsep : p.Separable)
    (B : Finset (Fin p.natDegree)) (σ : p.Gal) :
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

end

end Submission.Vdw
