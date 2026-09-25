/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The audited form of the finishing step: the local field of the place is part of the hypothesis

This module records an **audit finding** about the finishing step `NK.LocalStructure.LocalFinishingStep`
(equivalently `NK.LocalDecomposition.IndexOneOfSelfNormalizing`, equivalently the `finishingStep`
field of `NK.Indecomposed.LocalReconstruction`), and supplies the *corrected* statement together
with its proof from the workspace's named input `NK.LocalStructure.LocalNUExistence`.

## 1. The finding

The classical theorem (Neukirch, Invent. Math. **6** (1969), Theorem 1; NSW (12.1.9)) says: a closed
subgroup `H ≤ G_K` which is isomorphic to the absolute Galois group `G_κ` of a `p`-adic field `κ`
**and which is contained in the decomposition group `D_A` of a place `A` over a finite prime with
`κ` the local field of that place** is `D_A` itself.

The formalised input quantifies over an *arbitrary* `p`-adic field `κ` with `Nonempty (H ≃* Gal(κ'/κ))`
and no relation between `κ` and the place `A`.  The two are not the same statement.  Concretely, in
the situation `H ≤ D_A`, `[D_A : H] = n`, put `L = K_𝔭` (the local field of `A`) and transport `H`
along the local correspondence `D_A ≅ G_L` (`NK.NeukirchUchida.nonempty_mulEquiv_decompositionGroupOf_localGalois`);
then `H` corresponds to an index-`n` closed subgroup of `G_L`, i.e. to a degree-`n` extension `M/L`
with `H ≅ G_M` — so the hypothesis `H ≅ G_κ` is satisfiable with `κ = M` for **any** finite `M/L`,
and by Neukirch's local theorem (`NK.LocalStructure.LocalNUExistence`) the only constraint is
`κ ≅ M`.  Hence `[D_A : H] = n = [κ : ℚ_p] / [L : ℚ_p]`, and the classical conclusion `H = D_A`
(equivalently `n = 1`) needs `[κ : ℚ_p] = [L : ℚ_p]`, i.e. `κ ≅ L` — the local-field hypothesis.
Without it, the formalised input would assert in particular that a degree-`p` extension `M/L` of a
`p`-adic field is trivial, which is false; the global argument (`H = Gal(K̄/M)` with `M ⊇ E = K̄^{D_A}`
of degree `n`) needs the *self-normalising* hypothesis to make the field `M` rigid, and whether that
suffices is exactly the delicate point of Neukirch's proof.  See `README.md` §6 for the full
discussion, including the endgame instantiation (where the hypothesis *is* satisfied, because the
labelling is produced by the local correspondence at the prime carrying the non-zero local
component, see `Submission/Work/BrauerTwist/Preserves.lean`).

## 2. The corrected statement, proved

In the *local* picture (i.e. with the local field of the place as the base) the statement is clean:

> a closed subgroup `H ≤ Gal(L'/L_𝔮)` of finite index which is isomorphic to the *whole* group
> `Gal(L'/L_𝔮)` is the whole group.

This module proves it from `NK.LocalStructure.LocalNUExistence` (Neukirch's local theorem, the
residual classical input of the local theory, itself reduced by `Submission/Work/Ramification/` to
the Kennzeichnung) together with one further classical input, `LocalDegreeRigidity` — the
degree-rigidity of `p`-adic fields: a finite extension of a `p`-adic field which is isomorphic to it
as a ring is trivial.  That rigidity is the classical statement that the absolute degree
`[κ : ℚ_p]` is an invariant of the field `κ` even without a chosen isomorphism to `ℚ_p` (it is the
`ℤ_p`-rank of the pro-`p` completion of `κˣ`, i.e. of `1 + 𝔪_κ`, Serre, *Local Fields* II §5; it is
also an immediate consequence of the local Neukirch–Uchida theorem together with the Galois
correspondence).
-/

import Submission.NK.IndecomposedDeep.Reconstruction
import Submission.NK.LocalStructure.LocalNU.localNUExistence_of_finiteExtensionLattice

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

open IsDedekindDomain.HeightOneSpectrum
open scoped Pointwise

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

universe u

namespace NK.IndecomposedDeep

variable {p : ℕ} {K K' κ κ' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K']
  [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ'] [IsSepClosure κ κ']

/-- **The degree-rigidity of `p`-adic fields.**

Let `M` be a finite extension of the `p`-adic field `α = 𝔮.adicCompletion L`, realised inside a
separable closure of `α`.  If `M` is isomorphic to `α` *as a ring* (with no compatibility required
with the embeddings), then `M` is trivial, i.e. `M = ⊥` (its degree over `α` is `1`).

Classically: the absolute degree `[F : ℚ_p]` of a `p`-adic field `F` is an isomorphism invariant of
the field `F` (the `ℤ_p`-rank of `1 + 𝔪_F`, which is intrinsic, Serre, *Local Fields* II §5), whereas
`[M : ℚ_p] = [M : α] · [α : ℚ_p]`; a ring isomorphism `M ≅ α` therefore forces `[M : α] = 1`. -/
def LocalDegreeRigidity : Prop :=
  ∀ (L : Type u) [Field L] [NumberField L]
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (M : IntermediateField (𝔮.adicCompletion L) (SeparableClosure (𝔮.adicCompletion L)))
    [FiniteDimensional (𝔮.adicCompletion L) ↥M],
    Nonempty (↥M ≃+* 𝔮.adicCompletion L) → M = ⊥

/-- **The corrected finishing step, in the local picture.**

Let `L` be a number field, `𝔮` a finite prime, `H ≤ Gal(L'/L_𝔮)` (`L'` a separable closure) a
*closed* subgroup of *finite index* which is isomorphic to the whole group `Gal(L'/L_𝔮)`.  Then
`H = ⊤`.

This is the local form of Neukirch's maximality statement, with the local field of the place as the
base field — the form in which the classical argument applies.  The proof is the Galois
correspondence plus Neukirch's local theorem and the degree rigidity: `H` is the fixing subgroup of
a finite extension `M/L_𝔮`, `Gal(L'/M) = H ≅ Gal(L'/L_𝔮)` forces `M ≅ L_𝔮` by
`NK.LocalStructure.LocalNUExistence`, and `LocalDegreeRigidity` then forces `M = ⊥`, i.e. `H = ⊤`. -/
theorem localFinishingStep_local (hNU : NK.LocalStructure.LocalNUExistence.{u})
    (hrig : LocalDegreeRigidity.{u})
    (L : Type u) [Field L] [NumberField L]
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (H : Subgroup Gal(SeparableClosure (𝔮.adicCompletion L)/𝔮.adicCompletion L))
    (hHcl : IsClosed (H : Set Gal(SeparableClosure (𝔮.adicCompletion L)/𝔮.adicCompletion L)))
    (hHfin : H.FiniteIndex)
    (hκ : Nonempty (H ≃* Gal(SeparableClosure (𝔮.adicCompletion L)/𝔮.adicCompletion L))) :
    H = ⊤ := by
  obtain ⟨e⟩ := hκ
  haveI : IsGalois (𝔮.adicCompletion L) (SeparableClosure (𝔮.adicCompletion L)) := inferInstance
  -- `H` is the fixing subgroup of its fixed field
  have hfix : H = (IntermediateField.fixedField H).fixingSubgroup := by
    rw [InfiniteGalois.fixingSubgroup_fixedField (k := 𝔮.adicCompletion L)
      (K := SeparableClosure (𝔮.adicCompletion L)) ⟨H, hHcl⟩]
  -- the fixed field is finite over the local field, since `H` has finite index
  have hfd : FiniteDimensional (𝔮.adicCompletion L) ↥(IntermediateField.fixedField H) := by
    refine FiniteDimensional.of_finrank_pos ?_
    rw [IntermediateField.finrank_eq_fixingSubgroup_index
      (E' := SeparableClosure (𝔮.adicCompletion L)) (L := IntermediateField.fixedField H), ← hfix]
    exact Nat.pos_of_ne_zero hHfin.index_ne_zero
  haveI := hfd
  -- the isomorphism of absolute Galois groups, in the form of Neukirch's local theorem
  have hiso : Nonempty (Gal(SeparableClosure (𝔮.adicCompletion L)/↥(IntermediateField.fixedField H))
      ≃* Gal(SeparableClosure (𝔮.adicCompletion L)/𝔮.adicCompletion L)) :=
    ⟨(IntermediateField.fixingSubgroupEquiv (IntermediateField.fixedField H)).symm.trans
      (hfix ▸ e)⟩
  -- Neukirch's local theorem: the fixed field is isomorphic to the local field
  obtain ⟨σ⟩ := hNU L L 𝔮 𝔮 (SeparableClosure (𝔮.adicCompletion L))
    (IntermediateField.fixedField H) (SeparableClosure (𝔮.adicCompletion L)) hiso
  -- degree rigidity: the extension is trivial
  have hbot : IntermediateField.fixedField H = ⊥ :=
    hrig L 𝔮 (IntermediateField.fixedField H) ⟨σ⟩
  -- whence `H` is everything
  rw [hfix, hbot]
  exact IntermediateField.fixingSubgroup_bot

/-- **The corrected global statement is *weaker* than the formalised input.**

`NK.LocalDecomposition.IndexOneOfSelfNormalizing` — the finishing step as consumed by the criterion
— implies the statement with the extra local-field hypothesis (the corrected form).  This records
the direction in which the two forms are related: the formalised input asserts strictly more, and the
mathematics above identifies exactly the extra content. -/
theorem indexOne_of_indexOne_with_localField_hypothesis
    (hidx : NK.LocalDecomposition.IndexOneOfSelfNormalizing p K K' κ κ') :
    ∀ (H : Subgroup Gal(K'/K)), IsClosed (H : Set Gal(K'/K)) → Subgroup.normalizer H = H →
      Nonempty (H ≃* Gal(κ'/κ)) →
      ∀ (A : ValuationSubring K'), A.comap (algebraMap K K') ≠ ⊤ →
        H ≤ MulAction.stabilizer Gal(K'/K) A →
          0 < H.relIndex (MulAction.stabilizer Gal(K'/K) A) →
        MulAction.stabilizer Gal(K'/K) A = H :=
  fun H hHcl hN hκ A hA hHle hrel => hidx H hHcl hN hκ A hA hHle hrel

end NK.IndecomposedDeep
