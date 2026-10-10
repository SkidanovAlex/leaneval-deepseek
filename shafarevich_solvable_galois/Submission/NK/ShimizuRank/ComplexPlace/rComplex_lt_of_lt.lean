import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Submission.NK.ShimizuRank.Basic
import Submission.NK.ShimizuRank.ComplexPlace.nrComplexPlaces_lt_of_finrank_lt
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.ShimizuRank.ComplexPlace

attribute [local instance] NK.Reconstruct.NumFieldIn.finite NK.Reconstruct.NumFieldIn.numberField

/-
**Shimizu's Lemma 4f.2, arithmetic half, in the `NumFieldIn` form used by the rank inputs.**

For number-field levels `M ⊆ N` of a separable closure `Ω` of `ℚ` with `M ≠ N` and `N` having a
complex prime, the number of complex places strictly increases.  This is the statement consumed by
`NK.ShimizuRank.rankStrictMonoLevelInputGen_of_leopoldt`.

Here `NK.Reconstruct.NumFieldIn ℚ Ω` (module `Submission/Work/Reconstruct/NumFieldIn.lean`) has
field `L : IntermediateField ℚ Ω` and instances `NumFieldIn.finite` / `NumFieldIn.numberField`
(declared as local instances by the `attribute` line above), and
`NK.Reconstruct.rComplex K := Nat.card {v : NumberField.InfinitePlace K // IsComplex v}`.

Intended proof.  Build the relative algebra structure `Algebra ↥M.L ↥N.L` from the inclusion
`fun x => ⟨x.1, h x.2⟩` (`RingHom.toAlgebra`); the same pattern appears in
`NK.Reconstruct.numberField_complex_of_le` in `Submission/Work/Reconstruct/fourf5Gen.lean`.
Transport `FiniteDimensional ↥M.L ↥N.L` (from `Module.Finite.of_restrictScalars_finite ℚ ↥M.L ↥N.L`
plus `Module.Finite.finiteDimensional` for a field extension).  Show `1 < Module.finrank ↥M.L ↥N.L`:
`hne` together with `h` gives `x ∈ N.L` with `x ∉ M.L`, so `↥M.L ∙ 1 ≠ ⊤` as a
`Submodule ↥M.L ↥N.L` and `Submodule.finrank_lt` gives
`1 = Module.finrank ↥M.L (↥M.L ∙ 1) < Module.finrank ↥M.L ↥N.L`.
Then apply `NK.ShimizuRank.ComplexPlace.nrComplexPlaces_lt_of_finrank_lt` and identify
`rComplex K = NumberField.InfinitePlace.nrComplexPlaces K` (`Nat.card` of a finite subtype is the
`Finset.card` of the corresponding `univ.filter`; `Fintype.card_subtype` does the rewriting).

Please declare the result in namespace `NK.ShimizuRank.ComplexPlace` (module
`Submission.NK.ShimizuRank.ComplexPlace.rComplex_lt_of_lt`).

Implementation note.  Rather than the *type* `↥N.L` as the top of the relative tower, the proof
uses the intermediate field `IntermediateField.extendScalars h : IntermediateField ↥M.L Ω`, whose
carrier is `N.L`; this is the shape in which the `ℚ`-scalar tower `ℚ ≤ ↥M.L ≤ ·` is found
automatically by the `IntermediateField` instances (see
`NK.Reconstruct.isFrobElementAt_restrictScalars_of_inertiaDeg_eq_one`).  Since
`IntermediateField.mem_extendScalars` is `Iff.rfl`, the types `↥(extendScalars h)` and `↥N.L` are
definitionally equal, so the conclusion transfers by `rfl`.
-/
theorem rComplex_lt_of_lt {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
    (M N : NK.Reconstruct.NumFieldIn ℚ Ω) [IsSepClosure ↥M.L Ω] [IsSepClosure ↥N.L Ω]
    (h : M.L ≤ N.L) (hne : M.L ≠ N.L)
    (hv : ∃ v : NumberField.InfinitePlace ↥N.L, NumberField.InfinitePlace.IsComplex v) :
    NK.Reconstruct.rComplex ↥M.L < NK.Reconstruct.rComplex ↥N.L := by
  classical
  -- The relative level `N` viewed over `↥M.L`.
  let LLsub : IntermediateField ↥M.L Ω := IntermediateField.extendScalars h
  haveI : Module.Finite ℚ ↥LLsub := N.finite
  haveI hfin : FiniteDimensional ↥M.L LLsub :=
    Module.Finite.of_restrictScalars_finite ℚ ↥M.L ↥LLsub
  haveI hnf : NumberField ↥LLsub := inferInstanceAs (NumberField ↥N.L)
  -- The relative degree is `> 1`: `M.L ≠ N.L`.
  have h1 : 1 < Module.finrank ↥M.L LLsub := by
    have hlt : M.L < N.L := lt_of_le_of_ne h hne
    obtain ⟨x, hxN, hxM⟩ := Set.exists_of_ssubset hlt
    let y : ↥LLsub := ⟨x, hxN⟩
    have hy : y ∉ Set.range (algebraMap ↥M.L ↥LLsub) := by
      rintro ⟨a, ha⟩
      have hval : (a : Ω) = x := congrArg Subtype.val ha
      exact hxM (hval ▸ a.2)
    have hp : (↥M.L ∙ (1 : ↥LLsub)) ≠ ⊤ := by
      intro hp
      have : y ∈ (↥M.L ∙ (1 : ↥LLsub)) := by rw [hp]; trivial
      rw [Submodule.mem_span_singleton] at this
      obtain ⟨a, ha⟩ := this
      exact hy ⟨a, by rw [← ha, Algebra.algebraMap_eq_smul_one]⟩
    have hspan : Module.finrank ↥M.L ↥(↥M.L ∙ (1 : ↥LLsub)) = 1 :=
      finrank_span_singleton (K := ↥M.L) (v := (1 : ↥LLsub)) one_ne_zero
    have := Submodule.finrank_lt (K := ↥M.L) (V := ↥LLsub) hp
    omega
  -- The counting lemma for a nontrivial extension with a complex prime.
  have hv' : ∃ v : NumberField.InfinitePlace ↥LLsub, NumberField.InfinitePlace.IsComplex v := hv
  have hmain := nrComplexPlaces_lt_of_finrank_lt (K := ↥M.L) (L := ↥LLsub) h1 hv'
  -- `rComplex` is `nrComplexPlaces`.
  have hM : NK.Reconstruct.rComplex ↥M.L = NumberField.InfinitePlace.nrComplexPlaces ↥M.L := by
    rw [NK.Reconstruct.rComplex, NumberField.InfinitePlace.nrComplexPlaces,
      Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hN : NK.Reconstruct.rComplex ↥N.L = NumberField.InfinitePlace.nrComplexPlaces ↥N.L := by
    rw [NK.Reconstruct.rComplex, NumberField.InfinitePlace.nrComplexPlaces,
      Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hM, hN]
  exact hmain

end NK.ShimizuRank.ComplexPlace
