import Mathlib
import Submission.Work.Thom.localThom_eq_of_cover
import Submission.Work.Thom.localThom_union
import Submission.Work.Thom.localThomMap_pdCohMap
import Submission.Work.Thom.Coh_zero_cover_injective_gen

open Work.TangentClasses CategoryTheory CategoryTheory.Limits

namespace Work.Thom

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type}

/-- **Two local Thom classes over a piece which agree on those pieces of an open cover that lie
inside the piece are equal.**

This is `Work.Thom.localThom_eq_of_cover` with the hypothesis `hVsub : ∀ k, V k ⊆ P` weakened to
`hVsub : ∀ k ∈ S, V k ⊆ P`: only the pieces `V k` with `k ∈ S` are used (the cover `hcov` and the
two restrictions `hτk`, `hag` are all indexed by `k ∈ S`), so the pieces outside `S` need not lie in
`P`.  This is the form needed in the finite-cover induction, where the cover pieces are
`U k ∩ U a` for `k ∈ T` and `U k ⊄ W` for `k ∉ T`.

PROOF: this is a one-line corollary of the already-proven `Work.Thom.localThom_eq_of_cover`
(`Submission/Work/Thom/localThom_eq_of_cover.lean`).  Reindex to the subtype `{k // k ∈ S}`: put
`V' j := V j.1`, `S' := Finset.univ`, `hVsub' j := hVsub j.1 j.2`, convert `hcov` into
`P ⊆ ⋃ j, V' j` (`Set.biUnion_univ` and `Set.iUnion_subtype`, or an `ext`/`simp` argument), and
feed `fun j => hτk j.1 j.2` and `fun j => hag j.1 j.2` to the old lemma. -/
theorem localThom_eq_of_cover_rel {ι' : Type} (Z : RealBundle B F ι) (n : ℕ)
    {P : Set B} (V : ι' → Set B) (hVopen : ∀ k, IsOpen (V k))
    (S : Finset ι') (hVsub : ∀ k ∈ S, V k ⊆ P) (hcov : P ⊆ ⋃ k ∈ (S : Set ι'), V k)
    (τ τ' : Work.Thom.PieceCoh Z P n)
    (hτ : Function.Bijective (Work.Thom.localThomMap Z n P τ 0))
    (hτk : ∀ (k : ι') (hk : k ∈ S), Function.Injective (Work.Thom.localThomMap Z n (V k)
        ((Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
          (Z.proj ⁻¹' P) (Z.proj ⁻¹' (V k)) (Set.preimage_mono (hVsub k hk)) n).hom τ) 0))
    (hag : ∀ (k : ι') (hk : k ∈ S), (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace)
          (Work.Thom.zeroComplement Z) (Z.proj ⁻¹' P) (Z.proj ⁻¹' (V k))
          (Set.preimage_mono (hVsub k hk)) n).hom τ'
        = (Work.Cohomology.pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
          (Z.proj ⁻¹' P) (Z.proj ⁻¹' (V k)) (Set.preimage_mono (hVsub k hk)) n).hom τ) :
    τ' = τ := by
  classical
  -- Reindex the cover to the subtype of indices lying in `S`; there the full-subset condition
  -- `∀ k, V k ⊆ P` holds, so the original lemma applies.
  have hcov' : P ⊆ ⋃ j ∈ (Finset.univ : Finset {k : ι' // k ∈ S}), V j.1 := by
    intro x hx
    have hx' : x ∈ ⋃ k ∈ (S : Set ι'), V k := hcov hx
    simp only [Set.mem_iUnion] at hx' ⊢
    obtain ⟨k, hk, hxk⟩ := hx'
    exact ⟨⟨k, hk⟩, Finset.mem_univ _, hxk⟩
  exact localThom_eq_of_cover Z n (fun j : {k : ι' // k ∈ S} => V j.1)
    (fun j => hVopen j.1) (fun j => hVsub j.1 j.2) Finset.univ hcov' τ τ' hτ
    (fun j _ => hτk j.1 j.2) (fun j _ => hag j.1 j.2)


end Work.Thom
