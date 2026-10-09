import Mathlib
import Submission.Work.SSGRoute.ZSplit.levelK_reciprocity_baseChange
import Submission.Work.SSGRoute.ZConstruction.AuxInterface
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZConstruction

set_option linter.unusedSectionVars false

/-- **Transport of the unramified orthogonality to level `K`.**  (The same statement as
`SSGRoute/ZConstruction/unramifiedOrthogonal_lkPair`, proved here so that a `sorry`-free module can
be imported.)

If a pairing `pair'` on the cocycles of `G_{↥K} = (⊥ : IntermediateField ↥K Ω).fixingSubgroup` is
orthogonal on the two inertia-trivial classes at every finite place
(`Work.SSGRoute.IsUnramifiedOrthogonal` at the trivial extension `⊥`), then the transported
level-`K` pairing `Work.SSGRoute.ZSplit.lkPair p k Ω K pair'` is orthogonal on the inertia-trivial
level-`K` classes.

The proof is a direct transport along the base change `k ↝ ↥K`:

* the level-`K` local group `decomp k A ⊓ K.fixingSubgroup` is the `↥K`-decomposition group
  (`ZSplit.mapFix_kLocalGroup`), and `lkPair` at that group is `pair'` at the transported group
  (`ZSplit.lkPair_kLocalGroup`);
* the two cochain hypotheses (cocycle and local constancy) transport along
  `IntermediateField.fixingSubgroupEquiv K` (`ZSplit.KTransport.isCocycleOn_mapFix_iff`,
  `ZSplit.KTransport.isLocConstOn_mapFix_iff`), with the agreement hypothesis supplied by
  `ZSplit.restrFun_agree`;
* the two inertia hypotheses transport by `SSGRoute.isInertia_baseChange`;
* the finiteness of the place by `SSGRoute.isFinPlace_baseChange`. -/
theorem unramifiedOrthogonal_lkPairTransport (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (pair' : Subgroup (Ω ≃ₐ[↥K] Ω) → ((Ω ≃ₐ[↥K] Ω) → ZMod p) →
      ((Ω ≃ₐ[↥K] Ω) → ZMod p) → ZMod p)
    (hunr : Work.SSGRoute.IsUnramifiedOrthogonal (p := p)
      (K := (⊥ : IntermediateField ↥K Ω)) pair') :
    Work.SSGRoute.IsUnramifiedOrthogonal (p := p) (K := K)
      (Work.SSGRoute.ZSplit.lkPair p k Ω K pair') := by
  intro A hA a b ha hb hIa hIb
  rw [Work.SSGRoute.ZSplit.lkPair_kLocalGroup p k Ω K pair' A a b]
  refine hunr A ((Work.SSGRoute.isFinPlace_baseChange k Ω K A).mpr hA)
    (Work.SSGRoute.ZSplit.restrFun k Ω K (ZMod p) a)
    (Work.SSGRoute.ZSplit.restrFun k Ω K (ZMod p) b) ?_ ?_ ?_ ?_
  · -- the cocycle and local-constancy hypotheses for `a`
    refine ⟨?_, ?_⟩
    · rw [← Work.SSGRoute.ZSplit.mapFix_kLocalGroup k Ω K A]
      exact (Work.SSGRoute.ZSplit.KTransport.isCocycleOn_mapFix_iff k Ω K p
        (SSGRoute.decomp k A ⊓ K.fixingSubgroup) inf_le_right a _
        (fun x => Work.SSGRoute.ZSplit.restrFun_agree p k Ω K a x)).mp ha.1
    · rw [← Work.SSGRoute.ZSplit.mapFix_kLocalGroup k Ω K A]
      exact (Work.SSGRoute.ZSplit.KTransport.isLocConstOn_mapFix_iff k Ω K p
        (SSGRoute.decomp k A ⊓ K.fixingSubgroup) inf_le_right a _
        (fun x => Work.SSGRoute.ZSplit.restrFun_agree p k Ω K a x)).mp ha.2
  · -- the cocycle and local-constancy hypotheses for `b`
    refine ⟨?_, ?_⟩
    · rw [← Work.SSGRoute.ZSplit.mapFix_kLocalGroup k Ω K A]
      exact (Work.SSGRoute.ZSplit.KTransport.isCocycleOn_mapFix_iff k Ω K p
        (SSGRoute.decomp k A ⊓ K.fixingSubgroup) inf_le_right b _
        (fun x => Work.SSGRoute.ZSplit.restrFun_agree p k Ω K b x)).mp hb.1
    · rw [← Work.SSGRoute.ZSplit.mapFix_kLocalGroup k Ω K A]
      exact (Work.SSGRoute.ZSplit.KTransport.isLocConstOn_mapFix_iff k Ω K p
        (SSGRoute.decomp k A ⊓ K.fixingSubgroup) inf_le_right b _
        (fun x => Work.SSGRoute.ZSplit.restrFun_agree p k Ω K b x)).mp hb.2
  · -- the inertia-triviality of `a`
    intro σ _ hσ
    obtain ⟨u, rfl⟩ : ∃ u : ↥(K.fixingSubgroup),
        (IntermediateField.fixingSubgroupEquiv K) u = σ :=
      ⟨(IntermediateField.fixingSubgroupEquiv K).symm σ, MulEquiv.apply_symm_apply _ _⟩
    rw [Work.SSGRoute.ZSplit.restrFun_agree p k Ω K a u]
    exact hIa (u : Ω ≃ₐ[k] Ω) u.2
      ((Work.SSGRoute.isInertia_baseChange k Ω K A (u : Ω ≃ₐ[k] Ω) u.2).mp hσ)
  · -- the inertia-triviality of `b`
    intro σ _ hσ
    obtain ⟨u, rfl⟩ : ∃ u : ↥(K.fixingSubgroup),
        (IntermediateField.fixingSubgroupEquiv K) u = σ :=
      ⟨(IntermediateField.fixingSubgroupEquiv K).symm σ, MulEquiv.apply_symm_apply _ _⟩
    rw [Work.SSGRoute.ZSplit.restrFun_agree p k Ω K b u]
    exact hIb (u : Ω ≃ₐ[k] Ω) u.2
      ((Work.SSGRoute.isInertia_baseChange k Ω K A (u : Ω ≃ₐ[k] Ω) u.2).mp hσ)

end Work.SSGRoute.ZConstruction
