import Submission.NK.Mine.EndgameWiring
import Submission.NK.Mine.ResidueCharAutomatic
import Submission.NK.Mine.finiteIndex_isClosed_of_towerRankCore
import Submission.NK.LocalStructure.Tower.other_bounded_of_towerCore
import Submission.NK.LocalStructure.Tower.proP_unbounded_of_towerCore
import Submission.NK.LocalStructure.Tower.other_bounded_of_towerCore
import Submission.NK.LocalInputs.PowerQuotient.localFieldInputs_of_prime
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The corrected local bundle from the tower ranks and local reciprocity alone

*SUPERSEDED* (session 27, later) as the capstone: see
`NK.Mine.neukirch_uchida_of_finalLeaves` (`Submission/Work/Mine/FinalLeaves.lean`), which uses the
same block-(ii) reduction `NK.Mine.localGaloisInputsTop_of_coreData` *and* the sharpened block-(i)
of `Submission/Work/Indecomposed/`.  The block-(ii) reduction proved here remains the one to use.

`NK.PTorsionTop.LocalGaloisInputsTop K 𝔭 K' p` (the corrected local structure bundle consumed by
the `(a)`-chain) has five fields: `hp`, `proP_unbounded`, `other_bounded`, `abelian_rank`,
`reciprocity`.  This file *derives* the first four of the last four from the two chapters that are
already on disk:

* the two **tower-rank** fields from `NK.LocalStructure.TowerRankCore K 𝔭 K' p`
  (`NK.LocalStructure.Tower.proP_unbounded_of_towerCore`,
  `other_bounded_of_towerCore`) — the residual of which is the counting of extensions of the finite
  extensions of `κ`, plus Nikolov–Segal;
* the **abelian rank** `d + 1 + δ` from the reciprocity datum `NK.LocalCFT.ArtinReciprocity`
  (`NK.Mine.hasAbelianFrattiniRank_of_artinReciprocity`) together with the *proved* power-class
  count `NK.LocalInputs.PowerQuotient.localFieldInputs_of_prime`
  (`NK.LocalInputs.hasFrattiniRank_completionUnits_adicCompletion`) — the openness hypothesis is
  Nikolov–Segal for `κˣ`, and follows from `TowerRankCore.finiteIndex_isClosed` via
  `Subgroup.isOpen_of_isClosed_of_finiteIndex` (the transport along `botGalEquiv` is left explicit
  here because it is only used in this shape).

Consequently `LocalGaloisInputsTop` is equivalent to

  `p.Prime` + `CharP (ResidueField (𝔭.adicCompletionIntegers K)) p`
  + `TowerRankCore K 𝔭 K' p` + `Nonempty (ArtinReciprocity (𝔭.adicCompletion K) K')`
  + openness (Nikolov–Segal),

and `NK.Mine.neukirch_uchida_of_reducedInputs` below is the whole challenge theorem with the two
per-prime blocks stated in that reduced vocabulary.
-/

namespace NK.Mine

open scoped Pointwise
open IsDedekindDomain.HeightOneSpectrum

universe u

/-- **The corrected local bundle from the tower ranks, local reciprocity and the arithmetic of the
local field.** -/
theorem localGaloisInputsTop_of_coreData {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type u}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K'] {p : ℕ}
    (hp : p.Prime)
    (hres : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p)
    (hT : NK.LocalStructure.TowerRankCore K 𝔭 K' p)
    (hD : Nonempty (NK.LocalCFT.ArtinReciprocity (𝔭.adicCompletion K) K'))
    (hopen : ∀ H : Subgroup (Gal(K'/𝔭.adicCompletion K)), H.index = p → H.Normal →
      IsOpen (H : Set (Gal(K'/𝔭.adicCompletion K)))) :
    NK.PTorsionTop.LocalGaloisInputsTop K 𝔭 K' p where
  hp := hp
  proP_unbounded := NK.LocalStructure.Tower.proP_unbounded_of_towerCore 𝔭 hT
  other_bounded := NK.LocalStructure.Tower.other_bounded_of_towerCore 𝔭 hT
  abelian_rank := by
    haveI : IsGalois (𝔭.adicCompletion K) K' := IsSepClosure.isGalois
    exact hasAbelianFrattiniRank_of_artinReciprocity (Classical.choice hD) hopen
      (NK.LocalInputs.hasFrattiniRank_completionUnits_adicCompletion 𝔭
        (NK.LocalInputs.PowerQuotient.localFieldInputs_of_prime 𝔭 hp hres))
  reciprocity := hD

section Capstone

variable {K₁ K₂ K₁' K₂' : Type u} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

theorem neukirch_uchida_of_reducedInputs
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ)
    (hB₁ : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁)),
      ∃ p : ℕ, p.Prime ∧
        NK.BrauerTwist.LocalH2Input p K₂ K₂'
          (𝔭.adicCompletion K₁) (SeparableClosure (𝔭.adicCompletion K₁)) ∧
        NK.HasseTwist.Sha2Input p K₂ K₂'
          (𝔭.adicCompletion K₁) (SeparableClosure (𝔭.adicCompletion K₁)) ∧
        NK.BrauerTwist.LocalDecompositionCriterion p K₂ K₂'
          (𝔭.adicCompletion K₁) (SeparableClosure (𝔭.adicCompletion K₁)))
    (hB₂ : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂)),
      ∃ p : ℕ, p.Prime ∧
        NK.BrauerTwist.LocalH2Input p K₁ K₁'
          (𝔮.adicCompletion K₂) (SeparableClosure (𝔮.adicCompletion K₂)) ∧
        NK.HasseTwist.Sha2Input p K₁ K₁'
          (𝔮.adicCompletion K₂) (SeparableClosure (𝔮.adicCompletion K₂)) ∧
        NK.BrauerTwist.LocalDecompositionCriterion p K₁ K₁'
          (𝔮.adicCompletion K₂) (SeparableClosure (𝔮.adicCompletion K₂)))
    (k₁ : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁)),
      ∃ p : ℕ, p.Prime ∧
        CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K₁)) p ∧
        NK.LocalStructure.TowerRankCore K₁ 𝔭
          (SeparableClosure (𝔭.adicCompletion K₁)) p ∧
        Nonempty (NK.LocalCFT.ArtinReciprocity (𝔭.adicCompletion K₁)
          (SeparableClosure (𝔭.adicCompletion K₁))) ∧
        (∀ H : Subgroup (Gal(SeparableClosure (𝔭.adicCompletion K₁)/𝔭.adicCompletion K₁)),
          H.index = p → H.Normal →
            IsOpen (H : Set (Gal(SeparableClosure (𝔭.adicCompletion K₁)/𝔭.adicCompletion K₁)))))
    (k₂ : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂)),
      ∃ q : ℕ, q.Prime ∧
        CharP (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K₂)) q ∧
        NK.LocalStructure.TowerRankCore K₂ 𝔮
          (SeparableClosure (𝔮.adicCompletion K₂)) q ∧
        Nonempty (NK.LocalCFT.ArtinReciprocity (𝔮.adicCompletion K₂)
          (SeparableClosure (𝔮.adicCompletion K₂))) ∧
        (∀ H : Subgroup (Gal(SeparableClosure (𝔮.adicCompletion K₂)/𝔮.adicCompletion K₂)),
          H.index = q → H.Normal →
            IsOpen (H : Set (Gal(SeparableClosure (𝔮.adicCompletion K₂)/𝔮.adicCompletion K₂)))))
    (hlev : NK.ReconstructField.LevelIsoInput ϕ he) :
    ∃! σ : K₂' ≃+* K₁',
      Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ ∧
        ∀ g : Gal(K₁'/K₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm) := by
  have k₁' : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁)),
      ∃ p : ℕ, p.Prime ∧
        CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K₁)) p ∧
        NK.PTorsionTop.LocalGaloisInputsTop K₁ 𝔭
          (SeparableClosure (𝔭.adicCompletion K₁)) p := by
    intro 𝔭
    obtain ⟨p, hp, hres, hT, hD, hopen⟩ := k₁ 𝔭
    exact ⟨p, hp, hres,
      localGaloisInputsTop_of_coreData 𝔭 hp hres hT hD hopen⟩
  have k₂' : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂)),
      ∃ q : ℕ, q.Prime ∧
        CharP (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K₂)) q ∧
        NK.PTorsionTop.LocalGaloisInputsTop K₂ 𝔮
          (SeparableClosure (𝔮.adicCompletion K₂)) q := by
    intro 𝔮
    obtain ⟨q, hq, hres, hT, hD, hopen⟩ := k₂ 𝔮
    exact ⟨q, hq, hres,
      localGaloisInputsTop_of_coreData 𝔮 hq hres hT hD hopen⟩
  exact neukirch_uchida_of_coreInputs ϕ he hB₁ hB₂ k₁' k₂' hlev

end Capstone

/-! ## The sharpest current capstone: local class field theory + the tower ranks

The residue characteristic of a completion is automatic
(`NK.Mine.exists_prime_charP_residueField_adicCompletion`), so the per-prime hypothesis of
`NK.Mine.neukirch_uchida_of_reducedInputs` can be stated without the existential `∃ p` and without
`CharP`: the prime is `ringChar (ResidueField (𝔭.adicCompletionIntegers K))`, and the leaf left
standing at a finite prime `𝔭` is then exactly

* `NK.LocalStructure.TowerRankCore K 𝔭 K' (ringChar …)` — the tower ranks of the local Galois group;
* `Nonempty (NK.LocalCFT.ArtinReciprocity (𝔭.adicCompletion K) K')` — **local class field theory**;
* openness of index-`p` subgroups (Nikolov–Segal).

The rest of block (ii) — the abelian rank `d + 1 + δ`, the `δ`-detection, the residue characteristic
and the local degree — are then theorems (`NK.Mine.localGaloisInputsTop_of_coreData` and
`Submission/Work/PTorsionTop/`). -/

section LocalCft

variable {k₁ k₂ k₁' k₂' : Type u} [Field k₁] [Field k₂] [Field k₁'] [Field k₂']
  [NumberField k₁] [NumberField k₂] [Algebra k₁ k₁'] [Algebra k₂ k₂']
  [IsSepClosure k₁ k₁'] [IsSepClosure k₂ k₂']

theorem neukirch_uchida_of_localCft
    (ϕ : Gal(k₁'/k₁) ≃* Gal(k₂'/k₂)) (he : IsHomeomorph ϕ)
    (hB₁ : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k₁)),
      ∃ p : ℕ, p.Prime ∧
        NK.BrauerTwist.LocalH2Input p k₂ k₂'
          (𝔭.adicCompletion k₁) (SeparableClosure (𝔭.adicCompletion k₁)) ∧
        NK.HasseTwist.Sha2Input p k₂ k₂'
          (𝔭.adicCompletion k₁) (SeparableClosure (𝔭.adicCompletion k₁)) ∧
        NK.BrauerTwist.LocalDecompositionCriterion p k₂ k₂'
          (𝔭.adicCompletion k₁) (SeparableClosure (𝔭.adicCompletion k₁)))
    (hB₂ : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k₂)),
      ∃ p : ℕ, p.Prime ∧
        NK.BrauerTwist.LocalH2Input p k₁ k₁'
          (𝔮.adicCompletion k₂) (SeparableClosure (𝔮.adicCompletion k₂)) ∧
        NK.HasseTwist.Sha2Input p k₁ k₁'
          (𝔮.adicCompletion k₂) (SeparableClosure (𝔮.adicCompletion k₂)) ∧
        NK.BrauerTwist.LocalDecompositionCriterion p k₁ k₁'
          (𝔮.adicCompletion k₂) (SeparableClosure (𝔮.adicCompletion k₂)))
    (k₁i : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k₁)),
      NK.LocalStructure.TowerRankCore k₁ 𝔭 (SeparableClosure (𝔭.adicCompletion k₁))
        (ringChar (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers k₁))) ∧
      Nonempty (NK.LocalCFT.ArtinReciprocity (𝔭.adicCompletion k₁)
        (SeparableClosure (𝔭.adicCompletion k₁))) ∧
      (∀ H : Subgroup (Gal(SeparableClosure (𝔭.adicCompletion k₁)/𝔭.adicCompletion k₁)),
        H.index = ringChar (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers k₁)) → H.Normal →
          IsOpen (H : Set (Gal(SeparableClosure (𝔭.adicCompletion k₁)/𝔭.adicCompletion k₁)))))
    (k₂i : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k₂)),
      NK.LocalStructure.TowerRankCore k₂ 𝔮 (SeparableClosure (𝔮.adicCompletion k₂))
        (ringChar (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers k₂))) ∧
      Nonempty (NK.LocalCFT.ArtinReciprocity (𝔮.adicCompletion k₂)
        (SeparableClosure (𝔮.adicCompletion k₂))) ∧
      (∀ H : Subgroup (Gal(SeparableClosure (𝔮.adicCompletion k₂)/𝔮.adicCompletion k₂)),
        H.index = ringChar (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers k₂)) → H.Normal →
          IsOpen (H : Set (Gal(SeparableClosure (𝔮.adicCompletion k₂)/𝔮.adicCompletion k₂)))))
    (hlev : NK.ReconstructField.LevelIsoInput ϕ he) :
    ∃! σ : k₂' ≃+* k₁',
      Submission.NeukirchUchida.MapsBase (algebraMap k₁ k₁') (algebraMap k₂ k₂') σ ∧
        ∀ g : Gal(k₁'/k₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm) := by
  have k₁' : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k₁)),
      ∃ p : ℕ, p.Prime ∧
        CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers k₁)) p ∧
        NK.PTorsionTop.LocalGaloisInputsTop k₁ 𝔭
          (SeparableClosure (𝔭.adicCompletion k₁)) p := by
    intro 𝔭
    have hp : (ringChar (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers k₁))).Prime :=
      prime_ringChar_residueField_adicCompletion 𝔭
    have hres : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers k₁))
        (ringChar (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers k₁))) :=
      charP_ringChar_residueField_adicCompletion 𝔭
    exact ⟨_, hp, hres,
      localGaloisInputsTop_of_coreData 𝔭 hp hres (k₁i 𝔭).1 (k₁i 𝔭).2.1 (k₁i 𝔭).2.2⟩
  have k₂' : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k₂)),
      ∃ q : ℕ, q.Prime ∧
        CharP (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers k₂)) q ∧
        NK.PTorsionTop.LocalGaloisInputsTop k₂ 𝔮
          (SeparableClosure (𝔮.adicCompletion k₂)) q := by
    intro 𝔮
    have hq : (ringChar (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers k₂))).Prime :=
      prime_ringChar_residueField_adicCompletion 𝔮
    have hres : CharP (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers k₂))
        (ringChar (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers k₂))) :=
      charP_ringChar_residueField_adicCompletion 𝔮
    exact ⟨_, hq, hres,
      localGaloisInputsTop_of_coreData 𝔮 hq hres (k₂i 𝔮).1 (k₂i 𝔮).2.1 (k₂i 𝔮).2.2⟩
  exact neukirch_uchida_of_coreInputs ϕ he hB₁ hB₂ k₁' k₂' hlev

end LocalCft

/-! ## The openness hypothesis is a theorem

`NK.Mine.finiteIndex_isClosed_of_towerRankCore` turns the Nikolov–Segal field of `TowerRankCore`
into closedness of *every* finite-index subgroup of `Gal(K'/𝔭.adicCompletion K)`; a finite-index
subgroup is then open by `Subgroup.isOpen_of_isClosed_of_finiteIndex`.  So the openness hypothesis
of `NK.Mine.neukirch_uchida_of_localCft` is redundant, and the per-prime leaf of block (ii)
becomes exactly `TowerRankCore K 𝔭 K' (ringChar …) ∧ Nonempty (ArtinReciprocity κ K')`. -/

/-- **Index-`p` normal subgroups of a `p`-adic absolute Galois group are open**, from the reduced
tower-rank core (and Nikolov–Segal inside it). -/
theorem isOpen_of_index_prime_of_towerRankCore {K : Type} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K'] {p : ℕ}
    (h : NK.LocalStructure.TowerRankCore K 𝔭 K' p) {H : Subgroup (Gal(K'/𝔭.adicCompletion K))}
    (hH : H.index = p) (hN : H.Normal) :
    IsOpen (H : Set (Gal(K'/𝔭.adicCompletion K))) := by
  haveI : H.FiniteIndex :=
    Subgroup.finiteIndex_iff.mpr (by rw [hH]; exact h.hp.ne_zero)
  exact Subgroup.isOpen_of_isClosed_of_finiteIndex H
    (finiteIndex_isClosed_of_towerRankCore 𝔭 h H inferInstance)


/-- **Universe-polymorphic form of `NK.Mine.finiteIndex_isClosed_of_towerRankCore`** (the
delegated statement lives in the bottom universe; the endgame needs it at `Type u`).  The proof is
the same: transport along `botGalEquiv`, which is the identity on underlying functions and
continuous. -/
theorem finiteIndex_isClosed_of_towerRankCorePoly {K : Type u} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type u}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K'] {p : ℕ}
    (h : NK.LocalStructure.TowerRankCore K 𝔭 K' p) :
    ∀ H : Subgroup (Gal(K'/𝔭.adicCompletion K)), H.FiniteIndex →
      IsClosed (H : Set (Gal(K'/𝔭.adicCompletion K))) := by
  intro H hH
  haveI : IsGalois (𝔭.adicCompletion K) K' := IsSepClosure.isGalois
  have hidx : (H.map (NK.LocalStructure.Tower.botGalEquiv (κ := 𝔭.adicCompletion K)
      (K' := K')).toMonoidHom).index = H.index :=
    Subgroup.index_map_equiv H (NK.LocalStructure.Tower.botGalEquiv (κ := 𝔭.adicCompletion K)
      (K' := K'))
  have hfin : (H.map (NK.LocalStructure.Tower.botGalEquiv (κ := 𝔭.adicCompletion K)
      (K' := K')).toMonoidHom).FiniteIndex :=
    ⟨by rw [hidx]; exact hH.index_ne_zero⟩
  have hcl := h.finiteIndex_isClosed ⊥ _ hfin
  have hsub : (H : Set (Gal(K'/𝔭.adicCompletion K))) =
      (NK.LocalStructure.Tower.botGalEquiv (κ := 𝔭.adicCompletion K) (K' := K')) ⁻¹'
        ((H.map (NK.LocalStructure.Tower.botGalEquiv (κ := 𝔭.adicCompletion K)
          (K' := K')).toMonoidHom :
          Subgroup Gal(K'/↥(⊥ : IntermediateField (𝔭.adicCompletion K) K'))) :
            Set Gal(K'/↥(⊥ : IntermediateField (𝔭.adicCompletion K) K'))) := by
    ext σ
    simp only [Set.mem_preimage, SetLike.mem_coe]
    rw [Subgroup.mem_map_equiv]
    simp
  rw [hsub]
  exact hcl.preimage (NK.Mine.continuous_botGalEquiv (κ := 𝔭.adicCompletion K) (K' := K'))

/-- **Universe-polymorphic form of the openness corollary** (see
`NK.Mine.finiteIndex_isClosed_of_towerRankCorePoly`). -/
theorem isOpen_of_index_prime_of_towerRankCorePoly {K : Type u} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type u}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K'] {p : ℕ}
    (h : NK.LocalStructure.TowerRankCore K 𝔭 K' p) {H : Subgroup (Gal(K'/𝔭.adicCompletion K))}
    (hH : H.index = p) (hN : H.Normal) :
    IsOpen (H : Set (Gal(K'/𝔭.adicCompletion K))) := by
  haveI : H.FiniteIndex :=
    Subgroup.finiteIndex_iff.mpr (by rw [hH]; exact h.hp.ne_zero)
  exact Subgroup.isOpen_of_isClosed_of_finiteIndex H
    (finiteIndex_isClosed_of_towerRankCorePoly 𝔭 h H inferInstance)

section LocalCftSharp

variable {k₁ k₂ k₁' k₂' : Type u} [Field k₁] [Field k₂] [Field k₁'] [Field k₂']
  [NumberField k₁] [NumberField k₂] [Algebra k₁ k₁'] [Algebra k₂ k₂']
  [IsSepClosure k₁ k₁'] [IsSepClosure k₂ k₂']

/-- **The sharpest current form of the endgame**: at every finite prime, only the reduced tower-rank
core and local class field theory are assumed; everything else in block (ii) is a theorem. -/
theorem neukirch_uchida_of_localCftSharp
    (ϕ : Gal(k₁'/k₁) ≃* Gal(k₂'/k₂)) (he : IsHomeomorph ϕ)
    (hB₁ : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k₁)),
      ∃ p : ℕ, p.Prime ∧
        NK.BrauerTwist.LocalH2Input p k₂ k₂'
          (𝔭.adicCompletion k₁) (SeparableClosure (𝔭.adicCompletion k₁)) ∧
        NK.HasseTwist.Sha2Input p k₂ k₂'
          (𝔭.adicCompletion k₁) (SeparableClosure (𝔭.adicCompletion k₁)) ∧
        NK.BrauerTwist.LocalDecompositionCriterion p k₂ k₂'
          (𝔭.adicCompletion k₁) (SeparableClosure (𝔭.adicCompletion k₁)))
    (hB₂ : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k₂)),
      ∃ p : ℕ, p.Prime ∧
        NK.BrauerTwist.LocalH2Input p k₁ k₁'
          (𝔮.adicCompletion k₂) (SeparableClosure (𝔮.adicCompletion k₂)) ∧
        NK.HasseTwist.Sha2Input p k₁ k₁'
          (𝔮.adicCompletion k₂) (SeparableClosure (𝔮.adicCompletion k₂)) ∧
        NK.BrauerTwist.LocalDecompositionCriterion p k₁ k₁'
          (𝔮.adicCompletion k₂) (SeparableClosure (𝔮.adicCompletion k₂)))
    (k₁i : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k₁)),
      NK.LocalStructure.TowerRankCore k₁ 𝔭 (SeparableClosure (𝔭.adicCompletion k₁))
        (ringChar (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers k₁))) ∧
      Nonempty (NK.LocalCFT.ArtinReciprocity (𝔭.adicCompletion k₁)
        (SeparableClosure (𝔭.adicCompletion k₁))))
    (k₂i : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k₂)),
      NK.LocalStructure.TowerRankCore k₂ 𝔮 (SeparableClosure (𝔮.adicCompletion k₂))
        (ringChar (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers k₂))) ∧
      Nonempty (NK.LocalCFT.ArtinReciprocity (𝔮.adicCompletion k₂)
        (SeparableClosure (𝔮.adicCompletion k₂))))
    (hlev : NK.ReconstructField.LevelIsoInput ϕ he) :
    ∃! σ : k₂' ≃+* k₁',
      Submission.NeukirchUchida.MapsBase (algebraMap k₁ k₁') (algebraMap k₂ k₂') σ ∧
        ∀ g : Gal(k₁'/k₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm) := by
  refine neukirch_uchida_of_localCft ϕ he hB₁ hB₂ (fun 𝔭 => ?_) (fun 𝔮 => ?_) hlev
  · exact ⟨(k₁i 𝔭).1, (k₁i 𝔭).2,
      fun H hH hN => isOpen_of_index_prime_of_towerRankCorePoly 𝔭 (k₁i 𝔭).1 hH hN⟩
  · exact ⟨(k₂i 𝔮).1, (k₂i 𝔮).2,
      fun H hH hN => isOpen_of_index_prime_of_towerRankCorePoly 𝔮 (k₂i 𝔮).1 hH hN⟩

end LocalCftSharp

end NK.Mine


