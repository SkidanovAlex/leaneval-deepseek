import Mathlib.Order.CompletePartialOrder
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.NumberTheory.NumberField.Basic
import Submission.NK.Reconstruct.eq_of_restrictNormalHom_eq
import Submission.NK.ReconstructField.LevelMatch
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The compactness limit of the reconstruction (CoNF XII §12.2)

This file turns the *level-wise* form of the reconstruction into the global statement
`NK.ReconstructField.LevelMatch` for one single isomorphism of the separable closures:

```lean
theorem NK.ReconstructField.compactness_conjHomEquiv
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ) (τ₀ : K₁ ≃+* K₂)
    (hL : ∀ L, ∃ σ, MapsBase … σ ∧ (∀ x, σ (algebraMap K₂ K₂' (τ₀ x)) = algebraMap K₁ K₁' x) ∧
        NK.ReconstructField.LevelMatch ϕ hϕ σ _ L) :
    ∃ σ hσ, Submission.NeukirchUchida.conjHomEquiv hσ = ϕ
```

The hypothesis `hL` supplies, for each finite Galois level `L ⊆ K₁'`, *some* isomorphism `σ_L` of
the separable closures mapping the embedded `K₂` onto the embedded `K₁` and matching `ϕ` modulo
`Gal(K₂'/levelMap ϕ L)`.  The `σ_L` need not be compatible with each other; the point of the
argument is that they are *forced* to have a common refinement.

## The argument

Fix `τ₀`; the isomorphisms of the closure mapping the embedded `K₂` onto the embedded `K₁` through
`τ₀` are exactly the Galois twists `liftTwist τ₀ k`, `k ∈ Gal(K₂'/K₂)`
(`NK.ReconstructField.eq_liftTwist_of_apply_base`), and conjugation by such a twist is

`conj (liftTwist τ₀ k) g = k⁻¹ * conj (liftBase τ₀) g * k`

(`compactness_conj_liftTwist`).  Hence the level-wise condition becomes a condition

`CompactMatchAt ϕ τ₀ k L  :⟺  ∀ g, k⁻¹ * conj (liftBase τ₀) g * k * (ϕ g)⁻¹ ∈ Gal(K₂'/levelMap ϕ L)`

on the *compact* group `Gal(K₂'/K₂)` — the "compactness" of the title.  For each level `L` this is
a closed subset (`compactness_isClosed_matchAt`: an intersection of preimages of the closed subgroup
`Gal(K₂'/levelMap ϕ L)` under the continuous maps `k ↦ k⁻¹ c k d`), the family of levels is
directed under `⊆` (`L ⊔ L'`), and each `C_L` is non-empty by `hL` and `eq_liftTwist_of_apply_base`.
Compactness of the Krull topology therefore gives `k ∈ ⋂_L C_L`.

For this `k` all the level-wise conditions hold, so `d := conj (liftTwist τ₀ k) g * (ϕ g)⁻¹` lies in
`Gal(K₂'/levelMap ϕ L)` for every level `L`.  Pulling `d` back along `ϕ` and using
`(levelMap ϕ L).fixingSubgroup = Gal(K₁'/L).map ϕ` shows that `ϕ⁻¹ d` lies in `Gal(K₁'/L)` for
every finite Galois level `L`; since the finite Galois levels are cofinal in the separable closure,
`NK.Reconstruct.eq_of_restrictNormalHom_eq` gives `ϕ⁻¹ d = 1`, that is `conj (liftTwist τ₀ k) = ϕ`.
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace NK.ReconstructField

open NK.Reconstruct

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-! ### 1. Conjugation by a Galois twist of the chosen lift -/

/-- **Conjugation by a Galois twist.**  For a base-field isomorphism `τ` and `k ∈ Gal(K₂'/K₂)`, the
conjugate of `g` by the twist `liftTwist τ k` of the chosen lift `liftBase τ` is the conjugate of
`g` by the lift, conjugated by `k`. -/
theorem compactness_conj_liftTwist (τ : K₁ ≃+* K₂) (k : Gal(K₂'/K₂)) (g : Gal(K₁'/K₁)) :
    Submission.NeukirchUchida.conj (liftTwist_mapsBase K₁ K₂ K₁' K₂' τ k) g =
      k⁻¹ * Submission.NeukirchUchida.conj (liftBase_mapsBase K₁ K₂ K₁' K₂' τ) g * k := by
  ext x
  simp [Submission.NeukirchUchida.conj_apply, liftTwist, AlgEquiv.coe_inv]

/-- The isomorphism `conjHomEquiv hσ` is conjugation by `hσ`, by definition. -/
theorem compactness_conjHomEquiv_apply {σ : K₂' ≃+* K₁'}
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ)
    (g : Gal(K₁'/K₁)) :
    (Submission.NeukirchUchida.conjHomEquiv hσ) g = Submission.NeukirchUchida.conj hσ g := rfl

/-! ### 2. The level-wise condition on the compact group `Gal(K₂'/K₂)` -/

/-- **The `k`-form of the level-wise matching condition.**  An element `k ∈ Gal(K₂'/K₂)` matches the
level `L` if the twist `liftTwist τ k` matches `ϕ` at `L`; by `compactness_conj_liftTwist` this is the condition
`∀ g, k⁻¹ * conj (liftBase τ) g * k * (ϕ g)⁻¹ ∈ Gal(K₂'/levelMap ϕ L)`. -/
def CompactMatchAt (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (τ : K₁ ≃+* K₂) (k : Gal(K₂'/K₂))
    (L : IntermediateField K₁ K₁') : Prop :=
  ∀ g : Gal(K₁'/K₁),
    k⁻¹ * Submission.NeukirchUchida.conj (liftBase_mapsBase K₁ K₂ K₁' K₂' τ) g * k * (ϕ g)⁻¹ ∈
      (NK.Reconstruct.levelMap ϕ L).fixingSubgroup

/-- **`CompactMatchAt` is the level-wise matching condition for the corresponding twist.** -/
theorem compactMatchAt_iff_levelMatch (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (τ : K₁ ≃+* K₂) (k : Gal(K₂'/K₂)) (L : IntermediateField K₁ K₁') [FiniteDimensional K₁ L]
    [Normal K₁ L] [NumberField ↥L] [FiniteDimensional K₂ (NK.Reconstruct.levelMap ϕ L)]
    [Normal K₂ (NK.Reconstruct.levelMap ϕ L)] [NumberField ↥(NK.Reconstruct.levelMap ϕ L)] :
    CompactMatchAt ϕ τ k L ↔
      LevelMatch ϕ hϕ (liftTwist K₁ K₂ K₁' K₂' τ k) (liftTwist_mapsBase K₁ K₂ K₁' K₂' τ k) L := by
  unfold CompactMatchAt LevelMatch
  refine forall_congr' (fun g => ?_)
  rw [compactness_conjHomEquiv_apply, compactness_conj_liftTwist]

/-- **The image of a level under `ϕ` is monotone.** -/
theorem levelMap_mono (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) {L L' : IntermediateField K₁ K₁'}
    (h : L ≤ L') : NK.Reconstruct.levelMap ϕ L ≤ NK.Reconstruct.levelMap ϕ L' := by
  intro x hx
  rw [NK.Reconstruct.mem_levelMap_iff] at hx ⊢
  intro g hg
  exact hx g (fun y => hg ⟨y.1, h y.2⟩)

/-- **The matching condition is monotone in the level**: matching at a larger level implies matching
at a smaller one. -/
theorem compactMatchAt_mono (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (τ : K₁ ≃+* K₂)
    {L L' : IntermediateField K₁ K₁'} (h : L ≤ L') :
    {k : Gal(K₂'/K₂) | CompactMatchAt ϕ τ k L'} ⊆ {k : Gal(K₂'/K₂) | CompactMatchAt ϕ τ k L} :=
  fun k hk g => (IntermediateField.fixingSubgroup_antitone (levelMap_mono ϕ h)) (hk g)

/-- The map `k ↦ k⁻¹ * c * k * d` is continuous on a topological group. -/
theorem compactness_continuous_inv_mul_conj_mul {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (c d : G) : Continuous (fun k : G => k⁻¹ * c * k * d) :=
  ((continuous_inv.mul continuous_const).mul continuous_id).mul continuous_const

/-- **The set of elements matching a level is closed** in the Krull topology.  It is the intersection
over `g : Gal(K₁'/K₁)` of the preimages of the closed subgroup `Gal(K₂'/levelMap ϕ L)` under the
continuous maps `k ↦ k⁻¹ * conj (liftBase τ) g * k * (ϕ g)⁻¹`. -/
theorem compactness_isClosed_matchAt (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (τ : K₁ ≃+* K₂) (L : IntermediateField K₁ K₁') [FiniteDimensional K₁ L] :
    IsClosed {k : Gal(K₂'/K₂) | CompactMatchAt ϕ τ k L} := by
  haveI : FiniteDimensional K₂ (NK.Reconstruct.levelMap ϕ L) :=
    NK.Reconstruct.finiteDimensional_levelMap hϕ L
  have hbase : IsClosed ((NK.Reconstruct.levelMap ϕ L).fixingSubgroup : Set Gal(K₂'/K₂)) :=
    IntermediateField.fixingSubgroup_isClosed _
  have hset : {k : Gal(K₂'/K₂) | CompactMatchAt ϕ τ k L} = ⋂ g : Gal(K₁'/K₁),
      {k : Gal(K₂'/K₂) | k⁻¹ * Submission.NeukirchUchida.conj (liftBase_mapsBase K₁ K₂ K₁' K₂' τ) g
        * k * (ϕ g)⁻¹ ∈ (NK.Reconstruct.levelMap ϕ L).fixingSubgroup} := by
    ext k; simp [CompactMatchAt]
  rw [hset]
  exact isClosed_iInter (fun g => hbase.preimage (compactness_continuous_inv_mul_conj_mul _ ((ϕ g)⁻¹)))

/-! ### 3. The index type of finite Galois levels and the compactness limit -/

/-- The finite Galois levels of `K₁'/K₁` which are number fields; these index the compactness
argument. -/
abbrev CompactLevelIdx (K : Type*) [Field K] (K' : Type*) [Field K'] [Algebra K K'] :=
  {L : IntermediateField K K' // FiniteDimensional K L ∧ Normal K L ∧ NumberField ↥L}

/-- The bottom level, exhibiting the non-emptiness of `CompactLevelIdx`. -/
noncomputable def compactnessBaseLevelIdx (K : Type*) [Field K] [NumberField K] (K' : Type*) [Field K']
    [Algebra K K'] : CompactLevelIdx K K' :=
  ⟨⊥, by infer_instance, by infer_instance, by infer_instance⟩

/-- **The compositum of two finite Galois levels is a finite Galois level.** -/
noncomputable def compactLevelIdxSup (i j : CompactLevelIdx K₁ K₁') : CompactLevelIdx K₁ K₁' := by
  haveI : FiniteDimensional K₁ i.1 := i.2.1
  haveI : FiniteDimensional K₁ j.1 := j.2.1
  haveI : Normal K₁ i.1 := i.2.2.1
  haveI : Normal K₁ j.1 := j.2.2.1
  haveI hfd : FiniteDimensional K₁ (i.1 ⊔ j.1 : IntermediateField K₁ K₁') := inferInstance
  exact ⟨(i.1 ⊔ j.1 : IntermediateField K₁ K₁'), hfd, inferInstance,
    NumberField.of_module_finite K₁ ↥(i.1 ⊔ j.1)⟩

/-- **The level-wise matching condition propagates to the common refinement of two levels.** -/
theorem compactMatchAt_sup_le (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (τ : K₁ ≃+* K₂)
    (i j : CompactLevelIdx K₁ K₁') :
    {k : Gal(K₂'/K₂) | CompactMatchAt ϕ τ k (compactLevelIdxSup i j).1} ⊆
      {k : Gal(K₂'/K₂) | CompactMatchAt ϕ τ k i.1} ∧
    {k : Gal(K₂'/K₂) | CompactMatchAt ϕ τ k (compactLevelIdxSup i j).1} ⊆
      {k : Gal(K₂'/K₂) | CompactMatchAt ϕ τ k j.1} :=
  ⟨compactMatchAt_mono ϕ τ (le_sup_left : i.1 ≤ (i.1 ⊔ j.1 : IntermediateField K₁ K₁')),
    compactMatchAt_mono ϕ τ (le_sup_right : j.1 ≤ (i.1 ⊔ j.1 : IntermediateField K₁ K₁'))⟩

/-- **The family of level-wise matching sets is directed downwards.** -/
theorem compactnessDirectedMatchAt (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (τ : K₁ ≃+* K₂) :
    Directed (· ⊇ ·) (fun i : CompactLevelIdx K₁ K₁' => {k : Gal(K₂'/K₂) | CompactMatchAt ϕ τ k i.1}) := by
  intro i j
  exact ⟨compactLevelIdxSup i j, (compactMatchAt_sup_le ϕ τ i j).1, (compactMatchAt_sup_le ϕ τ i j).2⟩

/-- **Every level-wise matching set is non-empty**, by the hypothesis `hL` together with the
parametrisation of the `MapsBase` isomorphisms by the Galois twists of the chosen lift. -/
theorem compactnessMatchAt_nonempty (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ) (τ₀ : K₁ ≃+* K₂)
    (hL : ∀ (L : IntermediateField K₁ K₁') [FiniteDimensional K₁ L] [Normal K₁ L]
      [NumberField ↥L] [FiniteDimensional K₂ (NK.Reconstruct.levelMap ϕ L)]
      [Normal K₂ (NK.Reconstruct.levelMap ϕ L)] [NumberField ↥(NK.Reconstruct.levelMap ϕ L)],
      ∃ (σ : K₂' ≃+* K₁')
        (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ),
        (∀ x : K₁, σ (algebraMap K₂ K₂' (τ₀ x)) = algebraMap K₁ K₁' x) ∧
          LevelMatch ϕ hϕ σ hσ L)
    (i : CompactLevelIdx K₁ K₁') :
    ({k : Gal(K₂'/K₂) | CompactMatchAt ϕ τ₀ k i.1}).Nonempty := by
  haveI : FiniteDimensional K₁ i.1 := i.2.1
  haveI : Normal K₁ i.1 := i.2.2.1
  haveI : NumberField ↥i.1 := i.2.2.2
  haveI : FiniteDimensional K₂ (NK.Reconstruct.levelMap ϕ i.1) :=
    NK.Reconstruct.finiteDimensional_levelMap hϕ i.1
  haveI : Normal K₂ (NK.Reconstruct.levelMap ϕ i.1) :=
    NK.Reconstruct.normal_levelMap hϕ i.1
  haveI : NumberField ↥(NK.Reconstruct.levelMap ϕ i.1) :=
    NK.Reconstruct.numberField_levelMap hϕ i.1
  obtain ⟨σ, hσ, hbase, hlt⟩ := hL i.1
  obtain ⟨k, hk⟩ := eq_liftTwist_of_apply_base K₁ K₂ K₁' K₂' (τ := τ₀) hbase
  subst hk
  refine ⟨k, ?_⟩
  rw [Set.mem_ofPred_eq, compactMatchAt_iff_levelMatch ϕ hϕ τ₀ k i.1]
  exact hlt

/-! ### 4. From the compactness limit to the identity `conjHomEquiv hσ = ϕ` -/

/-- **The level-wise conditions at *all* finite Galois levels force the global identity.** -/
theorem compactness_conjHomEquiv_eq_of_matchAt (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (τ : K₁ ≃+* K₂) {k : Gal(K₂'/K₂)} (hk : ∀ i : CompactLevelIdx K₁ K₁', CompactMatchAt ϕ τ k i.1) :
    Submission.NeukirchUchida.conjHomEquiv (liftTwist_mapsBase K₁ K₂ K₁' K₂' τ k) = ϕ := by
  haveI hgal₁ : IsGalois K₁ K₁' := IsSepClosure.isGalois
  refine MulEquiv.ext (fun g => ?_)
  set d : Gal(K₂'/K₂) :=
    Submission.NeukirchUchida.conj (liftTwist_mapsBase K₁ K₂ K₁' K₂' τ k) g * (ϕ g)⁻¹ with hd_def
  have hd : ∀ i : CompactLevelIdx K₁ K₁', d ∈ (NK.Reconstruct.levelMap ϕ i.1).fixingSubgroup := by
    intro i
    rw [hd_def, compactness_conj_liftTwist]
    exact hk i g
  -- pull `d` back along `ϕ`: it lies in every `Gal(K₁'/L)`
  let u : Gal(K₁'/K₁) := ϕ.symm d
  have hu : u = 1 := by
    refine NK.Reconstruct.eq_of_restrictNormalHom_eq (K := K₁) (K' := K₁') (u := u) (v := 1) ?_
    intro L hfd hnorm hnf
    have hdL : d ∈ (NK.Reconstruct.levelMap ϕ L).fixingSubgroup := hd ⟨L, hfd, hnorm, hnf⟩
    rw [NK.Reconstruct.fixingSubgroup_levelMap hϕ L] at hdL
    have hmem : u ∈ L.fixingSubgroup := Subgroup.mem_map_equiv.mp hdL
    have hker : u ∈ (AlgEquiv.restrictNormalHom ↥L).ker := by
      rw [IntermediateField.restrictNormalHom_ker L]
      exact hmem
    rw [MonoidHom.mem_ker] at hker
    simpa using hker
  have hd1 : d = 1 := by
    have hdu : d = ϕ u := by
      rw [show u = ϕ.symm d from rfl]
      exact (ϕ.apply_symm_apply d).symm
    rw [hdu, hu, map_one]
  rw [hd_def] at hd1
  exact (mul_inv_eq_one.mp hd1)

/-! ### 5. The compactness theorem -/

theorem compactness_conjHomEquiv {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂]
    [Field K₁'] [Field K₂'] [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ) (τ₀ : K₁ ≃+* K₂)
    (hL : ∀ (L : IntermediateField K₁ K₁') [FiniteDimensional K₁ L] [Normal K₁ L] [NumberField ↥L]
      [FiniteDimensional K₂ (NK.Reconstruct.levelMap ϕ L)]
      [Normal K₂ (NK.Reconstruct.levelMap ϕ L)] [NumberField ↥(NK.Reconstruct.levelMap ϕ L)],
      ∃ (σ : K₂' ≃+* K₁')
        (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ),
        (∀ x : K₁, σ (algebraMap K₂ K₂' (τ₀ x)) = algebraMap K₁ K₁' x) ∧
          NK.ReconstructField.LevelMatch ϕ hϕ σ hσ L) :
    ∃ (σ : K₂' ≃+* K₁')
      (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ),
      Submission.NeukirchUchida.conjHomEquiv hσ = ϕ := by
  haveI hgal₂ : IsGalois K₂ K₂' := IsSepClosure.isGalois
  haveI : Nonempty (CompactLevelIdx K₁ K₁') := ⟨compactnessBaseLevelIdx K₁ K₁'⟩
  have hclosed : ∀ i : CompactLevelIdx K₁ K₁', IsClosed {k : Gal(K₂'/K₂) | CompactMatchAt ϕ τ₀ k i.1} :=
    fun i => by
      haveI : FiniteDimensional K₁ i.1 := i.2.1
      exact compactness_isClosed_matchAt ϕ hϕ τ₀ i.1
  have hdir := compactnessDirectedMatchAt ϕ τ₀
  have hne : ∀ i : CompactLevelIdx K₁ K₁', ({k : Gal(K₂'/K₂) | CompactMatchAt ϕ τ₀ k i.1}).Nonempty :=
    fun i => compactnessMatchAt_nonempty ϕ hϕ τ₀ hL i
  have hnonempty : (⋂ i : CompactLevelIdx K₁ K₁', {k : Gal(K₂'/K₂) | CompactMatchAt ϕ τ₀ k i.1}).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    obtain ⟨i, hi⟩ := isCompact_univ.elim_directed_family_closed
      (fun i : CompactLevelIdx K₁ K₁' => {k : Gal(K₂'/K₂) | CompactMatchAt ϕ τ₀ k i.1}) hclosed
      (by simpa using h) hdir
    exact (hne i).ne_empty (by simpa using hi)
  obtain ⟨k, hk⟩ := hnonempty
  exact ⟨liftTwist K₁ K₂ K₁' K₂' τ₀ k, liftTwist_mapsBase K₁ K₂ K₁' K₂' τ₀ k,
    compactness_conjHomEquiv_eq_of_matchAt ϕ hϕ τ₀ (fun i => Set.mem_iInter.mp hk i)⟩

end NK.ReconstructField
