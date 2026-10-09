import Mathlib
import Submission.Work.SSGRoute.levelInertia_defs
import Submission.Commons.FieldTheory.Galois.isClosed_stabilizer_valuationSubring
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# An open subgroup containing the inertia contains a level subgroup

For a number field `k`, an algebraic closure `Ω`, a finite place `B` of `Ω` and an *open* subgroup
`V ≤ G_k = Ω ≃ₐ[k] Ω` containing every inertia element at `B`, we produce a finite normal
intermediate field `M ⊆ Ω` with `levelSub B M ≤ V`.

The proof has no arithmetic content beyond the two structural facts already available:

* `mem_levelSub_iff` (`Submission/Work/SSGRoute/levelInertia_defs.lean`), which identifies the
  intersection of all the level subgroups with the set of inertia elements at `B`:
  `⋂_M levelSub B M = {σ | IsInertia k B σ} ⊆ V`;
* the Krull topology on `G_k` is compact (`Mathlib.FieldTheory.Galois.Profinite`) and each
  `levelSub B M` is closed, because it is the preimage of a subgroup of the *finite* group
  `Gal(M/k)` under the continuous restriction map, intersected with the (closed) decomposition
  group of `B` (`levelSub_eq_preimage` + `isClosed_levelSub` below).

The level subgroups are directed decreasing in `M` (`levelSub_antitone`) and closed, so if none of
them were contained in `V`, compactness would produce an element of `⋂_M levelSub B M` (a subset of
`V`) outside `V` — a contradiction. Note that this argument really uses the *openness* of `V`: the
complement of an arbitrary subgroup need not be closed.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.SSGRoute

/-- **`levelSub B M` as a preimage of the restriction map.**

For a finite normal level `M`, an element `δ ∈ G_k` lies in `levelSub B M` exactly when `δ` lies in
the decomposition group of `B` and its restriction `δ|_M` acts on `M` trivially modulo the maximal
ideal of the valuation subring `B ∩ M` of `M`.  (The two valuation conditions are the same because
the valuation of `B ∩ M` is the restriction of the valuation of `B`.) -/
lemma levelSub_eq_preimage {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (B : ValuationSubring Ω) (M : IntermediateField k Ω)
    [FiniteDimensional k M] [Normal k M] :
    (levelSub B M : Set (Ω ≃ₐ[k] Ω)) = (SSGRoute.decomp k B : Set _) ∩
      (AlgEquiv.restrictNormalHom M) ⁻¹'
        {τ : M ≃ₐ[k] M | ∀ x : ↥(B.comap (algebraMap ↥M Ω)),
          (B.comap (algebraMap ↥M Ω)).valuation (τ (x : ↥M) - (x : ↥M)) < 1} := by
  ext δ
  constructor
  · intro hδ
    refine ⟨hδ.1, ?_⟩
    intro x
    rw [comap_valuation_lt_one_iff, map_sub,
      show (AlgEquiv.restrictNormalHom M δ) (x : ↥M)
        = AlgEquiv.restrictNormal δ M (x : ↥M) from rfl,
      AlgEquiv.restrictNormal_commutes δ M (x : ↥M)]
    exact hδ.2 x
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun x => ?_⟩
    have h := h2 x
    rw [comap_valuation_lt_one_iff, map_sub,
      show (AlgEquiv.restrictNormalHom M δ) (x : ↥M)
        = AlgEquiv.restrictNormal δ M (x : ↥M) from rfl,
      AlgEquiv.restrictNormal_commutes δ M (x : ↥M)] at h
    exact h

/-- **Every level subgroup is closed** in the Krull topology: it is the preimage of a subgroup of the
finite (hence discrete) group `Gal(M/k)` under the continuous restriction map, intersected with the
decomposition group of `B`, which is closed by
`Commons.FieldTheory.Galois.isClosed_stabilizer_valuationSubring`. -/
lemma isClosed_levelSub {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (B : ValuationSubring Ω) (M : IntermediateField k Ω)
    [FiniteDimensional k M] [Normal k M] :
    IsClosed ((levelSub B M : Set (Ω ≃ₐ[k] Ω))) := by
  haveI : IsGalois k Ω := inferInstance
  rw [levelSub_eq_preimage B M]
  refine (Commons.FieldTheory.Galois.isClosed_stabilizer_valuationSubring
    (K := k) (K' := Ω) B).inter ?_
  exact (isClosed_discrete _).preimage (InfiniteGalois.restrictNormalHom_continuous M)

theorem exists_levelSub_le_of_isOpen (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (B : ValuationSubring Ω) (hB : SSGRoute.IsFinPlace k B)
    (V : Subgroup (Ω ≃ₐ[k] Ω)) (hV : IsOpen (V : Set (Ω ≃ₐ[k] Ω)))
    (hI : ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ → σ ∈ V) :
    ∃ (M : IntermediateField k Ω) (_ : FiniteDimensional k M) (_ : Normal k M),
      levelSub B M ≤ V := by
  classical
  haveI : IsGalois k Ω := inferInstance
  haveI : CompactSpace (Ω ≃ₐ[k] Ω) := inferInstance
  -- the finite normal levels, as an index type closed under binary composita
  let ι := {M : IntermediateField k Ω // FiniteDimensional k M ∧ Normal k M}
  have hι : Nonempty ι := ⟨⟨⊥, inferInstance, inferInstance⟩⟩
  -- the family of closed sets whose emptiness is what we want
  let t : ι → Set (Ω ≃ₐ[k] Ω) := fun i =>
    letI : FiniteDimensional k i.1 := i.2.1
    letI : Normal k i.1 := i.2.2
    ((levelSub B i.1 : Subgroup (Ω ≃ₐ[k] Ω)) : Set _) ∩ (V : Set (Ω ≃ₐ[k] Ω))ᶜ
  -- the family is directed for reverse inclusion: enlarging the level shrinks the level subgroup
  have htd : Directed (· ⊇ ·) t := by
    rintro ⟨M₁, h1fd, h1n⟩ ⟨M₂, h2fd, h2n⟩
    haveI := h1fd; haveI := h1n; haveI := h2fd; haveI := h2n
    refine ⟨⟨M₁ ⊔ M₂, inferInstance, inferInstance⟩, ?_, ?_⟩
    · intro x hx
      exact ⟨levelSub_antitone (B := B) (M := M₁) (M' := M₁ ⊔ M₂) le_sup_left hx.1, hx.2⟩
    · intro x hx
      exact ⟨levelSub_antitone (B := B) (M := M₂) (M' := M₁ ⊔ M₂) le_sup_right hx.1, hx.2⟩
  have htc : ∀ i, IsClosed (t i) := by
    rintro ⟨M, hfd, hn⟩
    haveI := hfd; haveI := hn
    exact (isClosed_levelSub B M).inter hV.isClosed_compl
  -- the total intersection is empty: it is the inertia, which is contained in `V`
  have hst : (⋂ i, t i) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro δ hδ
    rw [Set.mem_iInter] at hδ
    have hmem : δ ∈ V :=
      hI δ ((mem_levelSub_iff B δ).mp (fun M hfd hn => (hδ ⟨M, hfd, hn⟩).1))
    exact (hδ hι.some).2 hmem
  -- suppose no level subgroup is contained in `V`; compactness then contradicts `hst`
  by_contra hcon
  have hne : ∀ i, (t i).Nonempty := by
    rintro ⟨M, hfd, hn⟩
    rw [Set.nonempty_iff_ne_empty]
    intro hempty
    apply hcon
    refine ⟨M, hfd, hn, fun δ hδ => ?_⟩
    by_contra hδV
    have hmem : δ ∈ t ⟨M, hfd, hn⟩ := ⟨hδ, hδV⟩
    rw [hempty] at hmem
    exact hmem
  have hnon := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t htd hne
    (fun i => (htc i).isCompact) htc
  rw [hst] at hnon
  exact Set.not_nonempty_empty hnon

end Work.SSGRoute
