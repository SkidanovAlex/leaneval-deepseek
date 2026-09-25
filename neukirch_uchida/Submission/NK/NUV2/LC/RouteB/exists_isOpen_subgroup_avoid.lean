import Mathlib
import Submission.NK.NUV2.LC.RouteB.Defs

/-! Guidance from the project lead (the requester):

FULL ROUTE: read Submission/Work/NUV2/LC/RouteB/DESIGN_containment_v3.md first (the orchestrator's redesign of decompContainment_B; your lemma is one node). Never use the circular le_stabSubgroup_of_localType, SurjTwo/HasseTwo/ABHNSurjectivity shapes. hFC and hKC are PROVED (NK.CFTLib.fundamentalClassElement, NK.NUV2.kernelCondition_all).

# exists_isOpen_subgroup_avoid (helper S1, formal)

**Target file** `Submission/Work/NUV2/LC/RouteB/exists_isOpen_subgroup_avoid.lean`, namespace
`NK.NUV2.LC.RouteB`. Imports: `Submission.NK.NUV2.LC.RouteB.Defs`.

**Math.** `V` is closed, so `V = ⋂_L (V ⊔ Gal(K'/L))` over finite Galois `L` (each `V ⊔ G_L` is an open
subgroup because `G_L` is open normal). `Z` is closed in a compact space, so it is compact. The open
sets `(V ⊔ G_L)ᶜ` cover `Z` (a point of `Z` is not in `V`, and `⋂ (V ⊔ G_L) = V`); take a finite
subcover, let `L*` be the compositum: `(V ⊔ G_{L*}) ∩ Z = ∅`. Put `W' := (V ⊔ G_{L*}) ⊓ W`.

**Assets.** `NK.NUV2.LC.RouteB.exists_le_sup_fixingSubgroup_of_iInf_eq`
(`RouteB/exists_le_sup_fixingSubgroup_of_iInf_eq.lean`), `isOpen_sup_fixingSubgroup_inf`
(`RouteB/res_surjective_open.lean`), the first lemma of `RouteB/kill_one_place.lean` (same shape),
`krullTopology_mem_nhds_one_iff`, `IsCompact.elim_finite_subcover`.

**Uses (all in this design).** Claim U: `Z = (D_{A₁} \ C₁) ∪ (D_{A₂} \ C₂) ∪ {g | g • A₁ = A₂}`.
Claim E is served by `kill_one_place` instead. The `{g | g • A₁ = A₂}` piece is closed: empty, or the
coset `g₀ • D_{A₁}` (`NK.LocalDecomposition.isClosed_stabSubgroup`).

**Sanity check.** `K = ℚ`, `V = W = rootFix ζ₃` (open), `Z = ∅`: take `W' = V`.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Topology

universe u

namespace NK.NUV2.LC.RouteB

/-- **Finite intersection property, directed form.**  Let `F : ι → Set X` be a family of closed sets
of a compact space, directed downwards (`hdir`), and let `U` be an open set containing the
intersection `⋂ i, F i`.  Then a *single* member of the family is already contained in `U`.

Proof: if no `F i` were contained in `U`, the sets `F i ∩ Uᶜ` would be non-empty closed sets,
directed downwards, so by Cantor's intersection theorem
(`IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed`) their intersection would be
non-empty; but it is contained in `⋂ i, F i ⊆ U` and in `Uᶜ`. -/
lemma exists_subset_iInf_subset_open {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] {ι : Type*} [Nonempty ι] {F : ι → Set X} (hF : ∀ i, IsClosed (F i))
    (hdir : ∀ i j, ∃ k, F k ⊆ F i ∩ F j) {U : Set X} (hU : IsOpen U)
    (hsub : (⋂ i, F i) ⊆ U) : ∃ i, F i ⊆ U := by
  by_contra hcon
  have hne : ∀ i, (F i ∩ (Uᶜ : Set X)).Nonempty := by
    intro i
    obtain ⟨y, hyF, hyU⟩ := Set.not_subset.mp (fun hsub_i => hcon ⟨i, hsub_i⟩)
    exact ⟨y, hyF, hyU⟩
  have hdir' : Directed (· ⊇ ·) (fun i => F i ∩ (Uᶜ : Set X)) := by
    intro i j
    obtain ⟨k, hk⟩ := hdir i j
    exact ⟨k, fun y hy => ⟨(hk hy.1).1, hy.2⟩, fun y hy => ⟨(hk hy.1).2, hy.2⟩⟩
  have hne' : (⋂ i, (F i ∩ (Uᶜ : Set X))).Nonempty :=
    IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed _
      hdir' hne (fun i => (hF i).isCompact.inter hU.isClosed_compl.isCompact)
      (fun i => (hF i).inter hU.isClosed_compl)
  obtain ⟨y, hy⟩ := hne'
  have hyU : y ∈ U := hsub (Set.mem_iInter.mpr (fun i => (Set.mem_iInter.mp hy i).1))
  exact (Set.mem_iInter.mp hy (Classical.arbitrary ι)).2 hyU

/-- **Compactness: a closed subgroup `V` inside an open subgroup `W` of `Gal(K'/K)` and disjoint from
a closed set `Z` lies in an open subgroup `W' ≤ W` still disjoint from `Z`.**

Since `V` is closed and `Gal(K'/K)` is the pro-finite group with the Krull topology, `V` is the
intersection of the open subgroups `V ⊔ Gal(K'/L)` (`L` ranging over the finite Galois intermediate
fields of `K'/K`, `NK.HassePrinciple.iInf_sup_eq_of_isClosed`).  The complements of these open
subgroups form an open cover of the compact set `Z` (as `V ∩ Z = ∅`), so -- the family being directed
-- a *single* level `L` already has `(V ⊔ Gal(K'/L)) ∩ Z = ∅` (finite intersection property in the
compact group).  The subgroup `W' := (V ⊔ Gal(K'/L)) ⊓ W` is open (it contains `Gal(K'/L) ⊓ W`),
lies between `V` and `W`, and is disjoint from `Z`. -/
theorem exists_isOpen_subgroup_avoid {K K' : Type} [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] {V W : Subgroup Gal(K'/K)}
    (hVcl : IsClosed (V : Set Gal(K'/K))) (hW : IsOpen (W : Set Gal(K'/K))) (hVW : V ≤ W)
    {Z : Set Gal(K'/K)} (hZ : IsClosed Z) (hVZ : Disjoint (V : Set Gal(K'/K)) Z) :
    ∃ W' : Subgroup Gal(K'/K), V ≤ W' ∧ W' ≤ W ∧ IsOpen (W' : Set Gal(K'/K)) ∧
      Disjoint (W' : Set Gal(K'/K)) Z := by
  classical
  haveI : IsGalois K K' := IsSepClosure.isGalois
  -- the fixing subgroups of the finite Galois intermediate fields are open
  have hfixopen : ∀ L : FiniteGaloisIntermediateField K K',
      IsOpen ((L.fixingSubgroup : Subgroup Gal(K'/K)) : Set Gal(K'/K)) :=
    fun L => IntermediateField.fixingSubgroup_isOpen (L : IntermediateField K K')
  -- they form a cofinal system of neighbourhoods of `1`
  have hB : ∀ U ∈ 𝓝 (1 : Gal(K'/K)), ∃ L : FiniteGaloisIntermediateField K K',
      (L.fixingSubgroup : Set Gal(K'/K)) ⊆ U := by
    intro U hU
    rw [krullTopology_mem_nhds_one_iff_of_normal K K'] at hU
    obtain ⟨E, hEfin, hEnorm, hEsub⟩ := hU
    refine ⟨{ toIntermediateField := E
              finiteDimensional := hEfin
              isGalois := { to_isSeparable :=
                              Algebra.IsSeparable.of_algHom K K' (IntermediateField.val E)
                            to_normal := hEnorm } }, ?_⟩
    simpa using hEsub
  -- hence `V` is the intersection of the open subgroups `V ⊔ Gal(K'/L)`
  have hVinf : (⨅ L : FiniteGaloisIntermediateField K K',
      (V ⊔ L.fixingSubgroup : Subgroup Gal(K'/K))) = V :=
    NK.HassePrinciple.iInf_sup_eq_of_isClosed V hVcl
      (fun L : FiniteGaloisIntermediateField K K' => L.fixingSubgroup)
      (fun L => inferInstance) hB
  -- the family `V ⊔ Gal(K'/L)` is a directed family of closed sets
  have hFclosed : ∀ L : FiniteGaloisIntermediateField K K',
      IsClosed (((V ⊔ L.fixingSubgroup : Subgroup Gal(K'/K)) : Set Gal(K'/K))) :=
    fun L => Subgroup.isClosed_of_isOpen _ (Subgroup.isOpen_mono le_sup_right (hfixopen L))
  have hdir : ∀ L₁ L₂ : FiniteGaloisIntermediateField K K',
      ∃ L : FiniteGaloisIntermediateField K K',
        (((V ⊔ L.fixingSubgroup : Subgroup Gal(K'/K)) : Set Gal(K'/K))) ⊆
          (((V ⊔ L₁.fixingSubgroup : Subgroup Gal(K'/K)) : Set Gal(K'/K))) ∩
            (((V ⊔ L₂.fixingSubgroup : Subgroup Gal(K'/K)) : Set Gal(K'/K))) := by
    intro L₁ L₂
    refine ⟨L₁ ⊔ L₂, fun x hx => ⟨?_, ?_⟩⟩
    · exact (sup_le_sup_left (IntermediateField.fixingSubgroup_le
        (show (L₁ : IntermediateField K K') ≤
          ((L₁ ⊔ L₂ : FiniteGaloisIntermediateField K K') : IntermediateField K K')
          from le_sup_left)) V) hx
    · exact (sup_le_sup_left (IntermediateField.fixingSubgroup_le
        (show (L₂ : IntermediateField K K') ≤
          ((L₁ ⊔ L₂ : FiniteGaloisIntermediateField K K') : IntermediateField K K')
          from le_sup_right)) V) hx
  -- the intersection is `V`, which is disjoint from `Z`
  have hsub : (⋂ L : FiniteGaloisIntermediateField K K',
      ((V ⊔ L.fixingSubgroup : Subgroup Gal(K'/K)) : Set Gal(K'/K))) ⊆ Zᶜ := by
    rw [← Subgroup.coe_iInf, hVinf]
    intro x hx hxZ
    exact (Set.disjoint_left.mp hVZ) hx hxZ
  -- compactness: a single level already avoids `Z`
  obtain ⟨L, hL⟩ := exists_subset_iInf_subset_open hFclosed hdir hZ.isOpen_compl hsub
  refine ⟨(V ⊔ L.fixingSubgroup) ⊓ W, le_inf le_sup_left hVW, inf_le_right, ?_, ?_⟩
  · -- openness: `W'` contains the open subgroup `Gal(K'/L) ⊓ W`
    have hopen : IsOpen (((L.fixingSubgroup ⊓ W : Subgroup Gal(K'/K)) : Set Gal(K'/K))) := by
      rw [Subgroup.coe_inf]
      exact (hfixopen L).inter hW
    have hle : L.fixingSubgroup ⊓ W ≤ (V ⊔ L.fixingSubgroup) ⊓ W := by
      intro x hx
      exact ⟨Subgroup.mem_sup_right hx.1, hx.2⟩
    exact Subgroup.isOpen_mono hle hopen
  · rw [Set.disjoint_left]
    intro x hx hxZ
    exact hL hx.1 hxZ

end NK.NUV2.LC.RouteB
