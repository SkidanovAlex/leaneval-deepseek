import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.InertiaDefs
import Submission.Work.SSGRoute.exists_levelSub_le_of_isOpen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT.G1plusOwn

open scoped Pointwise

set_option linter.style.haveILetI false

/-- In a topological group `G`, if `W ≤ G` is open and `W ⊓ H ≤ Z`, then the elements of the
subgroup `H` (endowed with the subspace topology) that lie in `Z` form an open subset of `↥H`.

This is the observation that `Z ∩ H` is a union of cosets of the open subgroup `W ⊓ H`: it equals
`⋃_{g ∈ Z ∩ H} (g·W) ∩ H`, each of which is open in `↥H`. -/
lemma isOpen_subtype_val_preimage_of_le {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (H Z W : Subgroup G) (hW : IsOpen (W : Set G))
    (hWH : W ⊓ H ≤ Z) :
    IsOpen ((Subtype.val ⁻¹' (Z : Set G)) : Set ↥H) := by
  have hU : ∀ g : {g : ↥H // (g : G) ∈ Z},
      IsOpen {x : ↥H | ((g : ↥H) : G)⁻¹ * (x : G) ∈ (W : Set G)} := by
    intro g
    exact hW.preimage ((continuous_const.mul continuous_subtype_val :
      Continuous (fun x : ↥H => ((g : ↥H) : G)⁻¹ * (x : G))))
  rw [show (Subtype.val ⁻¹' (Z : Set G) : Set ↥H) =
      ⋃ (g : {g : ↥H // (g : G) ∈ Z}),
        {x : ↥H | ((g : ↥H) : G)⁻¹ * (x : G) ∈ (W : Set G)} from ?_]
  · exact isOpen_iUnion hU
  · ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · intro hx
      exact ⟨⟨x, hx⟩, by simp⟩
    · rintro ⟨g, hg⟩
      have hgH : ((g : ↥H) : G) ∈ H := (g : ↥H).2
      have hgZ : ((g : ↥H) : G) ∈ Z := g.2
      have hmemW : ((g : ↥H) : G)⁻¹ * (x : G) ∈ (W ⊓ H : Subgroup G) :=
        ⟨hg, H.mul_mem (H.inv_mem hgH) x.2⟩
      have hfin : ((g : ↥H) : G) * (((g : ↥H) : G)⁻¹ * (x : G)) ∈ Z :=
        Z.mul_mem hgZ (hWH hmemW)
      simpa using hfin

/-- **Compactness: if the subgroup `Z ≤ G_k` contains `W ⊓ D_A` for an open `W ≤ G_k` (and
`Z ⊇ I_A`), then the fixing subgroup of some finite Galois level `L ⊇ K` unramified at `A` meets
`D_A` inside `Z`.**

`k` a number field, `Ω` an algebraic closure, `K ≤ Ω` finite Galois unramified at the finite place
`A` (`hramA`), `Z ≤ G_k = Ω ≃ₐ[k] Ω` a subgroup containing `I_A` (`hIZ`) and containing `W ⊓ D_A`
for some open subgroup `W ≤ G_k` (`hW`).  Then there is a finite Galois level `L ⊇ K`, unramified
at `A`, with `∀ σ ∈ D_A, σ ∈ L.fixingSubgroup → σ ∈ Z`.

ROUTE (finite intersection property in the compact space `↥(decomp k A)`):

* `hW` makes `Z` open in the subspace `↥D_A`: `Z = ⋃_{z ∈ Z} z·(W ⊓ D_A)` as subsets of `D_A`
  (both are subgroups of `D_A`), and each `z·(W ⊓ D_A) = {δ : ↥D_A | z*δ ∈ W}` is the preimage of
  the open `W` under the continuous map `δ ↦ z*δ`.  (This is why `IsClosed Z` alone is NOT enough:
  `D_A ⊓ fix(L)` is an open — finite index — subgroup of `D_A`, so `Z = I_A` would be a
  counterexample; and no open subgroup of `D_A` is contained in `I_A`.)
* `𝒲 := {M : IntermediateField k Ω // FiniteDimensional k M ∧ Normal k M ∧ K ≤ M ∧
  I_A ≤ M.fixingSubgroup}` is nonempty (`K` is in it, `hramA`) and directed by `⊔`.
* `↥D_A` is compact (`Commons.FieldTheory.Galois.isClosed_stabilizer_valuationSubring` and
  `isCompact_iff_compactSpace`, `[CompactSpace G_k]`; `D_A` is a closed subgroup of the compact
  group `G_k`).
* The sets `s M := {δ : ↥D_A | δ ∈ M.fixingSubgroup} \ {δ : ↥D_A | δ ∈ Z}` are closed in `↥D_A`
  (`IntermediateField.fixingSubgroup_isClosed` and the openness of `Z` just established), and
  directed downward.
* `⋂_{M ∈ 𝒲} s M = ∅`: `δ` in the intersection lies in `D_A`, fixes every `M ∈ 𝒲` pointwise, so the
  hypothesis `hinter` (applied to `δ`, `hδD` and the family property) gives `δ ∈ I_A ≤ Z`,
  contradicting `δ ∉ Z`.
* `IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed` then shows that some `s M` is
  empty, i.e. `M.fixingSubgroup ⊓ D_A ≤ Z`; set `L := M`, with `IsGalois k L` from `Normal` +
  finite + `CharZero k` (`Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero`).

`hinter` is not an extra assumption in practice: it is exactly
`Work.SSGRoute.PT.G1plusOwn.mem_inertia_of_fixes_levels` of the sibling module, whose proof is
independent of the present statement. -/
theorem exists_level_unramified_le_of_isOpen
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (hramA : ¬ SSGRoute.IsRamifiedIn k K A)
    (Z : Subgroup (Ω ≃ₐ[k] Ω))
    (hW : ∃ W : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (W : Set (Ω ≃ₐ[k] Ω)) ∧
      W ⊓ SSGRoute.decomp k A ≤ Z)
    (hIZ : Work.SSGRoute.inertiaSub k Ω A ≤ Z)
    (hinter : ∀ δ ∈ SSGRoute.decomp k A,
      (∀ (M : IntermediateField k Ω) [FiniteDimensional k M] [Normal k M],
        K ≤ M → Work.SSGRoute.inertiaSub k Ω A ≤ M.fixingSubgroup → δ ∈ M.fixingSubgroup) →
      δ ∈ Work.SSGRoute.inertiaSub k Ω A) :
    ∃ (L : IntermediateField k Ω) (_ : FiniteDimensional k L) (_ : IsGalois k L),
      K ≤ L ∧ Work.SSGRoute.inertiaSub k Ω A ≤ L.fixingSubgroup ∧
      ∀ σ ∈ SSGRoute.decomp k A, σ ∈ L.fixingSubgroup → σ ∈ Z := by
  classical
  haveI : IsGalois k Ω := inferInstance
  haveI : CompactSpace (Ω ≃ₐ[k] Ω) := inferInstance
  -- `D_A` is closed in `G_k`, hence compact for the subspace topology.
  have hHclosed : IsClosed
      ((SSGRoute.decomp k A : Subgroup (Ω ≃ₐ[k] Ω)) : Set (Ω ≃ₐ[k] Ω)) :=
    Commons.FieldTheory.Galois.isClosed_stabilizer_valuationSubring (K := k) (K' := Ω) A
  haveI : CompactSpace ↥(SSGRoute.decomp k A) :=
    isCompact_iff_compactSpace.mp hHclosed.isCompact
  -- `W ⊓ D_A` is open in `↥D_A` and contained in `Z`, so `Z` is open in `↥D_A`.
  obtain ⟨W, hWopen, hWle⟩ := hW
  have hZopen : IsOpen
      ((Subtype.val ⁻¹' (Z : Set (Ω ≃ₐ[k] Ω))) : Set ↥(SSGRoute.decomp k A)) :=
    isOpen_subtype_val_preimage_of_le (SSGRoute.decomp k A) Z W hWopen hWle
  -- `K` is unramified at `A`, i.e. its fixing subgroup contains the inertia.
  have hIK : Work.SSGRoute.inertiaSub k Ω A ≤ K.fixingSubgroup := by
    intro σ hσ
    by_contra hnot
    exact hramA ⟨σ, (Work.SSGRoute.mem_inertiaSub k Ω A σ).mp hσ, hnot⟩
  -- the family of finite normal levels `M ≥ K` unramified at `A`
  let ι := {M : IntermediateField k Ω // FiniteDimensional k M ∧ Normal k M ∧ K ≤ M ∧
    Work.SSGRoute.inertiaSub k Ω A ≤ M.fixingSubgroup}
  haveI hιne : Nonempty ι := ⟨⟨K, inferInstance, inferInstance, le_rfl, hIK⟩⟩
  -- the closed subsets of `↥D_A` whose emptiness is the claim
  let t : ι → Set ↥(SSGRoute.decomp k A) := fun i =>
    {δ | (δ : Ω ≃ₐ[k] Ω) ∈ i.1.fixingSubgroup} ∩ {δ | (δ : Ω ≃ₐ[k] Ω) ∈ Z}ᶜ
  -- the family is directed downward: the compositum of two levels is a smaller set
  have htd : Directed (· ⊇ ·) t := by
    rintro ⟨M₁, h1fd, h1n, h1K, h1I⟩ ⟨M₂, h2fd, h2n, h2K, h2I⟩
    haveI := h1fd; haveI := h1n; haveI := h2fd; haveI := h2n
    have hsup : Work.SSGRoute.inertiaSub k Ω A ≤ (M₁ ⊔ M₂).fixingSubgroup := by
      rw [IntermediateField.fixingSubgroup_sup]
      exact le_inf h1I h2I
    refine ⟨⟨M₁ ⊔ M₂, inferInstance, inferInstance,
      h1K.trans le_sup_left, hsup⟩, ?_, ?_⟩
    · intro x hx
      exact ⟨IntermediateField.fixingSubgroup_le le_sup_left hx.1, hx.2⟩
    · intro x hx
      exact ⟨IntermediateField.fixingSubgroup_le le_sup_right hx.1, hx.2⟩
  -- each member of the family is closed in `↥D_A`
  have htc : ∀ i, IsClosed (t i) := by
    rintro ⟨M, hfd, hn, hK, hI⟩
    haveI := hfd; haveI := hn
    exact ((IntermediateField.fixingSubgroup_isClosed M).preimage
      continuous_subtype_val).inter hZopen.isClosed_compl
  -- the total intersection is empty: a common point fixes every level, hence is inertial
  have hst : (⋂ i, t i) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro δ hδ
    rw [Set.mem_iInter] at hδ
    have hfix : ∀ (M : IntermediateField k Ω) [FiniteDimensional k M] [Normal k M],
        K ≤ M → Work.SSGRoute.inertiaSub k Ω A ≤ M.fixingSubgroup →
        (δ : Ω ≃ₐ[k] Ω) ∈ M.fixingSubgroup := by
      intro M hfd hn hK hI
      exact (hδ ⟨M, hfd, hn, hK, hI⟩).1
    exact (hδ hιne.some).2 (hIZ (hinter (δ : Ω ≃ₐ[k] Ω) δ.2 hfix))
  -- if no member of the family were empty, compactness would give a common point
  by_contra hcon
  have hne : ∀ i, (t i).Nonempty := by
    rintro ⟨M, hfd, hn, hK, hI⟩
    haveI := hfd; haveI := hn
    rw [Set.nonempty_iff_ne_empty]
    intro hempty
    have hZ : ∀ σ ∈ SSGRoute.decomp k A, σ ∈ M.fixingSubgroup → σ ∈ Z := by
      intro σ hσD hσM
      by_contra hσZ
      have hmem : (⟨σ, hσD⟩ : ↥(SSGRoute.decomp k A)) ∈ t ⟨M, hfd, hn, hK, hI⟩ :=
        ⟨hσM, hσZ⟩
      rw [hempty] at hmem
      exact hmem
    exact hcon ⟨M, hfd,
      Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero, hK, hI, hZ⟩
  have hnon := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t htd hne
    (fun i => (htc i).isCompact) htc
  rw [hst] at hnon
  exact Set.not_nonempty_empty hnon

end Work.SSGRoute.PT.G1plusOwn
