import Mathlib
import Submission.Work.SSGRoute.InertiaDefs
import Submission.Work.SSGRoute.exists_levelSub_le_of_isOpen
import Submission.Work.SSGRoute.levelInertia_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Level subgroups of the decomposition group refine open subgroups containing the inertia

Let `k` be a number field, `Ω` an algebraic closure of `k`, `K ⊆ Ω` a finite Galois extension of `k`
and `A` a finite place of `Ω`.  Write `H = D_A ∩ G_K` for the decomposition group of `A` cut down to
the Galois group of `K`.

The level subgroups `levelSub A M` (elements of `D_A` acting trivially modulo the maximal ideal on
the level subring `B ∩ M`) are closed in the Krull topology (`Work.SSGRoute.isClosed_levelSub`),
decrease with `M` (`Work.SSGRoute.levelSub_antitone`) and their intersection over all finite normal
`M` is the inertia subgroup `I_A` (`Work.SSGRoute.mem_levelSub_iff`).  Consequently, for a subgroup
`N ≤ H` whose intersection with a *closed* set is protected by an open subgroup (`hNopen`) and which
contains `I_A ∩ H`, some level subgroup meets `H` inside `N`.  The proof is the usual compactness /
finite intersection property argument.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped Pointwise

namespace Work.SSGRoute.ZConstruction

theorem levelKDecomp_exists_levelSub_le (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (N : Subgroup (Ω ≃ₐ[k] Ω))
    (hNle : N ≤ SSGRoute.decomp k A ⊓ K.fixingSubgroup)
    (hNopen : ∃ V : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (V : Set (Ω ≃ₐ[k] Ω)) ∧
      V ⊓ (SSGRoute.decomp k A ⊓ K.fixingSubgroup) ≤ N)
    (hI : SSGRoute.inertiaSub k Ω A ⊓ (SSGRoute.decomp k A ⊓ K.fixingSubgroup) ≤ N) :
    ∃ (M : IntermediateField k Ω) (_ : FiniteDimensional k M) (_ : Normal k M),
      Work.SSGRoute.levelSub A M ⊓ (SSGRoute.decomp k A ⊓ K.fixingSubgroup) ≤ N := by
  classical
  haveI : IsGalois k Ω := inferInstance
  haveI : CompactSpace (Ω ≃ₐ[k] Ω) := inferInstance
  obtain ⟨V, hVopen, hVle⟩ := hNopen
  -- `H`, the decomposition group of `A` cut down to `G_K`
  let H : Subgroup (Ω ≃ₐ[k] Ω) := SSGRoute.decomp k A ⊓ K.fixingSubgroup
  have hHraw : H = SSGRoute.decomp k A ⊓ K.fixingSubgroup := rfl
  -- `H` is closed (stable ℓ-adic/: intersection of the closed stabiliser with the open `G_K`)
  have hHclosed : IsClosed ((H : Subgroup (Ω ≃ₐ[k] Ω)) : Set (Ω ≃ₐ[k] Ω)) := by
    rw [hHraw]
    exact (Commons.FieldTheory.Galois.isClosed_stabilizer_valuationSubring (K := k) (K' := Ω) A).inter
      (IntermediateField.fixingSubgroup_isClosed K)
  -- the open set `N * V` meets `H` exactly in `N`
  have hNVopen : IsOpen (((N : Set (Ω ≃ₐ[k] Ω)) * (V : Set (Ω ≃ₐ[k] Ω)))) :=
    IsOpen.mul_left hVopen
  have hNVH : ∀ x : Ω ≃ₐ[k] Ω, x ∈ H →
      (x ∈ (N : Set (Ω ≃ₐ[k] Ω)) * (V : Set (Ω ≃ₐ[k] Ω)) ↔ x ∈ N) := by
    intro x hxH
    constructor
    · rintro ⟨a, ha, b, hb, hab⟩
      have haH : a ∈ H := hNle ha
      have hbH : b ∈ H := by
        have hb' : b = a⁻¹ * x := by rw [← hab]; simp
        rw [hb']
        exact H.mul_mem (H.inv_mem haH) hxH
      have hbN : b ∈ N := hVle ⟨hb, hbH⟩
      rw [← hab]
      exact N.mul_mem ha hbN
    · intro hxN
      exact ⟨x, hxN, 1, V.one_mem, mul_one x⟩
  -- the index type of finite normal levels
  let ι := {M : IntermediateField k Ω // FiniteDimensional k M ∧ Normal k M}
  haveI hι : Nonempty ι := ⟨⟨⊥, inferInstance, inferInstance⟩⟩
  -- the compact family whose emptiness is the claim
  let t : ι → Set (Ω ≃ₐ[k] Ω) := fun i =>
    letI : FiniteDimensional k i.1 := i.2.1
    letI : Normal k i.1 := i.2.2
    (((Work.SSGRoute.levelSub A i.1 : Subgroup (Ω ≃ₐ[k] Ω)) : Set (Ω ≃ₐ[k] Ω)) ∩
      (((N : Set (Ω ≃ₐ[k] Ω)) * (V : Set (Ω ≃ₐ[k] Ω)))ᶜ)) ∩ (H : Set (Ω ≃ₐ[k] Ω))
  have htd : Directed (· ⊇ ·) t := by
    rintro ⟨M₁, h1fd, h1n⟩ ⟨M₂, h2fd, h2n⟩
    haveI := h1fd; haveI := h1n; haveI := h2fd; haveI := h2n
    refine ⟨⟨M₁ ⊔ M₂, inferInstance, inferInstance⟩, ?_, ?_⟩
    · intro x hx
      exact ⟨⟨levelSub_antitone (B := A) (M := M₁) (M' := M₁ ⊔ M₂) le_sup_left hx.1.1, hx.1.2⟩,
        hx.2⟩
    · intro x hx
      exact ⟨⟨levelSub_antitone (B := A) (M := M₂) (M' := M₁ ⊔ M₂) le_sup_right hx.1.1, hx.1.2⟩,
        hx.2⟩
  have htc : ∀ i, IsClosed (t i) := by
    rintro ⟨M, hfd, hn⟩
    haveI := hfd; haveI := hn
    exact ((isClosed_levelSub A M).inter hNVopen.isClosed_compl).inter hHclosed
  -- the total intersection is empty
  have hst : (⋂ i, t i) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro δ hδ
    rw [Set.mem_iInter] at hδ
    have hInertia : SSGRoute.IsInertia k A δ :=
      (mem_levelSub_iff A δ).mp (fun M hfd hn => (hδ ⟨M, hfd, hn⟩).1.1)
    have hδH : δ ∈ H := (hδ ⟨⊥, inferInstance, inferInstance⟩).2
    have hδN : δ ∈ N := hI ⟨(mem_inertiaSub k Ω A δ).mpr hInertia, hδH⟩
    exact (hδ ⟨⊥, inferInstance, inferInstance⟩).1.2 ((hNVH δ hδH).mpr hδN)
  -- suppose no level subgroup works; compactness contradicts `hst`
  by_contra hcon
  have hne : ∀ i, (t i).Nonempty := by
    rintro ⟨M, hfd, hn⟩
    rw [Set.nonempty_iff_ne_empty]
    intro hempty
    apply hcon
    refine ⟨M, hfd, hn, fun x hx => ?_⟩
    by_contra hxN
    have hxL : x ∈ Work.SSGRoute.levelSub A M := hx.1
    have hxH : x ∈ H := hx.2
    have hxNV : x ∉ (N : Set (Ω ≃ₐ[k] Ω)) * (V : Set (Ω ≃ₐ[k] Ω)) :=
      fun h => hxN ((hNVH x hxH).mp h)
    have hmem : x ∈ t ⟨M, hfd, hn⟩ := ⟨⟨hxL, hxNV⟩, hxH⟩
    rw [hempty] at hmem
    exact hmem
  have hnon := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t htd hne
    (fun i => (htc i).isCompact) htc
  rw [hst] at hnon
  exact Set.not_nonempty_empty hnon

end Work.SSGRoute.ZConstruction
