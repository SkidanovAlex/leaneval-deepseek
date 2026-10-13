import Mathlib
import Submission.Work.WilE2.VcbDefs

/-!
  `Work.WilE2.mv_locallyConnected`

  If `V` is locally connected (as a subspace) and `G` is continuous on `V`, then the number of
  connected components of the superlevel set `V ∩ {G ≥ c}` is bounded by the number of connected
  components of the level set `V ∩ {G = c}` plus the number of connected components of `V`.

  The proof is the standard "inject the components" argument, in the form used for
  `Work.WilE2.mv_superlevel_encard`:

  * a component `U` of `V ∩ {G ≥ c}` meeting the level set is sent to the component of the level
    set it contains — this is injective because a component of the level set is a connected subset
    of the superlevel set, hence lies in a unique component;
  * a nonempty component `U` of `V ∩ {G ≥ c}` disjoint from the level set is a component of `V`:
    its points satisfy `G > c`, so `U` is a component of the *open* set `V ∩ {G > c}`, hence open
    (local connectedness), and it is a component of the closed set `V ∩ {G ≥ c}`, hence closed;
    a clopen connected subset of `V` is a component of `V`.

  The only place where the hypotheses are used beyond `mv_superlevel_encard` is the second point,
  isolated below as `connectedComponentIn_superlevel_eq`.
-/

namespace Work.WilE2

open Classical
open Set.Notation

/-- A connected component of a **closed** set is closed in the ambient space. -/
theorem isClosed_connectedComponentIn_of_isClosed {X : Type*} [TopologicalSpace X] {F : Set X}
    {x : X} (hF : IsClosed F) (hx : x ∈ F) : IsClosed (connectedComponentIn F x) := by
  rw [connectedComponentIn_eq_image hx, ← closure_subset_iff_isClosed]
  intro y hy
  have hyF : y ∈ F := hF.closure_subset (closure_mono (Set.image_val_subset) hy)
  have hmem : (⟨y, hyF⟩ : F) ∈ closure (connectedComponent (⟨x, hx⟩ : F)) := by
    rw [closure_subtype]
    exact hy
  rw [isClosed_connectedComponent.closure_eq] at hmem
  exact Set.mem_image_of_mem _ hmem

/-- The connected component of `p` in the subspace `V ↓∩ S` of `V`, pushed forward to `α`, is the
connected component of `p` in `S`.  (Here `S ⊆ V`.)  This is the dictionary between components
computed in `α` and components computed in the subtype `V`. -/
theorem image_val_connectedComponentIn {α : Type*} [TopologicalSpace α] {V S : Set α}
    (hSV : S ⊆ V) (p : V) (hp : (p : α) ∈ S) :
    (Subtype.val '' connectedComponentIn (V ↓∩ S) p : Set α) = connectedComponentIn S (p : α) := by
  apply Set.Subset.antisymm
  · have hpre : IsPreconnected (Subtype.val '' connectedComponentIn (V ↓∩ S) p) :=
      (Topology.IsInducing.subtypeVal.isPreconnected_image).mpr isPreconnected_connectedComponentIn
    have hsub : (Subtype.val '' connectedComponentIn (V ↓∩ S) p : Set α) ⊆ S := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact connectedComponentIn_subset (V ↓∩ S) p hy
    exact hpre.subset_connectedComponentIn
      (Set.mem_image_of_mem _ (mem_connectedComponentIn hp)) hsub
  · rw [connectedComponentIn_eq_image hp]
    set D : Set α := Subtype.val '' connectedComponent (⟨(p:α), hp⟩ : S) with hD
    have hDsub : D ⊆ V := by
      intro x hx
      rw [hD] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact hSV (connectedComponentIn_subset S (p:α) (by
        rw [connectedComponentIn_eq_image hp]; exact Set.mem_image_of_mem _ hy))
    set D' : Set V := V ↓∩ D with hD'
    have hD'img : (Subtype.val '' D' : Set α) = D := by
      rw [hD', Subtype.image_preimage_coe, Set.inter_eq_right.mpr hDsub]
    have hD'pre : IsPreconnected D' := by
      rw [← Topology.IsInducing.subtypeVal.isPreconnected_image, hD'img, hD]
      exact (Topology.IsInducing.subtypeVal.isPreconnected_image).mpr
        (isPreconnected_connectedComponent (x := (⟨(p:α), hp⟩ : S)))
    have hpD' : p ∈ D' := by
      rw [hD', hD]
      exact Set.mem_image_of_mem _ (mem_connectedComponent (x := (⟨(p:α), hp⟩ : S)))
    have hD'sub : D' ⊆ V ↓∩ S := by
      intro x hx
      have hxD : (x:α) ∈ D := by
        rw [← hD'img]
        exact Set.mem_image_of_mem _ hx
      rw [hD] at hxD
      obtain ⟨y, hy, hye⟩ := hxD
      have hyS : (y:α) ∈ S := connectedComponentIn_subset S (p:α) (by
        rw [connectedComponentIn_eq_image hp]; exact Set.mem_image_of_mem _ hy)
      show (x:α) ∈ S
      rw [← hye]
      exact hyS
    have hstep : D' ⊆ connectedComponentIn (V ↓∩ S) p :=
      hD'pre.subset_connectedComponentIn hpD' hD'sub
    rw [← hD'img]
    exact Set.image_val_mono hstep

/-- **A component of a closed set avoiding its frontier is a component of the whole space**, in a
locally connected space: it is closed (component of a closed set), and it is open (it is a
component of the open set `interior A`).  Hence it is a clopen connected set, i.e. a connected
component of the ambient space. -/
theorem connectedComponentIn_eq_connectedComponent_of_frontier_subset {X : Type*}
    [TopologicalSpace X] [LocallyConnectedSpace X] {A B : Set X} {x : X} (hA : IsClosed A)
    (hx : x ∈ A) (hfr : frontier A ⊆ B) (hdisj : Disjoint (connectedComponentIn A x) B) :
    connectedComponentIn A x = connectedComponent x := by
  set C := connectedComponentIn A x with hC
  have hCsub : C ⊆ interior A := by
    intro y hy
    have hyA : y ∈ A := connectedComponentIn_subset A x hy
    by_contra hyint
    have hyfr : y ∈ frontier A := by
      rw [hA.frontier_eq]; exact ⟨hyA, hyint⟩
    exact (Set.disjoint_left.mp hdisj hy) (hfr hyfr)
  have hxC : x ∈ C := mem_connectedComponentIn hx
  have hCint : C = connectedComponentIn (interior A) x := by
    apply Set.Subset.antisymm
    · exact (isPreconnected_connectedComponentIn).subset_connectedComponentIn hxC hCsub
    · exact connectedComponentIn_mono x interior_subset
  have hCopen : IsOpen C := by rw [hCint]; exact isOpen_interior.connectedComponentIn
  have hCclosed : IsClosed C := isClosed_connectedComponentIn_of_isClosed hA hx
  have h1 : C ⊆ connectedComponent x :=
    (isPreconnected_connectedComponentIn).subset_connectedComponent hxC
  have h2 : connectedComponent x ⊆ C :=
    IsClopen.connectedComponent_subset (⟨hCclosed, hCopen⟩ : IsClopen C) hxC
  exact Set.Subset.antisymm h1 h2

/-- **Key step.**  A component of the superlevel set `V ∩ {G ≥ c}` which does not meet the level
set `V ∩ {G = c}` is already a connected component of `V`.  This is the locally connected case of
`Work.WilE2.superlevel_component_eq`. -/
theorem connectedComponentIn_superlevel_eq {α : Type*} [TopologicalSpace α] (V : Set α)
    [LocallyConnectedSpace V] (G : α → ℝ) (c : ℝ) (hG : ContinuousOn G V) {x : α} (hxV : x ∈ V)
    (hxc : c ≤ G x)
    (h : connectedComponentIn (V ∩ {y | G y ≥ c}) x ∩ (V ∩ {y | G y = c}) = ∅) :
    connectedComponentIn (V ∩ {y | G y ≥ c}) x = connectedComponentIn V x := by
  set A : Set α := V ∩ {y | G y ≥ c} with hA
  set B : Set α := V ∩ {y | G y = c} with hB
  have hAV : A ⊆ V := by rw [hA]; exact Set.inter_subset_left
  have hBV : B ⊆ V := by rw [hB]; exact Set.inter_subset_left
  let p : V := ⟨x, hxV⟩
  have hpcoe : (p : α) = x := rfl
  have hpA : (p : α) ∈ A := by rw [hpcoe]; show x ∈ A; rw [hA]; exact ⟨hxV, hxc⟩
  have hpA' : p ∈ V ↓∩ A := hpA
  -- `V ↓∩ A` is closed in the space `V`, and its frontier lies in `V ↓∩ B`
  have hA'closed : IsClosed (V ↓∩ A) := by
    have heq : (V ↓∩ A) = {q : V | c ≤ G ↑q} := by
      ext q; rw [hA]; simp
    rw [heq]
    exact isClosed_le continuous_const hG.domRestrict
  have hfr : frontier (V ↓∩ A) ⊆ (V ↓∩ B) := by
    intro q hq
    rw [hA'closed.frontier_eq] at hq
    obtain ⟨hqA, hqint⟩ := hq
    have hqmem : (q:α) ∈ V ∩ {y | G y ≥ c} := hqA
    have hcq : c ≤ G ↑q := hqmem.2
    have hqV : (q:α) ∈ V := hqmem.1
    have hqeq : G ↑q = c := by
      by_contra hne
      have hlt : c < G ↑q := lt_of_le_of_ne hcq (Ne.symm hne)
      refine hqint (mem_interior_iff_mem_nhds.mpr ?_)
      have hWopen : IsOpen {r : V | c < G ↑r} := isOpen_lt continuous_const hG.domRestrict
      refine Filter.mem_of_superset (hWopen.mem_nhds hlt) ?_
      intro r hr
      exact ⟨r.2, by simpa using le_of_lt hr⟩
    show (q:α) ∈ V ∩ {y | G y = c}
    exact ⟨hqV, hqeq⟩
  have hdisj' : Disjoint (connectedComponentIn (V ↓∩ A) p) (V ↓∩ B) := by
    rw [Set.disjoint_left]
    intro z hz1 hz2
    have himg := image_val_connectedComponentIn hAV p hpA
    have hz1' : (z:α) ∈ connectedComponentIn A x := by
      have hmem : (z:α) ∈ (Subtype.val '' connectedComponentIn (V ↓∩ A) p : Set α) :=
        Set.mem_image_of_mem _ hz1
      rw [himg, hpcoe] at hmem
      exact hmem
    have hz2' : (z:α) ∈ B := by
      have himgB : (Subtype.val '' (V ↓∩ B) : Set α) = B := by
        rw [Subtype.image_preimage_coe, Set.inter_eq_right.mpr hBV]
      have hmem : (z:α) ∈ (Subtype.val '' (V ↓∩ B) : Set α) := Set.mem_image_of_mem _ hz2
      rwa [himgB] at hmem
    have hcontra : (z:α) ∈ connectedComponentIn A x ∩ B := ⟨hz1', hz2'⟩
    rw [h] at hcontra
    exact hcontra
  have hcrux := connectedComponentIn_eq_connectedComponent_of_frontier_subset hA'closed hpA' hfr hdisj'
  have hfinal : (Subtype.val '' connectedComponentIn (V ↓∩ A) p : Set α) = connectedComponentIn A x := by
    rw [image_val_connectedComponentIn hAV p hpA, hpcoe]
  rw [← hfinal, hcrux, connectedComponentIn_eq_image hxV]

/-- Auxiliary map used in the proof of `mv_locallyConnected`: a component of the superlevel set
is sent either to the empty set, to a component of the level set it contains, or to itself
(which will be a component of `V`). -/
private noncomputable def smap {α : Type*} [TopologicalSpace α] (V : Set α) (G : α → ℝ) (c : ℝ)
    (U : Set α) : Set α ⊕ Set α :=
  if h : (U ∩ (V ∩ {y | G y = c})).Nonempty then
    Sum.inl (connectedComponentIn (V ∩ {y | G y = c}) h.some)
  else if _ : U = ∅ then Sum.inl ∅
  else Sum.inr U

private lemma smap_of_mem {α : Type*} [TopologicalSpace α] (V : Set α) (G : α → ℝ) (c : ℝ)
    {U : Set α} (h : (U ∩ (V ∩ {y | G y = c})).Nonempty) :
    smap V G c U = Sum.inl (connectedComponentIn (V ∩ {y | G y = c}) h.some) := by
  rw [smap]; rw [dif_pos h]

private lemma smap_of_empty {α : Type*} [TopologicalSpace α] (V : Set α) (G : α → ℝ) (c : ℝ)
    {U : Set α} (h : ¬ (U ∩ (V ∩ {y | G y = c})).Nonempty) (hU : U = ∅) :
    smap V G c U = Sum.inl ∅ := by
  rw [smap]; rw [dif_neg h]; rw [dif_pos hU]

private lemma smap_of_ne {α : Type*} [TopologicalSpace α] (V : Set α) (G : α → ℝ) (c : ℝ)
    {U : Set α} (h : ¬ (U ∩ (V ∩ {y | G y = c})).Nonempty) (hU : U ≠ ∅) :
    smap V G c U = Sum.inr U := by
  rw [smap]; rw [dif_neg h]; rw [dif_neg hU]

/-- The number of connected components of a superlevel set `V ∩ {G ≥ c}` is bounded by the number
of connected components of the level set `V ∩ {G = c}` plus the number of connected components of
`V`, when `V` is locally connected and `G` is continuous on `V`. -/
theorem mv_locallyConnected {α : Type*} [TopologicalSpace α] (V : Set α) [LocallyConnectedSpace V]
    (G : α → ℝ) (c : ℝ) (hG : ContinuousOn G V) :
    (Set.range (connectedComponentIn (V ∩ {x | G x ≥ c}))).encard ≤
      (Set.range (connectedComponentIn (V ∩ {x | G x = c}))).encard +
        (Set.range (connectedComponentIn V)).encard := by
  set A : Set α := V ∩ {x | G x ≥ c} with hA
  set B : Set α := V ∩ {x | G x = c} with hB
  have hBsubA : B ⊆ A := by intro z hz; exact ⟨hz.1, ge_of_eq hz.2⟩
  have hBcomp : ∀ b ∈ B, connectedComponentIn B b ⊆ connectedComponentIn A b := by
    intro b hb
    exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn hb) (Set.Subset.trans (connectedComponentIn_subset B b) hBsubA)
  -- a component of `A` meeting `B` contains the component of `B` through any of its points
  have hKsub : ∀ U ∈ Set.range (connectedComponentIn A), ∀ b ∈ U ∩ B,
      connectedComponentIn B b ⊆ U := by
    intro U hU b hb
    obtain ⟨y, hy⟩ := hU
    have hbAy : b ∈ connectedComponentIn A y := hy.symm ▸ hb.1
    have hUA : U = connectedComponentIn A b := by
      rw [← hy, connectedComponentIn_eq hbAy]
    rw [hUA]; exact hBcomp b hb.2
  -- a component of `A` equals the component of `A` through any of its points
  have hUeq : ∀ U ∈ Set.range (connectedComponentIn A), ∀ b ∈ U, b ∈ A →
      U = connectedComponentIn A b := by
    intro U hU b hbU hbA
    obtain ⟨y, hy⟩ := hU
    have : connectedComponentIn A y = connectedComponentIn A b :=
      connectedComponentIn_eq (by rw [hy]; exact hbU)
    rw [← hy]; exact this
  -- a nonempty component of `A` disjoint from `B` is a component of `V`
  have hcase1 : ∀ U ∈ Set.range (connectedComponentIn A), U ≠ ∅ → ¬ (U ∩ B).Nonempty →
      U ∈ Set.range (connectedComponentIn V) := by
    intro U hU hUne hnoB
    obtain ⟨x, hx⟩ := hU
    have hxmem : x ∈ A := by
      by_contra hxn
      rw [connectedComponentIn_eq_empty hxn] at hx
      exact hUne hx.symm
    have hdisj : connectedComponentIn (V ∩ {y | G y ≥ c}) x ∩ (V ∩ {y | G y = c}) = ∅ := by
      rw [← hA, ← hB, hx]
      exact Set.not_nonempty_iff_eq_empty.mp hnoB
    have := connectedComponentIn_superlevel_eq V G c hG hxmem.1 hxmem.2 hdisj
    exact ⟨x, by rw [← this, hx]⟩
  set T : Set (Set α ⊕ Set α) :=
    (Sum.inl '' Set.range (connectedComponentIn B)) ∪
      (Sum.inr '' Set.range (connectedComponentIn V)) with hT
  have hMaps : Set.MapsTo (smap V G c) (Set.range (connectedComponentIn A)) T := by
    intro U hU
    rw [hT]
    simp only [Set.mem_union, Set.mem_image, Set.mem_range]
    by_cases h : (U ∩ B).Nonempty
    · rw [smap_of_mem V G c h]; left
      exact ⟨connectedComponentIn B h.some, ⟨h.some, rfl⟩, rfl⟩
    · by_cases hU0 : U = ∅
      · rw [smap_of_empty V G c h hU0]; left
        obtain ⟨z, hz⟩ := hU
        have hzA : z ∉ A := by
          intro hzain
          have hne : (connectedComponentIn A z).Nonempty :=
            connectedComponentIn_nonempty_iff.mpr hzain
          rw [hz, hU0] at hne
          exact Set.not_nonempty_empty hne
        have hzB : z ∉ B := fun hzb => hzA (hBsubA hzb)
        exact ⟨∅, ⟨z, connectedComponentIn_eq_empty hzB⟩, rfl⟩
      · rw [smap_of_ne V G c h hU0]; right
        exact ⟨U, hcase1 U hU hU0 h, rfl⟩
  have hInj : Set.InjOn (smap V G c) (Set.range (connectedComponentIn A)) := by
    intro U1 hU1 U2 hU2 heq
    by_cases h1 : (U1 ∩ B).Nonempty
    · rw [smap_of_mem V G c h1] at heq
      by_cases h2 : (U2 ∩ B).Nonempty
      · rw [smap_of_mem V G c h2] at heq
        have hK : connectedComponentIn B h1.some = connectedComponentIn B h2.some :=
          Sum.inl.inj heq
        have hsub1 : connectedComponentIn B h1.some ⊆ U1 :=
          hKsub U1 hU1 h1.some h1.some_mem
        have hsub2 : connectedComponentIn B h1.some ⊆ U2 := by
          rw [hK]; exact hKsub U2 hU2 h2.some h2.some_mem
        have hb1U2 : h1.some ∈ U2 := hsub2 (mem_connectedComponentIn h1.some_mem.2)
        have hb1A : h1.some ∈ A := hBsubA h1.some_mem.2
        rw [hUeq U1 hU1 h1.some h1.some_mem.1 hb1A,
          hUeq U2 hU2 h1.some hb1U2 hb1A]
      · by_cases hU2 : U2 = ∅
        · rw [smap_of_empty V G c h2 hU2] at heq
          exact absurd (Sum.inl.inj heq)
            (Set.Nonempty.ne_empty ⟨_, mem_connectedComponentIn h1.some_mem.2⟩)
        · rw [smap_of_ne V G c h2 hU2] at heq
          exact absurd heq (fun hc => Sum.inl_ne_inr hc)
    · by_cases hU1 : U1 = ∅
      · rw [smap_of_empty V G c h1 hU1] at heq
        by_cases h2 : (U2 ∩ B).Nonempty
        · rw [smap_of_mem V G c h2] at heq
          exact absurd (Sum.inl.inj heq).symm
            (Set.Nonempty.ne_empty ⟨_, mem_connectedComponentIn h2.some_mem.2⟩)
        · by_cases hU2 : U2 = ∅
          · rw [smap_of_empty V G c h2 hU2] at heq
            exact hU1.trans hU2.symm
          · rw [smap_of_ne V G c h2 hU2] at heq
            exact absurd heq (fun hc => Sum.inl_ne_inr hc)
      · rw [smap_of_ne V G c h1 hU1] at heq
        by_cases h2 : (U2 ∩ B).Nonempty
        · rw [smap_of_mem V G c h2] at heq
          exact absurd heq (fun hc => Sum.inl_ne_inr hc.symm)
        · by_cases hU2 : U2 = ∅
          · rw [smap_of_empty V G c h2 hU2] at heq
            exact absurd heq (fun hc => Sum.inl_ne_inr hc.symm)
          · rw [smap_of_ne V G c h2 hU2] at heq
            exact Sum.inr.inj heq
  have hle : (Set.range (connectedComponentIn A)).encard ≤ T.encard :=
    Set.encard_le_encard_of_injOn hMaps hInj
  have hdisj : Disjoint (Sum.inl '' Set.range (connectedComponentIn B))
      (Sum.inr '' Set.range (connectedComponentIn V)) := by
    rw [Set.disjoint_left]
    intro y hy1 hy2
    rw [Set.mem_image] at hy1 hy2
    obtain ⟨a, _, ha⟩ := hy1
    obtain ⟨b, _, hb⟩ := hy2
    exact Sum.inl_ne_inr (ha.trans hb.symm)
  have hTenc : T.encard = (Set.range (connectedComponentIn B)).encard +
      (Set.range (connectedComponentIn V)).encard := by
    rw [hT, Set.encard_union_eq hdisj,
      Function.Injective.encard_image Sum.inl_injective,
      Function.Injective.encard_image Sum.inr_injective]
  rw [← hTenc]
  exact hle

end Work.WilE2
