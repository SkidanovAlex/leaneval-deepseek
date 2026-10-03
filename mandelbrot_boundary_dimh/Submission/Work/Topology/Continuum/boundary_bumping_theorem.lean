import Mathlib

/-!
# The Boundary Bumping Theorem

We prove the classical *boundary bumping theorem* of continuum theory (Whyburn, Nadler):

if `Z` is a continuum (a compact, connected Hausdorff space) and `p ≠ c` are points of `Z`,
then `p` lies in the closure of the connected component of `c` in `Z \ {p}`.

The proof is organised as a small chapter of the missing Mathlib theory:

* `closure_connectedComponentIn_inter_subset` : components of a subspace are closed in it;
* `isPreconnected_sInter_of_isChain` : the intersection of a chain of closed preconnected sets
  of a compact Hausdorff space is preconnected;
* `exists_isClopen_disjoint_of_disjoint_connectedComponent` : in a compact Hausdorff space a
  connected component and a disjoint closed set can be separated by a clopen set (this is the
  "quasi-components = components" theorem `connectedComponent_eq_iInter_isClopen` together with
  compactness);
* `exists_isClopen_subset_interior_of_disjoint_frontier` and
  `connectedComponentIn_inter_frontier_nonempty` : **boundary bumping** in the form
  "a component of a closed subset meets the boundary of that subset";
* `boundary_bumping_theorem` : the statement requested.
-/

namespace Work.Topology.Continuum

/-- The connected component of a point inside a subset is closed in that subset:
`closure C ∩ F = C` for `C = connectedComponentIn F x`. -/
private theorem closure_connectedComponentIn_inter_subset {α : Type*} [TopologicalSpace α]
    {F : Set α} {x : α} :
    closure (connectedComponentIn F x) ∩ F ⊆ connectedComponentIn F x := by
  by_cases hx : x ∈ F
  · rw [connectedComponentIn_eq_image hx]
    have hE : IsClosed (connectedComponent (⟨x, hx⟩ : F) : Set F) := isClosed_connectedComponent
    rw [isClosed_induced_iff'] at hE
    intro z hz
    obtain ⟨hzcl, hzF⟩ := hz
    rw [← Subtype.range_val (s := F)] at hzF
    obtain ⟨y, rfl⟩ := hzF
    exact ⟨y, hE y hzcl, rfl⟩
  · rw [connectedComponentIn_eq_empty hx]; simp

/-- The intersection of a chain of closed preconnected subsets of a compact Hausdorff space is
preconnected. -/
private theorem isPreconnected_sInter_of_isChain {Z : Type*} [TopologicalSpace Z]
    [CompactSpace Z] [T2Space Z] {S : Set (Set Z)} (hne : S.Nonempty)
    (hch : IsChain (· ⊆ ·) S) (hcl : ∀ s ∈ S, IsClosed s)
    (hpr : ∀ s ∈ S, IsPreconnected s) :
    IsPreconnected (⋂₀ S) := by
  haveI : Nonempty S := Set.Nonempty.to_subtype hne
  obtain ⟨s₀, hs₀⟩ := hne
  have hPcl : IsClosed (⋂₀ S) := isClosed_sInter hcl
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed hPcl]
  intro u v hu hv hPuv huv
  by_cases hR : (⋂₀ S ∩ u).Nonempty
  · by_cases hT : (⋂₀ S ∩ v).Nonempty
    · exfalso
      have hdisj : Disjoint (⋂₀ S ∩ u) (⋂₀ S ∩ v) := by
        rw [Set.disjoint_left]
        intro x hx1 hx2
        exact Set.disjoint_left.mp huv hx1.2 hx2.2
      obtain ⟨U, V, hUo, hVo, hRU, hTV, hUV⟩ :=
        normal_separation (hPcl.inter hu) (hPcl.inter hv) hdisj
      have hWcl : IsClosed ((U ∪ V)ᶜ : Set Z) := (hUo.union hVo).isClosed_compl
      have hsne : ∀ s ∈ S, (s ∩ (U ∪ V)ᶜ).Nonempty := by
        intro s hsS
        by_contra hne'
        rw [Set.not_nonempty_iff_eq_empty] at hne'
        have hsUV : s ⊆ U ∪ V := by
          intro x hx
          by_contra hx'
          have hmem : x ∈ s ∩ (U ∪ V)ᶜ := ⟨hx, hx'⟩
          rw [hne'] at hmem
          exact hmem
        have hRs : ⋂₀ S ∩ u ⊆ s :=
          (Set.inter_subset_left).trans (Set.sInter_subset_of_mem hsS)
        have hTs : ⋂₀ S ∩ v ⊆ s :=
          (Set.inter_subset_left).trans (Set.sInter_subset_of_mem hsS)
        have h1 : (s ∩ U).Nonempty := hR.mono (fun x hx => ⟨hRs hx, hRU hx⟩)
        have h2 : (s ∩ V).Nonempty := hT.mono (fun x hx => ⟨hTs hx, hTV hx⟩)
        have hcontra := hpr s hsS U V hUo hVo hsUV h1 h2
        obtain ⟨x, _, hx2, hx3⟩ := hcontra
        exact Set.disjoint_left.mp hUV hx2 hx3
      let t : S → Set Z := fun s => (s : Set Z) ∩ (U ∪ V)ᶜ
      have htclosed : ∀ s : S, IsClosed (t s) := fun s => (hcl s.1 s.2).inter hWcl
      have htcompact : ∀ s : S, IsCompact (t s) := fun s => (htclosed s).isCompact
      have htnonempty : ∀ s : S, (t s).Nonempty := fun s => hsne s.1 s.2
      have htdir : Directed (· ⊇ ·) t := by
        intro s1 s2
        rcases eq_or_ne s1 s2 with h | h
        · subst h; exact ⟨s1, subset_rfl, subset_rfl⟩
        · have hcmp : (s1 : Set Z) ⊆ s2 ∨ (s2 : Set Z) ⊆ s1 :=
            hch s1.2 s2.2 (fun hh => h (Subtype.ext hh))
          rcases hcmp with hle | hle
          · exact ⟨s1, subset_rfl, fun x hx => ⟨hle hx.1, hx.2⟩⟩
          · exact ⟨s2, (fun x hx => ⟨hle hx.1, hx.2⟩), subset_rfl⟩
      obtain ⟨x, hx⟩ :=
        IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
          t htdir htnonempty htcompact htclosed
      have hxW : x ∉ U ∪ V := (Set.mem_iInter.mp hx ⟨s₀, hs₀⟩).2
      have hPUV : ⋂₀ S ⊆ U ∪ V := by
        intro y hy
        rcases hPuv hy with hyu | hyv
        · exact Or.inl (hRU ⟨hy, hyu⟩)
        · exact Or.inr (hTV ⟨hy, hyv⟩)
      have hxP : x ∈ ⋂₀ S := by
        rw [Set.mem_sInter]
        intro s hsS
        exact (Set.mem_iInter.mp hx ⟨s, hsS⟩).1
      exact hxW (hPUV hxP)
    · left
      rw [Set.not_nonempty_iff_eq_empty] at hT
      intro x hx
      rcases hPuv hx with hxu | hxv
      · exact hxu
      · exfalso
        have hmem : x ∈ ⋂₀ S ∩ v := ⟨hx, hxv⟩
        rw [hT] at hmem
        exact hmem
  · right
    rw [Set.not_nonempty_iff_eq_empty] at hR
    intro x hx
    rcases hPuv hx with hxu | hxv
    · exfalso
      have hmem : x ∈ ⋂₀ S ∩ u := ⟨hx, hxu⟩
      rw [hR] at hmem
      exact hmem
    · exact hxv

/-- In a compact Hausdorff space, a connected component and a disjoint closed set can be
separated by a clopen set. -/
private theorem exists_isClopen_disjoint_of_disjoint_connectedComponent {Y : Type*}
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] {y : Y} {F : Set Y} (hFcl : IsClosed F)
    (hdisj : Disjoint (connectedComponent y) F) :
    ∃ W : Set Y, IsClopen W ∧ y ∈ W ∧ Disjoint W F := by
  have hF : IsCompact F := hFcl.isCompact
  have hd : Disjoint F (⋂ i : {s : Set Y // IsClopen s ∧ y ∈ s}, (i : Set Y)) := by
    rw [← connectedComponent_eq_iInter_isClopen y]
    exact hdisj.symm
  obtain ⟨u, hu⟩ := hF.elim_finite_subfamily_closed
    (fun i : {s : Set Y // IsClopen s ∧ y ∈ s} => (i : Set Y))
    (fun i => i.2.1.isClosed) hd
  refine ⟨⋂ i ∈ u, (i : Set Y), isClopen_biInter_finset (fun i _ => i.2.1), ?_, hu.symm⟩
  rw [Set.mem_iInter]
  intro i
  rw [Set.mem_iInter]
  intro _
  exact i.2.2

/-- In a compact Hausdorff space `X`, if `A` is closed and the connected component of `x ∈ A`
inside `A` misses the frontier of `A`, then that component can be separated from the frontier of
`A` by a clopen subset of `X` lying in the interior of `A`. -/
private theorem exists_isClopen_subset_interior_of_disjoint_frontier {X : Type*}
    [TopologicalSpace X] [CompactSpace X] [T2Space X] {A : Set X} (hAcl : IsClosed A) {x : X}
    (hx : x ∈ A) (hdisj : Disjoint (connectedComponentIn A x) (frontier A)) :
    ∃ W : Set X, IsClopen W ∧ connectedComponentIn A x ⊆ W ∧ W ⊆ interior A := by
  haveI : CompactSpace A := isCompact_iff_compactSpace.mp hAcl.isCompact
  let y : A := ⟨x, hx⟩
  have hFcl : IsClosed ((Subtype.val : A → X) ⁻¹' frontier A) :=
    isClosed_frontier.preimage continuous_subtype_val
  have hdisj' : Disjoint (connectedComponent y) ((Subtype.val : A → X) ⁻¹' frontier A) := by
    rw [Set.disjoint_left]
    intro z hz1 hz2
    have hzC : (z : X) ∈ connectedComponentIn A x := by
      rw [connectedComponentIn_eq_image hx]
      exact ⟨z, hz1, rfl⟩
    exact Set.disjoint_left.mp hdisj hzC hz2
  obtain ⟨Wbar, hWbar, hyWbar, hWd⟩ :=
    exists_isClopen_disjoint_of_disjoint_connectedComponent hFcl hdisj'
  have hsub : connectedComponent y ⊆ Wbar := by
    rw [connectedComponent_eq_iInter_isClopen]
    exact Set.iInter_subset (fun i : {s : Set A // IsClopen s ∧ y ∈ s} => (i : Set A))
      ⟨Wbar, hWbar, hyWbar⟩
  have hWint : (Subtype.val : A → X) '' Wbar ⊆ interior A := by
    have h1 : Disjoint ((Subtype.val : A → X) '' Wbar) (frontier A) := by
      rw [Set.disjoint_left]
      rintro w ⟨z, hz, rfl⟩ hwf
      exact Set.disjoint_left.mp hWd hz hwf
    rw [← self_sdiff_frontier A]
    intro w hw
    refine ⟨?_, ?_⟩
    · obtain ⟨z, _, rfl⟩ := hw
      exact z.2
    · exact (Set.disjoint_left.mp h1) hw
  refine ⟨(Subtype.val : A → X) '' Wbar, ?_, ?_, hWint⟩
  · constructor
    · obtain ⟨T, hTcl, hT⟩ := (isClosed_induced_iff (f := (Subtype.val : A → X))).mp hWbar.isClosed
      have hEq : (Subtype.val : A → X) '' Wbar = A ∩ T := by
        rw [← hT, Subtype.image_preimage_coe A T]
      rw [hEq]; exact hAcl.inter hTcl
    · obtain ⟨U, hUo, hU⟩ := (isOpen_induced_iff (f := (Subtype.val : A → X))).mp hWbar.isOpen
      have hEq : (Subtype.val : A → X) '' Wbar = U ∩ interior A := by
        rw [← hU, Subtype.image_preimage_coe A U]
        apply Set.Subset.antisymm
        · rintro w ⟨hwA, hwU⟩
          have hz : (⟨w, hwA⟩ : A) ∈ Wbar := by rw [← hU]; exact hwU
          exact ⟨hwU, hWint ⟨⟨w, hwA⟩, hz, rfl⟩⟩
        · rintro w ⟨hwU, hwi⟩
          exact ⟨interior_subset hwi, hwU⟩
      rw [hEq]; exact hUo.inter isOpen_interior
  · rw [connectedComponentIn_eq_image hx]
    exact Set.image_mono hsub

/-- **Boundary bumping** for a closed subset: a component of a closed proper subset of a continuum
meets the boundary of that subset. -/
private theorem connectedComponentIn_inter_frontier_nonempty {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] [ConnectedSpace X] {A : Set X} (hAcl : IsClosed A)
    (hAne : A ≠ Set.univ) {x : X} (hx : x ∈ A) :
    (connectedComponentIn A x ∩ frontier A).Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have hdisj : Disjoint (connectedComponentIn A x) (frontier A) :=
    Set.disjoint_iff_inter_eq_empty.mpr h
  obtain ⟨W, hWcl, hWsub, hWint⟩ :=
    exists_isClopen_subset_interior_of_disjoint_frontier hAcl hx hdisj
  have hWne : W.Nonempty := ⟨x, hWsub (mem_connectedComponentIn hx)⟩
  have hWproper : W ≠ Set.univ := by
    intro hW
    have hsub : (Set.univ : Set X) ⊆ interior A := hW ▸ hWint
    exact hAne (Set.eq_univ_of_univ_subset (hsub.trans interior_subset))
  have hz : ∃ z, z ∉ W := by
    by_contra hc
    simp only [not_exists, not_not] at hc
    exact hWproper (Set.eq_univ_iff_forall.mpr hc)
  obtain ⟨z, hzW⟩ := hz
  obtain ⟨w0, hw0⟩ := hWne
  obtain ⟨w, -, hwW, hwWc⟩ :=
    isPreconnected_univ (u := W) (v := Wᶜ) hWcl.isOpen hWcl.isClosed.isOpen_compl
      (by rw [Set.union_compl_self])
      ⟨w0, trivial, hw0⟩ ⟨z, trivial, hzW⟩
  exact hwWc hwW

/-- **Boundary Bumping Theorem** (classical, Whyburn/Nadler).

If `Z` is a continuum (compact, connected, Hausdorff) and `p ≠ c` are points, then the point `p`
lies in the closure of the connected component of `c` in `Z \ {p}`: components of the complement of
a point of a continuum "bump into" that point. -/
theorem boundary_bumping_theorem {Z : Type*} [TopologicalSpace Z] [CompactSpace Z] [T2Space Z]
    [ConnectedSpace Z] (p c : Z) (hc : c ≠ p) :
    p ∈ closure (connectedComponentIn ({p}ᶜ : Set Z) c) := by
  by_contra hp
  set C : Set Z := connectedComponentIn ({p}ᶜ : Set Z) c with hCdef
  have hcF : c ∈ ({p}ᶜ : Set Z) := by simpa using hc
  have hCc : c ∈ C := by rw [hCdef]; exact mem_connectedComponentIn hcF
  have hCpr : IsPreconnected C := by rw [hCdef]; exact isPreconnected_connectedComponentIn
  have hCcl : IsClosed C := by
    rw [← closure_subset_iff_isClosed]
    intro y hy
    have hyp : y ∈ ({p}ᶜ : Set Z) := by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hyq
      exact hp (hyq ▸ hy)
    have h0 := closure_connectedComponentIn_inter_subset (F := ({p}ᶜ : Set Z)) (x := c)
    rw [← hCdef] at h0
    exact h0 ⟨hy, hyp⟩
  have hdisj : Disjoint ({p} : Set Z) C := by
    rw [Set.disjoint_left]
    intro y hy1 hy2
    rw [Set.mem_singleton_iff] at hy1
    have : y ∈ ({p}ᶜ : Set Z) := by
      rw [hCdef] at hy2
      exact connectedComponentIn_subset _ _ hy2
    exact this (Set.mem_singleton_iff.mpr hy1)
  obtain ⟨U, V, hUo, hVo, hpU, hCV, hUV⟩ := normal_separation isClosed_singleton hCcl hdisj
  have hpinU : p ∈ U := hpU (Set.mem_singleton p)
  have hVcl : closure V ⊆ ({p}ᶜ : Set Z) := by
    intro y hy
    rw [Set.mem_compl_iff]
    intro hyp
    rw [Set.mem_singleton_iff] at hyp
    rw [hyp] at hy
    obtain ⟨w, hwU, hwV⟩ := (mem_closure_iff.mp hy) U hUo hpinU
    exact Set.disjoint_left.mp hUV hwU hwV
  set B : Set Z := closure V with hBdef
  have hBcl : IsClosed B := by rw [hBdef]; exact isClosed_closure
  have hCB : C ⊆ B := by rw [hBdef]; exact hCV.trans subset_closure
  have hcB : c ∈ B := hCB hCc
  have hBne : B ≠ Set.univ := by
    intro hB
    have hpB : p ∈ B := by rw [hB]; exact Set.mem_univ p
    exact (hVcl hpB) (Set.mem_singleton p)
  have hcomp : connectedComponentIn B c = C := by
    apply Set.Subset.antisymm
    · intro y hy
      have h2 : connectedComponentIn B c ⊆ ({p}ᶜ : Set Z) :=
        fun z hz => hVcl (connectedComponentIn_subset B c hz)
      have h3 := IsPreconnected.subset_connectedComponentIn (F := ({p}ᶜ : Set Z)) (x := c)
        (isPreconnected_connectedComponentIn (F := B)) (mem_connectedComponentIn hcB) h2 hy
      rw [← hCdef] at h3
      exact h3
    · intro y hy
      exact IsPreconnected.subset_connectedComponentIn hCpr hCc hCB hy
  have hne := connectedComponentIn_inter_frontier_nonempty hBcl hBne hcB
  rw [hcomp] at hne
  obtain ⟨w, hwC, hwf⟩ := hne
  have hwint : w ∈ interior B := by
    rw [hBdef]
    exact (hVo.subset_interior_iff.mpr subset_closure) (hCV hwC)
  rw [← closure_sdiff_interior] at hwf
  exact hwf.2 hwint

end Work.Topology.Continuum
