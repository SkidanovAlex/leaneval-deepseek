import Mathlib
import Submission.Work.BoxShrink.Pinch.janiszewskiDisjointCompact

/-!
# The Borsuk/Brouwer property: the frontier of a complementary domain of a continuum

**Reconstruction.**  This file had been lost from the sources of the workspace (only its compiled
artifact survived), which broke every module importing it: `Submission.Work.Smooth.SphereJordan.
outFrontierPath` and hence `hlocFix`, `loopInFrontier_chain_le`, `connectorWindingZero`,
`tauPocketConnector`, `envArcPiece`, `envPieceChain`, `chainAssemblyMine`, as well as
`Submission.Work.JordanSeparation.sphereJaniszewskiGen2`.

It re-establishes, *self-containedly*, the Borsuk–Brouwer property of the plane.  The development
below is the same Wilder argument that the workspace already carries in
`Submission.Work.Smooth.JordanSeparation.isPreconnected_frontier_connectedComponentIn`; it is
reproduced here (in the auxiliary namespace `Work.BoxShrink.Pinch.BorsukAux`) because that file
cannot be imported by `outFrontierPath`: both it and
`Submission.Work.Smooth.JordanSeparation.exists_continuum_separating` declare
`Work.Smooth.JordanSeparation.isPreconnected_insert_of_mem_closure`, so importing both clashes.
The two names that `outFrontierPath` uses are exported at the end, in `Work.BoxShrink.Pinch`.

The argument: the Phragmén–Brouwer property of the plane (`janiszewskiDisjointCompact`, Wilder's
Property I) implies Wilder's "Brouwer property" (Property II, Wilder, *Topology of Manifolds*,
II 4.1) via Wilder's Theorem II 4.3.
-/

namespace Work.BoxShrink.Pinch.BorsukAux

open Set

/-! ## Elementary connectedness helpers -/

/-- Adjoining a point of the closure to a preconnected set keeps it preconnected. -/
theorem isPreconnected_insert_of_mem_closure {α : Type*} [TopologicalSpace α] {S : Set α} {x : α}
    (hS : IsPreconnected S) (hx : x ∈ closure S) : IsPreconnected (insert x S) := by
  rw [isPreconnected_iff_subset_of_disjoint_closed]
  intro u v hu hv huv hdisj
  have hSuv : S ⊆ u ∪ v := (subset_insert x S).trans huv
  have hSdisj : S ∩ (u ∩ v) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem] at hdisj ⊢
    intro y hy
    exact hdisj y ⟨Or.inr hy.1, hy.2⟩
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hS) u v hu hv hSuv hSdisj with h | h
  · left
    rw [insert_subset_iff]
    exact ⟨hu.closure_eq ▸ closure_mono h hx, h⟩
  · right
    rw [insert_subset_iff]
    exact ⟨hv.closure_eq ▸ closure_mono h hx, h⟩

/-- If `s` and `t` are preconnected and `closure t` meets `s`, then `s ∪ t` is preconnected. -/
theorem IsPreconnected.union_of_closure_inter {α : Type*} [TopologicalSpace α] {s t : Set α}
    (hs : IsPreconnected s) (ht : IsPreconnected t) (h : (closure t ∩ s).Nonempty) :
    IsPreconnected (s ∪ t) := by
  rw [isPreconnected_iff_subset_of_disjoint]
  intro u v hu hv huv hdisj
  have hsuv : s ⊆ u ∪ v := fun z hz => huv (Or.inl hz)
  have htuv : t ⊆ u ∪ v := fun z hz => huv (Or.inr hz)
  have hsdisj : s ∩ (u ∩ v) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro z hz
    exact (Set.eq_empty_iff_forall_notMem.mp hdisj) z ⟨Or.inl hz.1, hz.2⟩
  have htdisj : t ∩ (u ∩ v) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro z hz
    exact (Set.eq_empty_iff_forall_notMem.mp hdisj) z ⟨Or.inr hz.1, hz.2⟩
  rcases (isPreconnected_iff_subset_of_disjoint.mp hs) u v hu hv hsuv hsdisj with hs' | hs'
  · rcases (isPreconnected_iff_subset_of_disjoint.mp ht) u v hu hv htuv htdisj with ht' | ht'
    · exact Or.inl (Set.union_subset hs' ht')
    · exfalso
      obtain ⟨w, hwt, hws⟩ := h
      have hwu : w ∈ u := hs' hws
      obtain ⟨g, hgu, hgt⟩ := mem_closure_iff.mp hwt u hu hwu
      exact (Set.eq_empty_iff_forall_notMem.mp hdisj) g ⟨Or.inr hgt, hgu, ht' hgt⟩
  · rcases (isPreconnected_iff_subset_of_disjoint.mp ht) u v hu hv htuv htdisj with ht' | ht'
    · exfalso
      obtain ⟨w, hwt, hws⟩ := h
      have hwv : w ∈ v := hs' hws
      obtain ⟨g, hgv, hgt⟩ := mem_closure_iff.mp hwt v hv hwv
      exact (Set.eq_empty_iff_forall_notMem.mp hdisj) g ⟨Or.inr hgt, ht' hgt, hgv⟩
    · exact Or.inr (Set.union_subset hs' ht')

/-- The complement of the frontier of an open set is the disjoint union of the set and of the
complement of its closure. -/
theorem compl_frontier_eq_of_isOpen {U : Set ℂ} (hU : IsOpen U) :
    (frontier U)ᶜ = U ∪ (closure U)ᶜ := by
  rw [hU.frontier_eq]
  ext z
  simp only [mem_compl_iff, mem_sdiff, mem_union, not_and]
  tauto

/-- The frontier of a connected component of the complement of a closed set is contained in that
set. -/
theorem frontier_connectedComponentIn_subset_closed {M : Set ℂ} (hM : IsClosed M) (x : ℂ) :
    frontier (connectedComponentIn Mᶜ x) ⊆ M := by
  by_cases hx : x ∈ Mᶜ
  · intro z hz
    by_contra hzM
    have hzMc : z ∈ Mᶜ := hzM
    set C : Set ℂ := connectedComponentIn Mᶜ x with hC
    have hCopen : IsOpen C := hM.isOpen_compl.connectedComponentIn
    have hzclC : z ∈ closure C := frontier_subset_closure hz
    have hznC : z ∉ C := by
      rw [hCopen.frontier_eq] at hz
      exact hz.2
    set Cz : Set ℂ := connectedComponentIn Mᶜ z with hCz
    have hCzopen : IsOpen Cz := hM.isOpen_compl.connectedComponentIn
    have hzCz : z ∈ Cz := mem_connectedComponentIn hzMc
    obtain ⟨w, hwCz, hwC⟩ := mem_closure_iff.mp hzclC Cz hCzopen hzCz
    have hunion : IsPreconnected (Cz ∪ C) :=
      IsPreconnected.union w hwCz hwC
        (isPreconnected_connectedComponentIn (F := Mᶜ) (x := z))
        (isPreconnected_connectedComponentIn (F := Mᶜ) (x := x))
    have hsub : Cz ∪ C ⊆ Mᶜ :=
      Set.union_subset (connectedComponentIn_subset Mᶜ z) (connectedComponentIn_subset Mᶜ x)
    have hxmem : x ∈ Cz ∪ C := Or.inr (mem_connectedComponentIn hx)
    have hzC : z ∈ C := hunion.subset_connectedComponentIn hxmem hsub (Or.inl hzCz)
    exact hznC hzC
  · rw [connectedComponentIn_eq_empty hx]
    simp

/-- In a connected, locally connected space, a component of a proper open set has closure meeting
the complement of that set. -/
theorem nonempty_closure_connectedComponentIn_inter_compl {X : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] [LocallyConnectedSpace X] {U : Set X} (hU : IsOpen U) {x : X}
    (hx : x ∈ U) (hUne : U ≠ univ) :
    (closure (connectedComponentIn U x) ∩ Uᶜ).Nonempty := by
  set C : Set X := connectedComponentIn U x with hC
  have hCopen : IsOpen C := hU.connectedComponentIn
  have hxcl : x ∈ C := mem_connectedComponentIn hx
  by_contra hcon
  rw [Set.not_nonempty_iff_eq_empty, Set.eq_empty_iff_forall_notMem] at hcon
  have hsub : closure C ⊆ U := by
    intro z hz
    by_contra hzU
    exact hcon z ⟨hz, hzU⟩
  have hcl_eq : closure C = C := by
    apply Set.Subset.antisymm _ subset_closure
    intro z hz
    have hzU : z ∈ U := hsub hz
    have hzCz : z ∈ connectedComponentIn U z := mem_connectedComponentIn hzU
    have hCzopen : IsOpen (connectedComponentIn U z) := hU.connectedComponentIn
    obtain ⟨w, hwCz, hwC⟩ :=
      mem_closure_iff.mp hz (connectedComponentIn U z) hCzopen hzCz
    have hunion : IsPreconnected (connectedComponentIn U z ∪ C) :=
      IsPreconnected.union w hwCz hwC
        (isPreconnected_connectedComponentIn (F := U) (x := z))
        (isPreconnected_connectedComponentIn (F := U) (x := x))
    have hsubU : connectedComponentIn U z ∪ C ⊆ U :=
      Set.union_subset (connectedComponentIn_subset U z) (connectedComponentIn_subset U x)
    have hxmem : x ∈ connectedComponentIn U z ∪ C := Or.inr hxcl
    exact hunion.subset_connectedComponentIn hxmem hsubU (Or.inl hzCz)
  have hCcl : IsClosed C := hcl_eq ▸ isClosed_closure
  have hclopen : IsClopen C := ⟨hCcl, hCopen⟩
  rcases (isClopen_iff.mp hclopen) with h | h
  · rw [h] at hxcl; exact absurd hxcl (notMem_empty x)
  · have hcu : (univ : Set X) ⊆ U := by
      have hc : closure C = univ := by rw [h]; simp
      rw [hc] at hsub; exact hsub
    exact hUne (top_unique hcu)

/-- For an open `U` and `x ∈ U`, the connected component of `x` in the complement of the frontier
of `U` is contained in `U`. -/
theorem connectedComponentIn_compl_frontier_subset {U : Set ℂ} (hU : IsOpen U) {x : ℂ}
    (hx : x ∈ U) : connectedComponentIn (frontier U)ᶜ x ⊆ U := by
  have hcompl : (frontier U)ᶜ = U ∪ (closure U)ᶜ := compl_frontier_eq_of_isOpen hU
  have hxmem : x ∈ (frontier U)ᶜ := by rw [hcompl]; exact Or.inl hx
  have hpre : IsPreconnected (connectedComponentIn (frontier U)ᶜ x) :=
    isPreconnected_connectedComponentIn
  have hsub : connectedComponentIn (frontier U)ᶜ x ⊆ U ∪ (closure U)ᶜ := by
    rw [← hcompl]; exact connectedComponentIn_subset _ _
  have hdisj : Disjoint U (closure U)ᶜ := by
    rw [Set.disjoint_left]
    exact fun z hzU hz => hz (subset_closure hzU)
  rcases hpre.subset_or_subset hU isClosed_closure.isOpen_compl hdisj hsub with h | h
  · exact h
  · have hx' := h (mem_connectedComponentIn hxmem)
    exact absurd (subset_closure hx) hx'

/-! ## Wilder's Theorem II 3.10 -/

/-- The `A`-side of `N` off `A ∪ B`: points of `N ∩ (A ∪ B)ᶜ` whose component of `(A ∪ B)ᶜ`
accumulates on `A`. -/
def aSideOf (A B N : Set ℂ) : Set ℂ :=
  {z : ℂ | z ∈ N ∧ z ∈ (A ∪ B)ᶜ ∧
    (closure (connectedComponentIn (A ∪ B)ᶜ z) ∩ A).Nonempty}

/-- The `B`-side of `N` off `A ∪ B`. -/
def bSideOf (A B N : Set ℂ) : Set ℂ :=
  {z : ℂ | z ∈ N ∧ z ∈ (A ∪ B)ᶜ ∧
    (closure (connectedComponentIn (A ∪ B)ᶜ z) ∩ B).Nonempty}

/-- The `A`-part of Wilder's auxiliary decomposition of `N`. -/
def aPrimeOf (A B N : Set ℂ) : Set ℂ := (N ∩ A) ∪ aSideOf A B N

/-- The `B`-part of Wilder's auxiliary decomposition of `N`. -/
def bPrimeOf (A B N : Set ℂ) : Set ℂ := (N ∩ B) ∪ bSideOf A B N

lemma mem_aSideOf {A B N : Set ℂ} {z : ℂ} :
    z ∈ aSideOf A B N ↔ z ∈ N ∧ z ∈ (A ∪ B)ᶜ ∧
      (closure (connectedComponentIn (A ∪ B)ᶜ z) ∩ A).Nonempty := by
  simp only [aSideOf, Set.mem_setOf_eq]

lemma mem_bSideOf {A B N : Set ℂ} {z : ℂ} :
    z ∈ bSideOf A B N ↔ z ∈ N ∧ z ∈ (A ∪ B)ᶜ ∧
      (closure (connectedComponentIn (A ∪ B)ᶜ z) ∩ B).Nonempty := by
  simp only [bSideOf, Set.mem_setOf_eq]

lemma mem_aPrimeOf {A B N : Set ℂ} {z : ℂ} :
    z ∈ aPrimeOf A B N ↔ (z ∈ N ∧ z ∈ A) ∨ z ∈ aSideOf A B N := by
  simp only [aPrimeOf, Set.mem_union, Set.mem_inter_iff]

lemma mem_bPrimeOf {A B N : Set ℂ} {z : ℂ} :
    z ∈ bPrimeOf A B N ↔ (z ∈ N ∧ z ∈ B) ∨ z ∈ bSideOf A B N := by
  simp only [bPrimeOf, Set.mem_union, Set.mem_inter_iff]

lemma aSideOf_eq_bSideOf_swap (A B N : Set ℂ) : aSideOf A B N = bSideOf B A N := by
  ext z
  simp only [mem_aSideOf, mem_bSideOf, Set.union_comm]

/-- **Core step of Wilder's Theorem II 3.10.**  If no preconnected `G ⊆ (A ∪ B)ᶜ` meeting `N` has
its closure meeting both `A` and `B`, then a point `p ∈ A` accumulating on the `B`-side of `N` and
a point `x` of that side, lying in a ball around `p` avoiding `B`, is impossible. -/
private lemma wilder_step {A B N : Set ℂ} (hAc : IsClosed A) (hBc : IsClosed B)
    (hnoG : ∀ G : Set ℂ, IsPreconnected G → G ⊆ (A ∪ B)ᶜ → (G ∩ N).Nonempty →
      ¬ ((closure G ∩ A).Nonempty ∧ (closure G ∩ B).Nonempty))
    {p x : ℂ} {ε : ℝ} (hpA : p ∈ A)
    (hpcl : p ∈ closure (bSideOf A B N))
    (hε : 0 < ε) (hBball : Metric.ball p ε ∩ B = ∅)
    (hxball : x ∈ Metric.ball p ε) (hxB : x ∈ bSideOf A B N) : False := by
  obtain ⟨hxN, hxΩ, hxQ⟩ := mem_bSideOf.mp hxB
  have hxA : x ∉ A := (by
    rw [Set.mem_compl_iff, Set.mem_union, not_or] at hxΩ
    exact hxΩ.1)
  have hCxpre : IsPreconnected (connectedComponentIn (A ∪ B)ᶜ x) :=
    isPreconnected_connectedComponentIn
  have hCxsub : connectedComponentIn (A ∪ B)ᶜ x ⊆ (A ∪ B)ᶜ := connectedComponentIn_subset _ _
  have hxmem : x ∈ connectedComponentIn (A ∪ B)ᶜ x := mem_connectedComponentIn hxΩ
  set σ : ℝ → ℂ := fun t => (1 - t) • x + t • p with hσdef
  have hσ : Continuous σ := by unfold σ; fun_prop
  have hσ0 : σ 0 = x := by simp [hσdef]
  have hσ1 : σ 1 = p := by simp [hσdef]
  set S : Set ℝ := Set.Icc 0 1 ∩ σ ⁻¹' A with hSdef
  have hSclosed : IsClosed S := isClosed_Icc.inter (hAc.preimage hσ)
  have hSne : S.Nonempty := ⟨1, by
    refine ⟨by norm_num, ?_⟩
    show σ 1 ∈ A
    rw [hσ1]; exact hpA⟩
  have hSbdd : BddBelow S := ⟨0, fun t ht => ht.1.1⟩
  have ht₀S : sInf S ∈ S := hSclosed.csInf_mem hSne hSbdd
  have ht₀A : σ (sInf S) ∈ A := ht₀S.2
  have ht₀Icc : sInf S ∈ Set.Icc (0:ℝ) 1 := ht₀S.1
  have h0notS : (0:ℝ) ∉ S := fun h => hxA (hσ0 ▸ h.2)
  have ht₀pos : 0 < sInf S :=
    lt_of_le_of_ne ht₀Icc.1 (fun h => h0notS (h ▸ ht₀S))
  have hIco_sub : Set.Ico 0 (sInf S) ⊆ Set.Icc (0:ℝ) 1 :=
    fun t ht => ⟨ht.1, le_trans ht.2.le ht₀Icc.2⟩
  have hnotA : ∀ t ∈ Set.Ico 0 (sInf S), σ t ∉ A := by
    intro t ht hA
    exact absurd (csInf_le hSbdd (show t ∈ S from ⟨hIco_sub ht, hA⟩)) (not_le.mpr ht.2)
  have hImgSub : σ '' Set.Ico 0 (sInf S) ⊆ Metric.ball p ε ∩ Aᶜ := by
    rintro z ⟨t, ht, rfl⟩
    refine ⟨?_, hnotA t ht⟩
    have ht01 := hIco_sub ht
    show (1 - t) • x + t • p ∈ Metric.ball p ε
    exact (convex_ball p ε) hxball (Metric.mem_ball_self hε)
      (by linarith [ht01.2]) ht01.1 (by ring)
  have hImgPre : IsPreconnected (σ '' Set.Ico 0 (sInf S)) :=
    (isPreconnected_Ico (a := (0:ℝ)) (b := sInf S)).image σ hσ.continuousOn
  have hImgΩ : σ '' Set.Ico 0 (sInf S) ⊆ (A ∪ B)ᶜ := by
    intro z hz
    obtain ⟨hzb, hzA⟩ := hImgSub hz
    rw [Set.mem_compl_iff, Set.mem_union, not_or]
    exact ⟨hzA, fun hzB => (Set.eq_empty_iff_forall_notMem.mp hBball) z ⟨hzb, hzB⟩⟩
  have hxmemImg : x ∈ σ '' Set.Ico 0 (sInf S) :=
    ⟨0, ⟨le_refl 0, ht₀pos⟩, hσ0⟩
  have hCxsup : σ '' Set.Ico 0 (sInf S) ⊆ connectedComponentIn (A ∪ B)ᶜ x :=
    hImgPre.subset_connectedComponentIn hxmemImg hImgΩ
  have ht₀cl : sInf S ∈ closure (Set.Ico 0 (sInf S)) := by
    rw [closure_Ico (a := (0:ℝ)) (b := sInf S) (ne_of_lt ht₀pos)]
    exact ⟨ht₀Icc.1, le_refl (sInf S)⟩
  have hσt₀cl : σ (sInf S) ∈ closure (σ '' Set.Ico 0 (sInf S)) :=
    image_closure_subset_closure_image hσ ⟨sInf S, ht₀cl, rfl⟩
  have hPx : (closure (connectedComponentIn (A ∪ B)ᶜ x) ∩ A).Nonempty :=
    ⟨σ (sInf S), closure_mono hCxsup hσt₀cl, ht₀A⟩
  exact hnoG (connectedComponentIn (A ∪ B)ᶜ x) hCxpre hCxsub ⟨x, hxmem, hxN⟩ ⟨hPx, hxQ⟩

/-- **Wilder's Theorem II 3.10 (the instance used here).**  If `A`, `B ⊆ ℂ` are disjoint closed sets
and `N` is a preconnected set meeting both, then there is a preconnected `G ⊆ (A ∪ B)ᶜ` meeting `N`
whose closure meets both `A` and `B`. -/
theorem exists_preconnected_closure_inter {A B : Set ℂ} (hAc : IsClosed A) (hBc : IsClosed B)
    (hAB : Disjoint A B) {N : Set ℂ} (hN : IsPreconnected N)
    (hNA : (N ∩ A).Nonempty) (hNB : (N ∩ B).Nonempty) :
    ∃ G : Set ℂ, IsPreconnected G ∧ G ⊆ (A ∪ B)ᶜ ∧ (G ∩ N).Nonempty ∧
      (closure G ∩ A).Nonempty ∧ (closure G ∩ B).Nonempty := by
  classical
  by_contra hcon
  have hnoG : ∀ G : Set ℂ, IsPreconnected G → G ⊆ (A ∪ B)ᶜ → (G ∩ N).Nonempty →
      ¬ ((closure G ∩ A).Nonempty ∧ (closure G ∩ B).Nonempty) :=
    fun G hG hGΩ hGN hg => hcon ⟨G, hG, hGΩ, hGN, hg.1, hg.2⟩
  have hΩne : (A ∪ B)ᶜ ≠ Set.univ := by
    obtain ⟨a, ha⟩ := hNA
    intro h
    have : a ∈ (A ∪ B)ᶜ := by rw [h]; exact Set.mem_univ a
    rw [Set.mem_compl_iff, Set.mem_union] at this
    exact this (Or.inl ha.2)
  have hP_or_Q : ∀ y, y ∈ N → y ∈ (A ∪ B)ᶜ →
      (closure (connectedComponentIn (A ∪ B)ᶜ y) ∩ A).Nonempty ∨
      (closure (connectedComponentIn (A ∪ B)ᶜ y) ∩ B).Nonempty := by
    intro y _ hyΩ
    have hpos : (closure (connectedComponentIn (A ∪ B)ᶜ y) ∩ ((A ∪ B)ᶜ)ᶜ).Nonempty :=
      Work.BoxShrink.Pinch.BorsukAux.nonempty_closure_connectedComponentIn_inter_compl
        (X := ℂ) (U := (A ∪ B)ᶜ) (hAc.union hBc).isOpen_compl hyΩ hΩne
    obtain ⟨z, hz, hzAB⟩ := hpos
    rw [compl_compl, Set.mem_union] at hzAB
    rcases hzAB with h | h
    · exact Or.inl ⟨z, hz, h⟩
    · exact Or.inr ⟨z, hz, h⟩
  have hnot_both : ∀ y, y ∈ N → y ∈ (A ∪ B)ᶜ →
      ¬ ((closure (connectedComponentIn (A ∪ B)ᶜ y) ∩ A).Nonempty ∧
        (closure (connectedComponentIn (A ∪ B)ᶜ y) ∩ B).Nonempty) :=
    fun y hyN hyΩ hboth => hnoG _ isPreconnected_connectedComponentIn
      (connectedComponentIn_subset _ _) ⟨y, mem_connectedComponentIn hyΩ, hyN⟩ hboth
  have hNsub : N ⊆ aPrimeOf A B N ∪ bPrimeOf A B N := by
    intro y hy
    by_cases hyA : y ∈ A
    · exact Or.inl (mem_aPrimeOf.mpr (Or.inl ⟨hy, hyA⟩))
    · by_cases hyB : y ∈ B
      · exact Or.inr (mem_bPrimeOf.mpr (Or.inl ⟨hy, hyB⟩))
      · have hyΩ : y ∈ (A ∪ B)ᶜ := by
          rw [Set.mem_compl_iff, Set.mem_union]; exact not_or.mpr ⟨hyA, hyB⟩
        rcases hP_or_Q y hy hyΩ with h | h
        · exact Or.inl (mem_aPrimeOf.mpr (Or.inr (mem_aSideOf.mpr ⟨hy, hyΩ, h⟩)))
        · exact Or.inr (mem_bPrimeOf.mpr (Or.inr (mem_bSideOf.mpr ⟨hy, hyΩ, h⟩)))
  have hA'B' : aPrimeOf A B N ∩ bPrimeOf A B N = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro y ⟨hyA', hyB'⟩
    rw [mem_aPrimeOf] at hyA'
    rw [mem_bPrimeOf] at hyB'
    rcases hyA' with ⟨hyN, hyA⟩ | hyAΩ
    · rcases hyB' with ⟨-, hyB⟩ | hyBΩ
      · exact Set.disjoint_left.mp hAB hyA hyB
      · have hb := (mem_bSideOf.mp hyBΩ).2.1
        rw [Set.mem_compl_iff, Set.mem_union, not_or] at hb
        exact hb.1 hyA
    · rcases hyB' with ⟨-, hyB⟩ | hyBΩ
      · have ha := (mem_aSideOf.mp hyAΩ).2.1
        rw [Set.mem_compl_iff, Set.mem_union, not_or] at ha
        exact ha.2 hyB
      · exact hnot_both y (mem_aSideOf.mp hyAΩ).1 (mem_aSideOf.mp hyAΩ).2.1
          ⟨(mem_aSideOf.mp hyAΩ).2.2, (mem_bSideOf.mp hyBΩ).2.2⟩
  have hA'ne : (aPrimeOf A B N).Nonempty := ⟨_, mem_aPrimeOf.mpr (Or.inl hNA.some_mem)⟩
  have hB'ne : (bPrimeOf A B N).Nonempty := ⟨_, mem_bPrimeOf.mpr (Or.inl hNB.some_mem)⟩
  have hA'subN : aPrimeOf A B N ⊆ N := by
    intro z hz
    rcases mem_aPrimeOf.mp hz with ⟨hzN, -⟩ | hzΩ
    · exact hzN
    · exact (mem_aSideOf.mp hzΩ).1
  have hB'subN : bPrimeOf A B N ⊆ N := by
    intro z hz
    rcases mem_bPrimeOf.mp hz with ⟨hzN, -⟩ | hzΩ
    · exact hzN
    · exact (mem_bSideOf.mp hzΩ).1
  have hnotsep : ¬ (aPrimeOf A B N ∩ (N ∩ closure (bPrimeOf A B N)) = ∅ ∧
      bPrimeOf A B N ∩ (N ∩ closure (aPrimeOf A B N)) = ∅) := by
    rintro ⟨h1, h2⟩
    have hdisj : N ∩ (closure (bPrimeOf A B N) ∩ closure (aPrimeOf A B N)) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro y ⟨hyN, hyb, hya⟩
      rcases hNsub hyN with hy | hy
      · rw [Set.eq_empty_iff_forall_notMem] at h1
        exact h1 y ⟨hy, hyN, hyb⟩
      · rw [Set.eq_empty_iff_forall_notMem] at h2
        exact h2 y ⟨hy, hyN, hya⟩
    have hNuv : N ⊆ closure (bPrimeOf A B N) ∪ closure (aPrimeOf A B N) := by
      intro y hy
      rcases hNsub hy with h | h
      · exact Or.inr (subset_closure h)
      · exact Or.inl (subset_closure h)
    rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hN) (closure (bPrimeOf A B N))
        (closure (aPrimeOf A B N)) isClosed_closure isClosed_closure hNuv hdisj with h | h
    · have hfull : aPrimeOf A B N ∩ (N ∩ closure (bPrimeOf A B N)) = aPrimeOf A B N :=
        Set.Subset.antisymm (fun z hz => hz.1) (fun z hz => ⟨hz, hA'subN hz, h (hA'subN hz)⟩)
      rw [hfull] at h1
      exact hA'ne.ne_empty h1
    · have hfull : bPrimeOf A B N ∩ (N ∩ closure (aPrimeOf A B N)) = bPrimeOf A B N :=
        Set.Subset.antisymm (fun z hz => hz.1) (fun z hz => ⟨hz, hB'subN hz, h (hB'subN hz)⟩)
      rw [hfull] at h2
      exact hB'ne.ne_empty h2
  have hclBΩ : ∀ p ∈ A, p ∈ closure (bPrimeOf A B N) → p ∈ closure (bSideOf A B N) := by
    intro p hpA hpcl
    have hpB : p ∉ B := fun h => Set.disjoint_left.mp hAB hpA h
    obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp hBc.isOpen_compl p hpB
    rw [mem_closure_iff] at hpcl ⊢
    intro W hW hpW
    obtain ⟨z, hzW, hzB'⟩ := hpcl (W ∩ Metric.ball p δ) (hW.inter Metric.isOpen_ball)
      ⟨hpW, Metric.mem_ball_self hδ⟩
    rw [mem_bPrimeOf] at hzB'
    refine ⟨z, hzW.1, ?_⟩
    rcases hzB' with ⟨-, hzB⟩ | hz
    · exact absurd hzB (hδsub hzW.2)
    · exact hz
  have hclAΩ : ∀ p ∈ B, p ∈ closure (aPrimeOf A B N) → p ∈ closure (aSideOf A B N) := by
    intro p hpB hpcl
    have hpA : p ∉ A := fun h => Set.disjoint_left.mp hAB h hpB
    obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp hAc.isOpen_compl p hpA
    rw [mem_closure_iff] at hpcl ⊢
    intro W hW hpW
    obtain ⟨z, hzW, hzA'⟩ := hpcl (W ∩ Metric.ball p δ) (hW.inter Metric.isOpen_ball)
      ⟨hpW, Metric.mem_ball_self hδ⟩
    rw [mem_aPrimeOf] at hzA'
    refine ⟨z, hzW.1, ?_⟩
    rcases hzA' with ⟨-, hzA⟩ | hz
    · exact absurd hzA (hδsub hzW.2)
    · exact hz
  rcases not_and_or.mp hnotsep with hkey | hkey
  · obtain ⟨p, hpA', hpNclB'⟩ := Set.nonempty_iff_ne_empty.mpr hkey
    have hpclB' : p ∈ closure (bPrimeOf A B N) := hpNclB'.2
    have hpN : p ∈ N := hpNclB'.1
    have hpΩ : p ∉ (A ∪ B)ᶜ := by
      intro hpΩmem
      have hpnotAB : p ∉ A ∧ p ∉ B := by
        rw [Set.mem_compl_iff, Set.mem_union, not_or] at hpΩmem
        exact hpΩmem
      have hpP : (closure (connectedComponentIn (A ∪ B)ᶜ p) ∩ A).Nonempty :=
        (mem_aPrimeOf.mp hpA').elim (fun h => absurd h.2 hpnotAB.1)
          (fun h => (mem_aSideOf.mp h).2.2)
      have hpnotAUB : p ∉ A ∪ B := by
        rw [Set.mem_union]; exact not_or.mpr hpnotAB
      obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp (hAc.union hBc).isOpen_compl p hpnotAUB
      obtain ⟨x, hxball, hxB'⟩ := mem_closure_iff.mp hpclB' (Metric.ball p ε) Metric.isOpen_ball
        (Metric.mem_ball_self hε)
      have hxnotAB : x ∉ A ∧ x ∉ B := by
        have h := hεsub hxball
        rw [Set.mem_compl_iff, Set.mem_union, not_or] at h
        exact h
      have hxSide : x ∈ bSideOf A B N := by
        rw [mem_bPrimeOf] at hxB'
        rcases hxB' with ⟨-, hxB⟩ | h
        · exact absurd hxB hxnotAB.2
        · exact h
      have hxmem2 : x ∈ connectedComponentIn (A ∪ B)ᶜ p :=
        (convex_ball p ε).isPreconnected.subset_connectedComponentIn (Metric.mem_ball_self hε)
          hεsub hxball
      have hxQ : (closure (connectedComponentIn (A ∪ B)ᶜ x) ∩ B).Nonempty :=
        (mem_bSideOf.mp hxSide).2.2
      rw [← connectedComponentIn_eq hxmem2] at hxQ
      exact hnoG (connectedComponentIn (A ∪ B)ᶜ p) isPreconnected_connectedComponentIn
        (connectedComponentIn_subset _ _)
        ⟨p, mem_connectedComponentIn (by rw [Set.mem_compl_iff]; exact hpΩmem), hpN⟩ ⟨hpP, hxQ⟩
    have hpAB : p ∈ A ∪ B := by
      by_contra h; exact hpΩ h
    have hpA : p ∈ A := by
      rcases hpAB with h | h
      · exact h
      · exfalso
        have : p ∈ bPrimeOf A B N := mem_bPrimeOf.mpr (Or.inl ⟨hpN, h⟩)
        exact (Set.eq_empty_iff_forall_notMem.mp hA'B') p ⟨hpA', this⟩
    have hpclBΩ : p ∈ closure (bSideOf A B N) := hclBΩ p hpA hpclB'
    obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp hBc.isOpen_compl p
      (fun h => Set.disjoint_left.mp hAB hpA h)
    have hballB : Metric.ball p ε ∩ B = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro z ⟨hzb, hzB⟩
      exact hεsub hzb hzB
    obtain ⟨x, hxball, hxBΩ⟩ := mem_closure_iff.mp hpclBΩ (Metric.ball p ε) Metric.isOpen_ball
      (Metric.mem_ball_self hε)
    exact wilder_step hAc hBc hnoG hpA hpclBΩ hε hballB hxball hxBΩ
  · obtain ⟨p, hpB', hpNclA'⟩ := Set.nonempty_iff_ne_empty.mpr hkey
    have hpclA' : p ∈ closure (aPrimeOf A B N) := hpNclA'.2
    have hpN : p ∈ N := hpNclA'.1
    have hpΩ : p ∉ (A ∪ B)ᶜ := by
      intro hpΩmem
      have hpnotAB : p ∉ A ∧ p ∉ B := by
        rw [Set.mem_compl_iff, Set.mem_union, not_or] at hpΩmem
        exact hpΩmem
      have hpQ : (closure (connectedComponentIn (A ∪ B)ᶜ p) ∩ B).Nonempty :=
        (mem_bPrimeOf.mp hpB').elim (fun h => absurd h.2 hpnotAB.2)
          (fun h => (mem_bSideOf.mp h).2.2)
      have hpnotAUB : p ∉ A ∪ B := by
        rw [Set.mem_union]; exact not_or.mpr hpnotAB
      obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp (hAc.union hBc).isOpen_compl p hpnotAUB
      obtain ⟨x, hxball, hxA'⟩ := mem_closure_iff.mp hpclA' (Metric.ball p ε) Metric.isOpen_ball
        (Metric.mem_ball_self hε)
      have hxnotAB : x ∉ A ∧ x ∉ B := by
        have h := hεsub hxball
        rw [Set.mem_compl_iff, Set.mem_union, not_or] at h
        exact h
      have hxSide : x ∈ aSideOf A B N := by
        rw [mem_aPrimeOf] at hxA'
        rcases hxA' with ⟨-, hxA⟩ | h
        · exact absurd hxA hxnotAB.1
        · exact h
      have hxmem2 : x ∈ connectedComponentIn (A ∪ B)ᶜ p :=
        (convex_ball p ε).isPreconnected.subset_connectedComponentIn (Metric.mem_ball_self hε)
          hεsub hxball
      have hxP : (closure (connectedComponentIn (A ∪ B)ᶜ x) ∩ A).Nonempty :=
        (mem_aSideOf.mp hxSide).2.2
      rw [← connectedComponentIn_eq hxmem2] at hxP
      exact hnoG (connectedComponentIn (A ∪ B)ᶜ p) isPreconnected_connectedComponentIn
        (connectedComponentIn_subset _ _)
        ⟨p, mem_connectedComponentIn (by rw [Set.mem_compl_iff]; exact hpΩmem), hpN⟩ ⟨hxP, hpQ⟩
    have hpAB : p ∈ A ∪ B := by
      by_contra h; exact hpΩ h
    have hpB : p ∈ B := by
      rcases hpAB with h | h
      · exfalso
        have : p ∈ aPrimeOf A B N := mem_aPrimeOf.mpr (Or.inl ⟨hpN, h⟩)
        exact (Set.eq_empty_iff_forall_notMem.mp hA'B') p ⟨this, hpB'⟩
      · exact h
    have hpclAΩ : p ∈ closure (aSideOf A B N) := hclAΩ p hpB hpclA'
    obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp hAc.isOpen_compl p
      (fun h => Set.disjoint_left.mp hAB h hpB)
    have hAball : Metric.ball p ε ∩ A = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro z ⟨hzb, hzA⟩
      exact hεsub hzb hzA
    obtain ⟨x, hxball, hxAΩ⟩ := mem_closure_iff.mp hpclAΩ (Metric.ball p ε) Metric.isOpen_ball
      (Metric.mem_ball_self hε)
    have hpclAΩ' : p ∈ closure (bSideOf B A N) := by
      rw [← aSideOf_eq_bSideOf_swap]; exact hpclAΩ
    have hxAΩ' : x ∈ bSideOf B A N := by
      rw [← aSideOf_eq_bSideOf_swap]; exact hxAΩ
    exact wilder_step hBc hAc (N := N)
      (fun G hG hGΩ hGN hg => hnoG G hG (by rwa [Set.union_comm]) hGN ⟨hg.2, hg.1⟩)
      hpB hpclAΩ' hε hAball hxball hxAΩ'

/-! ## The main theorem -/

/-- **The frontier of a complementary domain of a compact connected plane set is preconnected.**

This is Wilder's "Brouwer property" (Wilder, *Topology of Manifolds*, II 4.1), deduced from the
Phragmén–Brouwer property of the plane (Property I, `janiszewskiDisjointCompact`) by Wilder's
Theorem II 4.3.  For `x ∈ M` the component is empty and the statement is trivial; for `x ∉ M` the
component `C` is a complementary domain of the continuum `M`, and if its frontier `B` were
disconnected, `B = B₁ ⊔ B₂` with `B₁, B₂` disjoint compact, Wilder's Theorem II 3.10
(`exists_preconnected_closure_inter`) would give a preconnected `G ⊆ Bᶜ` meeting `M` whose closure
meets both `B₁` and `B₂`; the two preconnected sets `C ∪ B₂ ∪ G` and `C ∪ B₁ ∪ G` then show that
neither `B₁` nor `B₂` separates `x` from a point `y ∈ G ∩ M`, while `B = B₁ ∪ B₂` does — in
contradiction with the Phragmén–Brouwer property. -/
theorem isPreconnected_frontier_connectedComponentIn
    {M : Set ℂ} (hM : IsCompact M) (hMp : IsPreconnected M) (x : ℂ) :
    IsPreconnected (frontier (connectedComponentIn Mᶜ x)) := by
  by_cases hxM : x ∈ M
  · rw [connectedComponentIn_eq_empty (by simpa using hxM)]
    rw [frontier_empty]
    exact isPreconnected_empty
  · set C : Set ℂ := connectedComponentIn Mᶜ x with hCdef
    have hCopen : IsOpen C := hM.isClosed.isOpen_compl.connectedComponentIn
    have hCpre : IsPreconnected C := hCdef ▸ isPreconnected_connectedComponentIn
    have hxmem : x ∈ C := hCdef ▸ mem_connectedComponentIn (by simpa using hxM)
    have hCsub : C ⊆ Mᶜ := connectedComponentIn_subset Mᶜ x
    have hfr_sub : frontier C ⊆ M := frontier_connectedComponentIn_subset_closed hM.isClosed x
    have hCdisjB : ∀ z, z ∈ C → z ∈ frontier C → False := by
      intro z hzC hzB
      rw [hCopen.frontier_eq] at hzB
      exact hzB.2 hzC
    have hxnotB : x ∉ frontier C := fun h => hCdisjB x hxmem h
    rw [isPreconnected_iff_subset_of_disjoint_closed]
    intro u v hu hv huv hdisj
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨hnu, hnv⟩ := hcon
    have hB1ne : ((frontier C) ∩ u).Nonempty := by
      obtain ⟨z, hzB, hzv⟩ := not_subset.mp hnv
      exact ⟨z, hzB, by rcases huv hzB with h | h; exacts [h, absurd h hzv]⟩
    have hB2ne : ((frontier C) ∩ v).Nonempty := by
      obtain ⟨z, hzB, hzu⟩ := not_subset.mp hnu
      exact ⟨z, hzB, by rcases huv hzB with h | h; exacts [absurd h hzu, h]⟩
    have hB1c : IsCompact ((frontier C) ∩ u) :=
      (hM.of_isClosed_subset isClosed_frontier hfr_sub).of_isClosed_subset
        (isClosed_frontier.inter hu) inter_subset_left
    have hB2c : IsCompact ((frontier C) ∩ v) :=
      (hM.of_isClosed_subset isClosed_frontier hfr_sub).of_isClosed_subset
        (isClosed_frontier.inter hv) inter_subset_left
    have hdisjB : Disjoint ((frontier C) ∩ u) ((frontier C) ∩ v) := by
      rw [Set.disjoint_left]
      intro z hz1 hz2
      have hmem : z ∈ frontier C ∩ (u ∩ v) := ⟨hz1.1, hz1.2, hz2.2⟩
      rw [hdisj] at hmem
      exact hmem
    obtain ⟨G, hGpre, hGsub, hGN, hGA, hGB⟩ :=
      exists_preconnected_closure_inter (isClosed_frontier.inter hu) (isClosed_frontier.inter hv)
        hdisjB hMp
        ⟨_, hfr_sub hB1ne.some_mem.1, hB1ne.some_mem⟩
        ⟨_, hfr_sub hB2ne.some_mem.1, hB2ne.some_mem⟩
    obtain ⟨y, hyG, hyM⟩ := hGN
    have hynotC : y ∉ C := fun h => hCsub h hyM
    have hGsubB : G ⊆ (frontier C)ᶜ := by
      intro z hz hzB
      exact hGsub hz (by
        rcases huv hzB with h | h
        · exact Or.inl ⟨hzB, h⟩
        · exact Or.inr ⟨hzB, h⟩)
    have hCBpre : IsPreconnected (C ∪ (frontier C ∩ v)) :=
      hCpre.subset_closure subset_union_left (by
        rintro z (hz | hz)
        · exact subset_closure hz
        · exact frontier_subset_closure hz.1)
    have hCApre : IsPreconnected (C ∪ (frontier C ∩ u)) :=
      hCpre.subset_closure subset_union_left (by
        rintro z (hz | hz)
        · exact subset_closure hz
        · exact frontier_subset_closure hz.1)
    obtain ⟨w, hwcl, hwB2⟩ := hGB
    obtain ⟨w', hw'cl, hw'B1⟩ := hGA
    have hK1pre : IsPreconnected ((C ∪ (frontier C ∩ v)) ∪ G) :=
      IsPreconnected.union_of_closure_inter hCBpre hGpre ⟨w, hwcl, Or.inr hwB2⟩
    have hK2pre : IsPreconnected ((C ∪ (frontier C ∩ u)) ∪ G) :=
      IsPreconnected.union_of_closure_inter hCApre hGpre ⟨w', hw'cl, Or.inr hw'B1⟩
    have hK1sub : (C ∪ (frontier C ∩ v)) ∪ G ⊆ ((frontier C) ∩ u)ᶜ := by
      rintro z ((hz | hz) | hz)
      · exact fun h => hCdisjB z hz h.1
      · rintro ⟨hzB, hzu⟩
        have hmem : z ∈ frontier C ∩ (u ∩ v) := ⟨hzB, hzu, hz.2⟩
        rw [hdisj] at hmem
        exact hmem
      · exact fun h => hGsub hz (Or.inl h)
    have hK2sub : (C ∪ (frontier C ∩ u)) ∪ G ⊆ ((frontier C) ∩ v)ᶜ := by
      rintro z ((hz | hz) | hz)
      · exact fun h => hCdisjB z hz h.1
      · rintro ⟨hzB', hzv⟩
        have hmem : z ∈ frontier C ∩ (u ∩ v) := ⟨hzB', hz.2, hzv⟩
        rw [hdisj] at hmem
        exact hmem
      · exact fun h => hGsub hz (Or.inr h)
    have hy1 : y ∈ connectedComponentIn ((frontier C) ∩ u)ᶜ x :=
      hK1pre.subset_connectedComponentIn (Or.inl (Or.inl hxmem)) hK1sub (Or.inr hyG)
    have hy2 : y ∈ connectedComponentIn ((frontier C) ∩ v)ᶜ x :=
      hK2pre.subset_connectedComponentIn (Or.inl (Or.inl hxmem)) hK2sub (Or.inr hyG)
    have hxnotAB : x ∉ (frontier C ∩ u) ∪ (frontier C ∩ v) := by
      rintro (h | h)
      · exact hxnotB h.1
      · exact hxnotB h.1
    have hynotAB : y ∉ (frontier C ∩ u) ∪ (frontier C ∩ v) := by
      rintro (h | h)
      · exact hGsub hyG (Or.inl h)
      · exact hGsub hyG (Or.inr h)
    have hPB := Work.BoxShrink.Pinch.janiszewskiDisjointCompact hB1c hB2c hdisjB hxnotAB hynotAB
      hy1 hy2
    have hunion : (frontier C ∩ u) ∪ (frontier C ∩ v) = frontier C := by
      apply Set.Subset.antisymm
      · rintro z (h | h) <;> exact h.1
      · intro z hz
        rcases huv hz with h | h
        · exact Or.inl ⟨hz, h⟩
        · exact Or.inr ⟨hz, h⟩
    rw [hunion] at hPB
    exact hynotC (connectedComponentIn_compl_frontier_subset hCopen hxmem hPB)

end Work.BoxShrink.Pinch.BorsukAux

open Set

namespace Work.BoxShrink.Pinch

/-- **Borsuk–Brouwer property.**  For a compact preconnected set `M ⊆ ℂ` and any point `x`, the
frontier of the connected component of `x` in the complement `Mᶜ` is preconnected. -/
theorem borsuk_frontier_connectedComponentIn {M : Set ℂ} (hM : IsCompact M)
    (hMp : IsPreconnected M) (x : ℂ) :
    IsPreconnected (frontier (connectedComponentIn Mᶜ x)) :=
  Work.BoxShrink.Pinch.BorsukAux.isPreconnected_frontier_connectedComponentIn hM hMp x

/-- The closure (met with the open complement) of a complementary component stays inside it. -/
theorem closure_connectedComponentIn_inter_compl_subset_self {M : Set ℂ} {y : ℂ} :
    closure (connectedComponentIn Mᶜ y) ∩ Mᶜ ⊆ connectedComponentIn Mᶜ y := by
  intro z hz
  have hzcl : z ∈ closure (connectedComponentIn Mᶜ y) := hz.1
  have hzc : z ∈ Mᶜ := hz.2
  by_cases hy : y ∈ Mᶜ
  · have hpre : IsPreconnected ((connectedComponentIn Mᶜ y) ∪ {z}) :=
      isPreconnected_connectedComponentIn.subset_closure
        (by intro w hw; exact Or.inl hw)
        (by intro w hw; rcases hw with hw | hw
            · exact subset_closure hw
            · rw [Set.mem_singleton_iff] at hw; rw [hw]; exact hzcl)
    have hsub : (connectedComponentIn Mᶜ y) ∪ {z} ⊆ Mᶜ := by
      intro w hw
      rcases hw with hw | hw
      · exact connectedComponentIn_subset Mᶜ y hw
      · rw [Set.mem_singleton_iff] at hw; rw [hw]; exact hzc
    exact hpre.subset_connectedComponentIn (Or.inl (mem_connectedComponentIn hy)) hsub (Or.inr rfl)
  · rw [connectedComponentIn_eq_empty hy] at hzcl
    simpa using hzcl

end Work.BoxShrink.Pinch
