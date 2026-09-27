import Mathlib
import Submission.Work.Engulf.Defs
import Submission.Work.Engulf.Tools
import Submission.Work.Engulf.Basic
import Submission.Work.Engulf.Auxi.EngulfAux
import Submission.Work.Engulf.Auxi.SubdivCard
import Submission.Work.Engulf.Auxi.Carrier
import Submission.Work.Engulf.Auxi.TameTransfer

open Set Metric PL

namespace Work.Engulf.Chain

universe u

set_option maxHeartbeats 1000000

/-! ## Elementary API for `E2`

`E2` works with the subcomplexes of a *subdivision* `Γ₁ = sdIter r Γ` of the ambient complex
`Γ`: `P₁` (faces already mapped into `V`), `Sk` (faces with `≤ k` vertices) and the list `bad` of
the `(k+1)`-vertex faces whose image is not yet in `V`.  The lemmas below are the point-set and
combinatorial tools for that decomposition. -/

theorem isSubSp_simp {N : ℕ} {Γ : Cx N} {s : Finset (E N)} (hs : s ∈ Γ.faces) :
    Work.Engulf.IsSubSp Γ (simp s) :=
  ⟨fun _ hx => Geometry.SimplicialComplex.convexHull_subset_space hs hx,
   fun _ hx => ⟨s, hs, hx, fun _ hy => hy⟩⟩

theorem isSubSp_iUnion {N : ℕ} {Γ : Cx N} {ι : Sort*} {S : ι → Set (E N)}
    (h : ∀ i, Work.Engulf.IsSubSp Γ (S i)) : Work.Engulf.IsSubSp Γ (⋃ i, S i) :=
  ⟨fun x hx => by
     obtain ⟨i, hx⟩ := Set.mem_iUnion.1 hx
     exact (h i).1 hx,
   fun x hx => by
     obtain ⟨i, hx⟩ := Set.mem_iUnion.1 hx
     obtain ⟨s, hs, hxs, hsub⟩ := (h i).2 x hx
     exact ⟨s, hs, hxs, fun y hy => Set.mem_iUnion.2 ⟨i, hsub hy⟩⟩⟩

theorem isSubSp_biUnion_E2 {N : ℕ} {Γ : Cx N} {ι : Type*} (u : Finset ι) {S : ι → Set (E N)}
    (h : ∀ i ∈ u, Work.Engulf.IsSubSp Γ (S i)) : Work.Engulf.IsSubSp Γ (⋃ i ∈ u, S i) :=
  ⟨fun x hx => by
     obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.1 hx
     exact (h i hi).1 hx,
   fun x hx => by
     obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.1 hx
     obtain ⟨s, hs, hxs, hsub⟩ := (h i hi).2 x hx
     exact ⟨s, hs, hxs, fun y hy => Set.mem_iUnion₂.2 ⟨i, hi, hsub hy⟩⟩⟩

/-- **Decomposition tool.** A face `s` of `Γ` whose simplex is covered by a finite union of union
of faces lies in one of them (barycentre + uniqueness of barycentric coordinates). -/
theorem exists_of_simp_subset_iUnion {N : ℕ} {Γ : Cx N} {ι : Type*} {u : Finset ι}
    {S : ι → Set (E N)} (hS : ∀ i ∈ u, Work.Engulf.IsSubSp Γ (S i)) {s : Finset (E N)}
    (hs : s ∈ Γ.faces) (h : simp s ⊆ ⋃ i ∈ u, S i) : ∃ i ∈ u, simp s ⊆ S i := by
  have hsne : s.Nonempty := Γ.nonempty_of_mem_faces hs
  have hb : bary s ∈ ⋃ i ∈ u, S i := h (Work.Engulf.bary_mem_simp hsne)
  obtain ⟨i, hiu, hbi⟩ := Set.mem_iUnion₂.1 hb
  obtain ⟨t, ht, hbt, htS⟩ := (hS i hiu).2 (bary s) hbi
  exact ⟨i, hiu, (simp_mono (Work.Engulf.bary_mem_simp_subset hs ht hbt)).trans htS⟩

/-- The same for a union over an arbitrary type. -/
theorem exists_of_simp_subset_iUnion' {N : ℕ} {Γ : Cx N} {ι : Sort*} {S : ι → Set (E N)}
    (hS : ∀ i, Work.Engulf.IsSubSp Γ (S i)) {s : Finset (E N)} (hs : s ∈ Γ.faces)
    (h : simp s ⊆ ⋃ i, S i) : ∃ i, simp s ⊆ S i := by
  have hsne : s.Nonempty := Γ.nonempty_of_mem_faces hs
  have hb : bary s ∈ ⋃ i, S i := h (Work.Engulf.bary_mem_simp hsne)
  obtain ⟨i, hbi⟩ := Set.mem_iUnion.1 hb
  obtain ⟨t, ht, hbt, htS⟩ := (hS i).2 (bary s) hbi
  exact ⟨i, (simp_mono (Work.Engulf.bary_mem_simp_subset hs ht hbt)).trans htS⟩

/-- A face inside the union of two subcomplexes is inside one of them. -/
theorem subset_of_simp_subset_union {N : ℕ} {Γ : Cx N} {A B : Set (E N)}
    (hA : Work.Engulf.IsSubSp Γ A) (hB : Work.Engulf.IsSubSp Γ B) {s : Finset (E N)}
    (hs : s ∈ Γ.faces) (h : simp s ⊆ A ∪ B) : simp s ⊆ A ∨ simp s ⊆ B := by
  have hsne : s.Nonempty := Γ.nonempty_of_mem_faces hs
  have hb : bary s ∈ A ∪ B := h (Work.Engulf.bary_mem_simp hsne)
  rcases hb with hb | hb
  · obtain ⟨t, ht, hbt, htA⟩ := hA.2 (bary s) hb
    exact Or.inl ((simp_mono (Work.Engulf.bary_mem_simp_subset hs ht hbt)).trans htA)
  · obtain ⟨t, ht, hbt, htB⟩ := hB.2 (bary s) hb
    exact Or.inr ((simp_mono (Work.Engulf.bary_mem_simp_subset hs ht hbt)).trans htB)

/-- The three-fold version (`(A ∪ B) ∪ C`). -/
theorem subset_of_simp_subset_union3 {N : ℕ} {Γ : Cx N} {A B C : Set (E N)}
    (hA : Work.Engulf.IsSubSp Γ A) (hB : Work.Engulf.IsSubSp Γ B) (hC : Work.Engulf.IsSubSp Γ C)
    {s : Finset (E N)} (hs : s ∈ Γ.faces) (h : simp s ⊆ A ∪ B ∪ C) :
    simp s ⊆ A ∨ simp s ⊆ B ∨ simp s ⊆ C := by
  rcases subset_of_simp_subset_union (Work.Engulf.isSubSp_union hA hB) hC hs h with h' | h'
  · rcases subset_of_simp_subset_union hA hB hs h' with h'' | h''
    · exact Or.inl h''
    · exact Or.inr (Or.inl h'')
  · exact Or.inr (Or.inr h')

/-! ### Compactness and disjointness -/

/-- If `X ⊆ V` with `V` open then the part of `X ∪ g '' T` outside `V` is the compact part of
`g '' T`. -/
theorem isCompact_sdiff_of_subset {N : ℕ} {M : Type*} [MetricSpace M] {Γ : Cx N} {X : Set M}
    (hXc : IsClosed X) {T : Set (E N)} (hT : IsCompact T) (hTsp : T ⊆ Γ.space)
    {g : E N → M} (hg : ContinuousOn g Γ.space) {V : Set M} (hVo : IsOpen V) (hXV : X ⊆ V) :
    IsCompact ((X ∪ g '' T) \ V) := by
  have hImg : IsCompact (g '' T) := hT.image_of_continuousOn (hg.mono hTsp)
  refine hImg.of_isClosed_subset ((hXc.union hImg.isClosed).sdiff hVo) ?_
  intro z hz
  rw [Set.mem_sdiff] at hz
  obtain ⟨hzin, hzV⟩ := hz
  rw [Set.mem_union] at hzin
  rcases hzin with hz | hz
  · exact absurd (hXV hz) hzV
  · exact hz

/-- The same when `X ∪ g '' K` is already engulfed in `V`. -/
theorem isCompact_sdiff_of_engulfs_E2 {N : ℕ} {M : Type*} [MetricSpace M] {Γ : Cx N} {X : Set M}
    (hXc : IsClosed X) {K T : Set (E N)} (hK : Work.Engulf.IsSubSp Γ K) (hfin : Γ.faces.Finite)
    (hT : IsCompact T) (hTsp : T ⊆ Γ.space) {g : E N → M} (hg : ContinuousOn g Γ.space)
    {V : Set M} (hVo : IsOpen V) (hVK : X ∪ g '' K ⊆ V) :
    IsCompact ((X ∪ g '' (K ∪ T)) \ V) := by
  have hImgK : IsCompact (g '' K) :=
    (Work.Engulf.isCompact_of_isSubSp hfin hK).image_of_continuousOn (hg.mono hK.1)
  have hImgT : IsCompact (g '' T) := hT.image_of_continuousOn (hg.mono hTsp)
  have hclosed : IsClosed (X ∪ g '' (K ∪ T)) := by
    rw [Set.image_union]
    exact hXc.union (hImgK.union hImgT).isClosed
  refine hImgT.of_isClosed_subset (hclosed.sdiff hVo) ?_
  intro z hz
  rw [Set.mem_sdiff] at hz
  obtain ⟨hzin, hzV⟩ := hz
  rw [Set.mem_union] at hzin
  rcases hzin with hz | hz
  · exact absurd (hVK (Or.inl hz)) hzV
  · rw [Set.image_union, Set.mem_union] at hz
    rcases hz with hz | hz
    · exact absurd (hVK (Or.inr hz)) hzV
    · exact hz

/-- `g '' K` misses `X` once `g` is closer to `f` than the distance from `f '' K` to `X`. -/
theorem image_disjoint_of_margin {N : ℕ} {M : Type*} [MetricSpace M] {K : Set (E N)}
    {f g : E N → M} {X : Set M} {ρ : ℝ} (hρ : ∀ x ∈ K, ∀ y ∈ X, ρ ≤ dist (f x) y)
    (hd : ∀ x ∈ K, dist (g x) (f x) < ρ) : Disjoint (g '' K) X := by
  rw [Set.disjoint_left]
  rintro z ⟨x, hx, rfl⟩ hy
  have h1 : ρ ≤ dist (f x) (g x) := hρ x hx (g x) hy
  have h2 := hd x hx
  rw [dist_comm] at h2
  linarith

/-! ### The engulfed union of the `E2` loop -/

/-- The subcomplex engulfed by the `E2` loop after `j` steps. -/
def HjSet {N : ℕ} (P1 Sk : Set (E N)) (bad : List (Finset (E N))) (j : ℕ) : Set (E N) :=
  P1 ∪ Sk ∪ ⋃ i ∈ Finset.range j, ⋃ (hi : i < bad.length), simp bad[i]

/-- Splitting the union over `range (i+1)`. -/
theorem iUnion_range_succ' {α : Type*} (f : ℕ → Set α) (i : ℕ) :
    (⋃ j ∈ Finset.range (i + 1), f j) = f i ∪ ⋃ j ∈ Finset.range i, f j := by
  ext x
  simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_union, exists_prop]
  constructor
  · rintro ⟨j, hj, hx⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | rfl
    · exact Or.inr ⟨j, hj', hx⟩
    · exact Or.inl hx
  · rintro (hx | ⟨j, hj, hx⟩)
    · exact ⟨i, Nat.lt_succ_self i, hx⟩
    · exact ⟨j, Nat.lt_succ_of_lt hj, hx⟩

/-- Membership in the union over a list. -/
theorem mem_list_iUnion {N : ℕ} {bad : List (Finset (E N))} {x : E N} :
    x ∈ (⋃ s ∈ bad, simp s) ↔ ∃ s ∈ bad, x ∈ simp s := by
  simp only [Set.mem_iUnion, exists_prop]

/-- The union over a list is the union over its indices. -/
theorem iUnion_list_eq_range_E2 {N : ℕ} (bad : List (Finset (E N))) :
    (⋃ s ∈ bad, simp s) = ⋃ i ∈ Finset.range bad.length,
      ⋃ (hi : i < bad.length), simp bad[i] := by
  ext x
  rw [mem_list_iUnion]
  simp only [Set.mem_iUnion, Finset.mem_range, exists_prop]
  constructor
  · rintro ⟨s, hs, hxs⟩
    obtain ⟨i, his, rfl⟩ := List.mem_iff_get.1 hs
    exact ⟨i.1, i.2, i.2, hxs⟩
  · rintro ⟨i, hi, hi', hx⟩
    exact ⟨bad[i], List.getElem_mem hi', hx⟩

/-- **The cover lemma.** Every point of `H` lies in a face of the fine complex which is inside
`H`, and which is either small (`card ≤ k`), already mapped into `V`, or a bad `(k+1)`-face. -/
theorem cover_of_subdivides' {N : ℕ} {M : Type*} [MetricSpace M] (S : SubdivTools N)
    {K : Cx N} (hK : K.faces.Finite) {H : Set (E N)} (hH : Work.Engulf.IsSubSp K H)
    {f : E N → M} {V : Set M} {k : ℕ} (hbad : Work.Engulf.BadCard K H f V (k + 1)) {r : ℕ}
    {x : E N} (hx : x ∈ H) :
    (∃ s ∈ (S.sdIter r K hK).faces, simp s ⊆ H ∧ s.card ≤ k ∧ x ∈ simp s) ∨
    (∃ s ∈ (S.sdIter r K hK).faces, simp s ⊆ H ∧ f '' simp s ⊆ V ∧ x ∈ simp s) ∨
    (∃ s ∈ (S.sdIter r K hK).faces, simp s ⊆ H ∧ s.card = k + 1 ∧ ¬ (f '' simp s ⊆ V) ∧
      x ∈ simp s) := by
  obtain ⟨s, hs, hxs, hsH⟩ := (S.subsp r K hK H hH).2 x hx
  by_cases hV : f '' simp s ⊆ V
  · exact Or.inr (Or.inl ⟨s, hs, hsH, hV, hxs⟩)
  · have hc : s.card ≤ k + 1 := Work.Engulf.card_le_of_not_maps S hH hbad hs hsH hV
    by_cases h1 : s.card ≤ k
    · exact Or.inl ⟨s, hs, hsH, h1, hxs⟩
    · exact Or.inr (Or.inr ⟨s, hs, hsH, by omega, hV, hxs⟩)


/-- **`E2` = Newman's Lemma 6** (§11): `B k ∧ C1 (k+1) ⇒ B (k+1)`.  (Universe fixed after review: the hypotheses, the conclusion and `ToolsAll` all live at the *same* universe `u`, as in `Skeleton.lean`; with implicit universes `B`/`C1` would be instantiated at unrelated levels and the statement would be unprovable.)  Let `Z := (f⁻¹ X ∩ H) ∪ C_ov` (compact, mapped into `V`); subdivide `Γ` finely (`SubdivTools`) so that every face meeting `Z` maps into `V`; apply `B k` to engulf the union of the faces already in `V` and of the faces with `≤ k` vertices, then apply `C1 (k+1)` to each principal `(k+1)`-face in turn.  Invariant: `Work.Engulf.E2Inv`.  The faces of the subdivided complex covered by that union but not mapped into `V` must have `≤ k` vertices; this is `Work.Engulf.Aux.simplex_cover` plus `Work.Engulf.Aux.face_subset_of_subset_union`. -/
theorem E2 (n p k : ℕ) (T : Work.Engulf.ToolsAll.{u} n) (hB : Work.Engulf.B.{u} n p k)
    (hC : Work.Engulf.C1.{u} n p (k + 1)) : Work.Engulf.B.{u} n p (k + 1) := by
  classical
  intro M _ V X N Γ H L f A c hXV hBad ε hε
  -- ## 0. the control set `Z` and a fine subdivision
  obtain ⟨Cov, hCovc, hCovV, hCovcol, hCovX⟩ := c.ov
  have hHc : IsCompact H := Work.Engulf.isCompact_of_isSubSp c.fin c.subH
  set Z : Set (E N) := (H ∩ f ⁻¹' X) ∪ (Cov ∩ H) with hZdef
  have hZc : IsCompact Z := by
    rw [hZdef]
    exact (Work.Engulf.isCompact_inter_preimage c.fin c.cont hHc c.subH.1 c.Xc).union
      (hCovc.inter hHc)
  have hZspace : Z ⊆ Γ.space := by
    rw [hZdef]
    rintro x (⟨hxH, _⟩ | ⟨_, hxH⟩) <;> exact c.subH.1 hxH
  have hZV : f '' Z ⊆ V := by
    rw [hZdef]
    rintro y ⟨x, (⟨hxH, hxX⟩ | ⟨hxCov, _⟩), rfl⟩
    · exact hXV hxX
    · exact hCovV ⟨x, hxCov, rfl⟩
  obtain ⟨r, hr⟩ :=
    Work.Engulf.exists_subdiv_faces_map_into (T N).subdiv c.fin c.cont A.Vo hZc hZspace hZV
  set Γ₁ : Cx N := (T N).subdiv.sdIter r Γ c.fin with hΓ₁def
  have hfin₁ : Γ₁.faces.Finite := by rw [hΓ₁def]; exact (T N).subdiv.fin r Γ c.fin
  have hsubΓ₁ : PL.Subdivides Γ₁ Γ := by rw [hΓ₁def]; exact (T N).subdiv.subdiv r Γ c.fin
  have hspace : Γ₁.space = Γ.space := hsubΓ₁.1
  have hcont₁ : ContinuousOn f Γ₁.space := by rw [hspace]; exact c.cont
  have hLsub : Work.Engulf.IsSubSp Γ₁ L := by
    rw [hΓ₁def]; exact (T N).subdiv.subsp r Γ c.fin L c.subL
  have hdim₁ : PL.DimLE Γ₁ (p + 1) := by
    rw [hΓ₁def]; exact (T N).subdiv.dimle r Γ c.fin (p + 1) c.dimΓ
  have hfine : ∀ s ∈ Γ₁.faces, (simp s ∩ Z).Nonempty → f '' simp s ⊆ V := by
    intro s hs hmeet
    have hs' : s ∈ ((T N).subdiv.sdIter r Γ c.fin).faces := by rwa [← hΓ₁def]
    exact hr r le_rfl s hs' hmeet
  -- ## 1. the three families of faces of `Γ₁`
  set Pfam : Finset (Finset (E N)) :=
    hfin₁.toFinset.filter (fun s => simp s ⊆ H ∧ f '' simp s ⊆ V) with hPfamdef
  set Skfam : Finset (Finset (E N)) :=
    hfin₁.toFinset.filter (fun s => simp s ⊆ H ∧ s.card ≤ k) with hSkfamdef
  set badfam : Finset (Finset (E N)) :=
    hfin₁.toFinset.filter (fun s => simp s ⊆ H ∧ s.card = k + 1 ∧ ¬ (f '' simp s ⊆ V))
      with hbadfamdef
  set P1 : Set (E N) := ⋃ s ∈ Pfam, simp s with hP1def
  set Sk : Set (E N) := ⋃ s ∈ Skfam, simp s with hSkdef
  set bad : List (Finset (E N)) := badfam.toList with hbaddef
  have mem_pfam : ∀ s : Finset (E N), s ∈ Pfam ↔ s ∈ Γ₁.faces ∧ simp s ⊆ H ∧ f '' simp s ⊆ V := by
    intro s
    rw [hPfamdef, Finset.mem_filter, Set.Finite.mem_toFinset hfin₁]
  have mem_skfam : ∀ s : Finset (E N), s ∈ Skfam ↔ s ∈ Γ₁.faces ∧ simp s ⊆ H ∧ s.card ≤ k := by
    intro s
    rw [hSkfamdef, Finset.mem_filter, Set.Finite.mem_toFinset hfin₁]
  have mem_badfam : ∀ s : Finset (E N),
      s ∈ badfam ↔ s ∈ Γ₁.faces ∧ simp s ⊆ H ∧ s.card = k + 1 ∧ ¬ (f '' simp s ⊆ V) := by
    intro s
    rw [hbadfamdef, Finset.mem_filter, Set.Finite.mem_toFinset hfin₁]
  have mem_bad : ∀ s : Finset (E N), s ∈ bad ↔ s ∈ badfam := by
    intro s; rw [hbaddef, Finset.mem_toList]
  have bad_nodup : bad.Nodup := by rw [hbaddef]; exact Finset.nodup_toList _
  have bad_length : bad.length = badfam.card := by rw [hbaddef]; exact Finset.length_toList _
  have bad_get : ∀ i (hi : i < bad.length), bad[i] ∈ badfam :=
    fun i hi => (mem_bad _).1 (List.mem_iff_get.mpr ⟨⟨i, hi⟩, rfl⟩)
  have hP1_sub : P1 ⊆ H := by
    intro x hx
    rw [hP1def] at hx
    obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.1 hx
    exact ((mem_pfam s).1 hs).2.1 hxs
  have hSk_sub : Sk ⊆ H := by
    intro x hx
    rw [hSkdef] at hx
    obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.1 hx
    exact ((mem_skfam s).1 hs).2.1 hxs
  have hbad_sub : ∀ i (hi : i < bad.length), simp bad[i] ⊆ H :=
    fun i hi => ((mem_badfam _).1 (bad_get i hi)).2.1
  have hP1_isSubSp : Work.Engulf.IsSubSp Γ₁ P1 := by
    rw [hP1def]
    exact isSubSp_biUnion_E2 Pfam (fun t ht => isSubSp_simp ((mem_pfam t).1 ht).1)
  have hSk_isSubSp : Work.Engulf.IsSubSp Γ₁ Sk := by
    rw [hSkdef]
    exact isSubSp_biUnion_E2 Skfam (fun t ht => isSubSp_simp ((mem_skfam t).1 ht).1)
  have hbadUnionOne : ∀ i, Work.Engulf.IsSubSp Γ₁ (⋃ (hi : i < bad.length), simp bad[i]) :=
    fun i => isSubSp_iUnion (S := fun hi : i < bad.length => simp (bad[i]))
      (fun hi => isSubSp_simp ((mem_badfam _).1 (bad_get i hi)).1)
  have hbadUnion_isSubSp : ∀ j, Work.Engulf.IsSubSp Γ₁
      (⋃ i ∈ Finset.range j, ⋃ (hi : i < bad.length), simp bad[i]) :=
    fun j => isSubSp_biUnion_E2 (Finset.range j) (fun i _ => hbadUnionOne i)
  have hHj_isSubSp : ∀ j, Work.Engulf.IsSubSp Γ₁ (HjSet P1 Sk bad j) := by
    intro j
    unfold HjSet
    exact Work.Engulf.isSubSp_union (Work.Engulf.isSubSp_union hP1_isSubSp hSk_isSubSp)
      (hbadUnion_isSubSp j)
  have hHj_sub : ∀ j, HjSet P1 Sk bad j ⊆ H := by
    intro j x hx
    unfold HjSet at hx
    rw [Set.mem_union] at hx
    rcases hx with hx | hx
    · rw [Set.mem_union] at hx
      rcases hx with hx | hx
      · exact hP1_sub hx
      · exact hSk_sub hx
    · obtain ⟨i, _, hx'⟩ := Set.mem_iUnion₂.1 hx
      obtain ⟨hi, hxi⟩ := Set.mem_iUnion.1 hx'
      exact hbad_sub i hi hxi
  -- ## 2. the margin between the bad faces and `X`
  have hBadSet_isSubSp : Work.Engulf.IsSubSp Γ₁ (⋃ s ∈ badfam, simp s) :=
    isSubSp_biUnion_E2 badfam (fun t ht => isSubSp_simp ((mem_badfam t).1 ht).1)
  have hBadSetDisj : Disjoint (f '' (⋃ s ∈ badfam, simp s)) X := by
    rw [Set.disjoint_left]
    rintro z ⟨y, hy, rfl⟩ hzX
    obtain ⟨s, hs, hys⟩ := Set.mem_iUnion₂.1 hy
    have h1 := (mem_badfam s).1 hs
    exact h1.2.2.2 (hfine s h1.1 ⟨y, hys, Or.inl ⟨h1.2.1 hys, hzX⟩⟩)
  obtain ⟨μ, hμpos, hμle⟩ := Work.Engulf.exists_pos_le_dist_of_isCompact_disjoint
    ((Work.Engulf.isCompact_of_isSubSp hfin₁ hBadSet_isSubSp).image_of_continuousOn
      (hcont₁.mono hBadSet_isSubSp.1)) c.Xc hBadSetDisj
  have hμ : ∀ x ∈ (⋃ s ∈ badfam, simp s), ∀ y ∈ X, μ ≤ dist (f x) y :=
    fun x hx y hy => hμle (f x) ⟨x, hx, rfl⟩ y hy
  -- the budgets
  set b : ℝ := min (ε / 4) (μ / 4) with hbdef
  have hbpos : 0 < b := by rw [hbdef]; exact lt_min (by linarith) (by linarith)
  set η₀ : ℝ := b / 2 with hη₀def
  set η : ℝ := b / (2 * ((bad.length : ℝ) + 1)) with hηdef
  have hη₀pos : 0 < η₀ := by rw [hη₀def]; linarith
  have hηpos : 0 < η := by rw [hηdef]; positivity
  have hbudget : ∀ j ≤ bad.length, η₀ + (j : ℝ) * η < b := by
    intro j hj
    have hle : (j : ℝ) ≤ (bad.length : ℝ) := by exact_mod_cast hj
    have hkey : (bad.length : ℝ) * η < b / 2 := by
      have hden : (0 : ℝ) < 2 * ((bad.length : ℝ) + 1) := by positivity
      have hratio : (bad.length : ℝ) / (2 * ((bad.length : ℝ) + 1)) < 1 / 2 := by
        rw [div_lt_iff₀ hden]; linarith
      have h1 : (bad.length : ℝ) * η = ((bad.length : ℝ) / (2 * ((bad.length : ℝ) + 1))) * b := by
        rw [hηdef, div_eq_mul_inv]; ring
      rw [h1]
      linarith [mul_lt_mul_of_pos_right hratio hbpos]
    have h2 : (j : ℝ) * η ≤ (bad.length : ℝ) * η :=
      mul_le_mul_of_nonneg_right hle (le_of_lt hηpos)
    rw [hη₀def]; linarith
  have hbudget_ε : ∀ j ≤ bad.length, η₀ + (j : ℝ) * η < ε := by
    intro j hj
    refine lt_of_lt_of_le (hbudget j hj) (le_of_lt ?_)
    rw [hbdef]; have := min_le_left (ε / 4) (μ / 4); linarith
  have hbudget_μ : ∀ j ≤ bad.length, η₀ + (j : ℝ) * η < μ := by
    intro j hj
    refine lt_of_lt_of_le (hbudget j hj) (le_of_lt ?_)
    rw [hbdef]; have := min_le_right (ε / 4) (μ / 4); linarith
  -- ## 3. the `B k` step
  have hCfg₀ : Work.Engulf.Cfg n p V X Γ₁ (P1 ∪ Sk) L f :=
    { fin := hfin₁
      dimΓ := hdim₁
      room := c.room
      subH := Work.Engulf.isSubSp_union hP1_isSubSp hSk_isSubSp
      subL := hLsub
      dimH := fun s hs hsH => Work.Engulf.card_le_of_isSubSp (T N).subdiv (hK := c.fin)
        c.subH c.dimH hs (hsH.trans (Set.union_subset hP1_sub hSk_sub))
      cont := hcont₁
      Xc := c.Xc
      cpt := isCompact_sdiff_of_subset c.Xc
        (Work.Engulf.isCompact_of_isSubSp hfin₁ (Work.Engulf.isSubSp_union hP1_isSubSp hSk_isSubSp))
        (Work.Engulf.isSubSp_union hP1_isSubSp hSk_isSubSp).1 hcont₁ A.Vo hXV
      tame := Work.Engulf.tame_subdivision (T N).subdiv (hK := c.fin) c.subL c.tame
      ov := Work.Engulf.OvCtl.mono (Set.union_subset hP1_sub hSk_sub) c.ov }
  have hBadCard₀ : Work.Engulf.BadCard Γ₁ (P1 ∪ Sk) f V k := by
    intro s hs hsH hsV
    rcases subset_of_simp_subset_union hP1_isSubSp hSk_isSubSp hs hsH with h | h
    · obtain ⟨t, ht, hst⟩ := exists_of_simp_subset_iUnion (u := Pfam) (S := fun t => simp t)
        (fun t ht => isSubSp_simp ((mem_pfam t).1 ht).1) hs h
      exact absurd ((Set.image_mono hst).trans ((mem_pfam t).1 ht).2.2) hsV
    · obtain ⟨t, ht, hst⟩ := exists_of_simp_subset_iUnion (u := Skfam) (S := fun t => simp t)
        (fun t ht => isSubSp_simp ((mem_skfam t).1 ht).1) hs h
      exact le_trans
        (Finset.card_le_card ((Γ₁.face_subset_face_iff hs ((mem_skfam t).1 ht).1).1 hst))
        ((mem_skfam t).1 ht).2.2
  obtain ⟨g₀, hg₀cont, hg₀frz, hg₀near, h₀, h₀supp, h₀eng⟩ :=
    hB M V X N Γ₁ (P1 ∪ Sk) L f A hCfg₀ hXV hBadCard₀ η₀ hη₀pos
  have hbase : Work.Engulf.E2Inv V X Γ₁ L P1 Sk f bad η₀ η 0 g₀ h₀ :=
    { le := Nat.zero_le _
      cont := hg₀cont
      frz := hg₀frz
      near := by intro x hx; simpa using hg₀near x hx
      supp := h₀supp
      eng := by
        change X ∪ g₀ '' HjSet P1 Sk bad 0 ⊆ h₀ '' V
        have h0 : HjSet P1 Sk bad 0 = P1 ∪ Sk := by
          unfold HjSet
          simp
        rw [h0]
        exact h₀eng
      offX := by
        intro i hi _
        refine image_disjoint_of_margin (K := simp bad[i]) (f := f) (g := g₀) (X := X)
          (ρ := μ) ?_ ?_
        · intro x hx y hy
          exact hμ x (Set.mem_iUnion₂.mpr ⟨bad[i], bad_get i hi, hx⟩) y hy
        · intro x hx
          have hxc : x ∈ Γ₁.space :=
            Geometry.SimplicialComplex.convexHull_subset_space
              ((mem_badfam _).1 (bad_get i hi)).1 hx
          have h1 := hg₀near x hxc
          have h2 : η₀ < μ := by simpa using hbudget_μ 0 (Nat.zero_le _)
          linarith }
  -- ## 4. the loop over the bad faces
  have key : ∀ j, j < bad.length →
      (∃ (g : E N → M) (h : M ≃ₜ M), Work.Engulf.E2Inv V X Γ₁ L P1 Sk f bad η₀ η j g h) →
      ∃ (g : E N → M) (h : M ≃ₜ M), Work.Engulf.E2Inv V X Γ₁ L P1 Sk f bad η₀ η (j + 1) g h := by
    intro j hj prev
    obtain ⟨g, h, I⟩ := prev
    set σ : Finset (E N) := bad[j] with hσdef
    have hσbad : σ ∈ badfam := by rw [hσdef]; exact bad_get j hj
    have hσface : σ ∈ Γ₁.faces := ((mem_badfam σ).1 hσbad).1
    have hσH : simp σ ⊆ H := ((mem_badfam σ).1 hσbad).2.1
    have hσcard : σ.card = k + 1 := ((mem_badfam σ).1 hσbad).2.2.1
    have hσnotV : ¬ (f '' simp σ ⊆ V) := ((mem_badfam σ).1 hσbad).2.2.2
    have hσZ : simp σ ∩ Z = ∅ := by
      by_contra hne
      exact hσnotV (hfine σ hσface (Set.nonempty_iff_ne_empty.2 hne))
    have hσCov : ∀ x ∈ simp σ, x ∉ Cov := by
      intro x hx hxCov
      have hxZ : x ∈ Z := by
        rw [hZdef]
        exact Or.inr ⟨hxCov, hσH hx⟩
      have hmem : x ∈ simp σ ∩ Z := ⟨hx, hxZ⟩
      rw [hσZ] at hmem
      exact hmem
    have hVK : X ∪ g '' HjSet P1 Sk bad j ⊆ h '' V := I.eng
    have hXj : X ⊆ h '' V := fun x hx => hVK (Or.inl hx)
    have hHjT : HjSet P1 Sk bad j ∪ simp σ ⊆ H :=
      Set.union_subset (hHj_sub j) hσH
    -- the pushed configuration
    have hCfg' : Work.Engulf.Cfg n p (h '' V) X Γ₁ (HjSet P1 Sk bad j ∪ simp σ) L g :=
      { fin := hfin₁
        dimΓ := hdim₁
        room := c.room
        subH := Work.Engulf.isSubSp_union (hHj_isSubSp j) (isSubSp_simp hσface)
        subL := hLsub
        dimH := fun s hs hsH => Work.Engulf.card_le_of_isSubSp (T N).subdiv (hK := c.fin)
          c.subH c.dimH hs (hsH.trans hHjT)
        cont := I.cont
        Xc := c.Xc
        cpt := isCompact_sdiff_of_engulfs_E2 c.Xc (hHj_isSubSp j) hfin₁
          (Work.Engulf.isCompact_simp σ) (isSubSp_simp hσface).1 I.cont
          (h.isOpenMap V A.Vo) hVK
        tame := Work.Engulf.Tame.congr I.frz
          (Work.Engulf.tame_subdivision (T N).subdiv (hK := c.fin) c.subL c.tame)
        ov := by
          refine ⟨HjSet P1 Sk bad j ∩ L, ?_, ?_, ?_, ?_⟩
          · exact (Work.Engulf.isCompact_of_isSubSp hfin₁ (hHj_isSubSp j)).inter
              (Work.Engulf.isCompact_of_isSubSp hfin₁ hLsub)
          · rintro z ⟨x, ⟨hx, hxL⟩, rfl⟩
            exact hVK (Or.inr ⟨x, hx, rfl⟩)
          · rintro x ⟨hxor, hxL⟩ y ⟨hyor, hyL⟩ heq hne
            rw [I.frz hxL, I.frz hyL] at heq
            have hxH : x ∈ H := hHjT hxor
            have hyH : y ∈ H := hHjT hyor
            have hxCov : x ∈ Cov := hCovcol x ⟨hxH, hxL⟩ y ⟨hyH, hyL⟩ heq hne
            rcases hxor with hxor | hxor
            · exact ⟨hxor, hxL⟩
            · exact absurd hxCov (hσCov x hxor)
          · rintro x ⟨hxor, hxL⟩ hxX
            have hxH : x ∈ H := hHjT hxor
            rw [I.frz hxL] at hxX
            have hxCov : x ∈ Cov := hCovX x ⟨hxH, hxL⟩ hxX
            rcases hxor with hxor | hxor
            · exact ⟨hxor, hxL⟩
            · exact absurd hxCov (hσCov x hxor) }
    -- `σ` is principal in the pushed `H`
    have hprinc : ∀ s ∈ Γ₁.faces, simp s ⊆ HjSet P1 Sk bad j ∪ simp σ → σ ⊆ s → s = σ := by
      intro s hs hsH hσs
      have hσs' : simp σ ⊆ simp s := simp_mono hσs
      rcases subset_of_simp_subset_union (hHj_isSubSp j) (isSubSp_simp hσface) hs hsH with h | h
      · unfold HjSet at h
        rcases subset_of_simp_subset_union3 hP1_isSubSp hSk_isSubSp (hbadUnion_isSubSp j) hs h with
          h2 | h2 | h2
        · obtain ⟨t, ht, hσt⟩ := exists_of_simp_subset_iUnion (u := Pfam) (S := fun t => simp t)
            (fun t ht => isSubSp_simp ((mem_pfam t).1 ht).1) hσface (hσs'.trans h2)
          exact absurd ((Set.image_mono hσt).trans ((mem_pfam t).1 ht).2.2) hσnotV
        · obtain ⟨t, ht, hσt⟩ := exists_of_simp_subset_iUnion (u := Skfam) (S := fun t => simp t)
            (fun t ht => isSubSp_simp ((mem_skfam t).1 ht).1) hσface (hσs'.trans h2)
          have h1 : σ.card ≤ t.card :=
            Finset.card_le_card ((Γ₁.face_subset_face_iff hσface ((mem_skfam t).1 ht).1).1 hσt)
          have h2' : t.card ≤ k := ((mem_skfam t).1 ht).2.2
          omega
        · obtain ⟨i, hime, hσi⟩ := exists_of_simp_subset_iUnion (u := Finset.range j)
            (S := fun i => ⋃ (hi : i < bad.length), simp bad[i]) (fun i _ => hbadUnionOne i)
            hσface (hσs'.trans h2)
          have hij : i < j := Finset.mem_range.1 hime
          obtain ⟨hi', hσi'⟩ := exists_of_simp_subset_iUnion'
            (S := fun hi : i < bad.length => simp (bad[i]'hi))
            (fun hi => isSubSp_simp ((mem_badfam _).1 (bad_get i hi)).1) hσface hσi
          have hσsub : σ ⊆ bad[i] :=
            (Γ₁.face_subset_face_iff hσface ((mem_badfam _).1 (bad_get i hi')).1).1 hσi'
          have hcardi : (bad[i]'hi').card = k + 1 := ((mem_badfam _).1 (bad_get i hi')).2.2.1
          have hEq : σ = bad[i] :=
            Finset.eq_of_subset_of_card_le hσsub (by rw [hcardi]; exact le_of_eq hσcard.symm)
          have hbadji : bad.get ⟨j, hj⟩ = bad.get ⟨i, hi'⟩ := hσdef.symm.trans hEq
          have hidx : (⟨j, hj⟩ : Fin bad.length) = ⟨i, hi'⟩ := (bad_nodup.get_inj_iff).1 hbadji
          have hji' : j = i := by simpa using congrArg Fin.val hidx
          omega
      · have hst : s ⊆ σ := (Γ₁.face_subset_face_iff hs hσface).1 h
        exact (Finset.Subset.antisymm hσs hst).symm
    -- the other faces map into the current `V`
    have hother : ∀ s ∈ Γ₁.faces, simp s ⊆ HjSet P1 Sk bad j ∪ simp σ → s ≠ σ →
        g '' simp s ⊆ h '' V := by
      intro s hs hsH hsne
      rcases subset_of_simp_subset_union (hHj_isSubSp j) (isSubSp_simp hσface) hs hsH with h | h
      · intro z hz
        obtain ⟨y, hy, rfl⟩ := hz
        exact hVK (Or.inr ⟨y, h hy, rfl⟩)
      · have hst : s ⊆ σ := (Γ₁.face_subset_face_iff hs hσface).1 h
        have hssub : s ⊂ σ := Finset.ssubset_iff_subset_ne.2 ⟨hst, hsne⟩
        have hcard : s.card ≤ k := by
          have := Finset.card_lt_card hssub
          omega
        have hsSk : simp s ⊆ Sk := by
          rw [hSkdef]
          exact fun y hy => Set.mem_iUnion₂.mpr
            ⟨s, (mem_skfam s).2 ⟨hs, h.trans hσH, hcard⟩, hy⟩
        have h1 : simp s ⊆ HjSet P1 Sk bad j := by
          unfold HjSet
          intro y hy
          exact Or.inl (Or.inr (hsSk hy))
        intro z hz
        obtain ⟨y, hy, rfl⟩ := hz
        exact hVK (Or.inr ⟨y, h1 hy, rfl⟩)
    have hdisj : Disjoint (g '' simp σ) X := by
      simpa [hσdef] using I.offX j hj le_rfl
    have hclean : ∀ x ∈ simp σ ∩ L, ∀ y ∈ (HjSet P1 Sk bad j ∪ simp σ) ∩ L,
        g x = g y → x = y := by
      intro x hx y hy hxy
      have hxL : x ∈ L := hx.2
      have hyL : y ∈ L := hy.2
      have hxy' : f x = f y := by rw [← I.frz hxL, ← I.frz hyL]; exact hxy
      by_contra hne
      have hyH : y ∈ H := hHjT hy.1
      have hxCov : x ∈ Cov := hCovcol x ⟨hσH hx.1, hxL⟩ y ⟨hyH, hyL⟩ hxy' hne
      exact hσCov x hx.1 hxCov
    obtain ⟨g', hg'c, hg'fz, hg'near, h₂, h₂supp, h₂eng⟩ :=
      hC M (h '' V) X N Γ₁ (HjSet P1 Sk bad j ∪ simp σ) L g σ
        (Work.Engulf.Amb.image_homeomorph h A) hCfg' hXj hσface hσcard
        (Set.subset_union_right) hprinc hother hdisj hclean η hηpos
    refine ⟨g', h.trans h₂, ?_⟩
    refine { le := Nat.succ_le_of_lt hj
             cont := hg'c
             frz := hg'fz.trans I.frz
             near := ?_
             supp := Work.Engulf.csupp_trans I.supp h₂supp
             eng := ?_
             offX := ?_ }
    · intro x hx
      have h1 := hg'near x hx
      have h2 := I.near x hx
      have h4 : dist (g' x) (f x) < η + (η₀ + (j : ℝ) * η) :=
        lt_of_le_of_lt (dist_triangle _ _ _) (add_lt_add h1 h2)
      have h5 : η + (η₀ + (j : ℝ) * η) = η₀ + ((j + 1 : ℕ) : ℝ) * η := by push_cast; ring
      linarith
    · have himg : (h.trans h₂) '' V = h₂ '' (h '' V) := Work.Engulf.image_trans_image h h₂ V
      rw [himg]
      have hsub : P1 ∪ Sk ∪ ⋃ i ∈ Finset.range (j + 1),
            ⋃ (hi : i < bad.length), simp bad[i] ⊆ HjSet P1 Sk bad j ∪ simp σ := by
        intro x hx
        rw [Set.mem_union] at hx
        rcases hx with hx | hx
        · refine Or.inl ?_
          unfold HjSet
          exact Or.inl hx
        · rw [Set.mem_iUnion₂] at hx
          obtain ⟨i, hi, hx⟩ := hx
          rcases Nat.lt_succ_iff_lt_or_eq.1 (Finset.mem_range.1 hi) with hlt | heq
          · refine Or.inl ?_
            unfold HjSet
            exact Or.inr (Set.mem_iUnion₂.mpr ⟨i, Finset.mem_range.mpr hlt, hx⟩)
          · subst heq
            obtain ⟨hi', hxi⟩ := Set.mem_iUnion.1 hx
            refine Or.inr ?_
            rw [hσdef]
            exact hxi
      refine fun z hz => ?_
      rcases hz with hz | hz
      · exact h₂eng (Or.inl hz)
      · obtain ⟨y, hy, rfl⟩ := hz
        exact h₂eng (Or.inr ⟨y, hsub hy, rfl⟩)
    · intro i hi hji
      refine image_disjoint_of_margin (K := simp bad[i]) (f := f) (g := g') (X := X)
        (ρ := μ) ?_ ?_
      · intro x hx y hy
        exact hμ x (Set.mem_iUnion₂.mpr ⟨bad[i], bad_get i hi, hx⟩) y hy
      · intro x hx
        have hxc : x ∈ Γ₁.space :=
          Geometry.SimplicialComplex.convexHull_subset_space
            ((mem_badfam _).1 (bad_get i hi)).1 hx
        have h1 := hg'near x hxc
        have h2 := I.near x hxc
        have h3 := hbudget_μ (j + 1) (Nat.succ_le_of_lt hj)
        have h4 : dist (g' x) (f x) < η + (η₀ + (j : ℝ) * η) :=
          lt_of_le_of_lt (dist_triangle _ _ _) (add_lt_add h1 h2)
        have h5 : η + (η₀ + (j : ℝ) * η) = η₀ + ((j + 1 : ℕ) : ℝ) * η := by push_cast; ring
        linarith
  have loop : ∀ j ≤ bad.length, ∃ (g : E N → M) (h : M ≃ₜ M),
      Work.Engulf.E2Inv V X Γ₁ L P1 Sk f bad η₀ η j g h := by
    intro j
    induction j with
    | zero => intro _; exact ⟨g₀, h₀, hbase⟩
    | succ j ih => intro hj; exact key j (by omega) (ih (by omega))
  obtain ⟨g, h, I⟩ := loop bad.length le_rfl
  -- ## 5. the cover of `H` and the conclusion
  have hcover : H ⊆ HjSet P1 Sk bad bad.length := by
    intro x hx
    unfold HjSet
    rcases cover_of_subdivides' (T N).subdiv c.fin c.subH hBad (r := r) (x := x) hx with
      ⟨s, hs, hsH, hsc, hxs⟩ | ⟨s, hs, hsH, hsV, hxs⟩ | ⟨s, hs, hsH, hsc, hsV, hxs⟩
    · refine Or.inl (Or.inr ?_)
      exact Set.mem_iUnion₂.mpr ⟨s, (mem_skfam s).2 ⟨hs, hsH, hsc⟩, hxs⟩
    · refine Or.inl (Or.inl ?_)
      exact Set.mem_iUnion₂.mpr ⟨s, (mem_pfam s).2 ⟨hs, hsH, hsV⟩, hxs⟩
    · refine Or.inr ?_
      have hmem : x ∈ (⋃ t ∈ bad, simp t) :=
        Set.mem_iUnion₂.mpr ⟨s, (mem_bad _).2 ((mem_badfam s).2 ⟨hs, hsH, hsc, hsV⟩), hxs⟩
      rwa [iUnion_list_eq_range_E2] at hmem
  refine ⟨g, ?_, I.frz, ?_, h, I.supp, ?_⟩
  · refine I.cont.mono ?_
    rw [hspace]
  · intro x hx
    have hx₁ : x ∈ Γ₁.space := by rw [hspace]; exact hx
    have h1 := I.near x hx₁
    have h2 := hbudget_ε bad.length le_rfl
    linarith
  · refine fun z hz => ?_
    rcases hz with hz | hz
    · exact I.eng (Or.inl hz)
    · obtain ⟨y, hy, rfl⟩ := hz
      exact I.eng (Or.inr ⟨y, hcover hy, rfl⟩)

end Work.Engulf.Chain
