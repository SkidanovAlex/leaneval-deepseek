import Mathlib
import Submission.Work.Engulf.Defs
import Submission.Work.Engulf.Tools
import Submission.Work.Engulf.Basic
import Submission.Work.Engulf.DefsM
import Submission.Work.Engulf.E4alt.Defs2
import Submission.Work.Engulf.E4alt.Defs3
import Submission.Work.Engulf.E4alt.Api
import Submission.Work.Engulf.E4alt.tameOfNormData
import Submission.Work.Engulf.Auxi.tame_extend
import Submission.Work.Engulf.Auxi.smoothChart_extend
import Submission.Work.Engulf.Auxi.EngulfAux
import Submission.Work.Engulf.Auxi.face_subset_of_subset_union
import Submission.Work.Engulf.Auxi.SimplexCover
import Submission.Work.Engulf.E4P.Defs
import Submission.Work.Engulf.E4P.Core
import Submission.Work.Engulf.E4P.Far

/-!
# `Work.Engulf.E4P.Step` — one step of the piece loop of `E4c`

`NOTES_LEAD_poincare_E4c.md` §A.3.  From the state `PieceSt … r …` of the piece loop and the
`r`-th piece, attach the piece as a far face, set the moving map to `ψ ∘ A` on it, call
`B n p q` once (with `H := G ∪ P_{≤r}`, `Lc := L ∪ coreSet ∪ P_{≤r}` and budget `β/(R+1)`) and
produce the state at `r + 1`.  Newman (13.2)–(13.4).
-/

open Set Metric PL

namespace Work.Engulf.E4P

universe u

set_option maxHeartbeats 1600000 in
theorem step {n p q N : ℕ} {M : Type u} [MetricSpace M] {V X : Set M} {Γ : Cx N}
    {K L : Set (E N)} {f : E N → M} {τ₀ τ₁ : Finset (E N)} {ψ : CubeChart n M} {ε β : ℝ}
    (T : Work.Engulf.ToolsAllM M n) (hB : Work.Engulf.BM M n p q)
    (ND : Work.Engulf.Alt.NormData n p q N M V X Γ K L f τ₀ τ₁ ψ ε)
    (hc11 : Work.Engulf.Alt.Core11 ND) (H7 : Work.Engulf.L7Hyp n p q V X Γ K L f τ₀ τ₁)
    (A : Work.Engulf.Amb n p M V) (hq : q + 1 ≤ p + 1)
    (hLsub : IsSubSp ND.Γ₁ L)
    {G : Set (E N)} (hGsub : IsSubSp ND.Γ₁ G)
    (hGdim : ∀ s ∈ ND.Γ₁.faces, simp s ⊆ G → s.card ≤ p + 1)
    {g : E N → M} (hgfrz : EqOn g ND.g₁ (L ∪ Work.Engulf.Alt.coreSet ND.Γ₁ f ψ))
    (hβ : 0 < β) {pieces : List (Finset (E n))} (hpieces : PiecesOk (q := q) pieces)
    {r : ℕ} (hr : r < pieces.length)
    {Γc : Cx N} {P : Set (E N)} {gc : E N → M} {hc : M ≃ₜ M}
    (S : PieceSt n p V X ND.Γ₁ G L (Work.Engulf.Alt.coreSet ND.Γ₁ f ψ) ψ g pieces β
      r Γc P gc hc) :
    ∃ (Γc' : Cx N) (P' : Set (E N)) (gc' : E N → M) (hc' : M ≃ₜ M),
      PieceSt n p V X ND.Γ₁ G L (Work.Engulf.Alt.coreSet ND.Γ₁ f ψ) ψ g pieces β
        (r + 1) Γc' P' gc' hc' := by
  classical
  set Cr : Set (E N) := Work.Engulf.Alt.coreSet ND.Γ₁ f ψ with hCrdef
  have hCrsub : IsSubSp ND.Γ₁ Cr := by rw [hCrdef]; exact isSubSp_coreSet ND.Γ₁ f ψ
  have hCr11 : ∀ x ∈ Cr, ND.g₁ x ∈ ψ.toFun '' closedCube (11 / 16 : ℝ) := by
    rw [hCrdef]; exact core11_of_core ND hc11
  obtain ⟨hSle, hSsub, hSfin, hSdim, hSnewP, hSsubP, hSdisjP, hSdimP, hScont, hSfrz, hSchart,
    hSsimP, hSgaff, hSnear, hSeng, hSsupp⟩ := S
  -- ## the piece
  obtain ⟨hpne, hpaff, hpcard, hpcube⟩ := hpieces pieces[r] (List.getElem_mem hr)
  have hqp : q ≤ p := by omega
  have hqN : q ≤ N := by have hroom := H7.cfg.room; omega
  obtain ⟨Γc', Δ', Am, hfin', hsub', hΔ'mem, hfaces', hspace', hdisj', hcard', hAmimg, hAmsimp,
    hAminj, hAmopen⟩ := exists_far_piece_data hSfin hpne hpaff hpcard hqN hpcube
  have hspΓcΓc' : Γc.space ⊆ Γc'.space := Work.Engulf.Alt.space_mono hsub'
  have hspΓ₁Γc : ND.Γ₁.space ⊆ Γc.space := Work.Engulf.Alt.space_mono hSsub
  have hspΓ₁Γc' : ND.Γ₁.space ⊆ Γc'.space := fun x hx => hspΓcΓc' (hspΓ₁Γc hx)
  have hΔ'sp : simp Δ' ⊆ Γc'.space := by rw [hspace']; exact Set.subset_union_right
  have hΔ'disj : Disjoint (simp Δ') Γc.space := Set.disjoint_iff_inter_eq_empty.mpr hdisj'
  have hΔ'disjΓ₁ : Disjoint (simp Δ') ND.Γ₁.space :=
    Set.disjoint_left.mpr fun x hx1 hx2 => Set.disjoint_left.mp hΔ'disj hx1 (hspΓ₁Γc hx2)
  -- ## the new map
  set gc' : E N → M := fun x => if x ∈ simp Δ' then ψ.toFun (Am x) else gc x with hgc'def
  have gc'_apply : ∀ x : E N, gc' x = if x ∈ simp Δ' then ψ.toFun (Am x) else gc x :=
    fun x => by rw [hgc'def]
  have hoff : ∀ x ∈ Γc.space, gc' x = gc x := by
    intro x hx
    rw [gc'_apply, if_neg]
    exact fun hxΔ => Set.disjoint_left.mp hΔ'disj hxΔ hx
  have hoffG : ∀ x ∈ G, gc' x = gc x :=
    fun x hx => hoff x (hspΓ₁Γc (hGsub.subset_space hx))
  have hoffP : ∀ x ∈ P, gc' x = gc x := fun x hx => hoff x (hSsubP.subset_space hx)
  have hoffGP : ∀ x ∈ G ∪ P, gc' x = gc x := by
    rintro x (hx | hx)
    · exact hoffG x hx
    · exact hoffP x hx
  have hoffCr : ∀ x ∈ Cr, gc' x = gc x :=
    fun x hx => hoff x (hspΓ₁Γc (hCrsub.subset_space hx))
  have hoffL : ∀ x ∈ L, gc' x = gc x :=
    fun x hx => hoff x (hspΓ₁Γc (hLsub.subset_space hx))
  have hoffLc : ∀ x ∈ L ∪ Cr ∪ P, gc' x = gc x := by
    rintro x ((hx | hx) | hx)
    · exact hoffL x hx
    · exact hoffCr x hx
    · exact hoffP x hx
  -- ## continuity of the new map
  have hΔ'c : IsCompact (simp Δ') := isCompact_simp Δ'
  have hcontΔ' : ContinuousOn gc' (simp Δ') := by
    have hcomp : ContinuousOn (fun x => ψ.toFun (Am x)) (simp Δ') :=
      ψ.cont.comp (Am.continuous_of_finiteDimensional.continuousOn) (fun x hx => hAmopen x hx)
    exact hcomp.congr (fun x hx => by rw [gc'_apply, if_pos hx])
  have hcontΓc : ContinuousOn gc' Γc.space := hScont.congr (fun x hx => hoff x hx)
  have hcont' : ContinuousOn gc' Γc'.space := by
    rw [hspace']
    exact (continuousOn_union_iff_of_isClosed (Work.Engulf.isClosed_space hSfin)
      (isClosed_simp Δ')).2 ⟨hcontΓc, hcontΔ'⟩
  -- ## the new sets
  set P' : Set (E N) := P ∪ simp Δ' with hP'def
  have hP'sub : P ⊆ P' := Set.subset_union_left
  have hΔ'sub : simp Δ' ⊆ P' := Set.subset_union_right
  set H : Set (E N) := G ∪ P ∪ simp Δ' with hHdef
  set Lc : Set (E N) := L ∪ Cr ∪ P' with hLcdef
  have hGΓc : IsSubSp Γc G := Work.Engulf.Alt.isSubSp_mono hSsub hGsub
  have hGΓc' : IsSubSp Γc' G := Work.Engulf.Alt.isSubSp_mono hsub' hGΓc
  have hSsubP' : IsSubSp Γc' P := Work.Engulf.Alt.isSubSp_mono hsub' hSsubP
  have hP'Γc' : IsSubSp Γc' P' := isSubSp_union hSsubP' (isSubSp_simp_face hΔ'mem)
  have hHΓc' : IsSubSp Γc' H := by
    rw [hHdef]; exact isSubSp_union (isSubSp_union hGΓc' hSsubP') (isSubSp_simp_face hΔ'mem)
  have hCrΓc : IsSubSp Γc Cr := Work.Engulf.Alt.isSubSp_mono hSsub hCrsub
  have hCrΓc' : IsSubSp Γc' Cr := Work.Engulf.Alt.isSubSp_mono hsub' hCrΓc
  have hLΓc : IsSubSp Γc L := Work.Engulf.Alt.isSubSp_mono hSsub hLsub
  have hLΓc' : IsSubSp Γc' L := Work.Engulf.Alt.isSubSp_mono hsub' hLΓc
  have hLc₀Γc : IsSubSp Γc (L ∪ Cr ∪ P) := isSubSp_union (isSubSp_union hLΓc hCrΓc) hSsubP
  have hLcΓc' : IsSubSp Γc' Lc := by
    rw [hLcdef]; exact isSubSp_union (isSubSp_union hLΓc' hCrΓc') hP'Γc'
  have hGPΓc : IsSubSp Γc (G ∪ P) := isSubSp_union hGΓc hSsubP
  have hHval : H ⊆ Γc'.space := hHΓc'.subset_space
  have hmemLc : ∀ x ∈ L ∪ Cr ∪ P', x ∈ Lc := fun x hx => by rw [hLcdef]; exact hx
  have hmemLcP : ∀ x ∈ P', x ∈ Lc := fun x hx => by rw [hLcdef]; exact Or.inr hx
  have hmemLcΔ : ∀ x ∈ simp Δ', x ∈ Lc := fun x hx => hmemLcP x (hΔ'sub hx)
  -- ## the old part is engulfed
  have hGPimg : gc' '' (G ∪ P) ⊆ hc '' V := by
    rintro z ⟨x, hx, rfl⟩
    rw [hoffGP x hx]
    exact hSeng (Or.inr ⟨x, hx, rfl⟩)
  have hXhcV : X ⊆ hc '' V := fun x hx => hSeng (Or.inl hx)
  have hHsub : (X ∪ gc' '' H) ⊆ hc '' V ∪ gc' '' (simp Δ') := by
    rintro z (hz | ⟨x, hx, rfl⟩)
    · exact Or.inl (hXhcV hz)
    · rw [hHdef] at hx
      rcases hx with hx | hxΔ
      · exact Or.inl (hGPimg ⟨x, hx, rfl⟩)
      · exact Or.inr ⟨x, hxΔ, rfl⟩
  -- ## compactness of the exceptional set
  have hHc : IsCompact H := by
    rw [hHdef]
    exact (isCompact_of_isSubSp hSfin hGPΓc).union hΔ'c
  have hHimgc : IsCompact (gc' '' H) := hHc.image_of_continuousOn (hcont'.mono hHval)
  have hclosed_cpt : IsClosed ((X ∪ gc' '' H) \ hc '' V) := by
    refine IsClosed.inter ?_ ?_
    · exact H7.cfg.Xc.union hHimgc.isClosed
    · exact (hc.isOpen_image.mpr A.Vo).isClosed_compl
  have hcpt : IsCompact ((X ∪ gc' '' H) \ hc '' V) :=
    IsCompact.of_isClosed_subset (hΔ'c.image_of_continuousOn hcontΔ') hclosed_cpt (by
      intro z hz
      rcases hHsub hz.1 with h | h
      · exact absurd h hz.2
      · exact h)
  -- ## the three-way split of `H`, and the faces of `Γc'` inside `H`
  have hHsplit : ∀ t ∈ Γc'.faces, simp t ⊆ H → simp t ⊆ G ∪ P ∪ simp Δ' :=
    fun t _ htH => by rw [← hHdef]; exact htH
  have hdimH : ∀ t ∈ Γc'.faces, simp t ⊆ H → t.card ≤ p + 1 := by
    intro t ht htH
    rcases hfaces' t ht with htc | htΔ
    · have h1 : simp t ⊆ G ∪ P := by
        intro x hx
        have hx' := hHsplit t ht htH hx
        rcases hx' with hx'' | hx''
        · exact hx''
        · exact absurd hx'' (fun hxd => Set.disjoint_left.mp hΔ'disj hxd
            (Geometry.SimplicialComplex.convexHull_subset_space htc hx))
      rcases Work.Engulf.Aux.face_subset_of_subset_union hSfin hGΓc hSsubP htc h1
        with hG | hP
      · rcases hSnewP t htc with ht₁ | htP
        · exact hGdim t ht₁ hG
        · exact hSdimP t htc htP
      · exact hSdimP t htc hP
    · exact le_trans (Finset.card_le_card htΔ)
        (le_trans (le_of_eq hcard') (le_trans hpcard (by omega)))
  -- ## `BadCard`
  have hBad : BadCard Γc' H gc' (hc '' V) q := by
    intro t ht htH htbad
    rcases hfaces' t ht with htc | htΔ
    · have h1 : simp t ⊆ G ∪ P := by
        intro x hx
        have hx' := hHsplit t ht htH hx
        rcases hx' with hx'' | hx''
        · exact hx''
        · exact absurd hx'' (fun hxd => Set.disjoint_left.mp hΔ'disj hxd
            (Geometry.SimplicialComplex.convexHull_subset_space htc hx))
      rcases Work.Engulf.Aux.face_subset_of_subset_union hSfin hGΓc hSsubP htc h1
        with hG | hP
      · exfalso
        exact htbad fun z hz => by
          obtain ⟨x, hx, rfl⟩ := hz
          rw [hoffG x (hG hx)]
          exact hSeng (Or.inr ⟨x, Or.inl (hG hx), rfl⟩)
      · exfalso
        exact htbad fun z hz => by
          obtain ⟨x, hx, rfl⟩ := hz
          rw [hoffP x (hP hx)]
          exact hSeng (Or.inr ⟨x, Or.inr (hP hx), rfl⟩)
    · exact le_trans (Finset.card_le_card htΔ) (le_trans (le_of_eq hcard') hpcard)
  -- ## the injection of the far face
  have hInjgc' : Set.InjOn gc' (simp Δ') := by
    intro x hx y hy hxy
    rw [gc'_apply, if_pos hx, gc'_apply, if_pos hy] at hxy
    exact hAminj hx hy (Work.Engulf.Aux.CubeChart.injOn_openCube ψ
      (hAmopen x hx) (hAmopen y hy) hxy)
  -- ## overlap control
  set C₁ : Set (E N) := (G ∪ P) ∩ (L ∪ Cr ∪ P) with hC₁def
  have hC₁sub : C₁ ⊆ Γc'.space := fun x hx => hHval (by rw [hHdef]; exact Or.inl hx.1)
  have hC₁c : IsCompact C₁ := isCompact_of_isSubSp hSfin (isSubSp_inter hGPΓc hLc₀Γc)
  have hC₁eng : gc' '' C₁ ⊆ hc '' V := by
    rintro z ⟨x, hx, rfl⟩
    exact hGPimg ⟨x, hx.1, rfl⟩
  have hLcmem : ∀ x ∈ G ∪ P, x ∈ Lc → x ∈ L ∪ Cr ∪ P := by
    intro x hxGP hxL
    have hxsp : x ∈ Γc.space := hGPΓc.subset_space hxGP
    rw [hLcdef, hP'def] at hxL
    rcases hxL with (h | h) | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · rcases h with hP | hΔ
      · exact Or.inr hP
      · exact absurd hxsp (Set.disjoint_left.mp hΔ'disj hΔ)
  have hC₁mem : ∀ x ∈ H ∩ Lc, x ∈ G ∪ P → x ∈ C₁ := by
    intro x hx hxGP
    rw [hC₁def]
    exact ⟨hxGP, hLcmem x hxGP hx.2⟩
  have hTclosed : IsClosed (X ∪ gc' '' C₁) :=
    H7.cfg.Xc.union (hC₁c.image_of_continuousOn (hcont'.mono hC₁sub)).isClosed
  have hov : OvCtl (hc '' V) X H Lc gc' := by
    refine ⟨C₁ ∪ (simp Δ' ∩ gc' ⁻¹' (X ∪ gc' '' C₁)), ?_, ?_, ?_, ?_⟩
    · refine hC₁c.union ?_
      have h1 : IsClosed (Γc'.space ∩ gc' ⁻¹' (X ∪ gc' '' C₁)) :=
        hcont'.preimage_isClosed_of_isClosed (Work.Engulf.isClosed_space hfin') hTclosed
      rw [show simp Δ' ∩ gc' ⁻¹' (X ∪ gc' '' C₁) =
          simp Δ' ∩ (Γc'.space ∩ gc' ⁻¹' (X ∪ gc' '' C₁)) from by
        ext x; constructor
        · rintro ⟨hx1, hx2⟩; exact ⟨hx1, hΔ'sp hx1, hx2⟩
        · rintro ⟨hx1, -, hx2⟩; exact ⟨hx1, hx2⟩]
      exact hΔ'c.inter_right h1
    · rintro z ⟨x, hx, rfl⟩
      rcases hx with hx | hx
      · exact hC₁eng ⟨x, hx, rfl⟩
      · rcases hx.2 with h | h
        · exact hXhcV h
        · exact hC₁eng h
    · intro x hx y hy hxy hne
      rw [hHdef] at hx hy
      rcases hx.1 with hxGP | hxΔ
      · exact Or.inl (hC₁mem x ⟨Or.inl hxGP, hx.2⟩ hxGP)
      · refine Or.inr ⟨hxΔ, ?_⟩
        rcases hy.1 with hyGP | hyΔ
        · exact Or.inr ⟨y, hC₁mem y ⟨Or.inl hyGP, hy.2⟩ hyGP, hxy.symm⟩
        · exact absurd (hInjgc' hxΔ hyΔ hxy) hne
    · intro x hx hxX
      rw [hHdef] at hx
      rcases hx.1 with hxGP | hxΔ
      · exact Or.inl (hC₁mem x ⟨Or.inl hxGP, hx.2⟩ hxGP)
      · exact Or.inr ⟨hxΔ, Or.inl hxX⟩
  -- ## the smoothing data of the old state extends to the new complex and the new piece
  have hchartOld : SmoothChart p X Γc' (L ∪ Cr ∪ P) gc' ψ :=
    Work.Engulf.E4alt.smoothChart_of_carrier
      (Γ := Γc) (Γ₁ := Γc') (L := L ∪ Cr ∪ P) (f := gc) (g := gc')
      (fun x hx => hoffLc x hx) (by
        intro s hs hsL
        rcases hfaces' s hs with hsc | hsΔ
        · exact ⟨s, hsc, Subset.rfl, hsL⟩
        · exfalso
          obtain ⟨v, hv⟩ := Γc'.nonempty_of_mem_faces hs
          have hvL : v ∈ L ∪ Cr ∪ P := hsL (subset_simp hv)
          have hvΔ : v ∈ simp Δ' := subset_simp (hsΔ hv)
          rcases hvL with (h1 | h1) | h1
          · exact Set.disjoint_left.mp hΔ'disjΓ₁ hvΔ (hLsub.subset_space h1)
          · exact Set.disjoint_left.mp hΔ'disjΓ₁ hvΔ (hCrsub.subset_space h1)
          · exact Set.disjoint_left.mp hΔ'disj hvΔ (hSsubP.subset_space h1))
      hSchart
  have hchartNew : SmoothChart p X Γc' (L ∪ Cr ∪ P') gc' ψ := by
    have hsplit2 : ∀ s ∈ Γc'.faces, simp s ⊆ (L ∪ Cr ∪ P) ∪ simp Δ' →
        simp s ⊆ L ∪ Cr ∪ P ∨ simp s ⊆ simp Δ' :=
      fun s hs => Work.Engulf.Aux.face_subset_of_subset_union hfin'
        (isSubSp_union (isSubSp_union hLΓc' hCrΓc') hSsubP')
        (isSubSp_simp_face hΔ'mem) hs
    have hlin2 : ∀ s ∈ Γc'.faces, simp s ⊆ simp Δ' → LinIn ψ gc' (simp s) := by
      intro s hs hsΔ
      rcases hfaces' s hs with hsc | hsΔ'
      · exfalso
        obtain ⟨v, hv⟩ := Γc'.nonempty_of_mem_faces hs
        exact Set.disjoint_left.mp hΔ'disj (hsΔ (subset_simp hv))
          (Geometry.SimplicialComplex.convexHull_subset_space hsc (subset_simp hv))
      · refine ⟨Am, fun y hy => ⟨hAmopen y (hsΔ hy), ?_⟩⟩
        rw [gc'_apply, if_pos (hsΔ hy)]
    have h := Work.Engulf.Aux.smoothChart_extend (X := X) (Γ := Γc')
      (L := L ∪ Cr ∪ P) (S := simp Δ') (f := gc') hchartOld hsplit2 hlin2
    rwa [show (L ∪ Cr ∪ P) ∪ simp Δ' = L ∪ Cr ∪ P' from by
      rw [hP'def]; ext x; simp only [Set.mem_union]; tauto] at h
  -- ## `Tame` on `L`
  have htameL : Tame n p X Γc' L gc' :=
    Work.Engulf.E4alt.tame_of_carrier (Γ := ND.Γ₁) (Γ₁ := Γc') (L := L)
      (f := ND.g₁) (g := gc')
      (fun x hx => (hoffL x hx).trans ((hSfrz (Or.inl hx)).trans (hgfrz (Or.inl hx))))
      (by
        intro s hs hsL
        rcases hfaces' s hs with hsc | hsΔ
        · rcases hSnewP s hsc with hs₁ | hsP
          · exact ⟨s, hs₁, Subset.rfl, hsL⟩
          · exfalso
            obtain ⟨v, hv⟩ := Γc'.nonempty_of_mem_faces hs
            exact Set.disjoint_left.mp hSdisjP (hsP (subset_simp hv))
              (hLsub.subset_space (hsL (subset_simp hv)))
        · exfalso
          obtain ⟨v, hv⟩ := Γc'.nonempty_of_mem_faces hs
          exact Set.disjoint_left.mp hΔ'disjΓ₁ (subset_simp (hsΔ hv))
            (hLsub.subset_space (hsL (subset_simp hv))))
      (Work.Engulf.E4alt.tameOfNormData ND H7)
  -- ## the `Tame` of the configuration
  have hsimCr : gc' '' Cr ⊆ ψ.toFun '' closedCube (11 / 16 : ℝ) := by
    rintro z ⟨x, hx, rfl⟩
    rw [hoffCr x hx, hSfrz (Or.inr hx), hgfrz (Or.inr hx)]
    exact hCr11 x hx
  have hsimP' : gc' '' P' ⊆ ψ.toFun '' closedCube (11 / 16 : ℝ) := by
    rintro z ⟨x, hx, rfl⟩
    rw [hP'def] at hx
    rcases hx with hxP | hxΔ
    · rw [hoffP x hxP]; exact hSsimP ⟨x, hxP, rfl⟩
    · rw [gc'_apply, if_pos hxΔ]
      exact ⟨Am x, hpcube (by rw [← hAmsimp]; exact ⟨x, hxΔ, rfl⟩), rfl⟩
  have hsimTame : gc' '' (Cr ∪ P') ⊆ ψ.toFun '' closedCube (11 / 16 : ℝ) := by
    rw [Set.image_union]
    exact Set.union_subset hsimCr hsimP'
  have htameCfg : Tame n p X Γc' Lc gc' := by
    have hdisj : Disjoint (gc' '' (Cr ∪ P')) (gc' '' (∅ : Set (E N))) := by
      rw [Set.image_empty]; simp
    have h := Work.Engulf.Aux.tame_extend (X := X) (Γ := Γc') (L₀ := L)
      (L₁ := (∅ : Set (E N))) (S := Cr ∪ P') (f := gc') ψ (ρ := (11 / 16 : ℝ))
      (by norm_num) hfin' hcont' (isSubSp_empty Γc') (isSubSp_union hCrΓc' hP'Γc')
      (fun s hs hsLCS => by
        rw [Set.union_empty] at hsLCS
        rcases Work.Engulf.Aux.face_subset_of_subset_union hfin' hLΓc'
          (isSubSp_union hCrΓc' hP'Γc') hs hsLCS with h1 | h2
        · exact Or.inl h1
        · exact Or.inr (Or.inr h2))
      (by rw [Set.union_empty]; exact htameL)
      (by rw [show L ∪ (Cr ∪ P') = L ∪ Cr ∪ P' from by
            ext x; simp only [Set.mem_union]; tauto]; exact hchartNew)
      hsimTame hdisj
    rwa [show L ∪ (∅ : Set (E N)) ∪ (Cr ∪ P') = Lc from by
      rw [hLcdef]; ext x; simp only [Set.mem_union, Set.mem_empty_iff_false, false_or]
      tauto] at h
  -- ## the configuration and the call
  have hdim' : DimLE Γc' (p + 1) := by
    intro t ht
    rcases hfaces' t ht with htc | htΔ
    · exact hSdim t htc
    · exact le_trans (Finset.card_le_card htΔ)
        (le_trans (le_of_eq hcard') (le_trans hpcard (by omega)))
  have hAmb' : Work.Engulf.Amb n p M (hc '' V) := Work.Engulf.Amb.image_homeomorph hc A
  have hcfg : Work.Engulf.Cfg n p (hc '' V) X Γc' H Lc gc' :=
    { fin := hfin'
      dimΓ := hdim'
      room := H7.cfg.room
      subH := hHΓc'
      subL := hLcΓc'
      dimH := hdimH
      cont := hcont'
      Xc := H7.cfg.Xc
      cpt := hcpt
      tame := htameCfg
      ov := hov }
  have hεr : 0 < β / ((pieces.length : ℝ) + 1) := by positivity
  obtain ⟨gb, hgbcont, hgbLc, hgbdist, hb, hbsupp, hbeng⟩ :=
    hB M (hc '' V) X N Γc' H Lc gc' hAmb' hcfg hXhcV hBad
      (β / ((pieces.length : ℝ) + 1)) hεr
  -- ## the new state
  have hgb_gc' : ∀ x ∈ Lc, gb x = gc' x := fun x hx => hgbLc hx
  have hoffLC : ∀ x ∈ L ∪ Cr, gc' x = gc x := by
    rintro x (hx | hx)
    · exact hoffL x hx
    · exact hoffCr x hx
  have htrans : (hc.trans hb) '' V = hb '' (hc '' V) := Work.Engulf.image_trans_image hc hb V
  have hHb : H = G ∪ P' := by rw [hHdef, hP'def, Set.union_assoc]
  refine ⟨Γc', P', gb, hc.trans hb, ?_⟩
  refine
    { le := by omega
      sub := fun s hs => hsub' (hSsub hs)
      fin := hfin'
      dim := hdim'
      newP := ?_
      subP := hP'Γc'
      disjP := ?_
      dimP := ?_
      cont := hgbcont
      frz := ?_
      chart := ?_
      simP := ?_
      gaff := ?_
      near := ?_
      eng := ?_
      supp := Work.Engulf.csupp_trans hSsupp hbsupp }
  · intro s hs
    rcases hfaces' s hs with hsc | hsΔ
    · rcases hSnewP s hsc with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (h1.trans hP'sub)
    · exact Or.inr ((Work.Engulf.simp_mono hsΔ).trans hΔ'sub)
  · exact Set.disjoint_left.mpr fun x hx hxsp =>
      hx.elim (fun h1 => Set.disjoint_left.mp hSdisjP h1 hxsp)
        (fun h1 => Set.disjoint_left.mp hΔ'disjΓ₁ h1 hxsp)
  · intro s hs hsP
    rcases hfaces' s hs with hsc | hsΔ
    · rw [hP'def] at hsP
      have h1 : simp s ⊆ P := by
        intro x hx
        rcases hsP hx with h | h
        · exact h
        · exact absurd h (fun hxd => Set.disjoint_left.mp hΔ'disj hxd
            (Geometry.SimplicialComplex.convexHull_subset_space hsc hx))
      exact hSdimP s hsc h1
    · exact le_trans (Finset.card_le_card hsΔ)
        (le_trans (le_of_eq hcard') (le_trans hpcard (by omega)))
  · intro x hx
    exact (hgb_gc' x (by rw [hLcdef]; exact Or.inl hx)).trans
      ((hoffLC x hx).trans (hSfrz hx))
  · refine Work.Engulf.SmoothChart.congr (fun x hx => hgb_gc' x (hmemLc x hx)) hchartNew
  · rintro z ⟨x, hx, rfl⟩
    rw [hgb_gc' x (hmemLcP x hx)]
    exact hsimP' ⟨x, hx, rfl⟩
  · intro j hj hj'
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjr | hjeq
    · intro z hz
      obtain ⟨w, hw, rfl⟩ := hSgaff j hjr hj' hz
      exact ⟨w, hP'sub hw, (hgb_gc' w (hmemLcP w (hP'sub hw))).trans (hoffP w hw)⟩
    · subst j
      calc ψ.toFun '' simp pieces[r] = ψ.toFun '' (Am '' simp Δ') := by rw [hAmsimp]
        _ = (fun x => ψ.toFun (Am x)) '' simp Δ' := Set.image_image ψ.toFun Am (simp Δ')
        _ = gc' '' simp Δ' :=
            (Set.image_congr fun x hx => by rw [gc'_apply, if_pos hx]).symm
        _ = gb '' simp Δ' :=
            Set.image_congr fun x hx => (hgb_gc' x (hmemLcΔ x hx)).symm
        _ ⊆ gb '' P' := Set.image_mono hΔ'sub
  · intro x hx
    have hxΓc : x ∈ Γc.space := hspΓ₁Γc hx
    have hxΓc' : x ∈ Γc'.space := hspΓ₁Γc' hx
    have h1 : dist (gb x) (gc' x) < β / ((pieces.length : ℝ) + 1) := hgbdist x hxΓc'
    have h2 : dist (gc' x) (g x) ≤ (r : ℝ) * β / ((pieces.length : ℝ) + 1) := by
      rw [hoff x hxΓc]; exact hSnear x hx
    have h3 : dist (gb x) (g x) ≤
        β / ((pieces.length : ℝ) + 1) + (r : ℝ) * β / ((pieces.length : ℝ) + 1) :=
      le_trans (dist_triangle _ _ _) (add_le_add (le_of_lt h1) h2)
    have h4 : ((r + 1 : ℕ) : ℝ) * β / ((pieces.length : ℝ) + 1) =
        β / ((pieces.length : ℝ) + 1) + (r : ℝ) * β / ((pieces.length : ℝ) + 1) := by
      push_cast; ring
    rw [h4]; exact h3
  · rw [htrans, ← hHb]; exact hbeng

end Work.Engulf.E4P
