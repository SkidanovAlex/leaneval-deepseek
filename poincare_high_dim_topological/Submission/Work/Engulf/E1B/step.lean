import Mathlib
import Submission.Work.Engulf.Basic
import Submission.Work.Engulf.E1Inv
import Submission.Work.Engulf.Tools
import Submission.Work.Engulf.Chain.E1gAux
import Submission.Work.Engulf.E1g.far_piece
import Submission.Work.Engulf.Auxi.smoothChart_extend
import Submission.Work.Engulf.Auxi.tame_extend
import Submission.Work.Engulf.Auxi.EngulfAux
import Submission.Work.Engulf.Auxi.exists_thickening_subset
import Submission.Work.Engulf.Auxi.TameTransfer
import Submission.Work.Engulf.Auxi.SimplexCover
import Submission.Work.Engulf.Auxi.SubdivCard
import Submission.Work.Engulf.Auxi.face_subset_of_subset_union

/-!
# `Work.Engulf.E1B.step` — the inner loop step of one chart group (repaired Newman Lemma 5)

The statement **as requested** was

```
theorem step {n p N : ℕ} {M : Type*} [MetricSpace M] {V X : Set M} {Γ : PL.Cx N}
    ... (hB : Work.Engulf.B n p (p + 1)) (A : Work.Engulf.Amb n p M V) ... :
    ∃ Γ' G' g' h', Work.Engulf.Chain.E1GSt ... := (unprovable as written)
```

and it is **not provable as written**: Lean elaborates it with *two independent universe
parameters*, one for the space `M` and one for `B`.  `Work.Engulf.B` is universe-polymorphic
(`def B (n p k : ℕ) : Prop := ∀ (M : Type u) [MetricSpace M] …, …` in
`Submission/Work/Engulf/Defs.lean`), so with the implicit universes of the request the
declaration reads

    step.{u₁, u₂} : ∀ {M : Type u₁} [MetricSpace M] … (hB : B.{u₂} n p (p+1)) … → …

The conclusion `E1GSt …` must be produced for the space `M : Type u₁`, and the only tool that
can advance the state is `hB`, which speaks about spaces `M : Type u₂`.  Since `u₁` and `u₂` are
unrelated, the application `hB M` is rejected by Lean (“The argument `M` has type `Type u_1` of
sort `Type (u_1 + 1)` but is expected to have type `Type u_2`”), and the gap cannot be closed:
`E1GSt` at `r + 1` requires `ψ '' PL.simp pieces[r] ⊆ g' '' G'` (`E1GSt.gaff` at `j = r`), which
is obtained by `B n p (p+1)` engulfing the fresh far piece `q`; none of the other hypotheses
(`Amb`, `Cfg`, `E1GInv`, `E1GSt` at `r`) can manufacture it.

This is the same defect (universe polymorphism) that made `Engulf/Chain/E2` and
`Engulf/Chain/E3` unprovable; see the module docstrings of
`Submission/Work/Engulf/Chain/E2.lean` and `Submission/Work/Engulf/Chain/E3.lean`.

## What is proved below

The statement below is the requested one with the two universes identified by the file-level
`universe u` (`{M : Type u}` and `hB : Work.Engulf.B.{u} n p (p+1)`).  This is exactly the shape
used by the `Work.Engulf.Chain` twin of the lemma
(`Submission/Work/Engulf/Chain/E1gStep.lean`, `Work.Engulf.Chain.E1g_step`), and exactly the shape
the caller `Submission/Work/Engulf/E1B/group.lean` uses it in (`universe u`, `M : Type u`,
`hB : Work.Engulf.B.{u} n p (p+1)`), so it is the usable specialization of the request.  It is
proved: add the piece `pieces[r]` — whose `ψ`-image lies in the closed `5/8`-cube and is disjoint
from the frozen image `g '' F` — as a far face `q` of the current complex (`Work.Engulf.E1g.far_piece`),
extend `gr` to `g' := ψ ∘ Am` on `PL.simp q`, verify the `Cfg` axioms, and apply `hB` to engulf
`X₁ ∪ g' '' (H ∪ F ∪ G ∪ PL.simp q)`, producing the state at `r + 1`.
-/

open Set Metric PL Work.Engulf.Chain

universe u

namespace Work.Engulf.E1B

set_option maxHeartbeats 800000 in
theorem step {n p N : ℕ} {M : Type u} [MetricSpace M] {V X : Set M} {Γ : PL.Cx N}
    {H L : Set (PL.E N)} {f : PL.E N → M} {ψs : List (PL.CubeChart n M)} {ε : ℝ} {k : ℕ}
    {Γk : PL.Cx N} {F : Set (PL.E N)} {Xk : Set M} {g : PL.E N → M} {h : M ≃ₜ M}
    (hB : Work.Engulf.B.{u} n p (p + 1)) (A : Work.Engulf.Amb n p M V)
    (c : Work.Engulf.Cfg n p V X Γ H L f)
    (I : Work.Engulf.E1GInv n p V X Γ H L f ψs ε k Γk F Xk g h)
    {ψ : PL.CubeChart n M} {X₁ : Set M} {pieces : List (Finset (PL.E n))} {η : ℝ}
    (hη : 0 < η) (hX₁c : IsClosed X₁) (hX₁X : X₁ ⊆ X)
    (hpieces : ∀ j (hj : j < pieces.length),
      (pieces[j]).Nonempty ∧
      AffineIndependent ℝ (fun v : ↥(pieces[j]) => (v : PL.E n)) ∧
      (pieces[j]).card ≤ p + 1 ∧ PL.simp (pieces[j]) ⊆ PL.closedCube (5 / 8 : ℝ) ∧
      Disjoint (ψ.toFun '' PL.simp (pieces[j])) (g '' F))
    {r : ℕ} {Γr : PL.Cx N} {G : Set (PL.E N)} {gr : PL.E N → M} {hr : M ≃ₜ M}
    (hrl : r < pieces.length)
    (S : Work.Engulf.Chain.E1GSt (n := n) (p := p) V X Γk H L F ψ X₁ g pieces η r Γr G gr hr) :
    ∃ (Γ' : PL.Cx N) (G' : Set (PL.E N)) (g' : PL.E N → M) (h' : M ≃ₜ M),
      Work.Engulf.Chain.E1GSt (n := n) (p := p) V X Γk H L F ψ X₁ g pieces η (r + 1) Γ' G' g' h' := by
  classical
  obtain ⟨hle, hsub, hfin, hdim, hnewG, hsubG, hdisjG, hdimG, hcont, hfrz, hgaff, hnear, htame,
    hchart, heng, hsupp⟩ := S
  obtain ⟨hΔne, hΔaff, hΔcard, hΔcube, hΔfar⟩ := hpieces r hrl
  have hroom : 2 * p + 4 ≤ N := c.room
  -- ## the far piece
  obtain ⟨Γ', q, Am, hfin', hsub', hqmem, hfaces', hspace', hdisj', hcard', hAmq, hAsimp,
    hAinj⟩ := Work.Engulf.E1g.far_piece Γr hfin (pieces[r]) hΔne hΔaff (by omega)
  have hΓkΓr : Γk.space ⊆ Γr.space := space_mono hsub
  have hΓrΓ' : Γr.space ⊆ Γ'.space := by rw [hspace']; exact Set.subset_union_left
  have hΓkΓ' : Γk.faces ⊆ Γ'.faces := fun s hs => hsub' (hsub hs)
  have hqdisj : Disjoint (PL.simp q) Γr.space := Set.disjoint_iff_inter_eq_empty.mpr hdisj'
  have hsqΓ' : PL.simp q ⊆ Γ'.space := by rw [hspace']; exact Set.subset_union_right
  -- ## the new function
  set g' : PL.E N → M := fun x => if x ∈ PL.simp q then ψ.toFun (Am x) else gr x with hg'def
  have g'_apply : ∀ x : PL.E N, g' x = if x ∈ PL.simp q then ψ.toFun (Am x) else gr x := by
    intro x; rw [hg'def]
  have hoff : ∀ x ∈ Γr.space, g' x = gr x := by
    intro x hx
    rw [g'_apply, if_neg]
    exact fun hxq => Set.disjoint_left.mp hqdisj hxq hx
  have hAm_cube : ∀ x ∈ PL.simp q, Am x ∈ PL.openCube (1 : ℝ) := by
    intro x hx
    have h1 : Am x ∈ Am '' PL.simp q := ⟨x, hx, rfl⟩
    rw [hAsimp] at h1
    exact Work.Engulf.closedCube_subset_openCube (by norm_num) (hΔcube h1)
  have hgimg : g' '' PL.simp q = ψ.toFun '' PL.simp pieces[r] := by
    rw [← hAsimp, Set.image_image]
    exact Set.image_congr (fun x hx => by rw [g'_apply, if_pos hx])
  -- ## continuity
  have hcont_q : ContinuousOn g' (PL.simp q) := by
    have hcomp : ContinuousOn (fun x => ψ.toFun (Am x)) (PL.simp q) :=
      ψ.cont.comp (Am.continuous_of_finiteDimensional.continuousOn) (fun x hx => hAm_cube x hx)
    exact hcomp.congr (fun x hx => by rw [g'_apply, if_pos hx])
  have hcont_r : ContinuousOn g' Γr.space :=
    hcont.congr (fun x hx => hoff x hx)
  have hcont' : ContinuousOn g' Γ'.space := by
    rw [hspace']
    exact (continuousOn_union_iff_of_isClosed (Work.Engulf.isClosed_space hfin)
      (Work.Engulf.isClosed_simp q)).2 ⟨hcont_r, hcont_q⟩
  -- ## where the various sets live
  have hHFG_rspace : ∀ x ∈ H ∪ F ∪ G, x ∈ Γr.space := by
    intro x hx
    rcases hx with h1 | hxG
    · rcases h1 with hxH | hxF
      · exact hΓkΓr (space_mono I.sub (c.subH.subset_space hxH))
      · exact hΓkΓr (I.subF.subset_space hxF)
    · exact hsubG.subset_space hxG
  have hHLG_rspace : ∀ x ∈ (H ∩ L) ∪ F ∪ G, x ∈ Γr.space := by
    intro x hx
    rcases hx with h1 | hxG
    · rcases h1 with hxHL | hxF
      · exact hΓkΓr (space_mono I.sub (c.subH.subset_space hxHL.1))
      · exact hΓkΓr (I.subF.subset_space hxF)
    · exact hsubG.subset_space hxG
  have hLG_rspace : ∀ x ∈ L ∪ G, x ∈ Γr.space := by
    intro x hx
    rcases hx with hxL | hxG
    · exact hΓkΓr (space_mono I.sub (c.subL.subset_space hxL))
    · exact hsubG.subset_space hxG
  have hLT : ∀ x ∈ (H ∩ L) ∪ F ∪ G, g' x = gr x := fun x hx => hoff x (hHLG_rspace x hx)
  have hHFG_off : ∀ x ∈ H ∪ F ∪ G, g' x = gr x := fun x hx => hoff x (hHFG_rspace x hx)
  -- ## membership bookkeeping for the frozen sets
  have memL' : (L ∪ F ∪ (G ∪ PL.simp q)) ⊆ (L ∪ F ∪ G ∪ PL.simp q) := by
    intro x hx; simp only [Set.mem_union] at hx ⊢; tauto
  have memsqL' : PL.simp q ⊆ (L ∪ F ∪ G ∪ PL.simp q) := by
    intro x hx; simp only [Set.mem_union]; tauto
  have memGL' : G ⊆ (L ∪ F ∪ G ∪ PL.simp q) := by
    intro x hx; simp only [Set.mem_union]; tauto
  have hH'L' : ∀ x, x ∈ (H ∪ F ∪ G ∪ PL.simp q) ∩ (L ∪ F ∪ G ∪ PL.simp q) →
      x ∈ (H ∩ L) ∪ F ∪ G ∪ PL.simp q := by
    intro x hx
    have h1 := hx.1
    have h2 := hx.2
    simp only [Set.mem_union, Set.mem_inter_iff] at h1 h2 ⊢
    tauto
  have hHLq : ∀ x, x ∈ (H ∩ L) ∪ F ∪ G ∪ PL.simp q →
      x ∈ (H ∩ L) ∪ F ∪ G ∨ x ∈ PL.simp q := by
    intro x hx
    simpa only [Set.mem_union] using hx
  -- ## compactness of the parts of the overlap set
  have hHc : IsCompact (H ∩ L) :=
    Work.Engulf.isCompact_of_isSubSp c.fin (Work.Engulf.isSubSp_inter c.subH c.subL)
  have hFc : IsCompact F := Work.Engulf.isCompact_of_isSubSp I.fin I.subF
  have hGc : IsCompact G := Work.Engulf.isCompact_of_isSubSp hfin hsubG
  have hHFGc : IsCompact ((H ∩ L) ∪ F ∪ G) := (hHc.union hFc).union hGc
  have hgrHFGc : IsCompact (gr '' ((H ∩ L) ∪ F ∪ G)) :=
    hHFGc.image_of_continuousOn (hcont.mono (fun x hx => hHLG_rspace x hx))
  have hgrHFG_sub : gr '' ((H ∩ L) ∪ F ∪ G) ⊆ hr '' V := by
    rintro z ⟨x, hx, rfl⟩
    refine heng (Or.inr ⟨x, ?_, rfl⟩)
    rcases hx with h1 | hxG
    · rcases h1 with hxHL | hxF
      · exact Or.inl (Or.inl hxHL.1)
      · exact Or.inl (Or.inr hxF)
    · exact Or.inr hxG
  have hTclosed : IsClosed (X₁ ∪ gr '' ((H ∩ L) ∪ F ∪ G)) :=
    hX₁c.union hgrHFGc.isClosed
  have hX₁V : X₁ ⊆ hr '' V := fun x hx => heng (Or.inl hx)
  -- ## the overlap control
  have hov : Work.Engulf.OvCtl (hr '' V) X₁ (H ∪ F ∪ G ∪ PL.simp q)
      (L ∪ F ∪ G ∪ PL.simp q) g' := by
    refine ⟨((H ∩ L) ∪ F ∪ G) ∪
      (PL.simp q ∩ g' ⁻¹' (X₁ ∪ gr '' ((H ∩ L) ∪ F ∪ G))), ?_, ?_, ?_, ?_⟩
    · refine hHFGc.union ?_
      have h1 : IsClosed (Γ'.space ∩ g' ⁻¹' (X₁ ∪ gr '' ((H ∩ L) ∪ F ∪ G))) :=
        hcont'.preimage_isClosed_of_isClosed (Work.Engulf.isClosed_space hfin') hTclosed
      have h2 : PL.simp q ∩ g' ⁻¹' (X₁ ∪ gr '' ((H ∩ L) ∪ F ∪ G)) =
          PL.simp q ∩ (Γ'.space ∩ g' ⁻¹' (X₁ ∪ gr '' ((H ∩ L) ∪ F ∪ G))) := by
        ext x
        constructor
        · rintro ⟨hxq, hx⟩
          exact ⟨hxq, hsqΓ' hxq, hx⟩
        · rintro ⟨hxq, -, hx⟩
          exact ⟨hxq, hx⟩
      rw [h2]
      exact (Work.Engulf.isCompact_simp q).inter_right h1
    · rintro z ⟨x, hx, rfl⟩
      rcases hx with hx | hx
      · have hxg : x ∈ H ∪ F ∪ G := by
          rcases hx with h1 | hxG
          · rcases h1 with hxHL | hxF
            · exact Or.inl (Or.inl hxHL.1)
            · exact Or.inl (Or.inr hxF)
          · exact Or.inr hxG
        rw [hLT x hx]
        exact heng (Or.inr ⟨x, hxg, rfl⟩)
      · rcases (Set.mem_preimage.mp hx.2 : g' x ∈ X₁ ∪ gr '' ((H ∩ L) ∪ F ∪ G)) with h | h
        · exact hX₁V h
        · exact hgrHFG_sub h
    · intro x hx y hy hxy hne
      have hxq := hH'L' x hx
      rcases hHLq x hxq with hxcase | hxq'
      · exact Or.inl hxcase
      · refine Or.inr ⟨hxq', ?_⟩
        rcases hHLq y (hH'L' y hy) with hycase | hyq'
        · exact Or.inr ⟨y, hycase, by rw [hxy, hLT y hycase]⟩
        · exfalso
          refine hne (hAinj hxq' hyq' ?_)
          refine cubeChart_inj ψ (hAm_cube x hxq') (hAm_cube y hyq') ?_
          calc ψ.toFun (Am x) = g' x := by rw [g'_apply, if_pos hxq']
            _ = g' y := hxy
            _ = ψ.toFun (Am y) := by rw [g'_apply, if_pos hyq']
    · intro x hx hxX
      have hxq := hH'L' x hx
      rcases hHLq x hxq with hxcase | hxq'
      · exact Or.inl hxcase
      · exact Or.inr ⟨hxq', Or.inl hxX⟩
  -- ## the smoothing data
  have hchart1 : Work.Engulf.SmoothChart p X Γ' (L ∪ G) g' ψ := by
    refine smoothChart_mono (Subset.rfl : X ⊆ X) hsub' ?_ ?_ hchart
    · intro s hs hsL
      by_contra hsr
      obtain hsq : s ⊆ q := by
        rcases hfaces' s hs with h | h
        · exact absurd h hsr
        · exact h
      have h1 : PL.simp s ⊆ PL.simp q := Work.Engulf.simp_mono hsq
      have h2 : PL.simp s ⊆ Γr.space := fun x hx => hLG_rspace x (hsL hx)
      have : PL.simp s = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        intro x hx
        exact Set.disjoint_left.mp hqdisj (h1 hx) (h2 hx)
      exact absurd (Work.Engulf.simp_eq_empty_iff.mp this) (Γ'.nonempty_of_mem_faces hs).ne_empty
    · intro x hx
      exact hoff x (hLG_rspace x hx)
  have hsplit2 : ∀ s ∈ Γ'.faces, PL.simp s ⊆ (L ∪ G) ∪ PL.simp q →
      PL.simp s ⊆ L ∪ G ∨ PL.simp s ⊆ PL.simp q := by
    intro s hs hsub2
    rcases hfaces' s hs with hsr | hsq
    · refine Or.inl ?_
      intro x hx
      rcases hsub2 hx with h | h
      · exact h
      · exact absurd (Geometry.SimplicialComplex.convexHull_subset_space hsr hx)
          (Set.disjoint_left.mp hqdisj h)
    · exact Or.inr (Work.Engulf.simp_mono hsq)
  have hlin : ∀ s ∈ Γ'.faces, PL.simp s ⊆ PL.simp q → Work.Engulf.LinIn ψ g' (PL.simp s) := by
    intro s hs hsimp
    have hsq : s ⊆ q := (Γ'.face_subset_face_iff hs hqmem).mp hsimp
    refine ⟨Am, fun y hy => ⟨hAm_cube y (Work.Engulf.simp_mono hsq hy), ?_⟩⟩
    rw [g'_apply, if_pos (Work.Engulf.simp_mono hsq hy)]
  have hchart2 : Work.Engulf.SmoothChart p X Γ' ((L ∪ G) ∪ PL.simp q) g' ψ :=
    Work.Engulf.Aux.smoothChart_extend hchart1 hsplit2 hlin
  have hsplit3 : ∀ s ∈ Γ'.faces, PL.simp s ⊆ (L ∪ G) ∪ F ∪ PL.simp q →
      PL.simp s ⊆ L ∪ G ∨ PL.simp s ⊆ F ∨ PL.simp s ⊆ PL.simp q := by
    intro s hs hsub3
    rcases hfaces' s hs with hsr | hsq
    · rcases hnewG s hsr with hsk | hsG
      · rcases I.newF s hsk with hsΓ | hsF
        · refine Or.inl ?_
          intro x hx
          have hxΓ : x ∈ Γ.space := Geometry.SimplicialComplex.convexHull_subset_space hsΓ hx
          rcases hsub3 hx with h1 | hxq
          · rcases h1 with h2 | hxF
            · rcases h2 with hLG | hG
              · exact Or.inl hLG
              · exact absurd (space_mono I.sub hxΓ) (Set.disjoint_left.mp hdisjG hG)
            · exact absurd hxΓ (Set.disjoint_left.mp I.disjF hxF)
          · exact absurd (hΓkΓr (space_mono I.sub hxΓ)) (Set.disjoint_left.mp hqdisj hxq)
        · exact Or.inr (Or.inl hsF)
      · exact Or.inl (hsG.trans Set.subset_union_right)
    · exact Or.inr (Or.inr (Work.Engulf.simp_mono hsq))
  have htame_in : Work.Engulf.Tame n p X Γ' ((L ∪ G) ∪ F) g' := by
    refine tame_mono (p := p) (X := X) (X' := X) (L := (L ∪ G) ∪ F) (f := gr) (f' := g')
      (Subset.rfl : X ⊆ X) hsub' ?_ ?_ ?_
    · intro s hs hsLGF
      by_contra hsr
      obtain hsq : s ⊆ q := by
        rcases hfaces' s hs with h | h
        · exact absurd h hsr
        · exact h
      have h1 : PL.simp s ⊆ PL.simp q := Work.Engulf.simp_mono hsq
      have h2 : PL.simp s ⊆ Γr.space := by
        intro x hx
        rcases hsLGF hx with h | h
        · exact hLG_rspace x h
        · exact hΓkΓr (I.subF.subset_space h)
      have : PL.simp s = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        intro x hx
        exact Set.disjoint_left.mp hqdisj (h1 hx) (h2 hx)
      exact absurd (Work.Engulf.simp_eq_empty_iff.mp this) (Γ'.nonempty_of_mem_faces hs).ne_empty
    · intro x hx
      rcases hx with h | h
      · exact hoff x (hLG_rspace x h)
      · exact hoff x (hΓkΓr (I.subF.subset_space h))
    · have hEq : (L ∪ G) ∪ F = (L ∪ F) ∪ G := by
        ext x; simp only [Set.mem_union]; tauto
      rw [hEq]
      exact htame
  have hSim : g' '' PL.simp q ⊆ ψ.toFun '' PL.closedCube (5 / 8 : ℝ) := by
    rw [hgimg]
    rintro z ⟨y, hy, rfl⟩
    exact ⟨y, hΔcube hy, rfl⟩
  have hFT1 : g' '' F = gr '' F :=
    Set.image_congr (fun x hx => hoff x (hΓkΓr (I.subF.subset_space hx)))
  have hFT2 : gr '' F = g '' F := Set.image_congr (fun x hx => hfrz (Or.inr hx))
  have hdisjS : Disjoint (g' '' PL.simp q) (g' '' F) := by
    rw [hgimg, hFT1, hFT2]
    exact hΔfar
  have htame_cfg : Work.Engulf.Tame n p X Γ' (L ∪ F ∪ G ∪ PL.simp q) g' := by
    have h1 : Work.Engulf.IsSubSp Γ' F := isSubSp_mono hΓkΓ' I.subF
    have h2 : Work.Engulf.IsSubSp Γ' (PL.simp q) := isSubSp_simp_of_mem hqmem
    have h3 := Work.Engulf.Aux.tame_extend ψ (ρ := (5 / 8 : ℝ)) (by norm_num) hfin' hcont' h1 h2
      hsplit3 htame_in hchart2 hSim hdisjS
    have hEq : (L ∪ G) ∪ F ∪ PL.simp q = L ∪ F ∪ G ∪ PL.simp q := by
      ext x; simp only [Set.mem_union]; tauto
    rwa [hEq] at h3
  have htame_cfg₁ : Work.Engulf.Tame n p X₁ Γ' (L ∪ F ∪ G ∪ PL.simp q) g' :=
    tame_mono_X hX₁X htame_cfg
  -- ## the configuration and the subcomplex data
  have hsubH' : Work.Engulf.IsSubSp Γ' (H ∪ F ∪ G ∪ PL.simp q) :=
    Work.Engulf.isSubSp_union
      (Work.Engulf.isSubSp_union
        (Work.Engulf.isSubSp_union
          (isSubSp_mono hΓkΓ' (isSubSp_mono I.sub c.subH))
          (isSubSp_mono hΓkΓ' I.subF))
        (isSubSp_mono hsub' hsubG))
      (isSubSp_simp_of_mem hqmem)
  have hsubL' : Work.Engulf.IsSubSp Γ' (L ∪ F ∪ G ∪ PL.simp q) :=
    Work.Engulf.isSubSp_union
      (Work.Engulf.isSubSp_union
        (Work.Engulf.isSubSp_union
          (isSubSp_mono hΓkΓ' (isSubSp_mono I.sub c.subL))
          (isSubSp_mono hΓkΓ' I.subF))
        (isSubSp_mono hsub' hsubG))
      (isSubSp_simp_of_mem hqmem)
  have hdim' : PL.DimLE Γ' (p + 1) := by
    intro t ht
    rcases hfaces' t ht with htr | htq
    · exact hdim t htr
    · exact le_trans (Finset.card_le_card htq) (le_trans (le_of_eq hcard') (by omega))
  have hdimH' : ∀ t ∈ Γ'.faces, PL.simp t ⊆ H ∪ F ∪ G ∪ PL.simp q → t.card ≤ p + 1 := by
    intro t ht htH
    rcases hfaces' t ht with htr | htq
    · rcases hnewG t htr with htk | htG
      · rcases I.newF t htk with htΓ | htF
        · refine c.dimH t htΓ ?_
          intro x hx
          have hxΓ : x ∈ Γ.space := Geometry.SimplicialComplex.convexHull_subset_space htΓ hx
          have hxΓk : x ∈ Γk.space := space_mono I.sub hxΓ
          rcases htH hx with h1 | hxq
          · rcases h1 with h2 | hxG
            · rcases h2 with hxH | hxF
              · exact hxH
              · exact absurd hxΓ (Set.disjoint_left.mp I.disjF hxF)
            · exact absurd hxΓk (Set.disjoint_left.mp hdisjG hxG)
          · exact absurd (hΓkΓr hxΓk) (Set.disjoint_left.mp hqdisj hxq)
        · exact I.dimF t htk htF
      · exact hdimG t htr htG
    · exact le_trans (Finset.card_le_card htq) (le_trans (le_of_eq hcard') hΔcard)
  have hg'q_comp : IsCompact (g' '' PL.simp q) :=
    (Work.Engulf.isCompact_simp q).image_of_continuousOn hcont_q
  have hHFGq_c : IsCompact (H ∪ F ∪ G ∪ PL.simp q) :=
    (((Work.Engulf.isCompact_of_isSubSp c.fin c.subH).union
      (Work.Engulf.isCompact_of_isSubSp I.fin I.subF)).union
      (Work.Engulf.isCompact_of_isSubSp hfin hsubG)).union (Work.Engulf.isCompact_simp q)
  have hHFGq_sub : H ∪ F ∪ G ∪ PL.simp q ⊆ Γ'.space := by
    intro x hx
    rcases hx with h1 | hxq
    · rcases h1 with h2 | hxG
      · rcases h2 with hxH | hxF
        · exact hΓrΓ' (hHFG_rspace x (Or.inl (Or.inl hxH)))
        · exact hΓrΓ' (hHFG_rspace x (Or.inl (Or.inr hxF)))
      · exact hΓrΓ' (hHFG_rspace x (Or.inr hxG))
    · exact hsqΓ' hxq
  have hclosed_cpt : IsClosed ((X₁ ∪ g' '' (H ∪ F ∪ G ∪ PL.simp q)) \ hr '' V) := by
    refine IsClosed.inter ?_ ?_
    · refine hX₁c.union ?_
      exact (hHFGq_c.image_of_continuousOn (hcont'.mono hHFGq_sub)).isClosed
    · exact (hr.isOpen_image.mpr A.Vo).isClosed_compl
  have hval : (X₁ ∪ g' '' (H ∪ F ∪ G ∪ PL.simp q)) ⊆ hr '' V ∪ g' '' PL.simp q := by
    rintro z (hz | ⟨x, hx, rfl⟩)
    · exact Or.inl (hX₁V hz)
    · rcases hx with h1 | hxq
      · rcases h1 with h2 | hxG
        · rcases h2 with hxH | hxF
          · have hxg : x ∈ H ∪ F ∪ G := Or.inl (Or.inl hxH)
            rw [hHFG_off x hxg]
            exact Or.inl (heng (Or.inr ⟨x, hxg, rfl⟩))
          · have hxg : x ∈ H ∪ F ∪ G := Or.inl (Or.inr hxF)
            rw [hHFG_off x hxg]
            exact Or.inl (heng (Or.inr ⟨x, hxg, rfl⟩))
        · have hxg : x ∈ H ∪ F ∪ G := Or.inr hxG
          rw [hHFG_off x hxg]
          exact Or.inl (heng (Or.inr ⟨x, hxg, rfl⟩))
      · exact Or.inr ⟨x, hxq, rfl⟩
  have hcpt : IsCompact ((X₁ ∪ g' '' (H ∪ F ∪ G ∪ PL.simp q)) \ hr '' V) :=
    IsCompact.of_isClosed_subset hg'q_comp hclosed_cpt (by
      intro z hz
      rcases hval hz.1 with h | h
      · exact absurd h hz.2
      · exact h)
  have hcfg : Work.Engulf.Cfg n p (hr '' V) X₁ Γ' (H ∪ F ∪ G ∪ PL.simp q)
      (L ∪ F ∪ G ∪ PL.simp q) g' :=
    { fin := hfin'
      dimΓ := hdim'
      room := c.room
      subH := hsubH'
      subL := hsubL'
      dimH := hdimH'
      cont := hcont'
      Xc := hX₁c
      cpt := hcpt
      tame := tame_mono_X hX₁X htame_cfg
      ov := hov }
  have hAmb' : Work.Engulf.Amb n p M (hr '' V) := Work.Engulf.Amb.image_homeomorph hr A
  obtain ⟨gb, hgbcont, hgbL, hgbdist, hb, hbsupp, hbeng⟩ :=
    hB M (hr '' V) X₁ N Γ' (H ∪ F ∪ G ∪ PL.simp q) (L ∪ F ∪ G ∪ PL.simp q) g' hAmb' hcfg
      hX₁V (fun s hs hsH _ => hdimH' s hs hsH) η hη
  -- ## the new state
  have hcomp : (hr.trans hb) '' V = hb '' (hr '' V) := by
    rw [Set.image_image]; rfl
  refine ⟨Γ', G ∪ PL.simp q, gb, hr.trans hb,
    ⟨by omega, hΓkΓ', hfin', hdim', ?_, ?_, ?_, ?_, hgbcont, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro s hs
    rcases hfaces' s hs with hsr | hsq
    · exact (hnewG s hsr).imp id (fun h => h.trans Set.subset_union_left)
    · exact Or.inr ((Work.Engulf.simp_mono hsq).trans Set.subset_union_right)
  · exact Work.Engulf.isSubSp_union (isSubSp_mono hsub' hsubG)
      (isSubSp_simp_of_mem hqmem)
  · refine Set.disjoint_union_left.mpr ⟨hdisjG, ?_⟩
    exact Set.disjoint_left.mpr (fun x hxq hxk => Set.disjoint_left.mp hqdisj hxq (hΓkΓr hxk))
  · intro s hs hsGq
    rcases hfaces' s hs with hsr | hsq
    · refine hdimG s hsr ?_
      intro x hx
      rcases hsGq hx with hxG | hxq
      · exact hxG
      · exact absurd (Geometry.SimplicialComplex.convexHull_subset_space hsr hx)
          (Set.disjoint_left.mp hqdisj hxq)
    · exact le_trans (Finset.card_le_card hsq) (le_trans (le_of_eq hcard') hΔcard)
  · intro x hx
    have hxq : x ∈ L ∪ F ∪ (G ∪ PL.simp q) := by
      simp only [Set.mem_union] at hx ⊢; tauto
    have hxr : x ∈ Γr.space := by
      rcases hx with hxL | hxF
      · exact hLG_rspace x (Or.inl hxL)
      · exact hΓkΓr (I.subF.subset_space hxF)
    exact (hgbL (memL' hxq)).trans ((hoff x hxr).trans (hfrz hx))
  · intro j hj hj'
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjr | hjeq
    · refine (hgaff j hjr hj').trans ?_
      rintro z ⟨y, hy, rfl⟩
      exact ⟨y, Set.subset_union_left hy,
        (hgbL (memGL' hy)).trans (hoff y (hsubG.subset_space hy))⟩
    · subst j
      calc ψ.toFun '' PL.simp pieces[r] = g' '' PL.simp q := hgimg.symm
        _ = gb '' PL.simp q := Set.image_congr (fun x hx => (hgbL (memsqL' hx)).symm)
        _ ⊆ gb '' (G ∪ PL.simp q) := Set.image_mono Set.subset_union_right
  · intro x hx
    have hxr : x ∈ Γr.space := hΓkΓr hx
    have hx' : x ∈ Γ'.space := hΓrΓ' hxr
    have h1 : dist (gb x) (g' x) < η := hgbdist x hx'
    have h2 : dist (g' x) (g x) ≤ (r : ℝ) * η := by rw [hoff x hxr]; exact hnear x hx
    have h3 : dist (gb x) (g x) ≤ (r : ℝ) * η + η := by
      linarith [dist_triangle (gb x) (g' x) (g x)]
    have h4 : ((r + 1 : ℕ) : ℝ) * η = (r : ℝ) * η + η := by push_cast; ring
    rw [h4]; exact h3
  · have hEq : L ∪ F ∪ (G ∪ PL.simp q) = L ∪ F ∪ G ∪ PL.simp q := by
      ext x; simp only [Set.mem_union]; tauto
    rw [hEq]
    exact Work.Engulf.Tame.congr (fun x hx => hgbL hx) htame_cfg
  · have hEq : (L ∪ G) ∪ PL.simp q = L ∪ (G ∪ PL.simp q) := by
      ext x; simp only [Set.mem_union]; tauto
    rw [hEq] at hchart2
    exact Work.Engulf.SmoothChart.congr
      (fun x hx => hgbL (by simp only [Set.mem_union] at hx ⊢; tauto)) hchart2
  · rw [hcomp]
    intro z hz
    rcases hz with hz | ⟨x, hx, rfl⟩
    · exact hbeng (Or.inl hz)
    · refine hbeng (Or.inr ⟨x, ?_, rfl⟩)
      simp only [Set.mem_union] at hx ⊢
      tauto
  · exact Work.Engulf.csupp_trans hsupp hbsupp


end Work.Engulf.E1B
