import Mathlib
import Submission.Work.RatHurewicz.AttachPush.CellInterior
import Submission.Work.RatHurewicz.attachIncl_isOpenMap_range
import Submission.Work.RatHurewicz.AttachCells
import Submission.Work.RatHurewicz.attachCells_extension
import Submission.Work.StemsB.attachCells_openData

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Attaching a subfamily of cells inside a larger attachment

Given a space `Y` with a family of attaching maps `f : ι → C(S^{n+1}, Y)`, a subspace
`ψ : W ↪ Y`, a subfamily `e : J → ι` of cells whose attaching maps land in `ψ(W)`, and lifts
`h j` of the attaching maps `f (e j)` along `ψ`, the attachment `attachCells n W J h` maps into
`attachCells n Y ι f` as a subspace: the induced map `ψ'` is an embedding, it extends `ψ` (through
the two inclusions), and its range is exactly the union of the image of `ψ` and of the cells of the
subfamily.

## Main results

* `isOpen_cellDisk_interior_union_image` — the open model cell plus the image of an open part of
  the boundary sphere is open in the closed model cell;
* `attachSubmodel` — the target statement.
-/

open scoped Topology

namespace Work.StemsB

open Work.RatHurewicz

noncomputable section

/-- The union of the open model cell with the image of an open subset of the boundary sphere is
open in the closed model cell: its complement in the closed ball is the image of the closed
complement of the open subset of the boundary sphere, which is compact, hence closed. -/
theorem isOpen_cellDisk_interior_union_image (n : ℕ) (T : Set (cellSphere n)) (hT : IsOpen T) :
    IsOpen ({x : cellDisk n | ‖(x : CellVec n)‖ < 1} ∪ cellSphereToDisk n '' T) := by
  have hcompl : ({x : cellDisk n | ‖(x : CellVec n)‖ < 1} ∪ cellSphereToDisk n '' T)ᶜ
      = cellSphereToDisk n '' Tᶜ := by
    ext x
    constructor
    · intro hx
      have hx1 : ¬ ‖(x : CellVec n)‖ < 1 := fun h => hx (Or.inl h)
      have hxle : ‖(x : CellVec n)‖ ≤ 1 := by
        have h := Metric.mem_closedBall.mp x.2
        simpa [dist_eq_norm] using h
      have heq : ‖(x : CellVec n)‖ = 1 := le_antisymm hxle (not_lt.mp hx1)
      refine ⟨⟨(x : CellVec n), ?_⟩, fun hxT => hx (Or.inr ⟨_, hxT, rfl⟩), Subtype.ext rfl⟩
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
      exact heq
    · rintro ⟨z, hz, rfl⟩
      rintro (h | ⟨z', hz', hzz'⟩)
      · have h1 : ‖(((cellSphereToDisk n) z : cellDisk n) : CellVec n)‖ < 1 := h
        rw [norm_cellSphereToDisk n z] at h1
        exact absurd h1 (lt_irrefl 1)
      · exact hz (AttachRange.cellSphereToDisk_injective n hzz' ▸ hz')
  rw [← isClosed_compl_iff, hcompl]
  exact (IsCompact.image
    (IsCompact.of_isClosed_subset isCompact_univ hT.isClosed_compl (Set.subset_univ _))
    (cellSphereToDisk n).continuous).isClosed


/-- The map induced on a sub-attachment by the inclusion of the subspace and of the cells of a
subfamily is injective.  This is the pure quotient-set-theory half of `attachSubmodel`: two points
of `attachCells n W J κ` are equal as soon as their images are, because the two gluing relations
correspond under `w ↦ ψ w`, `(j,x) ↦ (e j, x)`. -/
theorem attachCells_lift_injective_aux (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphere n, Y))
    (W : Type) [TopologicalSpace W] (ψ : C(W, Y)) (hψ : Function.Injective (ψ : W → Y))
    {J : Type} (e : J → ι) (he : Function.Injective e)
    (κ : J → C(cellSphere n, W)) (hκ : ∀ j : J, ψ.comp (κ j) = f (e j))
    (ψ' : C(attachCells n W J κ, attachCells n Y ι f))
    (hψ'₁ : ψ'.comp (attachIncl n W J κ) = (attachIncl n Y ι f).comp ψ)
    (hψ'₂ : ∀ j : J, ψ'.comp (cellMap n W J κ j) = cellMap n Y ι f (e j)) :
    Function.Injective (ψ' : attachCells n W J κ → attachCells n Y ι f) := by
  classical
  -- the map induced on the disjoint unions
  let φ : W ⊕ (Σ _ : J, cellDisk n) → Y ⊕ (Σ _ : ι, cellDisk n) :=
    Sum.elim (fun w => Sum.inl (ψ w)) (fun p => Sum.inr ⟨e p.1, p.2⟩)
  have hqB : ∀ a₀ : W ⊕ (Σ _ : J, cellDisk n),
      ψ' (Quotient.mk'' a₀) = Quotient.mk'' (φ a₀) := by
    intro a₀
    cases a₀ with
    | inl w => exact DFunLike.congr_fun hψ'₁ w
    | inr p => obtain ⟨j, x⟩ := p; exact DFunLike.congr_fun (hψ'₂ j) x
  -- the class of a point of `Y`
  have key_inl : ∀ {w : W} {y : Y}, clsPt n Y ι f (Sum.inl (ψ w)) y → y = ψ w := by
    rintro w y (h | ⟨i, z, h, -⟩)
    · exact (Sum.inl.inj h).symm
    · exact absurd h Sum.inl_ne_inr
  have key_inr : ∀ {j : J} {x : cellDisk n} {y : Y},
      clsPt n Y ι f (Sum.inr (⟨e j, x⟩ : Σ _ : ι, cellDisk n)) y →
      ∃ z : cellSphere n, x = cellSphereToDisk n z ∧ y = f (e j) z := by
    rintro j x y (h | ⟨i, z, h, hf⟩)
    · exact absurd h Sum.inr_ne_inl
    · have hsig : (⟨e j, x⟩ : Σ _ : ι, cellDisk n) = ⟨i, cellSphereToDisk n z⟩ := Sum.inr.inj h
      have hi : e j = i := congrArg (fun p : Σ _ : ι, cellDisk n => p.1) hsig
      refine ⟨z, congrArg (fun p : Σ _ : ι, cellDisk n => p.2) hsig, ?_⟩
      rw [← hf, hi]
  -- a boundary point of the `j`-th cell is glued to `κ j z`
  have step : ∀ (j : J) (z : cellSphere n),
      Relation.EqvGen (attachRel n W J κ)
        (Sum.inr (⟨j, cellSphereToDisk n z⟩ : Σ _ : J, cellDisk n)) (Sum.inl (κ j z)) :=
    fun j z => Relation.EqvGen.symm _ _
      (Relation.EqvGen.rel (r := attachRel n W J κ) _ _ ⟨j, z, rfl, rfl⟩)
  -- the two gluing relations correspond
  have hrel : ∀ a₀ b₀ : W ⊕ (Σ _ : J, cellDisk n),
      Relation.EqvGen (attachRel n Y ι f) (φ a₀) (φ b₀) →
      Relation.EqvGen (attachRel n W J κ) a₀ b₀ := by
    intro a₀ b₀ h
    have hcls := (cls_iff n Y ι f (φ a₀) (φ b₀)).mp (AttachRange.eqvGen_le_cls n Y ι f h)
    rcases hcls with heq | ⟨y, h1, h2⟩
    · cases a₀ with
      | inl w =>
        cases b₀ with
        | inl w' =>
          have hww : w = w' := hψ (Sum.inl.inj heq)
          subst hww
          exact Relation.EqvGen.refl _
        | inr p => exact absurd heq Sum.inl_ne_inr
      | inr p =>
        obtain ⟨j, x⟩ := p
        cases b₀ with
        | inl w' => exact absurd heq Sum.inr_ne_inl
        | inr p' =>
          obtain ⟨j', x'⟩ := p'
          have hsig : (⟨e j, x⟩ : Σ _ : ι, cellDisk n) = ⟨e j', x'⟩ := Sum.inr.inj heq
          have hjj : j = j' := he (congrArg (fun p : Σ _ : ι, cellDisk n => p.1) hsig)
          have hxx : x = x' := congrArg (fun p : Σ _ : ι, cellDisk n => p.2) hsig
          subst hjj
          subst hxx
          exact Relation.EqvGen.refl _
    · cases a₀ with
      | inl w =>
        cases b₀ with
        | inl w' =>
          have hw : y = ψ w := key_inl h1
          have hw' : y = ψ w' := key_inl h2
          have hww : w = w' := hψ (hw.symm.trans hw')
          subst hww
          exact Relation.EqvGen.refl _
        | inr p' =>
          obtain ⟨j', x'⟩ := p'
          have hw : y = ψ w := key_inl h1
          obtain ⟨z', hx', hy'⟩ := key_inr (j := j') (x := x') h2
          have hκ' : ψ (κ j' z') = f (e j') z' := DFunLike.congr_fun (hκ j') z'
          have hwκ : w = κ j' z' := hψ (by rw [← hw, hy', hκ'])
          subst hwκ
          rw [hx']
          exact Relation.EqvGen.rel (r := attachRel n W J κ) _ _ ⟨j', z', rfl, rfl⟩
      | inr p =>
        obtain ⟨j, x⟩ := p
        cases b₀ with
        | inl w' =>
          have hw' : y = ψ w' := key_inl h2
          obtain ⟨z, hx, hy⟩ := key_inr (j := j) (x := x) h1
          have hκ' : ψ (κ j z) = f (e j) z := DFunLike.congr_fun (hκ j) z
          have hzw : κ j z = w' := hψ (by rw [hκ', ← hy, hw'])
          subst hzw
          rw [hx]
          exact step j z
        | inr p' =>
          obtain ⟨j', x'⟩ := p'
          obtain ⟨z, hx, hy⟩ := key_inr (j := j) (x := x) h1
          obtain ⟨z', hx', hy'⟩ := key_inr (j := j') (x := x') h2
          have hκ' : ψ (κ j z) = f (e j) z := DFunLike.congr_fun (hκ j) z
          have hκ'' : ψ (κ j' z') = f (e j') z' := DFunLike.congr_fun (hκ j') z'
          have hsum : f (e j) z = f (e j') z' := by rw [← hy, ← hy']
          have hκeq : κ j z = κ j' z' := hψ (by rw [hκ', hκ'', hsum])
          rw [hx, hx']
          have hY : Relation.EqvGen (attachRel n W J κ) (Sum.inl (κ j z))
              (Sum.inr (⟨j', cellSphereToDisk n z'⟩ : Σ _ : J, cellDisk n)) := by
            rw [hκeq]
            exact (step j' z').symm
          exact Relation.EqvGen.trans _ _ _ (step j z) hY
  -- injectivity
  intro a b hab
  obtain ⟨a₀, rfl⟩ := Quotient.exists_rep a
  obtain ⟨b₀, rfl⟩ := Quotient.exists_rep b
  have hφ : (Quotient.mk'' (φ a₀) : attachCells n Y ι f) = Quotient.mk'' (φ b₀) := by
    rw [← hqB a₀, ← hqB b₀]
    exact hab
  exact Quotient.sound (s := Relation.EqvGen.setoid (attachRel n W J κ))
    (hrel a₀ b₀ (Quotient.exact hφ))

theorem attachSubmodel (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y))
    (W : Type) [TopologicalSpace W] (ψ : C(W, Y)) (hψ : Topology.IsEmbedding (ψ : W → Y))
    {J : Type} (e : J → ι) (he : Function.Injective e)
    (hJ : ∀ j : J, Set.range (f (e j)) ⊆ Set.range (ψ : W → Y)) :
    ∃ (h : J → C(Work.RatHurewicz.cellSphere n, W)) (_ : ∀ j : J, ψ.comp (h j) = f (e j))
      (ψ' : C(Work.RatHurewicz.attachCells n W J h, Work.RatHurewicz.attachCells n Y ι f))
      (q : C(W, Work.RatHurewicz.attachCells n W J h)),
      Topology.IsEmbedding (ψ' : Work.RatHurewicz.attachCells n W J h →
        Work.RatHurewicz.attachCells n Y ι f) ∧
      ψ'.comp q = (Work.RatHurewicz.attachIncl n Y ι f).comp ψ ∧
      Set.range (ψ' : Work.RatHurewicz.attachCells n W J h →
        Work.RatHurewicz.attachCells n Y ι f)
        = Set.range ((Work.RatHurewicz.attachIncl n Y ι f).comp ψ)
          ∪ ⋃ j : J, Set.range (Work.RatHurewicz.cellMap n Y ι f (e j)) := by
  classical
  -- ## Step 1: the lifts `h j : S^{n+1} → W` of the attaching maps `f (e j)`
  let h : J → C(cellSphere n, W) := fun j =>
    ⟨fun z => (hψ.toHomeomorph.symm ⟨f (e j) z, hJ j ⟨z, rfl⟩⟩ : W),
      hψ.toHomeomorph.symm.continuous_toFun.comp
        ((f (e j)).continuous.subtype_mk (fun z => hJ j ⟨z, rfl⟩))⟩
  have hh : ∀ j : J, ψ.comp (h j) = f (e j) := by
    intro j
    ext z
    exact congrArg Subtype.val (hψ.toHomeomorph.apply_symm_apply (⟨f (e j) z, hJ j ⟨z, rfl⟩⟩ :
      Set.range (ψ : W → Y)))
  -- ## Step 2: the map `ψ'` out of the sub-attachment, by the universal property
  have hglue : ∀ (j : J) (z : cellSphere n),
      (cellMap n Y ι f (e j)) (cellSphereToDisk n z)
        = ((attachIncl n Y ι f).comp ψ) (h j z) := by
    intro j z
    have h1 : ψ (h j z) = f (e j) z := DFunLike.congr_fun (hh j) z
    rw [← attachIncl_attachRel n Y ι f (e j) z, ContinuousMap.comp_apply, h1]
  obtain ⟨ψ', hψ'₁, hψ'₂⟩ :=
    attachCells_extension n W J h ((attachIncl n Y ι f).comp ψ)
      (fun j => cellMap n Y ι f (e j)) hglue
  -- ## Step 3: injectivity and the range of `ψ'`
  have hinj : Function.Injective (ψ' : attachCells n W J h → attachCells n Y ι f) :=
    attachCells_lift_injective_aux n Y ι f W ψ hψ.injective e he h hh ψ' hψ'₁ hψ'₂
  have hrange : Set.range (ψ' : attachCells n W J h → attachCells n Y ι f)
      = Set.range (((attachIncl n Y ι f).comp ψ : C(W, attachCells n Y ι f)) : W → _)
        ∪ ⋃ j : J, Set.range (cellMap n Y ι f (e j)) := by
    ext b
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨a₀, rfl⟩ := Quotient.exists_rep a
      cases a₀ with
      | inl w =>
        refine Or.inl ⟨w, ?_⟩
        have h2 : ψ' (attachIncl n W J h w)
            = ((attachIncl n Y ι f).comp ψ : C(W, attachCells n Y ι f)) w :=
          DFunLike.congr_fun hψ'₁ w
        exact h2.symm
      | inr p =>
        obtain ⟨j, x⟩ := p
        refine Or.inr (Set.mem_iUnion.mpr ⟨j, ⟨x, ?_⟩⟩)
        have h2 : ψ' (cellMap n W J h j x) = cellMap n Y ι f (e j) x :=
          DFunLike.congr_fun (hψ'₂ j) x
        exact h2.symm
    · rintro (h1 | h2)
      · obtain ⟨w, rfl⟩ := h1
        exact ⟨attachIncl n W J h w, DFunLike.congr_fun hψ'₁ w⟩
      · obtain ⟨j, x, hx⟩ := Set.mem_iUnion.mp h2
        exact ⟨cellMap n W J h j x, (DFunLike.congr_fun (hψ'₂ j) x).trans hx⟩
  -- ## Step 4: `ψ'` is inducing
  have his : Topology.IsInducing (ψ' : attachCells n W J h → attachCells n Y ι f) := by
    rw [Topology.isInducing_iff]
    refine (TopologicalSpace.ext_iff).2 (fun Vopen => ?_)
    rw [isOpen_induced_iff]
    constructor
    · intro hV
      -- the data of `V` on `W` and on the cells of the subfamily
      set UW : Set W := attachIncl n W J h ⁻¹' Vopen with hUW
      set Uj : J → Set (cellDisk n) := fun j => cellMap n W J h j ⁻¹' Vopen with hUj
      have hUWo : IsOpen UW := hV.preimage (attachIncl n W J h).continuous
      have hUjo : ∀ j, IsOpen (Uj j) := fun j => hV.preimage (cellMap n W J h j).continuous
      -- the two pieces agree on the boundary sphere
      have hsat : ∀ (j : J) (z : cellSphere n), h j z ∈ UW ↔ cellSphereToDisk n z ∈ Uj j := by
        intro j z
        have heq := attachIncl_attachRel n W J h j z
        rw [hUW, hUj, Set.mem_preimage, Set.mem_preimage, heq]
      -- an open set of `Y` realizing `UW` on `W`
      obtain ⟨O, hOo, hOpre⟩ := (hψ.toIsInducing.isOpen_iff).1 hUWo
      have hOO : ∀ w : W, ψ w ∈ O ↔ w ∈ UW := fun w => by
        rw [← hOpre, Set.mem_preimage]
      -- the data of the open set of the big attachment: on the cells of the subfamily it is the
      -- data coming from `V`, on the other cells it is the open model cell together with the
      -- boundary points whose attaching map lies in `O`
      let Ai : ι → Set (cellDisk n) := fun i =>
        if hc : ∃ j : J, e j = i then Uj (Classical.choose hc)
        else {x : cellDisk n | ‖(x : CellVec n)‖ < 1} ∪ cellSphereToDisk n '' ((f i) ⁻¹' O)
      have hAie : ∀ j : J, Ai (e j) = Uj j := by
        intro j
        have hc : ∃ j' : J, e j' = e j := ⟨j, rfl⟩
        dsimp only [Ai]
        rw [dif_pos hc]
        exact congrArg Uj (he (Classical.choose_spec hc))
      have hAio : ∀ i, IsOpen (Ai i) := by
        intro i
        by_cases hc : ∃ j : J, e j = i
        · dsimp only [Ai]
          rw [dif_pos hc]
          exact hUjo (Classical.choose hc)
        · dsimp only [Ai]
          rw [dif_neg hc]
          exact isOpen_cellDisk_interior_union_image n _ ((f i).continuous.isOpen_preimage O hOo)
      have hcompat : ∀ (i : ι) (z : cellSphere n), f i z ∈ O ↔ cellSphereToDisk n z ∈ Ai i := by
        intro i z
        by_cases hc : ∃ j : J, e j = i
        · have hce : e (Classical.choose hc) = i := Classical.choose_spec hc
          have hcb : Ai i = Uj (Classical.choose hc) := by
            dsimp only [Ai]; rw [dif_pos hc]
          rw [hcb, ← hsat (Classical.choose hc) z, ← hOO (h (Classical.choose hc) z)]
          have h2 : ψ (h (Classical.choose hc) z) = f (e (Classical.choose hc)) z :=
            DFunLike.congr_fun (hh (Classical.choose hc)) z
          have hfe : f (e (Classical.choose hc)) z = f i z := congrArg (fun k => (f k) z) hce
          rw [← hfe, h2]
        · have hcb : Ai i = {x : cellDisk n | ‖(x : CellVec n)‖ < 1} ∪
              cellSphereToDisk n '' ((f i) ⁻¹' O) := by
            dsimp only [Ai]; rw [dif_neg hc]
          rw [hcb]
          constructor
          · intro hfz
            exact Or.inr ⟨z, hfz, rfl⟩
          · rintro (h1 | ⟨z', hz', hzz'⟩)
            · have h1' : ‖(((cellSphereToDisk n) z : cellDisk n) : CellVec n)‖ < 1 := h1
              rw [norm_cellSphereToDisk n z] at h1'
              exact absurd h1' (lt_irrefl 1)
            · rwa [AttachRange.cellSphereToDisk_injective n hzz'] at hz'
      -- the basic open set of the big attachment
      obtain ⟨V₀, hV₀o, hV₀pre, hV₀cell⟩ :=
        attachCells_openData n Y ι f O Ai hOo hAio hcompat
      refine ⟨V₀, hV₀o, ?_⟩
      have key₁ : ∀ w : W, ψ' (attachIncl n W J h w) ∈ V₀ ↔ attachIncl n W J h w ∈ Vopen := by
        intro w
        have h1 : attachIncl n Y ι f (ψ w) ∈ V₀ ↔ w ∈ UW := by
          rw [← Set.mem_preimage, hV₀pre]
          exact hOO w
        have h2 : ψ' (attachIncl n W J h w) = attachIncl n Y ι f (ψ w) :=
          DFunLike.congr_fun hψ'₁ w
        have h3 : attachIncl n W J h w ∈ Vopen ↔ w ∈ UW := by
          rw [hUW, Set.mem_preimage]
        rw [h2, h1, h3]
      have key₂ : ∀ (j : J) (x : cellDisk n),
          ψ' (cellMap n W J h j x) ∈ V₀ ↔ cellMap n W J h j x ∈ Vopen := by
        intro j x
        have h1 : cellMap n Y ι f (e j) x ∈ V₀ ↔ x ∈ Ai (e j) := by
          rw [← Set.mem_preimage, hV₀cell (e j)]
        have h2 : ψ' (cellMap n W J h j x) = cellMap n Y ι f (e j) x :=
          DFunLike.congr_fun (hψ'₂ j) x
        have h3 : cellMap n W J h j x ∈ Vopen ↔ x ∈ Ai (e j) := by
          rw [hAie j, hUj, Set.mem_preimage]
        rw [h2, h1, h3]
      ext a
      rw [Set.mem_preimage]
      obtain ⟨a₀, rfl⟩ := Quotient.exists_rep a
      cases a₀ with
      | inl w => exact key₁ w
      | inr p => obtain ⟨j, x⟩ := p; exact key₂ j x
    · rintro ⟨V₀, hV₀o, hV₀pre⟩
      rw [← hV₀pre]
      exact hV₀o.preimage (ψ'.continuous)
  exact ⟨h, hh, ψ', attachIncl n W J h, ⟨his, hinj⟩, hψ'₁, hrange⟩

end

end Work.StemsB
