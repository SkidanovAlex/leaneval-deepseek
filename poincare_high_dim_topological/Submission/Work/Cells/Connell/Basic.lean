import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.Cells.Connell.Defs
import Submission.Work.Cells.Connell.extOverDisc_of_homeomorph
import Submission.Work.Cells.Connell.cubeChart_isOpen_image_openCube

/-!
# Basic glue lemmas for the Connell chapter

Transport lemmas for `PL.IsOpenCell`, `PL.ExtOverDisc` and `PL.CellCover` along
homeomorphisms and to subspaces, plus the one-step padding `CellCover n M k → CellCover n M (k+1)`
for `1 ≤ k`.
-/

open Set Metric

namespace Work.Cells.Connell

/-- The identity map identifies `{x : ↥A | (x : X) ∈ V}` with `↥V` when `V ⊆ A`. -/
noncomputable def homeomorphSubtypeOfSubset {X : Type*} [TopologicalSpace X] {A V : Set X}
    (hVA : V ⊆ A) : ↥{x : ↥A | (x : X) ∈ V} ≃ₜ ↥V where
  toFun x := ⟨(x : ↥A).1, x.2⟩
  invFun y := ⟨⟨y.1, hVA y.2⟩, y.2⟩
  left_inv x := by ext; rfl
  right_inv y := by ext; rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- `ExtOverDisc` passes from `↥V` to the corresponding subset of a larger subtype `↥A`. -/
theorem extOverDisc_subtype {X : Type*} [TopologicalSpace X] {A V : Set X} (hVA : V ⊆ A) {j : ℕ}
    (h : PL.ExtOverDisc ↥V j) : PL.ExtOverDisc ↥{x : ↥A | (x : X) ∈ V} j :=
  extOverDisc_of_homeomorph (homeomorphSubtypeOfSubset hVA).symm h

/-- The image of an open `n`-cell under a self-homeomorphism is an open `n`-cell. -/
theorem isOpenCell_image_homeomorph {n : ℕ} {M : Type*} [TopologicalSpace M] (h : M ≃ₜ M)
    {U : Set M} (hU : PL.IsOpenCell n U) : PL.IsOpenCell n (h '' U) := by
  refine ⟨h.isOpenMap U hU.1, ?_⟩
  obtain ⟨e⟩ := hU.2
  exact ⟨(h.image U).symm.trans e⟩

/-- An open cell contained in a subspace remains an open cell of that subspace. -/
theorem isOpenCell_subtype {n : ℕ} {M : Type*} [TopologicalSpace M] {A U : Set M}
    (hU : PL.IsOpenCell n U) (hUA : U ⊆ A) : PL.IsOpenCell n {x : ↥A | (x : M) ∈ U} := by
  refine ⟨hU.1.preimage continuous_subtype_val, ?_⟩
  obtain ⟨e⟩ := hU.2
  exact ⟨(homeomorphSubtypeOfSubset hUA).trans e⟩

/-- Padding a cell cover: for `1 ≤ k`, a cover by `k` open cells is a cover by `k+1` open
cells (repeat one of the cells).  The case `k = 0` is excluded because `CellCover n M 0` says
that `M` is empty. -/
theorem cellCover_succ {n : ℕ} {M : Type*} [TopologicalSpace M] {k : ℕ} (hk : 1 ≤ k)
    (h : PL.CellCover n M k) : PL.CellCover n M (k + 1) := by
  obtain ⟨W, hW, hcov⟩ := h
  let i0 : Fin k := ⟨0, by omega⟩
  let W' : Fin (k + 1) → Set M := Fin.snoc (α := fun _ => Set M) W (W i0)
  refine ⟨W', ?_, ?_⟩
  · refine Fin.lastCases (motive := fun i => PL.IsOpenCell n (W' i)) ?_ ?_
    · simpa [W', Fin.snoc_last] using hW i0
    · intro i; simpa [W', Fin.snoc_castSucc] using hW i
  · refine Set.eq_univ_of_forall fun x => ?_
    have hx : x ∈ ⋃ i : Fin k, W i := by rw [hcov]; exact Set.mem_univ x
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨Fin.castSucc i, by simpa [W', Fin.snoc_castSucc] using hi⟩


/-- The point-avoidance lemma for a thin set, in its cleanest form: if `F` is a finite family of
compact subsets of `openCube 1` with empty interior and `L ⊆ ⋃ i, F i`, then the image of `L`
under a chart misses a point of any nonempty open set `Aᶜ` with `A` closed.  (Proof: a finite
union of nowhere dense sets is nowhere dense.) -/
theorem exists_notMem_image_of_thinFamily' {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    {A : Set M} (hA : IsClosed A) (hAne : (Aᶜ).Nonempty) (cC : PL.CubeChart n M)
    {ι : Type} [Finite ι] (F : ι → Set (PL.E n)) (hF : ThinFamily F) {L : Set (PL.E n)}
    (hL : L ⊆ ⋃ i, F i) : ∃ p ∈ Aᶜ, p ∉ cC.toFun '' L := by
  have hFnd : ∀ i, IsNowhereDense (F i) :=
    fun i => ((hF i).1.isClosed).isNowhereDense_iff.mpr (hF i).2.2
  have hndL : IsNowhereDense L := (IsNowhereDense.iUnion hFnd).mono hL
  have hIntClL : interior (closure L) = ∅ := hndL
  have himg : interior (cC.toFun '' L) = ∅ := by
    let U : Set (PL.E n) := PL.openCube (n := n) 1
    have hUopen : IsOpen U := isOpen_openCube n 1
    have hLU : L ⊆ U := by
      intro x hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hL hx)
      exact (hF i).2.1 hi
    let L' : Set ↥U := Subtype.val ⁻¹' L
    have hL'val : Subtype.val '' L' = L := by
      ext x; constructor
      · rintro ⟨y, hy, rfl⟩; exact hy
      · intro hx; exact ⟨⟨x, hLU hx⟩, hx, rfl⟩
    have hL'nd : IsNowhereDense L' := by
      rw [IsNowhereDense]
      have hcl : closure L' = Subtype.val ⁻¹' closure L := by
        rw [hUopen.isOpenEmbedding_subtypeVal.isEmbedding.closure_eq_preimage_closure_image L',
          hL'val]
      rw [hcl, ← hUopen.isOpenMap_subtype_val.preimage_interior_eq_interior_preimage
            continuous_subtype_val (closure L), hIntClL, preimage_empty]
    have hndImg : IsNowhereDense ((U.domRestrict cC.toFun) '' L') :=
      cC.emb.isInducing.isNowhereDense_image hL'nd
    have heq : (U.domRestrict cC.toFun) '' L' = cC.toFun '' L := by
      ext y; constructor
      · rintro ⟨x, hx, rfl⟩; exact ⟨x.1, hx, rfl⟩
      · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hLU hx⟩, hx, rfl⟩
    rw [heq] at hndImg
    exact eq_empty_of_subset_empty (hndImg ▸ interior_mono subset_closure)
  by_contra hcon
  push Not at hcon
  have hsub : Aᶜ ⊆ cC.toFun '' L := fun x hx => hcon x hx
  have hle : Aᶜ ⊆ interior (cC.toFun '' L) := interior_maximal hsub hA.isOpen_compl
  rw [himg] at hle
  obtain ⟨p, hp⟩ := hAne
  exact (notMem_empty p) (hle hp)

end Work.Cells.Connell
