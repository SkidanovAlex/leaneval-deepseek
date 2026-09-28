import Mathlib
import Submission.Work.Serre.csrDefs

namespace Work.Serre

open scoped Topology
open Work.RatHurewicz

/-- Elementary point-set facts about the half-balls around the centres of the attached cells, used by
the rational cell step.  For `Z = attachCells n Y ι f`, `o_i = csrOpenBall i` is the image of the
open model ball of radius `1/2`, `B_i = csrBall i` the image of the closed model ball of radius
`1/2`, `S_i = csrSphere i` its boundary sphere, `c_i = csrCentre i` the centre and `V = csrV` the
complement of all centres. -/
theorem csrGeom (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) :
    (∀ i, IsOpen (csrOpenBall n Y ι f i)) ∧
    (∀ i, IsClosed (csrBall n Y ι f i)) ∧
    (∀ i, csrOpenBall n Y ι f i ⊆ csrBall n Y ι f i) ∧
    (∀ i, csrBall n Y ι f i \ csrSphere n Y ι f i = csrOpenBall n Y ι f i) ∧
    (∀ i, csrCentre n Y ι f i ∈ csrOpenBall n Y ι f i) ∧
    (∀ i, csrBall n Y ι f i ⊆ Work.RatHurewicz.cellInterior n Y ι f i) ∧
    (∀ i j, i ≠ j → Disjoint (csrOpenBall n Y ι f i) (csrOpenBall n Y ι f j)) ∧
    (∀ i j, i ≠ j → Disjoint (csrBall n Y ι f i) (csrBall n Y ι f j)) ∧
    (∀ i, csrOpenBall n Y ι f i ∩ csrCentres n Y ι f = {csrCentre n Y ι f i}) ∧
    IsOpen (csrV n Y ι f) ∧
    ((⋃ i, csrOpenBall n Y ι f i) ∪ csrV n Y ι f = Set.univ) ∧
    ((⋃ i, csrOpenBall n Y ι f i) ∩ csrV n Y ι f =
      ⋃ i, (csrOpenBall n Y ι f i \ {csrCentre n Y ι f i})) := by
  classical
  -- the model-level set inclusions
  have hmodel1 : {y : cellDisk n | ‖(y : CellVec n)‖ < 1/2} ⊆ cellInner n :=
    fun y hy => mem_cellInner_of_norm_lt (lt_trans hy (by norm_num))
  have hmodel2 : {y : cellDisk n | ‖(y : CellVec n)‖ ≤ 1/2} ⊆ cellInner n :=
    fun y hy => mem_cellInner_of_norm_lt (lt_of_le_of_lt hy (by norm_num))
  have hmodel3 : {y : cellDisk n | ‖(y : CellVec n)‖ < 1/2} ⊆
      {y : cellDisk n | ‖(y : CellVec n)‖ ≤ 1/2} :=
    fun y hy => le_of_lt (show ‖(y : CellVec n)‖ < 1/2 from hy)
  have hOpen : ∀ i, IsOpen (csrOpenBall n Y ι f i) := by
    intro i
    exact Work.RatHurewicz.isOpen_cellMap_image
      (U := {y : cellDisk n | ‖(y : CellVec n)‖ < 1/2})
      (isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const) hmodel1
  have hClosed : ∀ i, IsClosed (csrBall n Y ι f i) := fun i =>
    Work.AttachPush.isClosed_cellMap_image_closedBall n Y ι f i (ρ := 1/2) (by norm_num)
  have hsub_ob : ∀ i, csrOpenBall n Y ι f i ⊆ csrBall n Y ι f i := fun i =>
    Set.image_mono (f := cellMap n Y ι f i) hmodel3
  have hb_int : ∀ i, csrBall n Y ι f i ⊆ Work.RatHurewicz.cellInterior n Y ι f i := fun i =>
    Set.image_mono (f := cellMap n Y ι f i) hmodel2
  have ho_int : ∀ i, csrOpenBall n Y ι f i ⊆ Work.RatHurewicz.cellInterior n Y ι f i :=
    fun i => (hsub_ob i).trans (hb_int i)
  have hdiff : ∀ i, csrBall n Y ι f i \ csrSphere n Y ι f i = csrOpenBall n Y ι f i := by
    intro i
    ext z
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hzS⟩
      have hxle : ‖(x : CellVec n)‖ ≤ 1/2 := hx
      have hxne : ¬ (‖(x : CellVec n)‖ = 1/2) := fun hxeq => hzS ⟨x, hxeq, rfl⟩
      exact ⟨x, lt_of_le_of_ne hxle hxne, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      have hxlt : ‖(x : CellVec n)‖ < 1/2 := hx
      refine ⟨⟨x, le_of_lt hxlt, rfl⟩, ?_⟩
      rintro ⟨y, hy, hyx⟩
      have hye : ‖(y : CellVec n)‖ = 1/2 := hy
      have hymem : y ∈ cellInner n :=
        mem_cellInner_of_norm_lt (by rw [hye]; norm_num)
      have hxmem : x ∈ cellInner n := mem_cellInner_of_norm_lt (lt_trans hxlt (by norm_num))
      have heq : (⟨y, hymem⟩ : ↥(cellInner n)) = ⟨x, hxmem⟩ :=
        Work.RatHurewicz.cellMap_injective_cellInner (f := f) i (by simpa using hyx)
      have hyx' : y = x := congrArg (fun t : ↥(cellInner n) => (t : cellDisk n)) heq
      have hylt : ‖(y : CellVec n)‖ < 1/2 := by rw [hyx']; exact hxlt
      exact absurd hye (ne_of_lt hylt)
  have hcentre : ∀ i, csrCentre n Y ι f i ∈ csrOpenBall n Y ι f i := fun i =>
    ⟨Work.RatHurewicz.cellDiskCentre n, by
      show ‖((Work.RatHurewicz.cellDiskCentre n : cellDisk n) : CellVec n)‖ < 1/2
      rw [Work.RatHurewicz.cellDiskCentre_coe]
      simp only [norm_zero]
      norm_num, rfl⟩
  have hdisj_o : ∀ i j, i ≠ j → Disjoint (csrOpenBall n Y ι f i) (csrOpenBall n Y ι f j) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro z hzi hzj
    exact Set.disjoint_left.mp (Work.RatHurewicz.disjoint_cellInterior (f := f) i j hij)
      (ho_int i hzi) (ho_int j hzj)
  have hdisj_b : ∀ i j, i ≠ j → Disjoint (csrBall n Y ι f i) (csrBall n Y ι f j) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro z hzi hzj
    exact Set.disjoint_left.mp (Work.RatHurewicz.disjoint_cellInterior (f := f) i j hij)
      (hb_int i hzi) (hb_int j hzj)
  have hcentre_inter : ∀ i, csrOpenBall n Y ι f i ∩ csrCentres n Y ι f = {csrCentre n Y ι f i} := by
    intro i
    ext z
    constructor
    · rintro ⟨hzO, hzC⟩
      obtain ⟨j, hj⟩ := hzC
      have hi : z ∈ Work.RatHurewicz.cellInterior n Y ι f i := ho_int i hzO
      have hj' : z ∈ Work.RatHurewicz.cellInterior n Y ι f j := by
        rw [← hj]
        exact Work.RatHurewicz.cellOrigin_mem_cellInterior n Y ι f j
      have hji : j = i := by
        by_contra hne
        exact Set.disjoint_left.mp (Work.RatHurewicz.disjoint_cellInterior (f := f) j i hne) hj' hi
      exact hj.symm.trans (congrArg (csrCentre n Y ι f) hji)
    · intro hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨hcentre i, ⟨i, rfl⟩⟩
  have hVopen : IsOpen (csrV n Y ι f) := by
    have hcc : IsClosed (csrCentres n Y ι f) := by
      show IsClosed (Work.RatHurewicz.cellCentres n Y ι f)
      exact Work.RatHurewicz.isClosed_cellCentres n Y ι f
    exact hcc.isOpen_compl
  have hcover : (⋃ i, csrOpenBall n Y ι f i) ∪ csrV n Y ι f = Set.univ := by
    ext z
    constructor
    · intro _; exact trivial
    · intro _
      by_cases hz : z ∈ csrV n Y ι f
      · exact Or.inr hz
      · refine Or.inl (Set.mem_iUnion.mpr ?_)
        have hzC : z ∈ csrCentres n Y ι f := by
          by_contra h
          exact hz (by simpa [csrV] using h)
        obtain ⟨i, hi⟩ := hzC
        exact ⟨i, by rw [← hi]; exact hcentre i⟩
  have hcap : (⋃ i, csrOpenBall n Y ι f i) ∩ csrV n Y ι f =
      ⋃ i, (csrOpenBall n Y ι f i \ {csrCentre n Y ι f i}) := by
    ext z
    constructor
    · rintro ⟨hzU, hzV⟩
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hzU
      refine Set.mem_iUnion.mpr ⟨i, hi, ?_⟩
      intro hzs
      rw [Set.mem_singleton_iff] at hzs
      exact hzV ⟨i, hzs.symm⟩
    · rintro hz
      obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion.mp hz
      refine ⟨Set.mem_iUnion.mpr ⟨i, hi⟩, ?_⟩
      intro hzC
      obtain ⟨j, hj⟩ := hzC
      have hmem : z ∈ csrOpenBall n Y ι f i ∩ csrCentres n Y ι f := ⟨hi, ⟨j, hj⟩⟩
      rw [hcentre_inter i] at hmem
      exact hzi hmem
  exact ⟨hOpen, hClosed, hsub_ob, hdiff, hcentre, hb_int, hdisj_o, hdisj_b,
    hcentre_inter, hVopen, hcover, hcap⟩

end Work.Serre
