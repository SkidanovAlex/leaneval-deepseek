import Mathlib
import Submission.Work.Serre.serreC0KillHomologyDefs
import Submission.Work.RatHurewicz.AttachPush.CellInterior

set_option synthInstance.maxHeartbeats 400000

/-!
# `serreC0KillHomology`: the cover and its shell pieces

Point-set facts about the cover `KillU ∪ KillV` of `KillX f = attachCells n Y ι f` and about the
shell pieces `KillQ f i`: they are open, pairwise disjoint, and their union is `KillZ f`, the
intersection of the two members of the cover.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Serre

noncomputable section

open Work.RatHurewicz

variable {n : ℕ} {Y : Type} [TopologicalSpace Y] {ι : Type}

/-- The outer member of the cover is open. -/
theorem isOpen_KillU (f : ι → C(cellSphere n, Y)) : IsOpen (KillU f) :=
  isOpen_cellU f (by norm_num)

/-- The inner member of the cover is open. -/
theorem isOpen_KillV (f : ι → C(cellSphere n, Y)) : IsOpen (KillV f) :=
  isOpen_cellV f (by norm_num)

/-- The two members cover `KillX f`. -/
theorem KillU_union_KillV (f : ι → C(cellSphere n, Y)) :
    KillU f ∪ KillV f = Set.univ :=
  cellU_union_cellV f (by norm_num)

/-- The intersection of the two members is the union of the model shells. -/
theorem KillZ_eq_cellShellImg (f : ι → C(cellSphere n, Y)) :
    KillZ f = cellShellImg f (1 / 4) (1 / 2) :=
  cellU_inter_cellV f (by norm_num) (by norm_num)

/-- **The coordinate description of the shell pieces.** -/
theorem mem_KillQ (f : ι → C(cellSphere n, Y)) (i : ι) (z : KillX f) :
    z ∈ KillQ f i ↔ ∃ x : cellDisk n,
      (1 / 4 : ℝ) < ‖(x : CellVec n)‖ ∧ ‖(x : CellVec n)‖ < 1 / 2 ∧
      cellMap n Y ι f i x = z := by
  constructor
  · intro hz
    rw [KillQ, Set.mem_inter_iff] at hz
    obtain ⟨h1, h2⟩ := hz
    obtain ⟨x, hx, hxeq⟩ := (mem_cellImg (f := f)).mp h1
    refine ⟨x, ?_, mem_cellOpenBallSet.mp hx, hxeq⟩
    by_contra hcon
    exact h2 ((mem_cellBallImg (f := f)).mpr ⟨i, x, mem_cellBallSet.mpr (not_lt.mp hcon), hxeq⟩)
  · rintro ⟨x, hx1, hx2, rfl⟩
    rw [KillQ, Set.mem_inter_iff]
    refine ⟨(mem_cellImg (f := f)).mpr ⟨x, mem_cellOpenBallSet.mpr hx2, rfl⟩, fun hmem => ?_⟩
    have hle : ‖(x : CellVec n)‖ ≤ 1 / 4 :=
      (Work.Serre.CellStep.cellMap_mem_cellBallImg_iff (f := f) (by norm_num) i x).mp hmem
    linarith

/-- The shell pieces are open. -/
theorem isOpen_KillQ (f : ι → C(cellSphere n, Y)) (i : ι) : IsOpen (KillQ f i) := by
  have h : KillQ f i = cellImg f i (cellInner n ∩ cellShellSet n (1 / 4) (1 / 2)) := by
    refine Set.ext fun z => ?_
    rw [mem_KillQ f i z, mem_cellImg]
    constructor
    · rintro ⟨x, hx1, hx2, hxz⟩
      exact ⟨x, ⟨lt_trans hx2 (by norm_num), hx1, hx2⟩, hxz⟩
    · rintro ⟨x, ⟨-, hx1, hx2⟩, hxz⟩
      exact ⟨x, hx1, hx2, hxz⟩
  rw [h, cellImg]
  exact isOpen_cellMap_image (i := i) (Y := Y) (f := f)
    ((isOpen_cellInner n).inter (isOpen_cellShellSet n _ _)) Set.inter_subset_left

/-- The shell pieces are pairwise disjoint. -/
theorem disjoint_KillQ (f : ι → C(cellSphere n, Y)) {i j : ι} (hij : i ≠ j) :
    Disjoint (KillQ f i) (KillQ f j) := by
  refine Set.disjoint_left.mpr fun z hzi hzj => ?_
  obtain ⟨x, -, hx2, hxeq⟩ := (mem_KillQ f i z).mp hzi
  obtain ⟨y, -, hy2, hyeq⟩ := (mem_KillQ f j z).mp hzj
  exact Set.disjoint_left.mp
    (disjoint_cellImg (f := f) hij (cellOpenBallSet_subset_cellInner (by norm_num)))
    (show z ∈ cellImg f i (cellOpenBallSet n (1 / 2)) from
      ⟨x, mem_cellOpenBallSet.mpr hx2, hxeq⟩)
    (show z ∈ cellImg f j (cellOpenBallSet n (1 / 2)) from
      ⟨y, mem_cellOpenBallSet.mpr hy2, hyeq⟩)

/-- **The intersection of the cover is the union of the shell pieces.** -/
theorem KillZ_eq_iUnion_KillQ (f : ι → C(cellSphere n, Y)) :
    KillZ f = ⋃ i, KillQ f i := by
  rw [KillZ_eq_cellShellImg]
  refine Set.ext fun z => ?_
  rw [mem_cellShellImg]
  constructor
  · rintro ⟨i, x, hx, hxeq⟩
    exact Set.mem_iUnion.mpr ⟨i, (mem_KillQ f i z).mpr ⟨x, hx.1, hx.2, hxeq⟩⟩
  · intro hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    obtain ⟨x, hx1, hx2, hxeq⟩ := (mem_KillQ f i z).mp hi
    exact ⟨i, x, ⟨hx1, hx2⟩, hxeq⟩

end

end Work.Serre

namespace Work.Serre

noncomputable section

open Work.RatHurewicz

variable {n : ℕ} {Y : Type} [TopologicalSpace Y] {ι : Type}

/-- A point of the image of a closed model ball of radius `ρ < 1` lies in the interior of a cell. -/
theorem cellBallImg_subset_iUnion_cellInterior (f : ι → C(cellSphere n, Y)) :
    cellBallImg f (1 / 4) ⊆ ⋃ i, cellInterior n Y ι f i := by
  intro z hz
  obtain ⟨i, x, hx, rfl⟩ := (mem_cellBallImg (f := f)).mp hz
  exact Set.mem_iUnion.mpr ⟨i, ⟨x, lt_of_le_of_lt (mem_cellBallSet.mp hx) (by norm_num), rfl⟩⟩

/-- The old part of the attachment lies in the outer member of the cover. -/
theorem KillA_subset_KillU (f : ι → C(cellSphere n, Y)) : KillA f ⊆ KillU f := by
  intro z hz
  rw [KillU, cellU, Set.mem_compl_iff]
  intro hmem
  have h1 : z ∈ (⋃ i, cellInterior n Y ι f i)ᶜ := by
    rw [← range_attachIncl_eq_compl_iUnion_cellInterior]
    exact hz
  exact h1 (cellBallImg_subset_iUnion_cellInterior f hmem)

/-- The shell pieces lie in the outer member of the cover. -/
theorem KillQ_subset_KillU (f : ι → C(cellSphere n, Y)) (i : ι) :
    KillQ f i ⊆ KillU f := by
  rw [KillQ, KillU, cellU]
  exact Set.inter_subset_right

/-- The intersection of the two members of the cover lies in the outer one. -/
theorem KillZ_subset_KillU (f : ι → C(cellSphere n, Y)) : KillZ f ⊆ KillU f :=
  Set.inter_subset_left

/-- The intersection of the two members of the cover lies in the inner one. -/
theorem KillZ_subset_KillV (f : ι → C(cellSphere n, Y)) : KillZ f ⊆ KillV f :=
  Set.inter_subset_right

/-- The underlying vector of a point of the model shell, normalised. -/
noncomputable def shellDirVec (x : ↥(cellShellSet n (1 / 4) (1 / 2))) : CellVec n :=
  (‖(((x : ↥(cellShellSet n (1 / 4) (1 / 2))) : cellDisk n) : CellVec n)‖)⁻¹ •
    (((x : ↥(cellShellSet n (1 / 4) (1 / 2))) : cellDisk n) : CellVec n)

/-- The normalised vector of a point of the model shell is a unit vector. -/
theorem shellDirVec_mem (x : ↥(cellShellSet n (1 / 4) (1 / 2))) :
    shellDirVec x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1 := by
  have hpos : 0 < ‖(((x : ↥(cellShellSet n (1 / 4) (1 / 2))) : cellDisk n) : CellVec n)‖ := by
    have hx := (mem_cellShellSet.mp x.2).1
    linarith
  rw [Metric.mem_sphere, dist_zero_right]
  unfold shellDirVec
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
    inv_mul_cancel₀ (ne_of_gt hpos)]

theorem continuous_shellDirVec : Continuous (shellDirVec (n := n)) := by
  unfold shellDirVec
  have hnorm : Continuous fun x : ↥(cellShellSet n (1 / 4) (1 / 2)) =>
      ‖(((x : ↥(cellShellSet n (1 / 4) (1 / 2))) : cellDisk n) : CellVec n)‖ :=
    (continuous_norm.comp continuous_subtype_val).comp continuous_subtype_val
  have hne : ∀ x : ↥(cellShellSet n (1 / 4) (1 / 2)),
      ‖(((x : ↥(cellShellSet n (1 / 4) (1 / 2))) : cellDisk n) : CellVec n)‖ ≠ 0 := by
    intro x
    have hx := (mem_cellShellSet.mp x.2).1
    have h0 : (0 : ℝ) ≤ ‖(((x : ↥(cellShellSet n (1 / 4) (1 / 2))) : cellDisk n) : CellVec n)‖ :=
      norm_nonneg _
    linarith
  exact Continuous.smul (hnorm.inv₀ hne)
    (continuous_subtype_val.comp continuous_subtype_val)

/-- **The direction of a point of the model shell**: the point of the model sphere obtained by
normalising it. -/
noncomputable def shellDir (x : ↥(cellShellSet n (1 / 4) (1 / 2))) : cellSphere n :=
  ⟨shellDirVec x, shellDirVec_mem x⟩

/-- **The direction map is continuous.** -/
theorem continuous_shellDir : Continuous (shellDir (n := n)) :=
  Continuous.subtype_mk continuous_shellDirVec shellDirVec_mem

/-- The map from the disjoint union of the model shells to the old part, given by the attaching
maps: `(i,x) ↦ attachIncl (f i (direction x))`. -/
noncomputable def KillShellToA (f : ι → C(cellSphere n, Y)) :
    C(Σ i : ι, ↥(cellShellSet n (1 / 4) (1 / 2)), ↥(KillA f)) :=
  ⟨fun p => ⟨attachIncl n Y ι f (f p.1 (shellDir p.2)), ⟨f p.1 (shellDir p.2), rfl⟩⟩,
    Continuous.subtype_mk
      ((attachIncl n Y ι f).continuous.comp
        (continuous_sigma (fun i => (f i).continuous.comp continuous_shellDir)))
      _⟩

end

end Work.Serre
