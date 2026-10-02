import Mathlib
import Submission.Work.RatHurewicz.AttachCells
import Submission.Work.RatHurewicz.AttachPush.PushOff
import Submission.Work.RatHurewicz.ExcisionSetup
import Submission.Work.RatHurewicz.compressRel_attachCells_range
import Submission.Work.Serre.AttachCompress.Chart
import Submission.Work.Cohomology.localHomology

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The geometry of a single cell attachment: balls, complements and the cover

For the cell step `Work.Serre.cellStep` we need the following geometric data on the space
`Γ' = attachCells n Γ ι f` (cells of dimension `n + 2`):

* `cellBallSet ρ`, `cellOpenBallSet ρ`, `cellShellSet ρ R` — the model closed ball, open ball and
  open shell inside the model cell `D^{n+2}`;
* `cellBallImg f ρ`, `cellOpenBallImg f R`, `cellShellImg f ρ R` — the unions of their images under
  the characteristic maps;
* `cellU f ρ = (cellBallImg f ρ)ᶜ` (the "old part", disjoint from the small closed balls) and
  `cellV f R = cellOpenBallImg f R` (the union of the larger open balls).

For `0 ≤ ρ < R ≤ 1` these satisfy: `U` and `V` are open, `U ∪ V = Γ'`, `U ∩ V = cellShellImg ρ R`
and the pieces `χᵢ '' (open ball R)` are pairwise disjoint.  For `ρ = 0` (`U` the complement of the
cell centres) the pair `(U, range attachIncl)` has the compression property in every dimension,
witnessed by the radial push-off from the cell centres.
-/

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

noncomputable section

open Work.RatHurewicz Work.RatHurewicz.AttachRange
open Work.Serre.AttachCompress

variable {n : ℕ} {Γ : Type} [TopologicalSpace Γ] {ι : Type} (f : ι → C(cellSphere n, Γ))

/-- The closed model ball of radius `ρ` inside the model cell `D^{n+2}`. -/
def cellBallSet (n : ℕ) (ρ : ℝ) : Set (cellDisk n) := {x | ‖(x : CellVec n)‖ ≤ ρ}

/-- The open model ball of radius `ρ` inside the model cell `D^{n+2}`. -/
def cellOpenBallSet (n : ℕ) (ρ : ℝ) : Set (cellDisk n) := {x | ‖(x : CellVec n)‖ < ρ}

/-- The open model shell `{ρ < ‖x‖ < R}` inside the model cell `D^{n+2}`. -/
def cellShellSet (n : ℕ) (ρ R : ℝ) : Set (cellDisk n) :=
  {x | ρ < ‖(x : CellVec n)‖ ∧ ‖(x : CellVec n)‖ < R}

@[simp] theorem mem_cellBallSet {n : ℕ} {ρ : ℝ} {x : cellDisk n} :
    x ∈ cellBallSet n ρ ↔ ‖(x : CellVec n)‖ ≤ ρ := Iff.rfl

@[simp] theorem mem_cellOpenBallSet {n : ℕ} {ρ : ℝ} {x : cellDisk n} :
    x ∈ cellOpenBallSet n ρ ↔ ‖(x : CellVec n)‖ < ρ := Iff.rfl

@[simp] theorem mem_cellShellSet {n : ℕ} {ρ R : ℝ} {x : cellDisk n} :
    x ∈ cellShellSet n ρ R ↔ ρ < ‖(x : CellVec n)‖ ∧ ‖(x : CellVec n)‖ < R := Iff.rfl

theorem cellBallSet_zero {n : ℕ} : cellBallSet n 0 = {cellDiskCentre n} := by
  ext x
  simp only [mem_cellBallSet, Set.mem_singleton_iff]
  constructor
  · intro h
    exact Subtype.ext (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))
  · rintro rfl
    simp

theorem cellOpenBallSet_subset_cellInner {n : ℕ} {ρ : ℝ} (hρ : ρ ≤ 1) :
    cellOpenBallSet n ρ ⊆ cellInner n := fun _ hx => lt_of_lt_of_le hx hρ

theorem cellShellSet_subset_cellInner {n : ℕ} {ρ R : ℝ} (hR : R ≤ 1) :
    cellShellSet n ρ R ⊆ cellInner n := fun _ hx => lt_of_lt_of_le hx.2 hR

theorem isClosed_cellBallSet (n : ℕ) (ρ : ℝ) : IsClosed (cellBallSet n ρ) :=
  isClosed_le (continuous_norm.comp continuous_subtype_val) continuous_const

theorem isOpen_cellOpenBallSet (n : ℕ) (ρ : ℝ) : IsOpen (cellOpenBallSet n ρ) :=
  isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const

theorem isOpen_cellShellSet (n : ℕ) (ρ R : ℝ) : IsOpen (cellShellSet n ρ R) :=
  (isOpen_lt continuous_const (continuous_norm.comp continuous_subtype_val)).inter
    (isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const)

/-- The image of a subset of the model cell under the characteristic map of the `i`-th cell. -/
def cellImg (i : ι) (S : Set (cellDisk n)) : Set (attachCells n Γ ι f) :=
  cellMap n Γ ι f i '' S

/-- The union of the images of the closed model balls of radius `ρ`. -/
def cellBallImg (ρ : ℝ) : Set (attachCells n Γ ι f) := ⋃ i, cellImg f i (cellBallSet n ρ)

/-- The union of the images of the open model balls of radius `ρ`. -/
def cellOpenBallImg (ρ : ℝ) : Set (attachCells n Γ ι f) :=
  ⋃ i, cellImg f i (cellOpenBallSet n ρ)

/-- The union of the images of the model shells `{ρ < ‖x‖ < R}`. -/
def cellShellImg (ρ R : ℝ) : Set (attachCells n Γ ι f) :=
  ⋃ i, cellImg f i (cellShellSet n ρ R)

/-- The complement of the union of the closed balls of radius `ρ`: the "old part" of the cover. -/
def cellU (ρ : ℝ) : Set (attachCells n Γ ι f) := (cellBallImg f ρ)ᶜ

/-- The union of the open balls of radius `R`: the "new part" of the cover. -/
def cellV (R : ℝ) : Set (attachCells n Γ ι f) := cellOpenBallImg f R

theorem mem_cellImg {i : ι} {S : Set (cellDisk n)} {z : attachCells n Γ ι f} :
    z ∈ cellImg f i S ↔ ∃ x ∈ S, cellMap n Γ ι f i x = z := Iff.rfl

theorem mem_cellBallImg {ρ : ℝ} {z : attachCells n Γ ι f} :
    z ∈ cellBallImg f ρ ↔
      ∃ (i : ι) (x : cellDisk n), x ∈ cellBallSet n ρ ∧ cellMap n Γ ι f i x = z := by
  simp only [cellBallImg, Set.mem_iUnion, mem_cellImg]

theorem mem_cellOpenBallImg {ρ : ℝ} {z : attachCells n Γ ι f} :
    z ∈ cellOpenBallImg f ρ ↔
      ∃ (i : ι) (x : cellDisk n), x ∈ cellOpenBallSet n ρ ∧ cellMap n Γ ι f i x = z := by
  simp only [cellOpenBallImg, Set.mem_iUnion, mem_cellImg]

theorem mem_cellShellImg {ρ R : ℝ} {z : attachCells n Γ ι f} :
    z ∈ cellShellImg f ρ R ↔
      ∃ (i : ι) (x : cellDisk n), x ∈ cellShellSet n ρ R ∧ cellMap n Γ ι f i x = z := by
  simp only [cellShellImg, Set.mem_iUnion, mem_cellImg]

theorem cellBallImg_subset_cellOpenBallImg {ρ R : ℝ} (h : ρ < R) :
    cellBallImg f ρ ⊆ cellOpenBallImg f R := by
  intro z hz
  obtain ⟨i, x, hx, rfl⟩ := (mem_cellBallImg f).mp hz
  exact (mem_cellOpenBallImg f).mpr ⟨i, x, lt_of_le_of_lt hx h, rfl⟩

theorem cellShellImg_subset_cellOpenBallImg {ρ R : ℝ} (h : ρ < R) :
    cellShellImg f ρ R ⊆ cellOpenBallImg f R := by
  intro z hz
  obtain ⟨i, x, hx, rfl⟩ := (mem_cellShellImg f).mp hz
  exact (mem_cellOpenBallImg f).mpr ⟨i, x, hx.2, rfl⟩

theorem disjoint_cellImg {i j : ι} (hij : i ≠ j) {S : Set (cellDisk n)}
    (hS : S ⊆ cellInner n) : Disjoint (cellImg f i S) (cellImg f j S) := by
  rw [Set.disjoint_left]
  rintro z ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
  have hrel : Relation.EqvGen (attachRel n Γ ι f) (Sum.inr ⟨j, y⟩) (Sum.inr ⟨i, x⟩) :=
    Quotient.exact (show (Quotient.mk'' (Sum.inr (⟨j, y⟩ : Σ _ : ι, cellDisk n)) :
      attachCells n Γ ι f) = Quotient.mk'' (Sum.inr (⟨i, x⟩ : Σ _ : ι, cellDisk n)) from hxy)
  exact hij ((cls_inner_inj f (hS hy) (hS hx) (eqvGen_le_cls n Γ ι f hrel)).1).symm

theorem cellImg_subset_iUnion_cellInterior {S : Set (cellDisk n)} (hS : S ⊆ cellInner n) (i : ι) :
    cellImg f i S ⊆ ⋃ j, cellInterior n Γ ι f j := by
  rintro z ⟨x, hx, rfl⟩
  exact Set.mem_iUnion.mpr ⟨i, x, hS hx, rfl⟩

/-- The images of the open model balls are pairwise disjoint. -/
theorem disjoint_cellOpenBallImg {R : ℝ} (hR : R ≤ 1) {i j : ι} (hij : i ≠ j) :
    Disjoint (cellImg f i (cellOpenBallSet n R)) (cellImg f j (cellOpenBallSet n R)) :=
  disjoint_cellImg f hij (cellOpenBallSet_subset_cellInner hR)

theorem disjoint_cellBallImg_range {ρ : ℝ} (hρ : ρ < 1) :
    Disjoint (cellBallImg f ρ) (Set.range (attachIncl n Γ ι f)) := by
  rw [Set.disjoint_left]
  rintro z hz hzr
  obtain ⟨i, x, hx, rfl⟩ := (mem_cellBallImg f).mp hz
  have hmem : cellMap n Γ ι f i x ∈ ⋃ j, cellInterior n Γ ι f j :=
    cellImg_subset_iUnion_cellInterior f (cellOpenBallSet_subset_cellInner le_rfl) i
      (show cellMap n Γ ι f i x ∈ cellImg f i (cellOpenBallSet n 1) from
        ⟨x, lt_of_le_of_lt hx hρ, rfl⟩)
  have hpart := (cellPartition n Γ ι f).1
  rw [hpart] at hzr
  exact hzr hmem

/-- **The image of an open model ball is open** (for radius at most `1`). -/
theorem isOpen_cellOpenBallImg {R : ℝ} (hR : R ≤ 1) : IsOpen (cellOpenBallImg f R) :=
  isOpen_iUnion fun i =>
    isOpen_image_of_open_inner f i (isOpen_cellOpenBallSet n R)
      (cellOpenBallSet_subset_cellInner hR)

/-- **The image of a closed model ball is closed** (for radius less than `1`). -/
theorem isClosed_cellBallImg {ρ : ℝ} (hρ : ρ < 1) : IsClosed (cellBallImg f ρ) := by
  have hq : Topology.IsCoinducing (Quotient.mk'' :
      (Γ ⊕ (Σ _ : ι, cellDisk n)) → attachCells n Γ ι f) :=
    (isQuotientMap_quotient_mk' (X := Γ ⊕ (Σ _ : ι, cellDisk n))
      (s := Relation.EqvGen.setoid (attachRel n Γ ι f))).isCoinducing
  have hpre : (Quotient.mk'' ⁻¹' cellBallImg f ρ : Set (Γ ⊕ (Σ _ : ι, cellDisk n))) =
      {a | ∃ (i : ι) (x : cellDisk n), a = Sum.inr ⟨i, x⟩ ∧ x ∈ cellBallSet n ρ} := by
    ext a
    constructor
    · intro ha
      obtain ⟨i, x, hx, hxq⟩ := Set.mem_iUnion.mp ha
      have hrel : Relation.EqvGen (attachRel n Γ ι f) (Sum.inr ⟨i, x⟩) a :=
        Quotient.exact (show (Quotient.mk'' (Sum.inr (⟨i, x⟩ : Σ _ : ι, cellDisk n)) :
          attachCells n Γ ι f) = Quotient.mk'' a from hxq)
      rcases eqvGen_le_cls n Γ ι f hrel with h | ⟨y, h1, h2⟩
      · exact ⟨i, x, h.symm, hx⟩
      · rcases h1 with h1 | ⟨i', z, h1, -⟩
        · exact absurd h1 Sum.inr_ne_inl
        · exfalso
          have h3 : x = cellSphereToDisk n z := congrArg Sigma.snd (Sum.inr.inj h1)
          have h4 : ‖(x : CellVec n)‖ = 1 := by rw [h3]; exact norm_cellSphereToDisk n z
          exact absurd h4 (ne_of_lt (lt_of_le_of_lt hx hρ))
    · rintro ⟨i, x, rfl, hx⟩
      exact Set.mem_iUnion.mpr ⟨i, x, hx, rfl⟩
  refine (hq.isClosed_preimage (s := cellBallImg f ρ)).1 ?_
  rw [hpre]
  rw [isClosed_sum_iff]
  constructor
  · have h0 : Sum.inl ⁻¹' {a : Γ ⊕ (Σ _ : ι, cellDisk n) |
        ∃ (i : ι) (x : cellDisk n), a = Sum.inr ⟨i, x⟩ ∧ x ∈ cellBallSet n ρ} = ∅ := by
      ext y; simp
    rw [h0]; exact isClosed_empty
  · rw [isClosed_sigma_iff]
    intro j
    have h1 : Sigma.mk j ⁻¹' Sum.inr ⁻¹'
        {a : Γ ⊕ (Σ _ : ι, cellDisk n) |
          ∃ (i : ι) (x : cellDisk n), a = Sum.inr ⟨i, x⟩ ∧ x ∈ cellBallSet n ρ} =
        cellBallSet n ρ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_setOf_eq]
      constructor
      · rintro ⟨i, x', heq, hx'⟩
        have h2 : (⟨j, x⟩ : Σ _ : ι, cellDisk n) = ⟨i, x'⟩ := Sum.inr.inj heq
        have h3 : j = i := congrArg Sigma.fst h2
        subst h3
        have h4 : x = x' := congrArg Sigma.snd h2
        rwa [h4]
      · intro hx
        exact ⟨j, x, rfl, hx⟩
    rw [h1]
    exact isClosed_cellBallSet n ρ

/-- **`U` is open**: the complement of the images of the closed model balls. -/
theorem isOpen_cellU {ρ : ℝ} (hρ : ρ < 1) : IsOpen (cellU f ρ) :=
  (isClosed_cellBallImg f hρ).isOpen_compl

/-- **`V` is open**: the union of the images of the open model balls. -/
theorem isOpen_cellV {R : ℝ} (hR : R ≤ 1) : IsOpen (cellV f R) :=
  isOpen_cellOpenBallImg f hR

/-- The cover: `U ∪ V = Γ'` (for `ρ < R`). -/
theorem cellU_union_cellV {ρ R : ℝ} (hρR : ρ < R) :
    cellU f ρ ∪ cellV f R = Set.univ := by
  ext z
  constructor
  · intro _; trivial
  · intro _
    by_cases hz : z ∈ cellBallImg f ρ
    · right
      exact cellBallImg_subset_cellOpenBallImg f hρR hz
    · left
      exact hz

/-- The pieces of the cover meet in the shell: `U ∩ V = cellShellImg ρ R` (for `R ≤ 1`). -/
theorem cellU_inter_cellV {ρ R : ℝ} (hR : R ≤ 1) (hρR : ρ < R) :
    cellU f ρ ∩ cellV f R = cellShellImg f ρ R := by
  ext z
  constructor
  · rintro ⟨hzU, hzV⟩
    obtain ⟨i, x, hx, rfl⟩ := (mem_cellOpenBallImg f).mp hzV
    refine (mem_cellShellImg f).mpr ⟨i, x, ⟨?_, hx⟩, rfl⟩
    by_contra hcon
    rw [not_lt] at hcon
    exact hzU ((mem_cellBallImg f).mpr ⟨i, x, hcon, rfl⟩)
  · intro hz
    obtain ⟨i, x, ⟨hx1, hx2⟩, rfl⟩ := (mem_cellShellImg f).mp hz
    refine ⟨?_, (mem_cellOpenBallImg f).mpr ⟨i, x, hx2, rfl⟩⟩
    intro hb
    obtain ⟨j, y, hy, hxy⟩ := (mem_cellBallImg f).mp hb
    have hrel : Relation.EqvGen (attachRel n Γ ι f) (Sum.inr ⟨j, y⟩) (Sum.inr ⟨i, x⟩) :=
      Quotient.exact (show (Quotient.mk'' (Sum.inr (⟨j, y⟩ : Σ _ : ι, cellDisk n)) :
        attachCells n Γ ι f) =
        Quotient.mk'' (Sum.inr (⟨i, x⟩ : Σ _ : ι, cellDisk n)) from hxy)
    have hyR : y ∈ cellOpenBallSet n R := lt_of_le_of_lt hy hρR
    have hinj := cls_inner_inj f
      (cellOpenBallSet_subset_cellInner hR hyR)
      (cellShellSet_subset_cellInner hR ⟨hx1, hx2⟩)
      (eqvGen_le_cls n Γ ι f hrel)
    have : y = x := hinj.2
    rw [this] at hy
    exact absurd hx1 (not_lt.mpr hy)

end

end Work.Serre
