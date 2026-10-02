import Mathlib
import Submission.Work.Serre.CellStep.Geom
import Submission.Work.StemsB.Fibrations
import Submission.Work.StemsB.hasHLP_pullback
import Submission.Work.Serre.cubeDiskHomeo

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The model geometry of a single `(n+2)`-cell

Fix `n` and the attaching data `f : ι → C(S^{n+1}, Y)`.  This file records the model subsets of the
closed model cell `cellDisk n` (the closed unit ball of `EuclideanSpace ℝ (Fin (n+2))`) in which
the per-cell computation of `Work.Serre.csrPerCell` is phrased:

* `dOpen n ρ` — the open ball of radius `ρ`;
* `dClosed n ρ` — the closed ball of radius `ρ`;
* `dSph n ρ` — the sphere of radius `ρ`;
* `dAnn n ε ρ` — the closed annulus `{ε ≤ ‖x‖ ≤ ρ}`;
* `dPunct n ρ` — the punctured open ball;
* `dPunctClosed n ρ` — the punctured closed ball.

It also records the chosen homeomorphism `cubeDiscHomeo n : I^{n+2} ≃ₜ cellDisk n` carrying the
boundary of the cube to the unit sphere (`Work.Serre.cubeDiskHomeo`, from
`Submission/Work/Serre/cubeDiskHomeo.lean`).
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

namespace Work.Serre

noncomputable section

/-- The open ball of radius `ρ` inside the model cell `cellDisk n`. -/
abbrev dOpen (n : ℕ) (ρ : ℝ) : Set (Work.RatHurewicz.cellDisk n) := cellOpenBallSet n ρ

/-- The closed ball of radius `ρ` inside the model cell `cellDisk n`. -/
abbrev dClosed (n : ℕ) (ρ : ℝ) : Set (Work.RatHurewicz.cellDisk n) := cellBallSet n ρ

/-- The sphere of radius `ρ` inside the model cell `cellDisk n`. -/
abbrev dSph (n : ℕ) (ρ : ℝ) : Set (Work.RatHurewicz.cellDisk n) :=
  {x | (x : Work.RatHurewicz.CellVec n) ∈ Metric.sphere 0 ρ}

/-- The closed annulus `{ε ≤ ‖x‖ ≤ ρ}` inside the model cell `cellDisk n`. -/
abbrev dAnn (n : ℕ) (ε ρ : ℝ) : Set (Work.RatHurewicz.cellDisk n) :=
  {x | ε ≤ ‖(x : Work.RatHurewicz.CellVec n)‖ ∧ ‖(x : Work.RatHurewicz.CellVec n)‖ ≤ ρ}

/-- The punctured open ball of radius `ρ` inside the model cell `cellDisk n`. -/
abbrev dPunct (n : ℕ) (ρ : ℝ) : Set (Work.RatHurewicz.cellDisk n) :=
  {x | x ∈ cellOpenBallSet n ρ ∧ (x : Work.RatHurewicz.CellVec n) ≠ 0}

/-- The punctured closed ball of radius `ρ` inside the model cell `cellDisk n`. -/
abbrev dPunctClosed (n : ℕ) (ρ : ℝ) : Set (Work.RatHurewicz.cellDisk n) :=
  {x | ‖(x : Work.RatHurewicz.CellVec n)‖ ≤ ρ ∧ (x : Work.RatHurewicz.CellVec n) ≠ 0}

@[simp] theorem mem_dOpen {n : ℕ} {ρ : ℝ} {x : Work.RatHurewicz.cellDisk n} :
    x ∈ dOpen n ρ ↔ ‖(x : Work.RatHurewicz.CellVec n)‖ < ρ := Iff.rfl

@[simp] theorem mem_dClosed {n : ℕ} {ρ : ℝ} {x : Work.RatHurewicz.cellDisk n} :
    x ∈ dClosed n ρ ↔ ‖(x : Work.RatHurewicz.CellVec n)‖ ≤ ρ := Iff.rfl

@[simp] theorem mem_dSph {n : ℕ} {ρ : ℝ} {x : Work.RatHurewicz.cellDisk n} :
    x ∈ dSph n ρ ↔ ‖(x : Work.RatHurewicz.CellVec n)‖ = ρ := by
  simp only [dSph, Set.mem_setOf_eq, Metric.mem_sphere, dist_zero_right]

@[simp] theorem mem_dAnn {n : ℕ} {ε ρ : ℝ} {x : Work.RatHurewicz.cellDisk n} :
    x ∈ dAnn n ε ρ ↔ ε ≤ ‖(x : Work.RatHurewicz.CellVec n)‖ ∧
      ‖(x : Work.RatHurewicz.CellVec n)‖ ≤ ρ := Iff.rfl

@[simp] theorem mem_dPunct {n : ℕ} {ρ : ℝ} {x : Work.RatHurewicz.cellDisk n} :
    x ∈ dPunct n ρ ↔ x ∈ dOpen n ρ ∧ (x : Work.RatHurewicz.CellVec n) ≠ 0 := Iff.rfl

@[simp] theorem mem_dPunctClosed {n : ℕ} {ρ : ℝ} {x : Work.RatHurewicz.cellDisk n} :
    x ∈ dPunctClosed n ρ ↔ ‖(x : Work.RatHurewicz.CellVec n)‖ ≤ ρ ∧
      (x : Work.RatHurewicz.CellVec n) ≠ 0 := Iff.rfl

theorem isClosed_dSph (n : ℕ) (ρ : ℝ) : IsClosed (dSph n ρ) :=
  Metric.isClosed_sphere.preimage continuous_subtype_val

theorem isClosed_dAnn (n : ℕ) (ε ρ : ℝ) : IsClosed (dAnn n ε ρ) :=
  (isClosed_le continuous_const (continuous_norm.comp continuous_subtype_val)).inter
    (isClosed_le (continuous_norm.comp continuous_subtype_val) continuous_const)

theorem isOpen_dOpen (n : ℕ) (ρ : ℝ) : IsOpen (dOpen n ρ) := isOpen_cellOpenBallSet n ρ

theorem dSph_subset_dClosed (n : ℕ) (ρ : ℝ) : dSph n ρ ⊆ dClosed n ρ := fun x hx => by
  rw [mem_dSph] at hx; rw [mem_dClosed]; exact le_of_eq hx

theorem dClosed_subset_dOpen {n : ℕ} {ε ρ : ℝ} (h : ε < ρ) : dClosed n ε ⊆ dOpen n ρ :=
  fun x hx => by rw [mem_dClosed] at hx; rw [mem_dOpen]; exact lt_of_le_of_lt hx h

theorem dSph_subset_dAnn (n : ℕ) (ε ρ : ℝ) (h : ε ≤ ρ) : dSph n ρ ⊆ dAnn n ε ρ := fun x hx => by
  rw [mem_dSph] at hx; rw [mem_dAnn]; exact ⟨h.trans (le_of_eq hx.symm), le_of_eq hx⟩

theorem dAnn_subset_dClosed (n : ℕ) (ε ρ : ℝ) : dAnn n ε ρ ⊆ dClosed n ρ := fun x hx => hx.2

theorem dPunct_subset_dOpen (n : ℕ) (ρ : ℝ) : dPunct n ρ ⊆ dOpen n ρ := fun x hx => hx.1

/-- A chosen homeomorphism from the cube `I^{n+2}` to the closed model cell `D^{n+2}`, carrying the
boundary of the cube to the unit sphere. -/
noncomputable def cubeDiscHomeo (n : ℕ) : Work.Stems.Cubical.IC (n+2) ≃ₜ
    Work.RatHurewicz.cellDisk n := Classical.choose (cubeDiskHomeo (n+2))

theorem cubeDiscHomeo_boundary (n : ℕ) (x : Work.Stems.Cubical.IC (n+2)) :
    x ∈ Cube.boundary (Fin (n+2)) ↔ cubeDiscHomeo n x ∈ dSph n 1 :=
  (Classical.choose_spec (cubeDiskHomeo (n+2))) x

/-- A homeomorphism of topological spaces, regarded as a continuous map. -/
def homeoToCM {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] (e : α ≃ₜ β) : C(α, β) where
  toFun := e
  continuous_toFun := e.continuous

@[simp] theorem homeoToCM_apply {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (e : α ≃ₜ β) (x : α) : homeoToCM e x = e x := rfl

/-- **The compression facts of the model cell.**  For `0 < σ < 1/2`, each of the six pairs of
concentric model subsets used by the per-cell computation is compressible in every dimension:
the larger set deformation-retracts onto the smaller one along the rays from the centre, fixing the
smaller set pointwise. -/
def CsrCompress (n : ℕ) (s : ℝ) : Prop :=
  (∀ d, Work.RatHurewicz.CompressRel ↥(dOpen n (1/2))
      {x : ↥(dOpen n (1/2)) | (x : Work.RatHurewicz.cellDisk n) ∈ dClosed n s} d) ∧
  (∀ d, Work.RatHurewicz.CompressRel ↥(dPunct n (1/2))
      {x : ↥(dPunct n (1/2)) | (x : Work.RatHurewicz.cellDisk n) ∈ dClosed n s} d) ∧
  (∀ d, Work.RatHurewicz.CompressRel ↥(dPunctClosed n s)
      {x : ↥(dPunctClosed n s) | (x : Work.RatHurewicz.cellDisk n) ∈ dSph n s} d) ∧
  (∀ d, Work.RatHurewicz.CompressRel ↥(dClosed n 1)
      {x : ↥(dClosed n 1) | (x : Work.RatHurewicz.cellDisk n) ∈ dClosed n s} d) ∧
  (∀ d, Work.RatHurewicz.CompressRel ↥(dAnn n s 1)
      {x : ↥(dAnn n s 1) | (x : Work.RatHurewicz.cellDisk n) ∈ dSph n s} d) ∧
  (∀ d, Work.RatHurewicz.CompressRel ↥(dAnn n s 1)
      {x : ↥(dAnn n s 1) | (x : Work.RatHurewicz.cellDisk n) ∈ dSph n 1} d)


section Pullback

variable {n : ℕ} {Y : Type} [TopologicalSpace Y] {ι : Type}

/-- The pullback of `q` along the characteristic map of the `i`-th `(n+2)`-cell: the total space of
the fibration restricted to the cell. -/
abbrev csrPull (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.RatHurewicz.attachCells n Y ι f)) (i : ι) : Type :=
  Work.StemsB.Pullback q (Work.RatHurewicz.cellMap n Y ι f i)

/-- The preimage in `csrPull f q i` of a subset of the model cell. -/
abbrev pPre (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.RatHurewicz.attachCells n Y ι f)) (i : ι) (S : Set (Work.RatHurewicz.cellDisk n)) :
    Set (csrPull f q i) :=
  {x | Work.StemsB.pullbackSnd q (Work.RatHurewicz.cellMap n Y ι f i) x ∈ S}

@[simp] theorem mem_pPre (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.RatHurewicz.attachCells n Y ι f)) (i : ι) (S : Set (Work.RatHurewicz.cellDisk n))
    (x : csrPull f q i) :
    x ∈ pPre f q i S ↔ Work.StemsB.pullbackSnd q (Work.RatHurewicz.cellMap n Y ι f i) x ∈ S :=
  Iff.rfl

/-- **The pullback of a Serre fibration along the characteristic map is a Serre fibration.** -/
theorem csrPull_serre (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.RatHurewicz.attachCells n Y ι f)) (hq : Work.StemsB.IsSerreFibration q) (i : ι) :
    Work.StemsB.IsSerreFibration
      (Work.StemsB.pullbackSnd q (Work.RatHurewicz.cellMap n Y ι f i)) :=
  fun d => Work.StemsB.hasHLP_pullback q (Work.RatHurewicz.cellMap n Y ι f i) (hq d)

end Pullback

end

end Work.Serre
