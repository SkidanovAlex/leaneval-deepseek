import Mathlib
import Submission.Work.StemsB.SphLoopBallGeom

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The standard hemispheres of `S^n`

The decomposition of the sphere `S^n` used by the transgression computation of
`Work.StemsB.SphLoopHomologyVanishes`: the closed upper hemisphere `upperHemi n`, the closed lower
hemisphere `lowerHemi n` (they cover `S^n` and meet in the equator `equatorHemi n`, a sphere of
dimension `n-1`), the north pole `eLast n` (the base point of the standard picture) and the south
pole `southPole n`.
-/

set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.StemsB

noncomputable section

/-- The unit sphere `S^n ⊆ ℝ^{n+1}` as a type (a local copy, definitionally equal to
`Work.StemsB.Sph`; kept here so that this module needs no import beyond the geometry of the
standard ball). -/
abbrev SphH (n : ℕ) : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

/-- The **north pole** `e_n` of `S^n`, as a point of the sphere. -/
def eLast (n : ℕ) : SphH n := ⟨npole n, by rw [Metric.mem_sphere, dist_zero_right]; exact norm_npole n⟩

/-- The **south pole** `-e_n` of `S^n`, as a point of the sphere. -/
def southPole (n : ℕ) : SphH n := ⟨spole n, by rw [Metric.mem_sphere, dist_zero_right]; exact norm_spole n⟩

@[simp] theorem coe_eLast (n : ℕ) : ((eLast n : SphH n) : EuclideanSpace ℝ (Fin (n+1))) = npole n := rfl

@[simp] theorem coe_southPole (n : ℕ) :
    ((southPole n : SphH n) : EuclideanSpace ℝ (Fin (n+1))) = spole n := rfl

theorem lastCoord_eLast (n : ℕ) : lastCoord n (eLast n) = 1 := by
  simp [lastCoord, eLast, npole_ofLp, Fin.last]

theorem lastCoord_southPole (n : ℕ) : lastCoord n (southPole n) = -1 := by
  simp [lastCoord, southPole, spole, npole_ofLp, Fin.last]

/-- The closed **upper hemisphere** `{x : 0 ≤ x_n}`. -/
def upperHemi (n : ℕ) : Set (SphH n) := {x | 0 ≤ lastCoord n x}

/-- The closed **lower hemisphere** `{x : x_n ≤ 0}`. -/
def lowerHemi (n : ℕ) : Set (SphH n) := {x | lastCoord n x ≤ 0}

/-- The **equator** `{x : x_n = 0}`. -/
def equatorHemi (n : ℕ) : Set (SphH n) := {x | lastCoord n x = 0}

@[simp] theorem mem_upperHemi {n : ℕ} {x : SphH n} : x ∈ upperHemi n ↔ 0 ≤ lastCoord n x := Iff.rfl

@[simp] theorem mem_lowerHemi {n : ℕ} {x : SphH n} : x ∈ lowerHemi n ↔ lastCoord n x ≤ 0 := Iff.rfl

@[simp] theorem mem_equatorHemi {n : ℕ} {x : SphH n} : x ∈ equatorHemi n ↔ lastCoord n x = 0 := Iff.rfl

theorem eLast_mem_upperHemi (n : ℕ) : eLast n ∈ upperHemi n := by
  rw [mem_upperHemi, lastCoord_eLast]; norm_num

theorem southPole_mem_lowerHemi (n : ℕ) : southPole n ∈ lowerHemi n := by
  rw [mem_lowerHemi, lastCoord_southPole]; norm_num

theorem eLast_notMem_lowerHemi (n : ℕ) : eLast n ∉ lowerHemi n := by
  rw [mem_lowerHemi, lastCoord_eLast]; norm_num

theorem southPole_notMem_upperHemi (n : ℕ) : southPole n ∉ upperHemi n := by
  rw [mem_upperHemi, lastCoord_southPole]; norm_num

theorem equatorHemi_subset_upperHemi (n : ℕ) : equatorHemi n ⊆ upperHemi n := by
  intro x hx; rw [mem_upperHemi]; rw [mem_equatorHemi] at hx; linarith

theorem equatorHemi_subset_lowerHemi (n : ℕ) : equatorHemi n ⊆ lowerHemi n := by
  intro x hx; rw [mem_lowerHemi]; rw [mem_equatorHemi] at hx; linarith

theorem union_upperHemi_lowerHemi (n : ℕ) : upperHemi n ∪ lowerHemi n = Set.univ := by
  ext x; simp only [Set.mem_union, Set.mem_univ, iff_true]
  rcases le_total (lastCoord n x) 0 with h | h
  · exact Or.inr h
  · exact Or.inl h

theorem inter_upperHemi_lowerHemi (n : ℕ) :
    upperHemi n ∩ lowerHemi n = equatorHemi n := by
  ext x; constructor
  · intro hx
    simp only [Set.mem_inter_iff, mem_upperHemi, mem_lowerHemi] at hx
    simp only [mem_equatorHemi]
    linarith [hx.1, hx.2]
  · intro hx
    simp only [mem_equatorHemi] at hx
    refine Set.mem_inter ?_ ?_
    · simp only [mem_upperHemi]; linarith
    · simp only [mem_lowerHemi]; linarith

/-- The upper level set `{a ≤ x_n}` of the sphere. -/
def upperLevel (n : ℕ) (a : ℝ) : Set (SphH n) := {x | a ≤ lastCoord n x}

/-- The strict lower level set `{x_n < b}` of the sphere. -/
def lowerLevelStrict (n : ℕ) (b : ℝ) : Set (SphH n) := {x | lastCoord n x < b}

/-- The strict upper level set `{a < x_n}` of the sphere. -/
def upperLevelStrict (n : ℕ) (a : ℝ) : Set (SphH n) := {x | a < lastCoord n x}

/-- The level sphere `{x_n = a}`. -/
def levelSphere (n : ℕ) (a : ℝ) : Set (SphH n) := {x | lastCoord n x = a}

/-- The closed southern cap `{x_n ≤ b}`. -/
def southLevel (n : ℕ) (b : ℝ) : Set (SphH n) := {x | lastCoord n x ≤ b}

@[simp] theorem mem_southLevel {n : ℕ} {b : ℝ} {x : SphH n} :
    x ∈ southLevel n b ↔ lastCoord n x ≤ b := Iff.rfl

@[simp] theorem mem_upperLevel {n : ℕ} {a : ℝ} {x : SphH n} :
    x ∈ upperLevel n a ↔ a ≤ lastCoord n x := Iff.rfl

@[simp] theorem mem_lowerLevelStrict {n : ℕ} {b : ℝ} {x : SphH n} :
    x ∈ lowerLevelStrict n b ↔ lastCoord n x < b := Iff.rfl

@[simp] theorem mem_upperLevelStrict {n : ℕ} {a : ℝ} {x : SphH n} :
    x ∈ upperLevelStrict n a ↔ a < lastCoord n x := Iff.rfl

@[simp] theorem mem_levelSphere {n : ℕ} {a : ℝ} {x : SphH n} :
    x ∈ levelSphere n a ↔ lastCoord n x = a := Iff.rfl

theorem eLast_mem_upperLevel (n : ℕ) (a : ℝ) (ha : a ≤ 1) : eLast n ∈ upperLevel n a := by
  rw [mem_upperLevel, lastCoord_eLast]; exact ha

theorem eLast_mem_upperLevelStrict (n : ℕ) (a : ℝ) (ha : a < 1) :
    eLast n ∈ upperLevelStrict n a := by
  rw [mem_upperLevelStrict, lastCoord_eLast]; exact ha

theorem southPole_mem_lowerLevelStrict (n : ℕ) (b : ℝ) (hb : -1 < b) :
    southPole n ∈ lowerLevelStrict n b := by
  rw [mem_lowerLevelStrict, lastCoord_southPole]; exact hb

theorem southPole_mem_upperLevel (n : ℕ) (a : ℝ) (ha : a ≤ -1) : southPole n ∈ upperLevel n a := by
  rw [mem_upperLevel, lastCoord_southPole]; exact ha

theorem isClosed_upperHemi (n : ℕ) : IsClosed (upperHemi n) :=
  isClosed_le continuous_const ((continuous_lastCoord n).comp continuous_subtype_val)

theorem isClosed_lowerHemi (n : ℕ) : IsClosed (lowerHemi n) :=
  isClosed_le ((continuous_lastCoord n).comp continuous_subtype_val) continuous_const

theorem isClosed_equatorHemi (n : ℕ) : IsClosed (equatorHemi n) :=
  isClosed_eq ((continuous_lastCoord n).comp continuous_subtype_val) continuous_const

/-- The last coordinate of a unit vector is at most `1` in absolute value. -/
theorem abs_lastCoord_le_one (n : ℕ) (x : SphH n) : |lastCoord n x| ≤ 1 := by
  have hx : ‖((x : SphH n) : EuclideanSpace ℝ (Fin (n+1)))‖ = 1 := by
    simpa using x.2
  calc |lastCoord n x| = |inner ℝ (x : EuclideanSpace ℝ (Fin (n+1))) (npole n)| := by
        rw [inner_npole]
    _ ≤ ‖(x : EuclideanSpace ℝ (Fin (n+1)))‖ * ‖npole n‖ := abs_real_inner_le_norm _ _
    _ = 1 := by rw [hx, norm_npole, one_mul]

end

end Work.StemsB
