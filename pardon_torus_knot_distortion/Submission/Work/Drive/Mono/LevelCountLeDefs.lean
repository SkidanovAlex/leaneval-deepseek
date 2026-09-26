import Mathlib
import Submission.Work.Drive.Mono.LevelCountDefs

/-!
# The level's face parameters at or *below* the level

`Work.Drive.Mono.facePts` collects the parameters of the knot which lie in the open box and on a
*face* of the tilted slab, strictly below the level: `{|⟪v,·⟫ - a| = h ∧ ℓ < lam}`.  For the level
count at an *arbitrary* level of the sweep (in particular at an exceptional level, where a
box-and-slab visit of the knot may reach the corner `{|⟪v,·⟫ - a| = h ∧ ℓ = lam}`) one replaces
the strict inequality by `ℓ ≤ lam`.  This is the content of `facePtsLe`; the corner point is then a
face parameter of the level, so the visit count of `facePtsLe ∪ wallPts` is still at most two per
visit (the wall point and at most one of the two endpoints of the visit can be at height `≤ lam`).

The definitions and elementary periodicity lemmas live here so that the visit lemmas
(`Submission.Work.Drive.Mono.visit_facts_le`, `Submission.Work.Drive.Mono.visit_cover_le`) and the
hero statement (`Submission.Work.Drive.Mono.levelCount_lt_min_all`) can share them.
-/

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

variable {K : Knot} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} {v : R3} {h : ℝ}
variable {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ}

/-- The **level face parameters at or below the level**: the knot in the open box, on a face of the
tilted slab, at height `≤ lam`.  This is `Work.Drive.Mono.facePts` with the strict inequality
`ℓ < lam` relaxed to `ℓ ≤ lam`, so that it also contains the corner points `{|⟪v,·⟫ - a| = h ∧
ℓ = lam}` of the level. -/
def facePtsLe (K : Knot) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) (v : R3) (h : ℝ)
    (ℓ : R3 →L[ℝ] ℝ) (lam : ℝ) : Set ℝ :=
  {t : ℝ | boxA K s c σ t < 0 ∧ |cutG K c u v t| = h ∧ wallW K ℓ t ≤ lam}

theorem facePts_subset_facePtsLe :
    facePts K s c σ u v h ℓ lam ⊆ facePtsLe K s c σ u v h ℓ lam := by
  intro t ht
  exact ⟨ht.1, ht.2.1, le_of_lt ht.2.2⟩

theorem facePtsLe_periodic (t : ℝ) :
    (t + 2 * Real.pi ∈ facePtsLe K s c σ u v h ℓ lam ↔
      t ∈ facePtsLe K s c σ u v h ℓ lam) := by
  simp only [facePtsLe, Set.mem_ofPred_eq]
  rw [periodic_boxA, periodic_cutG, periodic_wallW]

theorem facePtsLe_union_wallPts_periodic (t : ℝ) :
    (t + 2 * Real.pi ∈ facePtsLe K s c σ u v h ℓ lam ∪ wallPts K s c σ u v h ℓ lam ↔
      t ∈ facePtsLe K s c σ u v h ℓ lam ∪ wallPts K s c σ u v h ℓ lam) := by
  rw [Set.mem_union, Set.mem_union, facePtsLe_periodic, wallPts_periodic]

end

end Work.Drive.Mono
