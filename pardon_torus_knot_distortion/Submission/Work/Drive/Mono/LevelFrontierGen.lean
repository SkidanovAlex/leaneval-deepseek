import Mathlib
import Submission.Work.Drive.Mono.TiltedTraceData

/-!
# The genericity conditions of the level frontier of the tilted sweep

`Work.Drive.Mono.LevelFrontierGen` collects the three genericity conditions which the (proved)
brick `Work.Drive.Mono.tiltedLevel_disjoint_spheres` — "the frontier of a level is a finite disjoint
union of embedded spheres" — needs on the data, at every level of the window outside the exceptional
set `exc`:

* the wall `{ℓ = lam}` contains no edge of the box (if `lam` is the `ℓ`-value of a point of an edge
  in the `σ i` direction, then `ℓ` is non-constant along that direction);
* the wall passes through no vertex of the box;
* the wall is not tangent to the two face seams on the box sphere nor to the top of the strip
  (the `hseam` clauses of the brick, whose witnesses range over the **closed** box: over the open box
  they would be vacuous, since `ℓ v = 0` and `ℓ ≠ 0` allow one to move inside the box along `v^⊥`
  and increase `ℓ`).

This module is *low* (it imports only the definitions of the tilted sweep), so that statements
*about* `LevelFrontierGen` — in particular the existence of `exc`
(`Work.Drive.Mono.exists_levelFrontierGen`) and the derivation of the geometric input of clause 1
(`Work.Drive.Mono.levelSphereDecomposition_of_levelFrontierGen`, in the deliverable's file) — live in
modules which the deliverable's file can import.
-/

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

/-- **The genericity conditions of the brick `Work.Drive.Mono.tiltedLevel_disjoint_spheres` at every
non-exceptional level of the window**: the wall contains no edge of the box, passes through no vertex
of the box, and is tangent to none of the face seams (`hseam`, whose witnesses range over the *closed*
box).  All three hold at all but finitely many levels, so they are part of the choice of the data and
the finitely many levels are in `exc`. -/
def LevelFrontierGen (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) (v : R3) (h : ℝ)
    (ℓ : R3 →L[ℝ] ℝ) (exc : Finset ℝ) (lam0 lam1 : ℝ) : Prop :=
  ∀ lam ∈ Set.Icc lam0 lam1, lam ∉ (exc : Set ℝ) →
    (∀ (i : Fin 3) (ε : Fin 3 → Bool),
      lam = ℓ (WithLp.toLp 2 (fun k : Fin 3 => c k +
        (if k = σ i then (0:ℝ) else
          (if ε (σ.symm k) then 1 else -1) * Submission.boxSide (σ.symm k) * s))) →
      ℓ (EuclideanSpace.single (σ i) (1 : ℝ)) ≠ 0) ∧
    (∀ ε : Fin 3 → Bool,
      lam ≠ ℓ (WithLp.toLp 2 (fun j : Fin 3 => c j +
        (if ε (σ.symm j) then 1 else -1) * Submission.boxSide (σ.symm j) * s))) ∧
    (((∃ y ∈ closure (Submission.PBox s c σ),
          inner ℝ v y = inner ℝ v c + u + h ∧ ℓ y = lam) →
        (∃ z ∈ Submission.PBox s c σ,
          inner ℝ v z = inner ℝ v c + u + h ∧ lam < ℓ z)) ∧
      ((∃ y ∈ closure (Submission.PBox s c σ),
          inner ℝ v y = inner ℝ v c + u - h ∧ ℓ y = lam) →
        (∃ z ∈ Submission.PBox s c σ,
          inner ℝ v z = inner ℝ v c + u - h ∧ lam < ℓ z)) ∧
      ((∃ y ∈ closure (Submission.PBox s c σ),
          |inner ℝ v y - (inner ℝ v c + u)| ≤ h ∧ ℓ y = lam) →
        (∃ z ∈ Submission.PBox s c σ,
          |inner ℝ v z - (inner ℝ v c + u)| ≤ h ∧ lam < ℓ z)))

end

end Work.Drive.Mono
