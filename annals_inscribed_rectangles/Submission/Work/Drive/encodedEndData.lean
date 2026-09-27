import Mathlib
import Submission.Work.Drive.projCharted
import Submission.Work.Drive.projTimesLine
import Submission.Work.Drive.classTripleRegular

/-!
# The stage-1 regularity vocabulary of the ends clause (`NOTES_LEAD_hodd_blockT6.md` §1)

`Work.Drive.PairReg A B` and `Work.Drive.EndTripleReg F A B` are the *class-level* regularity
conditions of the ends-clause design: they are asked over **all** of `ℝ²` (the richness of the
`localSard` family is demanded at every zero in every compact `K`), so the rank clauses automatically
exclude the fold corners, the collapsed disc (`CHART_DEGENERACY.md`) and the folded end triples.

The definitions are those of the project lead's note; the vocabulary is used by

* `exists_homotopy_meet3Hyp_encoded` (`encodedGeneric.lean`, §2.1) — the per-clause genericity,
* `hasClassLinearization_of_endData` (§2.5) — the assembly,
* `endTripleReg_of_meet3Hyp_sweeps` / `pairReg_of_loopBoxData` — the producers from the design's data.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology

noncomputable section

set_option backward.isDefEq.respectTransparency false

attribute [local instance] Work.Drive.projCharted

/-- **The pair regularity of two class maps**: at every common value the two class `2`-planes span
`TℝP³`. -/
def PairReg (A B : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3)) : Prop :=
  ∀ y y' : EuclideanSpace ℝ (Fin 2), A y = B y' →
    (mfderiv (𝓡 2) (𝓡 3) A y).range ⊔ (mfderiv (𝓡 2) (𝓡 3) B y').range = ⊤

/-- **The end-triple regularity**: at every common value of the three class maps, the three class
derivatives are injective and their `2`-planes have trivial triple intersection — the shape the
`(3,2,2)` engine's `hV`-condition takes at an *end* of the homotopy, where the third chain has no free
direction. -/
def EndTripleReg (F A B : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3)) : Prop :=
  ∀ y₀ y₁ y₂ : EuclideanSpace ℝ (Fin 2), F y₀ = A y₁ → F y₀ = B y₂ →
    Function.Injective (mfderiv (𝓡 2) (𝓡 3) F y₀) ∧
    Function.Injective (mfderiv (𝓡 2) (𝓡 3) A y₁) ∧
    Function.Injective (mfderiv (𝓡 2) (𝓡 3) B y₂) ∧
    (mfderiv (𝓡 2) (𝓡 3) F y₀).range ⊓ (mfderiv (𝓡 2) (𝓡 3) A y₁).range ⊓
      (mfderiv (𝓡 2) (𝓡 3) B y₂).range = ⊥

/-- **The fold flatness of a plane class map**: its derivative kills the *boundary* coordinate
directions, i.e. `mfderiv A y (e_i) = 0` whenever `y i ∈ {0, 1}` (both `i : Fin 2`).

This is exactly the condition under which the box shear `Work.Drive.shear`, which *fixes* the boundary
coordinates (`(shear q y) i = y i` for `y i ∈ {0,1}`), loses only directions that `A` already kills —
the content of `Work.Drive.range_mfderiv_shear_eq`, and the reason the fold hypotheses are what
`hrich` needs at the fold meets (`ENCODED_GENERIC_DEAD.md` §1, `NOTES_LEAD_hodd_faces.md` §2).  It is a
**theorem** (not a hypothesis) for the design's own plane presentations:
`Work.Drive.mfderiv_planeClassMap_diskPlane_single` for the folded disk presentation and
`Work.Drive.mfderiv_planeClassMap_chartPert_diskPlane_single` for its chart perturbations. -/
def FoldFlat (A : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3)) : Prop :=
  ∀ (y : EuclideanSpace ℝ (Fin 2)) (i : Fin 2), (y i = 0 ∨ y i = 1) →
    mfderiv (𝓡 2) (𝓡 3) A y (EuclideanSpace.single i 1) = 0

/-- `FoldFlat` is the conjunction of its two coordinate clauses — the form in which the design's
producers state it. -/
theorem foldFlat_iff (A : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3)) :
    FoldFlat A ↔
      ((∀ y : EuclideanSpace ℝ (Fin 2), (y 0 = 0 ∨ y 0 = 1) →
          mfderiv (𝓡 2) (𝓡 3) A y (EuclideanSpace.single 0 1) = 0) ∧
       (∀ y : EuclideanSpace ℝ (Fin 2), (y 1 = 0 ∨ y 1 = 1) →
          mfderiv (𝓡 2) (𝓡 3) A y (EuclideanSpace.single 1 1) = 0)) := by
  constructor
  · intro h
    exact ⟨fun y hy => h y 0 hy, fun y hy => h y 1 hy⟩
  · rintro ⟨h0, h1⟩ y i hy
    fin_cases i
    · exact h0 y hy
    · exact h1 y hy

/-- A constant plane class map is fold flat (the derivative vanishes identically). -/
theorem foldFlat_const (c : Projectivization ℝ (Eucl 3)) :
    FoldFlat (fun _ : EuclideanSpace ℝ (Fin 2) => c) := by
  intro y i hy
  have h : mfderiv (𝓡 2) (𝓡 3) (fun _ : EuclideanSpace ℝ (Fin 2) => c) y = 0 :=
    mfderiv_const (I := 𝓡 2) (I' := 𝓡 3) (c := c) (x := y)
  rw [h]
  rfl

end

end Work.Drive
