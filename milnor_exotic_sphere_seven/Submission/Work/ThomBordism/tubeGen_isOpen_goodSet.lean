import Mathlib
import Submission.Work.Stems.Hurewicz
import Submission.Work.Stems.cubeToOnePoint_continuous

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option linter.unusedVariables false

/-!
# The "good set" of the cube is open

For `Y > 0` the set

  `{t : Iⁿ | t ∈ ∂Iⁿ ∨ ∃ j, Y < |cubeCoords n t j|}`

is open in the cube `Iⁿ`.  This is the set of cube points at which the collapsed coordinate map
`cubeCoords` (the coordinatewise homeomorphism `(-1,1) ≅ ℝ`) is unbounded above `Y`, together with
the whole boundary.

The proof is the compactness of `cubeToOnePoint`.  Put `K := {w : ℝⁿ | ∀ j, |w j| ≤ Y}`; it is
closed (a finite intersection of coordinate half-spaces) and compact (a product of the intervals
`[-Y, Y]`).  Hence its image in the one point compactification `OnePoint ℝⁿ` is compact, so its
complement

  `A := (↑ '' K)ᶜ = {∞} ∪ {w | ∃ j, Y < |w j|}`

is open in `OnePoint ℝⁿ`.  Since `cubeToOnePoint n` sends `∂Iⁿ` to `∞` and agrees with
`cubeCoords` off `∂Iⁿ`, the set in the statement is exactly `cubeToOnePoint n ⁻¹' A`, hence open.
-/

open scoped Topology OnePoint

namespace Work.ThomBordism

/-- `cubeToOnePoint` is `∞` on the boundary of the cube. -/
theorem cubeToOnePoint_of_mem_boundary {n : ℕ} {t : Work.Stems.CubeI n}
    (ht : t ∈ Cube.boundary (Fin n)) :
    Work.Stems.cubeToOnePoint n t = ∞ := by
  simp only [Work.Stems.cubeToOnePoint]
  rw [if_pos ht]

/-- Off the boundary of the cube, `cubeToOnePoint` is the coercion of `cubeCoords`. -/
theorem cubeToOnePoint_of_not_mem_boundary {n : ℕ} {t : Work.Stems.CubeI n}
    (ht : t ∉ Cube.boundary (Fin n)) :
    Work.Stems.cubeToOnePoint n t =
      (Work.Stems.cubeCoords n t : OnePoint (EuclideanSpace ℝ (Fin n))) := by
  simp only [Work.Stems.cubeToOnePoint]
  rw [if_neg ht]

theorem tubeGen_isOpen_goodSet {n : ℕ} (hn : 1 ≤ n) {Y : ℝ} (hY : 0 < Y) :
    IsOpen {t : Work.Stems.CubeI n |
      t ∈ Cube.boundary (Fin n) ∨ ∃ j : Fin n, Y < |Work.Stems.cubeCoords n t j|} := by
  set K : Set (EuclideanSpace ℝ (Fin n)) := {w | ∀ j, |w j| ≤ Y} with hKdef
  have hKclosed : IsClosed K := by
    have heq : K = ⋂ j, {w : EuclideanSpace ℝ (Fin n) | |w j| ≤ Y} := by
      ext w; simp [hKdef]
    rw [heq]
    exact isClosed_iInter fun j =>
      isClosed_le (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) j).abs continuous_const
  have hKcompact : IsCompact K := by
    set K' : Set (Fin n → ℝ) := {x | ∀ j, |x j| ≤ Y} with hK'def
    have hK'compact : IsCompact K' := by
      have heq : K' = Set.univ.pi (fun _ : Fin n => Set.Icc (-Y) Y) := by
        ext x
        simp only [hK'def, Set.mem_ofPred_eq, Set.mem_univ_pi, Set.mem_Icc]
        constructor
        · intro h j; exact abs_le.mp (h j)
        · intro h j; exact abs_le.mpr (h j)
      rw [heq]
      exact isCompact_univ_pi fun _ => isCompact_Icc
    have hpre : K = (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)) ⁻¹' K' := by
      ext w
      simp only [hKdef, hK'def, Set.mem_preimage, Set.mem_ofPred_eq]
      rfl
    rw [hpre]
    exact (Homeomorph.isCompact_preimage _).2 hK'compact
  have hA : IsOpen ((OnePoint.some '' K)ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin n)))) :=
    OnePoint.isOpen_compl_image_coe.2 ⟨hKclosed, hKcompact⟩
  have hcont : Continuous (Work.Stems.cubeToOnePoint n) := Work.Stems.cubeToOnePoint_continuous n
  have hset : {t : Work.Stems.CubeI n |
        t ∈ Cube.boundary (Fin n) ∨ ∃ j : Fin n, Y < |Work.Stems.cubeCoords n t j|}
      = (Work.Stems.cubeToOnePoint n) ⁻¹'
          ((OnePoint.some '' K)ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin n)))) := by
    ext t
    constructor
    · intro ht
      rw [Set.mem_preimage, Set.mem_compl_iff]
      rcases ht with hb | ⟨j, hj⟩
      · rw [cubeToOnePoint_of_mem_boundary hb]
        exact OnePoint.infty_notMem_image_coe
      · by_cases hb : t ∈ Cube.boundary (Fin n)
        · rw [cubeToOnePoint_of_mem_boundary hb]
          exact OnePoint.infty_notMem_image_coe
        · rw [cubeToOnePoint_of_not_mem_boundary hb]
          intro hmem
          rw [Set.mem_image] at hmem
          obtain ⟨w, hwK, hw⟩ := hmem
          have hweq : w = Work.Stems.cubeCoords n t := OnePoint.coe_injective hw
          have hj' := hwK j
          rw [hweq] at hj'
          exact absurd hj' (not_le.mpr hj)
    · intro ht
      rw [Set.mem_preimage, Set.mem_compl_iff] at ht
      by_cases hb : t ∈ Cube.boundary (Fin n)
      · exact Or.inl hb
      · refine Or.inr ?_
        have hcoe : Work.Stems.cubeToOnePoint n t =
            (Work.Stems.cubeCoords n t : OnePoint (EuclideanSpace ℝ (Fin n))) :=
          cubeToOnePoint_of_not_mem_boundary hb
        have hnk : Work.Stems.cubeCoords n t ∉ K := by
          intro hmem
          exact ht (by rw [hcoe]; exact ⟨Work.Stems.cubeCoords n t, hmem, rfl⟩)
        rw [hKdef] at hnk
        simp only [Set.mem_ofPred_eq, not_forall, not_le] at hnk
        exact hnk
  rw [hset]
  exact hA.preimage hcont

end Work.ThomBordism
