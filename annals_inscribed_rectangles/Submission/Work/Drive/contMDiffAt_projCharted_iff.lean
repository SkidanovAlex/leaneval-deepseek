import Mathlib
import Submission.Work.Drive.projCharted

/-!
# Testing `ContMDiffAt` into `ℝPⁿ` in an arbitrary projective chart

`Work.Drive.projCharted n` is the transparent smooth structure on `ℝPⁿ` whose atlas is the range of
the classical projective charts `Work.Drive.projChart i`.  This file records that a map
`f : ℝᵏ → ℝPⁿ` is `C^∞` at a point `z` (i.e. `ContMDiffAt` for that structure) if and only if it is
continuous at `z` and, in *any* chart of the atlas containing `f z`, the composite `projChartMap i ∘ f`
is `C^∞` at `z`.

The content is the general manifold fact that being `C^∞` is a local condition computed in any chart
of the maximal atlas (`contMDiffWithinAt_iff_of_mem_maximalAtlas'`), specialised to `projCharted n`:
`projChart i` belongs to the maximal atlas because it is a member of the atlas and the atlas admits
the smooth groupoid (`isManifold_projCharted n`), and the extended chart `(projChart i).extend (𝓡 n)`
is just `projChartMap i` since the model space is `EuclideanSpace ℝ (Fin n)` with the self model.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Set

noncomputable section

set_option linter.style.haveILetI false in

theorem contMDiffAt_projCharted_iff {n k : ℕ}
    (f : EuclideanSpace ℝ (Fin k) → Projectivization ℝ (EuclideanSpace ℝ (Fin (n + 1))))
    (z : EuclideanSpace ℝ (Fin k)) (i : Fin (n + 1)) (hz : f z ∈ Work.Drive.projChartSource i) :
    letI := Work.Drive.projCharted n
    (ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) f z ↔
      ContinuousAt f z ∧
      ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun w => Work.Drive.projChartMap i (f w)) z) := by
  letI := Work.Drive.projCharted n
  -- the target `ℝPⁿ` is a smooth manifold for the transparent structure
  haveI : IsManifold (𝓡 n) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Projectivization ℝ (EuclideanSpace ℝ (Fin (n + 1)))) := isManifold_projCharted n
  -- the `i`-th projective chart lies in the maximal atlas
  have he' : projChart i ∈ IsManifold.maximalAtlas (𝓡 n) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Projectivization ℝ (EuclideanSpace ℝ (Fin (n + 1)))) :=
    StructureGroupoid.subset_maximalAtlas _ (Set.mem_range_self i)
  have hz' : f z ∈ (projChart i).source := hz
  -- descend the second factor of the right-hand side to `ContDiffAt`
  rw [contMDiffAt_iff_contDiffAt]
  -- test `C^∞` of `f` in the chart `projChart i` of the maximal atlas
  rw [ContMDiffAt, contMDiffWithinAt_iff_of_mem_maximalAtlas' he' hz']
  simp only [continuousWithinAt_univ, preimage_univ, univ_inter]
  -- the chart `projChart i` extended by the self model is `projChartMap i`, and the source chart is
  -- the identity on `EuclideanSpace ℝ (Fin k)`
  simp only [OpenPartialHomeomorph.extend_coe, modelWithCornersSelf_coe, Set.range_id,
    Function.comp_def, id_eq, extChartAt_model_space_eq_id, PartialEquiv.refl_symm,
    PartialEquiv.refl_coe]
  rw [contDiffWithinAt_univ]
  simp only [projChart_apply]

end

end Work.Drive
