import Mathlib
import Submission.Work.Drive.projCharted
import Submission.Work.Drive.contMDiffAt_projCharted_iff

/-!
# The projective charts are smooth

`Work.Drive.projChartMap i` is the `i`-th classical affine chart on `ℝPⁿ`,
`[v] ↦ (v_j/v_i)_{j ≠ i}`, and `Work.Drive.projChartSource i` is its source `Uᵢ`.

`Work.Drive.projCharted n` is the transparent smooth structure on `ℝPⁿ` whose atlas is the range of
the charts `Work.Drive.projChart i`.  This file records the basic consequence: each chart is a
`C^∞` map of that manifold, i.e. `projChartMap i` is `C^∞` at every point of `projChartSource i`.

The content is a specialisation of the general manifold fact that every member of the maximal atlas
is `C^∞` on its source (`contMDiffAt_of_mem_maximalAtlas`): `projChart i` lies in the atlas, hence
in the maximal atlas because the atlas admits the smooth groupoid (`isManifold_projCharted n`), and
the coercion `↑(projChart i)` is `projChartMap i` by definition.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Set

noncomputable section

set_option linter.style.haveILetI false in
theorem contMDiffAt_projChartMap (n : ℕ) (i : Fin (n + 1))
    (p : Projectivization ℝ (Work.Drive.Eucl n)) (hp : p ∈ Work.Drive.projChartSource i) :
    @ContMDiffAt ℝ _ (EuclideanSpace ℝ (Fin n)) _ _ (EuclideanSpace ℝ (Fin n)) _
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (Projectivization ℝ (Work.Drive.Eucl n)) _
      (Work.Drive.projCharted n) (EuclideanSpace ℝ (Fin n)) _ _ (EuclideanSpace ℝ (Fin n)) _
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) (EuclideanSpace ℝ (Fin n)) _ _
      ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.Drive.projChartMap i) p := by
  -- work with the transparent charted-space structure, for which `projChart i` is a chart
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) (Projectivization ℝ (Work.Drive.Eucl n)) :=
    Work.Drive.projCharted n
  -- and which makes `ℝPⁿ` a smooth manifold
  haveI : IsManifold (𝓡 n) ((⊤ : ℕ∞) : WithTop ℕ∞) (Projectivization ℝ (Work.Drive.Eucl n)) :=
    Work.Drive.isManifold_projCharted n
  -- the `i`-th projective chart is a chart of the (maximal) atlas
  have he : Work.Drive.projChart i ∈ IsManifold.maximalAtlas (𝓡 n) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Projectivization ℝ (Work.Drive.Eucl n)) :=
    StructureGroupoid.subset_maximalAtlas _ (Set.mem_range_self i)
  have hp' : p ∈ (Work.Drive.projChart i).source := hp
  -- every atlas member is `C^∞` on its source, and `↑(projChart i) = projChartMap i`
  exact contMDiffAt_of_mem_maximalAtlas he hp'

end

end Work.Drive
