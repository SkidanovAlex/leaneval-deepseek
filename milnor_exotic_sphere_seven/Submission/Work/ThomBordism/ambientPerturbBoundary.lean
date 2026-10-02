import Submission.Work.PTGeometric.AmbientPreData

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter

namespace Work.PTGeometric

noncomputable section

open Work.ThomBordism

namespace AmbientPreData

variable {n k : ℕ} {ι : Type} [Fintype ι] {Fam : ι → Man8}

/-- **The ambient perturbation does not change the field on the boundary.**

`Work.PTGeometric.AmbientPreData.ambientCollapseEnd` replaces the field `v` by the perturbation
`Classical.choose (exists_ambient_perturbation …)`, whose cut-offs `χ l` vanish at every boundary
point (`hχint`: `χ l y ≠ 0 ⟹ y` is an interior point).  Hence at a boundary point the perturbed field
agrees with the original one.  This is what makes the level set `{v = 0}` of the collapse end agree
with the level set of the pre-data *near the boundary*, where its boundary part lives. -/
theorem ambientCollapseEnd_v_eq_on_boundary (D : AmbientPreData n k ι Fam)
    (x : D.M) (hx : x ∈ (𝓡∂ ((8 + k) + 1)).boundary D.M) :
    (D.ambientCollapseEnd).v x = D.v x := by
  classical
  -- the perturbed field, as a named term
  let w : D.M → EuclideanSpace ℝ (Fin n) :=
    Classical.choose (exists_ambient_perturbation D.C D.v D.hv D.mem D.χ D.hχsm D.hχrange
      D.hχU D.hχint D.hχbd D.hcov)
  have hwv : ∀ y, (∀ l, D.χ l y = 0) → w y = D.v y :=
    (Classical.choose_spec (exists_ambient_perturbation D.C D.v D.hv D.mem D.χ D.hχsm D.hχrange
      D.hχU D.hχint D.hχbd D.hcov)).2.2.1
  -- `χ l` vanishes at every boundary point
  have hchi : ∀ l, D.χ l x = 0 := by
    intro l
    by_contra h
    exact ((𝓡∂ ((8 + k) + 1)).isInteriorPoint_iff_not_isBoundaryPoint x).mp
      (D.hχint l x h) hx
  -- the projection of the collapse end is the perturbed field
  change w x = D.v x
  exact hwv x hchi

end AmbientPreData

end

end Work.PTGeometric
