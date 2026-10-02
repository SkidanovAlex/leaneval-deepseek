import Mathlib
import Submission.Work.Tubular.Collapse

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `cubeToEuc` is a topological embedding

The parametrisation `Work.Tubular.cubeToEuc N R : I^N → ℝ^N` of the box `[-R,R]^N` is the
`ℝ`-linear map `t ↦ (2R(t_i - 1/2))_i`.  For `R > 0` it is injective, and it is continuous on the
compact source `I^N` with Hausdorff target `ℝ^N`; hence it is a closed embedding, in particular a
topological embedding.

This is the elementary input needed by the Pontryagin–Thom source construction
(`Work.PTGeometric.*`), where one has to identify the cube model of the sphere with the box.
-/

namespace Work.PTGeometric

open Topology

/-- The cube parametrisation `Work.Tubular.cubeToEuc N R` is injective for `R ≠ 0`. -/
theorem injective_cubeToEuc (N : ℕ) {R : ℝ} (hR : R ≠ 0) :
    Function.Injective (⇑(Work.Tubular.cubeToEuc N R)) := by
  intro t t' h
  have h' : Work.Tubular.cubeToFun N R t = Work.Tubular.cubeToFun N R t' := by
    have h2 : Work.Tubular.funToEuc N (Work.Tubular.cubeToFun N R t)
        = Work.Tubular.funToEuc N (Work.Tubular.cubeToFun N R t') := h
    exact (Work.Tubular.funToEuc N).injective h2
  funext i
  apply Subtype.ext
  have hi := congrFun h' i
  simp only [Work.Tubular.cubeToFun_apply] at hi
  have h2R : (2 * R) ≠ 0 := mul_ne_zero two_ne_zero hR
  have hb := mul_left_cancel₀ h2R hi
  linarith

theorem isEmbedding_cubeToEuc (N : ℕ) {R : ℝ} (hR : 0 < R) :
    Topology.IsEmbedding (⇑(Work.Tubular.cubeToEuc N R)) :=
  ((Work.Tubular.cubeToEuc N R).continuous.isClosedEmbedding
    (injective_cubeToEuc N (ne_of_gt hR))).toIsEmbedding

end Work.PTGeometric
