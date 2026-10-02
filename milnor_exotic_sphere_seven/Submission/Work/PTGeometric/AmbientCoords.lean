import Submission.Work.PTGeometric.exists_projOfPlane
import Submission.Work.ThomBordism.Grassmann.PlaneAct

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: the ambient coordinates of a map into the total space of the tautological bundle

A continuous map `G : M → (tautologicalBundle k m).TotalSpace` into the total space of the
tautological bundle over the oriented Grassmannian is, in ambient coordinates, the pair

* `P x = projOfPlane k m (G x).proj` — the orthogonal projection onto the plane of `G x`, a continuous
  map into `Gr (k+m) k`, and
* `v x = evalVec (G x)` — the vector of the plane carried by `G x`,

and `P x (v x) = v x` by construction.  This is exactly the pair of fields that
`Work.PTGeometric.ContinuousAmbientData` consumes: the null-homotopy of the genuine collapse map is a
map into `TautologicalThomSpace k m = OnePoint (tautologicalBundle k m).TotalSpace`, and away from the
base point it yields such a `G`.

## Main results

* `Work.PTGeometric.continuous_ambientCoords`
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter

namespace Work.PTGeometric

noncomputable section

open Work.ThomBordism.Grassmann

/-- **The ambient coordinates of a continuous map into the total space of the tautological bundle.**
The orthogonal projection onto the plane, and the vector of the plane. -/
theorem continuous_ambientCoords (k m : ℕ) {M : Type} [TopologicalSpace M]
    (G : M → (tautologicalBundle k m).TotalSpace) (hG : Continuous G) :
    ∃ (P : M → Amb (k + m) →L[ℝ] Amb (k + m)) (v : M → Amb (k + m)),
      Continuous P ∧ (∀ x, P x ∈ Gr (k + m) k) ∧
      Continuous v ∧ (∀ x, P x (v x) = v x) := by
  refine ⟨fun x => projOfPlane k m ((tautologicalBundle k m).proj (G x)),
    fun x => evalVec (G x), ?_, ?_, ?_, ?_⟩
  · exact (continuous_projOfPlane k m).comp ((tautologicalBundle k m).continuous_proj.comp hG)
  · intro x; exact projOfPlane_mem_Gr k m _
  · exact continuous_evalVec.comp hG
  · intro x
    exact (projOfPlane_fixed_iff k m ((tautologicalBundle k m).proj (G x)) (evalVec (G x))).mpr
      (evalVec_memPlane (G x))

end

end Work.PTGeometric
