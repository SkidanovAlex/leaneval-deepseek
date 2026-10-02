import Submission.Work.ThomBordism.Grassmann.ThomTarget
import Submission.Work.Topology.VectorBundleCoreTotalSpaceLocallyCompact
import Submission.Work.Tubular.PuncturedDiscPair.t2Space_sphSub
import Submission.Work.ThomBordism.Grassmann.thomSpaceTorsionDetected

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Hausdorffness (and local compactness) of the universal Thom space, for the consumers

The universal target of area THOM is `Work.ThomBordism.Grassmann.grassmannThomTarget k m …`, whose
underlying space is the **Thom space** `Th(γ_k) = OnePoint (tautologicalBundle k m).TotalSpace`
(`Work.ThomBordism.Grassmann.TautologicalThomSpace`).  Consumers of the Pontryagin–Thom chapter
(area PTGEOMETRIC's collar/last-mile construction, the transversality arguments) need
`T2Space` of that space, and `T2Space (OnePoint X)` is **not** synthesised by type class search from
`T2Space X` alone: Mathlib derives it from `NormalSpace (OnePoint X)` (available for
`[WeaklyLocallyCompactSpace X] [R1Space X]`) via `T4Space → T3Space → T2Space`, and the missing
ingredient is the *local compactness* of the total space of the bundle.

This file supplies, as global instances (so that they are found without any local `haveI`):

* `LocallyCompactSpace (tautologicalBundle k m).TotalSpace`
  (`Work.Topology.VectorBundleCoreTotalSpaceLocallyCompact`, using `LocallyCompactSpace (OG k m)` from
  compactness + Hausdorffness of the oriented Grassmannian);
* `T2Space (tautologicalBundle k m).TotalSpace` (`Work.Tubular.PuncturedDiscPair.t2Space_totalSpace`);
* `T2Space (Grassmann.TautologicalThomSpace k m)`, and the same for the target itself,
  `T2Space (Grassmann.grassmannThomTarget k m …).T` (the two are the same type by
  `Grassmann.grassmannThomTarget_T`, which is `rfl`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace Work.ThomBordism

noncomputable section

/-- The total space of the tautological bundle over the oriented Grassmannian is locally compact. -/
instance instLocallyCompactSpaceTautologicalTotalSpace (k m : ℕ) :
    LocallyCompactSpace (Grassmann.tautologicalBundle k m).TotalSpace :=
  Work.Topology.VectorBundleCoreTotalSpaceLocallyCompact (Grassmann.tautologicalBundle k m)

/-- The total space of the tautological bundle over the oriented Grassmannian is Hausdorff. -/
instance instT2SpaceTautologicalTotalSpace (k m : ℕ) :
    T2Space (Grassmann.tautologicalBundle k m).TotalSpace :=
  Work.Tubular.PuncturedDiscPair.t2Space_totalSpace (Grassmann.tautologicalBundle k m)

/-- **The universal Thom space `Th γ_{k,m}` is Hausdorff**: it is the one-point compactification of a
locally compact Hausdorff space. -/
instance instT2SpaceTautologicalThomSpace (k m : ℕ) :
    T2Space (Grassmann.TautologicalThomSpace k m) := by
  infer_instance

/-- **The space of the universal target `grassmannThomTarget` is Hausdorff**, i.e. the instance above
read through the `ThomTarget` projection (the two types are the same by definition). -/
instance instT2SpaceGrassmannThomTarget (k m : ℕ) (hconn : Grassmann.ThomSpaceConnected k m)
    (U : Work.Thom.ThomClass (Grassmann.tautologicalBundle k m) k)
    (Φ : Work.Thom.OpenThom (Grassmann.tautologicalBundle k m) (8 + k) ≃ₗ[ℤ]
      Grassmann.TSCoh k m)
    (hdet : Grassmann.ThomSpaceClassesDetect k m U Φ) :
    T2Space (Grassmann.grassmannThomTarget k m hconn U Φ hdet).T :=
  instT2SpaceTautologicalThomSpace k m

end

end Work.ThomBordism
