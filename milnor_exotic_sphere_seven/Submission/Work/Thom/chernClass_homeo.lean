import Mathlib
import Submission.Work.Thom.Iso
import Submission.Work.Thom.IsoPunct
import Submission.Work.Thom.chernClass_comap
import Submission.Work.Thom.chernClass_BundleIso
import Submission.Work.Thom.tautQuotientCore_iso
import Submission.Work.Thom.thomClassRank_eulerClass_iso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Thom

/-- **Isomorphism-invariance of the Chern classes**: two isomorphic complex bundles of the same
rank over the same base have equal Chern classes. -/
theorem chernClass_BundleIso {m j : ℕ} {B : Type} [TopologicalSpace B]
    {ι ι' : Type} [Fintype ι] [Fintype ι']
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι')
    (e : Work.Thom.BundleIso Z Z') :
    Work.Thom.chernClass m j Z = Work.Thom.chernClass m j Z' :=
  (chernClass_BundleIso_of tautQuotientCore_iso thomClassRank_eulerClass_iso) m Z Z' e j

theorem chernClass_homeo {m j : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (Φ : X ≃ₜ Y) {ι ι' : Type} [Fintype ι] [Fintype ι']
    (Z : VectorBundleCore ℂ X (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ Y (EuclideanSpace ℂ (Fin m)) ι')
    (e : Work.Thom.BundleIso Z (Work.Thom.bundleComap Z' (Φ : C(X, Y)))) :
    (Work.Thom.CohMap (Φ : C(X, Y)) ℤ (2 * j)).hom (Work.Thom.chernClass m j Z') =
      Work.Thom.chernClass m j Z := by
  rw [← chernClass_comap Z' (Φ : C(X, Y))]
  exact (chernClass_BundleIso Z (bundleComap Z' (Φ : C(X,Y))) e).symm

end Work.Thom
