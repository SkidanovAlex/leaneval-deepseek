import Mathlib
import Submission.Work.Stems.spheresConnected

/-!
# The bridge from the geometric lemma to `Work.Stems.SphereMapNull`

`Submission/Work/Stems/sphereMap_null_of_lt.lean` (proved by a delegate) states the geometric input
for `j < n` with arbitrary `j`; `Work.Stems.SphereMapNull` only asks it for `1 ≤ j`.  This file
records the (trivial) implication, so that the connectivity of spheres follows from the geometric
lemma:

`sphereMap_null_of_lt → SphereMapNull → SphereConnectivity`.
-/

open scoped Topology Topology.Homotopy unitInterval

namespace Work.Stems

/-- `Work.Stems.SphereMapNull` from the geometric lemma in its general form. -/
theorem sphereMapNull_of_sphereMap_null_of_lt
    (h : ∀ (j n : ℕ), j < n → ∀ (b : sphere j) (x₀ : sphere n) (f : C(sphere j, sphere n)),
      f b = x₀ → ContinuousMap.HomotopicRel f (ContinuousMap.const _ x₀) {b}) :
    SphereMapNull :=
  fun j n _ hjn b x₀ f hb => h j n hjn b x₀ f hb

end Work.Stems
