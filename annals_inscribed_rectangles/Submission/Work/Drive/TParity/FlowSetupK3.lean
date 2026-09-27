import Mathlib
import Submission.Work.Drive.TParity.LocalGraph
import Submission.Work.Drive.TParity.FlowDefs

/-!
# The flow setup of a tangential field on the triple intersection set

The nine-box analogue of `Work.Drive.ManifoldParity.interSetSetup`.
-/

namespace Work.Drive.TParity

open scoped Manifold ContDiff Topology
open Manifold Set

noncomputable section

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) Ctop M]

/-- **The flow setup of a field `V` on the triple intersection set.** -/
def K3_setup (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M) (V : Amb 8 → Amb 8)
    (hV : ContDiff ℝ Ctop V) (hVs : HasCompactSupport V)
    (hmapsTo : ∀ x ∈ K3 D, ∀ t : ℝ,
      (∀ u ∈ Set.uIcc (0 : ℝ) t, flowV8 V hV hVs u x ∈ Submission.Drive.unitBox 8) →
      flowV8 V hV hVs t x ∈ K3 D) : Work.Drive.FlowSetup 8 where
  W := V
  Φ := flowV8 V hV hVs
  K := K3 D
  zero := flowV8_zero V hV hVs
  add := flowV8_add V hV hVs
  deriv := flowV8_deriv V hV hVs
  mapsTo := hmapsTo
  cont := hV.continuous

@[simp] theorem K3_setup_W (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M) (V : Amb 8 → Amb 8)
    (hV : ContDiff ℝ Ctop V) (hVs : HasCompactSupport V) (hmapsTo) :
    (K3_setup D V hV hVs hmapsTo).W = V := rfl

@[simp] theorem K3_setup_K (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M) (V : Amb 8 → Amb 8)
    (hV : ContDiff ℝ Ctop V) (hVs : HasCompactSupport V) (hmapsTo) :
    (K3_setup D V hV hVs hmapsTo).K = K3 D := rfl

end

end Work.Drive.TParity
