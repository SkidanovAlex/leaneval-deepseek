import Mathlib
import Submission.Work.Drive.collapseTransport
import Submission.Work.Drive.sideCountDefs
import Submission.Work.Drive.planeChain
import Submission.Work.Drive.squareDisk
import Submission.Work.Drive.sideGermDefs

/-!
# The vocabulary of the polar dictionary of the radial collapse

`Work.Drive.PolarDict β Q u t σ` is the *derivative* part of the polar dictionary of the collapse at
`s = 1` (`Submission/Work/Drive/PAIRONEDATA_PLAN.md`): the derivative of the radially collapsed plane
`colPlane β Q 1` at `u` is a scalar multiple of the core loop's tangent at `t`, and every direction it
kills — the *radial* direction of the disk point `sqDisk (foldBox u)` — is sent by the honest plane
`diskPlane Q` into the tangent line of the diameter loop `diamLoop Q t` at `σ`.

It is packaged as a `Prop` (rather than written inline) because statements *about* it must elaborate
without the local `ChartedSpace`/`IsManifold` instances of `Work.Drive.CappingSpace`: the `mfderiv`s
into the capping space need the concrete structure `Work.Drive.cappingCharted`, which is a `local
instance` in the files that build it.  A consumer only mentions `PolarDict`.
-/

namespace Work.Drive

open Manifold Set Filter
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

/-- **The derivative part of the polar dictionary of the collapse at `s = 1`.** -/
def PolarDict (β : ℝ → ℝ) (Q : ℂ → CappingSpace) (u : EuclideanSpace ℝ (Fin 2))
    (t σ : ℝ) : Prop :=
  (∀ a : EuclideanSpace ℝ (Fin 2), ∃ c : ℝ,
    mfderiv (𝓡 2) (𝓡 4) (colPlane β Q 1) u a
      = c • (mfderiv 𝓘(ℝ, ℝ) (𝓡 4) (coreLoop Q) t 1)) ∧
  (∀ a : EuclideanSpace ℝ (Fin 2),
    mfderiv (𝓡 2) (𝓡 4) (colPlane β Q 1) u a = 0 →
    mfderiv (𝓡 2) (𝓡 4) (diskPlane Q) u a
      ∈ (mfderiv 𝓘(ℝ, ℝ) (𝓡 4) (diamLoop Q t) σ).range)

/-- **The core loop is immersive at the parameter `t`**: the non-degeneracy that the second conjunct of
`Work.Drive.PolarDict` needs (it is *not* implied by smoothness of `Q`: the collapse's core loop can be
degenerate, e.g. for a chart with `mfderiv Q z = 0` on the unit circle).  In the application
(`Work.Drive.pairOneData_of_T6GenAt`) it is supplied by the `GoodLoopChain` of `T6GenAt` at the core
meet: the transversality `range dL ⊔ range dX = ⊤` forces `dL ≠ 0`. -/
def CoreImmersiveAt (Q : ℂ → CappingSpace) (t : ℝ) : Prop :=
  mfderiv 𝓘(ℝ, ℝ) (𝓡 4) (coreLoop Q) t ≠ 0

/-- The derivative of a loop, read in the *model* space of the capping space (the idiom of
`Work.Drive.mLoop`: `TangentSpace` is an opaque `def`, so the model-space form is the one in which the
linear algebra typechecks). -/
def loopDeriv (L : ℝ → CappingSpace) (t : ℝ) : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 4) :=
  mfderiv 𝓘(ℝ, ℝ) (𝓡 4) L t

/-- The derivative of a `3`-chain, read in the model space. -/
def chainDeriv (X : EuclideanSpace ℝ (Fin 3) → CappingSpace) (y : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 4) :=
  mfderiv (𝓡 3) (𝓡 4) X y

@[simp] lemma loopDeriv_apply (L : ℝ → CappingSpace) (t : ℝ) (v : ℝ) :
    loopDeriv L t v = mfderiv 𝓘(ℝ, ℝ) (𝓡 4) L t v := rfl

@[simp] lemma chainDeriv_apply (X : EuclideanSpace ℝ (Fin 3) → CappingSpace)
    (y : EuclideanSpace ℝ (Fin 3)) (v : EuclideanSpace ℝ (Fin 3)) :
    chainDeriv X y v = mfderiv (𝓡 3) (𝓡 4) X y v := rfl


end

end Work.Drive
