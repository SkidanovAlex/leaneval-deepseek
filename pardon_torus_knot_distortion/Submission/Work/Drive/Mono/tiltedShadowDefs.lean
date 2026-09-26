import Mathlib
import Submission.Work.Drive.Mono.TiltedTraceData
import Submission.Work.Drive.Mono.boxSphere_inter_slab_halfspace_connected
import Submission.Work.Drive.Mono.isEmbeddedSphere_frontier_slabCaps

/-!
# The `(p,q)`-shadow of the box, and the height functions of its fibres

The vocabulary of the *shadow route* to
`Work.Drive.Mono.tiltedLevel_spheres_decomposition_alt`: the level's pair of linear functionals
`(⟪v,·⟫, ℓ) : ℝ³ → ℝ²`, the shadow `π '' A` of a set `A`, the planar chamber
`K₀ = {|s - a| ≤ h} ∩ {t ≤ lam}` cut out by the slab and the wall, and the extremal values of a
transverse linear functional `ζ` on the fibres of the box over its shadow.

This module has no `sorry`; it is the `depends_on` of the two geometric bricks
`Work.Drive.Mono.fibreMax_continuous` and `Work.Drive.Mono.shadowChamber_discParam`.
-/

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion Set

noncomputable section

/-- **The pair `(⟪v,·⟫, ℓ)`**, the level's pair of linear functionals. -/
def sweepPair (v : R3) (ℓ : R3 →L[ℝ] ℝ) : R3 → ℝ × ℝ := fun y => (inner ℝ v y, ℓ y)

/-- The **shadow** of `A ⊆ ℝ³` under the level's pair of functionals. -/
def sweepShadow (v : R3) (ℓ : R3 →L[ℝ] ℝ) (A : Set R3) : Set (ℝ × ℝ) := sweepPair v ℓ '' A

/-- The **chamber** `K₀ = {|s - a| ≤ h} ∩ {t ≤ lam}` of the `(p,q)`-plane cut out by the slab and
the wall. -/
def chamber (a h lam : ℝ) : Set (ℝ × ℝ) := {w : ℝ × ℝ | |w.1 - a| ≤ h ∧ w.2 ≤ lam}

/-- The maximal value of `ζ` over the fibre of `X` over `w`. -/
def fibreMax (ζ p q : R3 →L[ℝ] ℝ) (X : Set R3) (w : ℝ × ℝ) : ℝ :=
  sSup (ζ '' {y ∈ X | p y = w.1 ∧ q y = w.2})

/-- The minimal value of `ζ` over the fibre of `X` over `w`. -/
def fibreMin (ζ p q : R3 →L[ℝ] ℝ) (X : Set R3) (w : ℝ × ℝ) : ℝ :=
  sInf (ζ '' {y ∈ X | p y = w.1 ∧ q y = w.2})

/-- The shadow of the closed box, as a set of the plane. -/
def boxShadow (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v : R3) (ℓ : R3 →L[ℝ] ℝ) :
    Set (ℝ × ℝ) := sweepShadow v ℓ (closure (Submission.PBox s c σ))

end

end Work.Drive.Mono

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion Set

noncomputable section

/-- **`IsEmbeddedSphere` in an arbitrary topological space**, parametrised by the fixed standard
sphere `S² ⊆ ℝ³`: the version of `Work.InnermostDisk.IsEmbeddedSphere` in which the ambient space
may be any topological space (used to state the "boundary of the solid over a disc" brick in the
`(p,q,ζ)`-coordinates and transport it along a homeomorphism).

For `α = ℝ³` it is the same proposition as `Work.InnermostDisk.IsEmbeddedSphere`. -/
def IsEmbeddedSphereIn (α : Type*) [TopologicalSpace α] (S : Set α) : Prop :=
  ∃ e : C(Metric.sphere (0 : R3) 1, α), Function.Injective e ∧ Set.range e = S

end

end Work.Drive.Mono
