import Mathlib
import Submission.Work.SimplyConnected.ABS.Defs
import Submission.Work.Drive.Interfaces

/-!
# The (weak) Green function at a prescribed pole

`Work.Drive.HasWeakGreen X` asks for *some* point `z₀` and a positive harmonic function on `X \ {z₀}`
with a unit logarithmic pole at `z₀`.  The local-boundedness lemma
`Work.Drive.greenExhaustion_locallyBounded` splits naturally according to whether such a function
exists **at the prescribed pole `a`**, whence this pointwise version.

* the existence at `a` makes the local boundedness of the normalised Green functions elementary
  (the weak Green function is a global superharmonic majorant of every Green function of the
  exhaustion);
* the non-existence at `a` is the "parabolic" case, in which the classical theorem on the
  Robin-normalised Green functions of an exhaustion is the content.

`Work.Drive.HasWeakGreen X` is equivalent to `∃ a, Work.Drive.WeakGreenAt X a`.
-/

open scoped Topology Manifold

namespace Work.Drive

/-- **A weak Green function at the point `a`**: a strictly positive harmonic function on `X \ {a}`
with a unit logarithmic pole at `a` (no decay at the ideal boundary is asked for). -/
def WeakGreenAt (X : Type*) [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [SecondCountableTopology X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    (a : X) : Prop :=
  ∃ E : X → ℝ, (∀ x : X, x ≠ a → 0 < E x) ∧ Submission.HarmonicOnX E (Set.univ \ {a}) ∧
    Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {a}) a E

/-- `HasWeakGreen X` is the pointwise statement at some point. -/
theorem hasWeakGreen_iff_exists_weakGreenAt {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] :
    HasWeakGreen X ↔ ∃ a : X, WeakGreenAt X a := Iff.rfl

end Work.Drive
