import Mathlib
import Submission.Work.Smooth.Jordan.Sphere
import Submission.Work.Smooth.Jordan.familyDiscs_of_schoenfliesData
import Submission.Work.Topology.Classical.Defs
import Submission.Work.Topology.Classical.SchoenfliesSphere

/-!
# The Jordan–Schoenflies datum of a family on a sphere homeomorphic to `S²`

`Work.Topology.Classical.schoenfliesData_of_jordanSchoenflies` transports the conclusion of
Jordan–Schoenflies — stated for the round unit sphere `Work.Topology.Classical.RoundSphere` — to an
arbitrary set `A ⊆ ℝ³` equipped with a homeomorphism `φ : RoundSphere ≃ₜ A`, giving a
`Work.Topology.Classical.SchoenfliesData A ι c` for every family of pairwise disjoint Jordan curves
on `A`.  `Work.Smooth.Jordan.familyDiscs_of_schoenfliesData` converts that classical datum into the
usable `Work.Smooth.Jordan.FamilyDiscs A ι c` (one spanning disc per curve, with the nesting
properties).

Here we compose the two, in the vocabulary of the smooth Jordan chapter: the round sphere is its
`Work.Smooth.Jordan.RoundSphere`, the curves are `Work.Smooth.Jordan.IsSimpleClosedCurveOn` (which is
definitionally `Work.Topology.Classical.IsJordanCurveOn`), and the conclusion is `FamilyDiscs`.
-/

namespace Work.Smooth.Jordan

theorem familyDiscs_of_jordanSchoenfliesSphere {A : Set LeanEval.KnotTheory.PardonDistortion.R3} {ι : Type} [Fintype ι] {c : ι → ℝ → LeanEval.KnotTheory.PardonDistortion.R3} (φ : Work.Smooth.Jordan.RoundSphere ≃ₜ ↥A) (h : Work.Topology.Classical.JordanSchoenfliesSphere) (hs : ∀ i : ι, IsSimpleClosedCurveOn A (c i)) (hd : Pairwise fun i j : ι => Disjoint (Set.range (c i)) (Set.range (c j))) : Nonempty (FamilyDiscs A ι c) := by
  obtain ⟨D⟩ := Work.Topology.Classical.schoenfliesData_of_jordanSchoenflies h φ hs hd
  exact Work.Smooth.Jordan.familyDiscs_of_schoenfliesData D hs hd

end Work.Smooth.Jordan
