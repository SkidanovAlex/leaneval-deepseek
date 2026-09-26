import Mathlib
import Submission.Work.Smooth.Jordan.Sphere
import Submission.Work.Topology.Classical.Defs
import Submission.Work.Topology.Classical.schoenfliesData_of_jordanSchoenflies

/-!
# Schoenflies on a surface homeomorphic to the round sphere

`Work.Smooth.Jordan.SchoenfliesOnInput A` asks that every simple closed curve of `A ⊆ ℝ³` be the
common boundary of two complementary embedded discs in `A`.  For arbitrary `A` this is the transport
along a homeomorphism of the round sphere of the classical Jordan--Schoenflies theorem in `S²`: the
curve is pulled back to `RoundSphere`, the theorem `Work.Topology.Classical.JordanSchoenfliesSphere`
supplies its two discs on the round sphere, and the discs are pushed forward along `φ : RoundSphere
≃ₜ A`.

The work is done by the already established transport
`Work.Topology.Classical.schoenfliesData_of_jordanSchoenflies` applied to the single curve
`PUnit → (ℝ → ℝ³)`; this file extracts from the resulting `SchoenfliesData` the (weaker)
`SphereSchoenflies` packaging of `Work.Smooth.Jordan`.
-/

open Set
open LeanEval.KnotTheory.PardonDistortion

namespace Work.Smooth.Jordan

noncomputable section

theorem schoenfliesOnInput_of_homeomorph {A : Set LeanEval.KnotTheory.PardonDistortion.R3} (φ : RoundSphere ≃ₜ A) (h : Work.Topology.Classical.JordanSchoenfliesSphere) : SchoenfliesOnInput A := by
  intro c hc
  -- the single curve `c` as a one-element family
  let c' : PUnit → ℝ → R3 := fun _ => c
  have hc' : ∀ i : PUnit, Work.Topology.Classical.IsJordanCurveOn A (c' i) := fun _ => hc
  have hd : Pairwise fun i j : PUnit => Disjoint (Set.range (c' i)) (Set.range (c' j)) :=
    fun i j hij => absurd (Subsingleton.elim i j) hij
  obtain ⟨D⟩ :=
    Work.Topology.Classical.schoenfliesData_of_jordanSchoenflies h φ hc' hd
  exact ⟨{ simple := hc
           e := D.e PUnit.unit
           e' := D.e' PUnit.unit
           inj := D.inj PUnit.unit
           inj' := D.inj' PUnit.unit
           boundary := D.boundary PUnit.unit
           boundary' := D.boundary' PUnit.unit
           mem := D.mem PUnit.unit
           mem' := D.mem' PUnit.unit
           cover := D.cover PUnit.unit
           meet := D.meet PUnit.unit }⟩

end

end Work.Smooth.Jordan
