import Mathlib
import Submission.Work.ORP311.P311Defs
import Submission.Work.ORBridgeLinnell.Basic
import Submission.Work.ORHughesFree.Section6.SubgroupComplexity

namespace Work.ORP311

/-- **The scalar `ι` factors through the `H`-side bridge.**  For `H₀ ≤ H ≤ G` and `t : H₀`, the
image of the group basis element `t` under the concrete envelope `ℂ[G] → U(G)` agrees with the
image of `t ∈ ℂ[↥H₀]` under the composite
`ℂ[↥H₀] → ℂ[↥H] → U(G)` formed from the subgroup inclusion `inducedMapRing H₀` and the bridge
`toUK (concreteEnvelope G) (RingHom.id ℂ) H`.

Both sides are `ι_G (single t 1)`: the group algebra inclusion carries `single t 1` to
`single (t : H) 1`, and `toUK` carries it to `genU E t`, which is `ι_G (single t 1)` by
`genU_apply`. -/
theorem scalar_iota_toUK (G : Type) [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] (H : Subgroup G) (H₀ : Subgroup ↥H) (t : H₀) : Work.ORP311.iota G (MonoidAlgebra.single ((t : H₀) : G) (1 : ℂ)) = ((Work.ORBridgeLinnell.toUK (Work.ORP311.concreteEnvelope G) (RingHom.id ℂ) H).toRingHom.comp (Work.ORHughesFree.inducedMapRing (K := ℂ) (G := ↥H) H₀)) (MonoidAlgebra.single t (1 : ℂ)) := by
  rw [RingHom.comp_apply,
    show (Work.ORHughesFree.inducedMapRing (K := ℂ) (G := ↥H) H₀) (MonoidAlgebra.single t 1) =
      MonoidAlgebra.single (H₀.subtype t) 1 from MonoidAlgebra.mapDomain_single,
    Work.ORP311.iota_apply]
  exact ((Work.ORBridgeLinnell.toUK_single (Work.ORP311.concreteEnvelope G) (RingHom.id ℂ) H
      (H₀.subtype t) 1).trans (by simp [Work.ORBridgeLinnell.genU_apply])).symm

end Work.ORP311
