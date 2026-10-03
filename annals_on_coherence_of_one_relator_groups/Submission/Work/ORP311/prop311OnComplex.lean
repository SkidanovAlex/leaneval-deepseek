import Mathlib
import Submission.Work.ORDivLoc.Prop311
import Submission.Work.ORP311.P311Defs
import Submission.Work.ORP311.closureCN_subset_range_liftUN
import Submission.Work.ORP311.twistData_map
import Submission.Work.ORP311.UN_toUK_le_closureCN
import Submission.Work.ORP311.isUnit_onePlus_of_range_twist
import Submission.Work.ORP311.scalar_iota_toUK
import Submission.Work.ORDivLoc.Closure.isHughesFreeEnv_toUK_of_complex
import Submission.Work.ORHughesFree.Section6.HughesFreeEnv
import Submission.Work.ORBridgeLinnell.Countable

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Work.ORP311

theorem prop311OnComplex (G : Type) [Group G] [Countable G] : Work.ORDivLoc.Prop311OnComplex G := by
  letI : MeasurableSpace G := ⊤
  haveI : MeasurableSingletonClass G := ⟨fun _ => trivial⟩
  haveI : MeasurableMul G := ⟨fun _ => fun s _ => trivial, fun _ => fun s _ => trivial⟩
  intro H hLI
  change Work.ORHughesFree.IsHughesFreeEnv
    (Work.ORBridgeLinnell.toUK (Work.ORP311.concreteEnvelope G) (RingHom.id ℂ) H).toRingHom
  intro H₀ hfg hne N hNnorm t hdec htinf n A
  let N₀ : Subgroup G := (N.map H₀.subtype).map H.subtype
  have hle : ((Work.Section6.UN
      ((Work.ORBridgeLinnell.toUK (Work.ORP311.concreteEnvelope G) (RingHom.id ℂ) H).toRingHom)
      H₀ N : Work.ORHughesFree.StarSubring (Work.ORP311.concreteEnvelope G).U) :
      Set (Work.ORP311.concreteEnvelope G).U)
      ⊆ (Work.ORP311.closureCN N₀ : Set (Work.ORP311.concreteEnvelope G).U) :=
    UN_toUK_le_closureCN (G := G) H H₀ N
  let A' : Matrix (Fin n) (Fin n) (closureCNty N₀) :=
    Matrix.of (fun i j => (⟨(A i j : (concreteEnvelope G).U), hle (A i j).2⟩ : closureCNty N₀))
  have hAeq : A'.map (closureCN.subtype N₀) = A.map Subtype.val :=
    Work.ORDivLoc.Closure.map_coe_eq hle A
  have hTw : P311.TwistData N₀ (((t : H₀) : ↥H) : G) := twistData_map H H₀ N hNnorm t htinf
  have hrange : ∀ i j, (A'.map (closureCN.subtype N₀)) i j ∈ Set.range (P311.liftUN N₀) := by
    intro i j
    exact closureCN_subset_range_liftUN N₀ (A' i j).2
  have hunit := isUnit_onePlus_of_range_twist N₀ (((t : H₀) : ↥H) : G) hTw
    (A'.map (closureCN.subtype N₀)) hrange
  rw [hAeq] at hunit
  have hscal : iota G (MonoidAlgebra.single (((t : H₀) : ↥H) : G) (1 : ℂ))
      = ((Work.ORBridgeLinnell.toUK (Work.ORP311.concreteEnvelope G) (RingHom.id ℂ) H).toRingHom.comp
          (Work.ORHughesFree.inducedMapRing (K := ℂ) (G := ↥H) H₀))
          (MonoidAlgebra.single t (1 : ℂ)) := scalar_iota_toUK G H H₀ t
  rw [hscal] at hunit
  exact hunit

end Work.ORP311
