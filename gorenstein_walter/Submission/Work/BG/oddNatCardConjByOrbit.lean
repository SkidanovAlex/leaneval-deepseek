import Mathlib
import Submission.Work.BG.CharBridge

namespace Work.BG

open OddOrder.RepresentationTheory in
theorem oddNatCardConjByOrbit {U : Type} [Group U] [Finite U] [Fintype U]
    (K : Subgroup U) [K.Normal] (hodd : Odd (Nat.card U)) (θ : IrreducibleCharacter K) :
    Odd (Nat.card {η : IrreducibleCharacter K //
      η ∈ IrreducibleCharacter.conjByOrbit (G := U) (H := K) θ}) := by
  rw [card_conjByOrbit_eq_index_inertia]
  exact hodd.of_dvd_nat (Subgroup.index_dvd_card _)

end Work.BG
