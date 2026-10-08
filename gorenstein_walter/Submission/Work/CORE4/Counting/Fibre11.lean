import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.Counting.Fibre11P

namespace Work.CORE4.Counting

/-- **Bender §4 (11), fibre decomposition.**  If `P ≤ G` has prime order `p`, `P` commutes
elementwise with `E`, `P ⊓ E = ⊥`, and every `(p,p)`-group `P ⊔ Y` (`Y ≤ E` of order `p`) contains
exactly `p1` conjugates of `P`, then `P ⊔ E` contains `(p1 - 1) · #{Y ≤ E : |Y| = p} + 1`
conjugates of `P`.

The proof is the assembly `Fibre11P` of the fibre decomposition `Work.CORE4.CountFibre` with the
projection `Work.CORE4.ProjOfInfBot` of the internal direct product `P ⊔ E`. -/
theorem Fibre11 {G : Type} [Group G] [Finite G]
    (P E : Subgroup G) (p p1 : ℕ) (hp : p.Prime)
    (hcardP : Nat.card P = p) (hPE : P ⊓ E = ⊥)
    (hcomm : ∀ x ∈ P, ∀ y ∈ E, x * y = y * x)
    (hbase : ∀ Y : Subgroup G, Y ≤ E → Nat.card Y = p →
      {X : Subgroup G | Nat.card X = p ∧ X ≤ P ⊔ Y ∧
        (∃ g : G, X = Work.GW2.conjSub g P)}.ncard = p1) :
    {X : Subgroup G | Nat.card X = p ∧ X ≤ P ⊔ E ∧
      (∃ g : G, X = Work.GW2.conjSub g P)}.ncard =
      (p1 - 1) * {Y : Subgroup G | Y ≤ E ∧ Nat.card Y = p}.ncard + 1 :=
  Fibre11P P E p p1 hp hcardP hPE hcomm hbase

end Work.CORE4.Counting
