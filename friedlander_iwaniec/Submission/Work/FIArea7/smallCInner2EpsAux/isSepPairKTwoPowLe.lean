import Mathlib
import Submission.Work.FIArea7.prop172defs

namespace Work.FIArea7.smallCInner2EpsAux

open Finset

/-- Every prime of the decreasing enumeration of the `k` prime factors of `d·m·n` is at least
`2`, hence `d·m·n = ∏ i, p i ≥ 2^k`. -/
theorem isSepPairKTwoPowLe {r k d m n : ℕ} (h : Work.FIArea7.IsSepPairK r k d m n) :
    2 ^ k ≤ d * m * n := by
  obtain ⟨p, hpl, -, -, -⟩ := h
  obtain ⟨-, hprime, hprod⟩ := hpl
  rw [hprod]
  calc 2 ^ k = ∏ _i : Fin k, 2 := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ ∏ i : Fin k, p i := Finset.prod_le_prod' (fun i _ => (hprime i).two_le)

end Work.FIArea7.smallCInner2EpsAux
