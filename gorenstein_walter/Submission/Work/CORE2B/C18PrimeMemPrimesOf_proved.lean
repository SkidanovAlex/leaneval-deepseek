import Mathlib
import Submission.Work.CORE2B.Defs
import Submission.Work.CORE2B.API

namespace Work.CORE2B

-- GW design pass 18, item A′, leaf H5 (copied from `Core18PrimeMemPrimesOf.lean`): a nontrivial
-- `p`-subgroup `X` of `Y` puts `p` in `π(Y) = primesOf Y`.
-- Sketch: `p ∣ |X|` (`IsPGroup` of a nontrivial group is a `p`-group of order `p^n ≠ 1`), and
-- `|X| ∣ |Y|` (`Subgroup.card_dvd_of_le`); `primesOf Y = {q | q ∈ (Nat.card Y).primeFactors}`.
theorem C18PrimeMemPrimesOf_proved {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (X Y : Subgroup G) (hXY : X ≤ Y) (hX : X ≠ ⊥) (hXp : IsPGroup p X) :
    p ∈ Work.GW2.primesOf Y := by
  change p ∈ (Nat.card Y).primeFactors
  rw [Nat.mem_primeFactors]
  -- `X` is nontrivial, so it has an element `x ≠ 1`; a `p`-group then has `p ∣ orderOf x`.
  obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hX
  have hdvdX : p ∣ Nat.card X := (hXp.dvd_orderOf hx).trans (orderOf_dvd_natCard x)
  refine ⟨Fact.out, hdvdX.trans (Subgroup.card_dvd_of_le hXY), ?_⟩
  exact Nat.card_ne_zero.mpr ⟨⟨1, Y.one_mem⟩, inferInstance⟩

end Work.CORE2B
