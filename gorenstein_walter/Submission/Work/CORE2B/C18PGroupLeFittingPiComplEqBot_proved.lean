import Mathlib
import Submission.Work.CORE2B.Defs
import Submission.Work.CORE2B.API
import Submission.Work.CORE2B.L27cf_centralizes_odd_pi_part

namespace Work.CORE2B

open Subgroup

-- GW design pass 18, item A′, leaf H4 (copied from `Core18PGroupLeFittingPiComplEqBot.lean`):
-- a `p`-subgroup of `F_{π'}(M)` with `p ∈ π` is trivial.
-- Sketch: `fittingPiIn πᶜ M = (piCore πᶜ (fitting M)).map _`; every element of `piCore πᶜ _` has
-- order with prime factors in `πᶜ`, while a nontrivial `p`-group has an element of order `p`
-- (Cauchy), and `p ∈ π`.
/--
A `p`-subgroup `K` of `F_{π'}(M)` with `p ∈ π` is trivial.

`F_{π'}(M) = O_{π'}(F(M))` is a `π'`-subgroup (`L27cf_isPiSubgroup_fittingPiIn`): every prime
`q` dividing its order lies in `πᶜ`.  If `K ≠ ⊥`, then `K`, being a nontrivial `p`-group, has
order `p ^ n` with `n ≠ 0`, so `p ∣ |K|`; since `K ≤ F_{π'}(M)` also `p ∣ |F_{π'}(M)|`, whence
`p ∈ πᶜ` — contradicting `p ∈ π`.
-/
theorem C18PGroupLeFittingPiComplEqBot_proved {G : Type} [Group G] [Finite G] (M : Subgroup G)
    (π : Set ℕ) (p : ℕ) [Fact p.Prime] (hpπ : p ∈ π) (K : Subgroup G) (hK : IsPGroup p K)
    (hKle : K ≤ Work.GW2.fittingPiIn πᶜ M) : K = ⊥ := by
  by_contra hne
  -- `K` is nontrivial, so its order is `p ^ n` with `n ≠ 0`, hence `p ∣ |K|`
  have hcard : Nat.card ↥K ≠ 1 := fun h => hne (Subgroup.card_eq_one.mp h)
  obtain ⟨n, hn⟩ := hK.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    exact hcard hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hpdvd : p ∣ Nat.card ↥K := by
    rw [hn, pow_succ]
    exact dvd_mul_left p (p ^ m)
  -- containment in `F_{π'}(M)` transports the divisibility
  have hdvd : p ∣ Nat.card ↥(Work.GW2.fittingPiIn πᶜ M) :=
    hpdvd.trans (Subgroup.card_dvd_of_le hKle)
  have hpmem : p ∈ (Nat.card ↥(Work.GW2.fittingPiIn πᶜ M)).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Nat.card_pos.ne'⟩
  -- but `F_{π'}(M)` is a `πᶜ`-subgroup
  exact (L27cf_isPiSubgroup_fittingPiIn πᶜ M p hpmem) hpπ

end Work.CORE2B
