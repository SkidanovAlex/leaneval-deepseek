import Mathlib
import Submission.Work.CORE2B.Defs
import Submission.OddOrder.Isaacs.Ch03_SplitExtensions.Theorem315

/-!
# `O(G) = O_{2'}(G)` has odd order

`Work.GW2.oddCore G = (sSup {N : Subgroup G | N.Normal ∧ Odd (Nat.card N)}).normalCore` is the
largest normal subgroup of odd order.  We show that its order is odd by comparing it with the
odd-order library's `π`-radical `O_π(G)` for `π = {q | q ≠ 2}`:

* `Odd (Nat.card N) ↔ N.IsPiSubgroup {q | q ≠ 2}` — a finite subgroup has odd order exactly when
  `2` is not among the primes dividing its order (`odd_iff_isPiSubgroup_ne_two`);
* every normal odd-order subgroup is a normal `{2}ᶜ`-subgroup, so
  `oddCore G ≤ O_{2'}(G)` (`oddCore_le_oPiCore`, via `Subgroup.IsPiGroup.le_oPiCore`);
* `O_π(G)` is itself a `π`-group (`OddOrder.Isaacs.Ch03.oPiCore.isPiGroup`), hence has odd order;
* `Nat.card (oddCore G) ∣ Nat.card (O_{2'}(G))`, so `oddCore_odd` follows from `Odd.of_dvd_nat`.
-/

namespace Work.CORE2B

open Subgroup

/-- A subgroup of a finite group has odd order if and only if every prime dividing its order is
different from `2`, i.e. it is a `{2}ᶜ`-subgroup. -/
theorem odd_iff_isPiSubgroup_ne_two {G : Type*} [Group G] [Finite G] (N : Subgroup G) :
    Odd (Nat.card N) ↔ Subgroup.IsPiSubgroup ({q : ℕ | q ≠ 2}) N := by
  unfold Subgroup.IsPiSubgroup
  have hne : Nat.card ↥N ≠ 0 := (Nat.card_pos (α := ↥N)).ne'
  constructor
  · intro hodd q hq hq2
    rw [hq2] at hq
    exact (Nat.not_even_iff_odd.mpr hodd)
      (even_iff_two_dvd.mpr (Nat.mem_primeFactors.mp hq).2.1)
  · intro h
    rw [← Nat.not_even_iff_odd]
    intro heven
    exact h 2 (Nat.mem_primeFactors.mpr
      ⟨by norm_num, even_iff_two_dvd.mp heven, hne⟩) rfl

/-- `O(G) ≤ O_{2'}(G)`: every normal subgroup of odd order is a normal `{2}ᶜ`-subgroup. -/
theorem oddCore_le_oPiCore (G : Type*) [Group G] [Finite G] :
    Work.GW2.oddCore G ≤ OddOrder.Isaacs.Ch03.oPiCore ({q : ℕ | q ≠ 2}) G := by
  rw [Work.GW2.oddCore]
  refine le_trans (Subgroup.normalCore_le _) (sSup_le fun N hN => ?_)
  exact @OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup.le_oPiCore G _ ({q : ℕ | q ≠ 2}) N hN.1
    ((odd_iff_isPiSubgroup_ne_two N).mp hN.2)

theorem oddCore_odd {G : Type} [Group G] [Finite G] : Odd (Nat.card (Work.GW2.oddCore G)) := by
  have hpi : Subgroup.IsPiSubgroup ({q : ℕ | q ≠ 2})
      (OddOrder.Isaacs.Ch03.oPiCore ({q : ℕ | q ≠ 2}) G) :=
    OddOrder.Isaacs.Ch03.oPiCore.isPiGroup ({q : ℕ | q ≠ 2})
  exact Odd.of_dvd_nat ((odd_iff_isPiSubgroup_ne_two _).mpr hpi)
    (Subgroup.card_dvd_of_le (oddCore_le_oPiCore G))

end Work.CORE2B
