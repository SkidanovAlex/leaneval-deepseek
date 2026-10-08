import Mathlib
import Submission.Work.ASM.Defs
import Submission.OddOrder.Isaacs.Ch03_SplitExtensions.Theorem315

/-!
# `O(G)` has odd order

`Work.GW2.oddCore G = (sSup {N | N.Normal ∧ Odd (Nat.card N)}).normalCore` is the largest
normal subgroup of odd order.  We show `Odd (Nat.card (oddCore G))` by comparing it with the
odd-order library's π-radical `O_π(G)` for `π = {q | q ≠ 2}`:

* a subgroup of a finite group has odd order iff every prime dividing its order is `≠ 2`, so
  `oddCore G ≤ O_{2'}(G)` (every normal odd subgroup is a normal `2'`-subgroup);
* `O_π(G)` is a `π`-group (`oPiCore.isPiGroup`), hence of odd order for `π = {2}ᶜ`;
* `Nat.card (oddCore G)` divides `Nat.card (O_{2'}(G))`, so it is odd too.
-/

namespace Work.ASM

/-- A subgroup of a finite group has odd order if and only if every prime dividing its
cardinality is different from `2`. -/
theorem odd_iff_isPiSubgroup_ne_two {G : Type*} [Group G] [Finite G] (N : Subgroup G) :
    Odd (Nat.card N) ↔ Subgroup.IsPiSubgroup ({q : ℕ | q ≠ 2}) N := by
  unfold Subgroup.IsPiSubgroup
  have hne : Nat.card ↥N ≠ 0 := Nat.card_pos.ne'
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
  refine le_trans (Subgroup.normalCore_le _) (sSup_le ?_)
  rintro N ⟨hN, hodd⟩
  have hNnormal : N.Normal := hN
  exact OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup.le_oPiCore
    ((odd_iff_isPiSubgroup_ne_two N).mp hodd)

theorem oddCore_odd (G : Type*) [Group G] [Finite G] : Odd (Nat.card (Work.GW2.oddCore G)) := by
  have hle := oddCore_le_oPiCore G
  have ho : Odd (Nat.card (OddOrder.Isaacs.Ch03.oPiCore ({q : ℕ | q ≠ 2}) G)) :=
    (odd_iff_isPiSubgroup_ne_two _).mpr
      (OddOrder.Isaacs.Ch03.oPiCore.isPiGroup (G := G) ({q : ℕ | q ≠ 2}))
  exact Odd.of_dvd_nat ho (Subgroup.card_dvd_of_le hle)

end Work.ASM
