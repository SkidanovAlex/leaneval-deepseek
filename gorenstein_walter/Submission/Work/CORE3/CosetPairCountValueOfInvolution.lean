import Mathlib
import Submission.Work.CORE3.Case1bEightNineDefs
import Submission.Work.CORE2A.Basic

/-!
# `Work.CORE3.CosetPairCountValueOfInvolution`

Bender 1981 §3, pp. 223–224: the value of the ordered commuting-pair count `cosetPairCount Hh z`
for a genuine involution `z ∉ Ĥ`, in terms of the involution count `cosetInvCount Hh z` of its
coset, under the two Bender §3 inputs

* `hLe4` — every coset of `Ĥ` outside `Ĥ` carries at most four involutions;
* `hFour` — a coset carrying four involutions carries six ordered commuting pairs (the
  commuting graph on those four involutions is a star `K_{1,3}`, Bender (7)/(8)).

Given those, the value is

* `2` when the coset carries two involutions (the two involutions of `2²`-type commute);
* `6` when it carries four (that is `hFour`);
* `0` otherwise — i.e. for `0`, `1` (at most one involution, no pair) or `3` involutions
  (Bender's (6) for `n ≤ 3`: `I_Ĥ(z) = {1, a, a * a}` is a cyclic group of order `3`, and two
  distinct coset involutions commute only if `a^{-i} a^{j}` has order dividing `2`).

All the group-theoretic content is already in `Submission/Work/CORE3/Case1bEightNineDefs.lean`;
the present file only performs the case distinction on `cosetInvCount Hh z ∈ {0,1,2,3,4}`.
-/

namespace Work.CORE3

open Work.GW2

/-- A coset containing at most one involution contributes no ordered pair of distinct commuting
involutions. -/
theorem cosetPairCount_eq_zero_of_cosetInvCount_le_one {G : Type} [Group G] [Finite G]
    (Hh : Subgroup G) {y : G} (h1 : Work.GW2.cosetInvCount Hh y ≤ 1) :
    Work.CORE3.cosetPairCount Hh y = 0 := by
  have h2 : (cosetInvolSet Hh y).ncard ≤ 1 := h1
  have hsub : ∀ a ∈ cosetInvolSet Hh y, ∀ b ∈ cosetInvolSet Hh y, a = b :=
    (Set.ncard_le_one (s := cosetInvolSet Hh y)).mp h2
  unfold cosetPairCount
  have hempty : {p : G × G | p.1 ∈ cosetInvolSet Hh y ∧ p.2 ∈ cosetInvolSet Hh y ∧
      p.1 ≠ p.2 ∧ p.1 * p.2 = p.2 * p.1} = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro ⟨a, b⟩ ⟨ha, hb, hne, -⟩
    exact hne (hsub a ha b hb)
  rw [hempty, Set.ncard_empty]

theorem CosetPairCountValueOfInvolution (G : Type) [Group G] [Finite G] (Hh : Subgroup G)
    (hLe4 : ∀ y : G, orderOf y = 2 → y ∉ Hh → Work.GW2.cosetInvCount Hh y ≤ 4)
    (hFour : ∀ y : G, orderOf y = 2 → y ∉ Hh → Work.GW2.cosetInvCount Hh y = 4 →
      Work.CORE3.cosetPairCount Hh y = 6)
    (z : G) (hz : orderOf z = 2) (hzH : z ∉ Hh) :
    Work.CORE3.cosetPairCount Hh z =
      (if Work.GW2.cosetInvCount Hh z = 2 then 2
        else if Work.GW2.cosetInvCount Hh z = 4 then 6 else 0) := by
  have hyy : z * z = 1 := by
    have h := pow_orderOf_eq_one z
    rw [hz, pow_two] at h
    exact h
  have hI : (invSetIn Hh z).ncard = Work.GW2.cosetInvCount Hh z :=
    ncard_invSetIn_eq_cosetInvCount Hh z hyy hzH
  have hle : Work.GW2.cosetInvCount Hh z ≤ 4 := hLe4 z hz hzH
  by_cases h2 : Work.GW2.cosetInvCount Hh z = 2
  · rw [ite_eq_left h2]
    exact cosetPairCount_eq_two_of_ncard_two hyy hzH (by rw [hI, h2])
  · rw [ite_eq_right h2]
    by_cases h4 : Work.GW2.cosetInvCount Hh z = 4
    · rw [ite_eq_left h4]
      exact hFour z hz hzH h4
    · rw [ite_eq_right h4]
      have hcases : Work.GW2.cosetInvCount Hh z = 0 ∨ Work.GW2.cosetInvCount Hh z = 1 ∨
          Work.GW2.cosetInvCount Hh z = 3 := by omega
      rcases hcases with h0 | h1 | h3
      · exact cosetPairCount_eq_zero_of_cosetInvCount_le_one Hh (by omega)
      · exact cosetPairCount_eq_zero_of_cosetInvCount_le_one Hh (by omega)
      · exact cosetPairCount_eq_zero_of_ncard_three hyy hzH (by rw [hI, h3])

end Work.CORE3
