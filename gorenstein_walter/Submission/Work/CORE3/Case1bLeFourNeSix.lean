import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.ASM.Defs
import Submission.Work.CORE2A.Defs
import Submission.Work.CORE3.Case1bLeFourNotLeD
import Submission.Work.CORE3.Case1bLeFourSplit
import Submission.Work.CORE3.Case1bLeFourV1
import Submission.Work.CORE3.Case1bDStructure
import Submission.Work.CORE3.SixInvSetElements
import Submission.Work.CORE3.SixInvSetMulTable
import Submission.Work.CORE3.InvSetVUSingleton
import Submission.Work.CORE3.CosetInvCountLeSix

/-!
# `Work.CORE3.Case1bLeFourNeSix`

Bender 1981, *Finite groups with dihedral Sylow 2-subgroups*, J. Algebra **70**, §3,
pp. 223–224, Case (1), subcase `V = O₂(Ĥ)` of type `(2,2)` with `|U| = |O(Ĥ)| = 3`:
**no coset of `Ĥ` containing an involution outside `Ĥ` carries exactly six involutions.**

Setting: `G` a minimal counterexample (`Work.GW2.BenderCtx G`), `B` a Bender setup,
`Case1 B`, `D : Case1bData B` (so `V = O₂(Ĥ)` is a four-group and `|S| = 8`),
`U = O(Ĥ)` with `|U| = 3`, and `y` an involution outside `Ĥ`.

Write `n := cosetInvCount Ĥ y`, `I := invSetIn Ĥ y`, `VU := O₂(Ĥ) ⊔ U`,
`Dd := Ĥ ⊓ Ĥ^y`, `M := Dd ⊓ VU`.  The argument assembles four facts already in the tree,
all in the `n = 6` configuration:

* `Work.CORE3.SixInvSetElements` (Bender's (6), first half): `I` contains an element `a` of
  order `3` and two distinct involutions `b₁ ≠ b₂`;
* `Work.CORE3.Case1bLeFourSplit` (Bender's (6), second half): `b₁ b₂ = h · v` with
  `h ∈ {a, a²}`, `v ∈ M`, and `v ≠ 1 → v ∈ U ∧ h v = v h`;
* `Work.CORE3.Case1bLeFourV1`: the case `v = 1` (i.e. `b₁b₂ ∈ {a, a²}`) is impossible — `y`
  inverts `b₁b₂` (because it inverts `a`) and fixes it (because it inverts the involutions
  `b₁`, `b₂`), so `b₁b₂` has order dividing both `2` and `3`;
* `Work.CORE3.Case1bLeFourNotLeD`: the case `U ≤ Dd` is impossible.

In the case `v ≠ 1` the element `v` lies in `U ∖ {1}`; since `|U| = 3` is prime, `U = ⟨v⟩`, and
`v ∈ M ≤ Dd` gives `U ≤ Dd`, contradicting the last item.  Hence `n = 6` is absurd.

The hypothesis `|U| = 3` (`hU3`) is used in this last step (and in `Case1bLeFourSplit`,
`Case1bLeFourV1`).
-/

namespace Work.CORE3

open Work.GW2
open Subgroup

theorem Case1bLeFourNeSix (G : Type) [Group G] [Finite G] (I : Work.CORE3.Case1Inputs)
    (hBc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B)
    (D : Work.GW2.Case1bData B) (hU3 : Nat.card B.U = 3)
    {y : G} (hy2 : orderOf y = 2) (hyH : y ∉ B.Hhat) :
    Work.GW2.cosetInvCount B.Hhat y ≠ 6 := by
  classical
  intro h6
  -- Bender's (5)
  have h5 : ∀ z : G, orderOf z = 2 → z ∉ B.Hhat →
      Work.GW2.invSet (Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U) z = {1} :=
    InvSetVUSingleton G I hBc B h1 D
  -- Bender's (6), first half: `a` of order `3`, two distinct involutions `b₁ ≠ b₂` in `I`
  obtain ⟨a, b1, b2, ha, ha3, hb1, hb1o, hb2, hb2o, h12⟩ :=
    SixInvSetElements G I hBc B h1 D h5 y hy2 hyH h6
  -- Bender's (6), second half: `b₁ b₂ = h · v` with `h ∈ {a, a²}` and `v ∈ M`
  obtain ⟨h, hh, v, hv, hprod, hsplit⟩ :=
    Case1bLeFourSplit G I hBc B h1 D hU3 hy2 hyH h6 ha ha3 hb1 hb1o hb2 hb2o h12
  by_cases hv1 : v = 1
  · -- `v = 1`: `b₁ b₂ ∈ {a, a²}` is impossible
    refine Case1bLeFourV1 G I hBc B h1 D hU3 hy2 hyH h6 ha ha3 hb1 hb1o hb2 hb2o h12 ?_
    rcases hh with hh1 | hh1
    · left; rw [hprod, hh1, hv1, mul_one]
    · right; rw [hprod, hh1, hv1, mul_one]
  · -- `v ≠ 1`: then `v ∈ U`, `|U| = 3` forces `U = ⟨v⟩ ≤ M ≤ Dd`, contradicting
    -- `Case1bLeFourNotLeD`
    obtain ⟨hvU, _hvcomm⟩ := hsplit hv1
    have hv3 : orderOf v = 3 := by
      have hdvd : orderOf v ∣ 3 := by
        have h := orderOf_dvd_natCard (⟨v, hvU⟩ : B.U)
        rw [hU3] at h
        simpa using h
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h' | h'
      · exact absurd h' (fun hc => hv1 (orderOf_eq_one_iff.mp hc))
      · exact h'
    have hUeq : Subgroup.zpowers v = B.U := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hvU) ?_
      rw [hU3, Nat.card_zpowers, hv3]
    have hzvM : Subgroup.zpowers v ≤
        (B.Hhat ⊓ Work.GW2.conjSub y B.Hhat) ⊓ (Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U) :=
      Subgroup.zpowers_le.mpr hv
    have hUleDd : B.U ≤ B.Hhat ⊓ Work.GW2.conjSub y B.Hhat := by
      rw [← hUeq]
      exact hzvM.trans inf_le_left
    exact Case1bLeFourNotLeD G I hBc B h1 D hU3 hy2 hyH h6 hUleDd

end Work.CORE3

#print axioms Work.CORE3.Case1bLeFourNeSix
