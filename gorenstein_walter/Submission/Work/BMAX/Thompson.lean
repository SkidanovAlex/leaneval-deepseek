/-
# BMAX — Bender 1970, 1.1 (Thompson lemma), proved

`Work.GW2.ThompsonLemmaProp` is the Thompson `P × K` lemma in the shape of the
odd-order library: the last step of Isaacs' Theorem 4.31,
`OddOrder.Isaacs.Ch04.actionCommutator_prodRight_eq_bot_of_prodRight_fixes_actionCommutator_prodLeft`.

That library theorem says: if `B` is a p-group, `Q` a p'-group, `P × Q` acts on `B` (via
`φ`), `Q` fixes `[B,P]` pointwise and every `P`-fixed element of `B` is `Q`-fixed, then
`[B,Q] = 1`.  Reading `[B,Q] = 1` through
`actionCommutator_eq_bot_iff_acts_trivially` gives exactly `Work.GW2.ThompsonLemmaProp`.

This is Bender 1970, §1.1, with `P` the p-group, `K` the group `O^p(K)` (here: a p'-group,
which is the case used in §1.7), the commuting actions of the product `PK`, and
`[C_B(P), K] = 1`; the extra hypothesis that `K` fixes `[B,P]` is the "obviously,
`[O_q(B) ∩ A, O^p(S)] = 1`" step of Bender's proof of §1.7.  See `Defs.lean` for the
full discussion.
-/
import Submission.Work.BMAX.Defs

open scoped MatrixGroups

namespace Work.GW2

open Subgroup

/-- **Bender 1970, 1.1 (Thompson lemma).** -/
theorem thompsonLemma11 : ThompsonLemmaProp := by
  intro B _ _ p _ P K _ _ _ φ hB _hP hcop hfix1 hfix2 k b
  have hp : Nat.Prime p := Fact.out
  have hQ : ¬ p ∣ Nat.card K := (Nat.Prime.coprime_iff_not_dvd hp).mp hcop
  have hker :
      OddOrder.Isaacs.Ch04.actionCommutator
        (φ.comp (OddOrder.Isaacs.Ch04.prodRightHom P K)) = ⊥ :=
    OddOrder.Isaacs.Ch04.actionCommutator_prodRight_eq_bot_of_prodRight_fixes_actionCommutator_prodLeft
      (p := p) φ hB hQ hfix2 (fun g hg y => hfix1 y g hg)
  exact (OddOrder.Isaacs.Ch04.actionCommutator_eq_bot_iff_acts_trivially _).mp hker k b

end Work.GW2
