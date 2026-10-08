import Mathlib
import Submission.Work.ThmF.Prove.Step9Defs
import Submission.Work.ThmF.ChV12.prop1b
import Submission.Work.S3.P_card_ne_two

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.Prove.n1NotDvdQ` — `|P| ∤ |Q|` in Peterfalvi II, Ch. V §3

In the standing context `CtxF H Q t s r P` of Peterfalvi II, Ch. V §3, step (3) (recorded as
`Step3Out Q P`, see `Work.ThmF.Prove.step3`) says that every prime `ℓ ∣ |O_{2'}(Q)|` is *not*
`|P|`:  `ℓ ≠ |P|`.

The present lemma is the immediate consequence that `|P|` does not divide `|Q|` at all.
`p = |P|` is an odd prime (`P_prime`, and `P_card_ne_two`); if `p ∣ |Q|` then Cauchy's theorem
supplies `z ∈ Q` of order `p`.  Such a `z` has odd order, so it lies in `O_{2'}(Q) = oddPart Q`,
whence `p = orderOf z ∣ |O_{2'}(Q)|`, and step (3) applied to `ℓ = p` contradicts itself.

Only step (3)'s output is used; `ChIIFourProp` and `ThompsonFrobeniusProp` are hypotheses of the
ambient development and do not occur in the argument.
-/

set_option linter.unusedVariables false

namespace Work.ThmF.Prove

theorem n1NotDvdQ {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (hC4 : Submission.Blueprint.ChIIFourProp) (hTh : Submission.Blueprint.ThompsonFrobeniusProp)
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) (h3 : Work.ThmF.Prove.Step3Out Q P) :
    ¬ Nat.card P ∣ Nat.card Q := by
  intro hdvd
  -- `p = |P|` is an odd prime
  have hp : (Nat.card P).Prime := c.P_prime
  have hpodd : Odd (Nat.card P) :=
    Nat.odd_iff.mpr (hp.eq_two_or_odd.resolve_left (Work.S3.P_card_ne_two c))
  have hfact : Fact (Nat.card P).Prime := ⟨hp⟩
  -- Cauchy: `Q` contains an element `z` of order `p`
  obtain ⟨z, hz⟩ := @exists_prime_orderOf_dvd_card' ↥Q _ _ (Nat.card P) hfact hdvd
  have hzG : orderOf ((z : Q) : G) = Nat.card P := by rw [Subgroup.orderOf_coe, hz]
  -- `z` has odd order, hence lies in `O_{2'}(Q) = oddPart Q`
  have hzmem : ((z : Q) : G) ∈ Work.ThmF.oddPart Q :=
    Work.ThmF.mem_oddPart_of_odd Q z.2 (by rw [hzG]; exact hpodd)
  -- so `p = orderOf z` divides `|O_{2'}(Q)|`
  have hpQ1 : Nat.card P ∣ Nat.card ↥(Work.ThmF.oddPart Q) := by
    have hle : Subgroup.zpowers (((z : Q) : G)) ≤ Work.ThmF.oddPart Q :=
      Subgroup.zpowers_le.mpr hzmem
    have hcard : Nat.card ↥(Subgroup.zpowers (((z : Q) : G))) = Nat.card P := by
      rw [Nat.card_zpowers, hzG]
    have hdvd' := Subgroup.card_subgroup_dvd_card
      ((Subgroup.zpowers (((z : Q) : G))).subgroupOf (Work.ThmF.oddPart Q))
    have heq : Nat.card ↥((Subgroup.zpowers (((z : Q) : G))).subgroupOf (Work.ThmF.oddPart Q))
        = Nat.card ↥(Subgroup.zpowers (((z : Q) : G))) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
    rw [heq, hcard] at hdvd'
    exact hdvd'
  -- step (3) applied to `ℓ = |P|` says `|P| ≠ |P|`
  exact absurd rfl (h3 (Nat.card P) hp hpQ1).2

end Work.ThmF.Prove
