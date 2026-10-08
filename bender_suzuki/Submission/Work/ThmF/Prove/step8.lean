import Mathlib
import Submission.Work.ThmF.ChV3.Chain15
import Submission.Work.ThmF.ChV3.NearField
import Submission.Work.ThmF.Prove.sigLemma2c
import Submission.Work.ThmF.Prove.fieldStep8

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.ThmF.Prove

open Classical

/-- **Peterfalvi II, Ch. V §3 step (8)** (the design's statement `Work.ThmF.ChV3Design.step8`,
with the (1)–(5) chain `h15` supplied in place of the design's `CtxF`-only hypotheses).

Assume `Q₁ = O_{2'}(Q) ≠ 1` and `Σ = C_W(P) ≠ 1`.  In the standing context, step (5) of the
chain (`h15.h5`) then forces `C_Q(P)` abelian: were it not, `Q₁ = 1`.  App. XI Prop. 1 (2)b
(`hNFF`) realises `C_Q(P)` as `F^×` for a finite field `F` of characteristic `f = o(st)` and
cardinality `|F| = f^m = |C_Q(P)| + 1`, with `Σ` acting faithfully on `F` by ring automorphisms;
for `w ≠ 1`, `|C_F(w)| = |C_{C_Q(P)}(w)| + 1`, and `C_{C_Q(P)}(w)`, being a subgroup of the
`2`-group `Q ⊓ C_G(w)` (`sigLemma2c`), has `2`-power order.  Hence `|C_F(w)| = 2^b + 1`, and
`sigLemma2c` also gives `f ∈ {3, 5}`.  The field-arithmetic theorem `fieldStep8` then yields
that `|Σ|` is prime and `|F| ∈ {3^{|Σ|}, 5^{|Σ|}, 9^{|Σ|}}`; finally `|F| = |C_Q(P)| + 1` turns
this into the claim. -/
theorem step8 {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (hA : Work.ThmF.ArithmeticNineTwoSeven) (hNFF : Work.ThmF.ChV3.NearFieldFieldProp)
    (hC4 : Submission.Blueprint.ChIIFourProp) (hnil : Group.IsNilpotent ↥Q)
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) (h15 : Work.ThmF.ChV3.Chain15 H Q t s r P)
    (hQ1 : Work.ThmF.oddPart Q ≠ ⊥) (hSig : Work.ThmF.ChV3.Sig H t P ≠ ⊥) :
    (Nat.card ↥(Work.ThmF.ChV3.Sig H t P)).Prime ∧
      (Nat.card ↥(Work.ThmF.ChV3.CQ Q P) + 1 = 3 ^ Nat.card ↥(Work.ThmF.ChV3.Sig H t P) ∨
       Nat.card ↥(Work.ThmF.ChV3.CQ Q P) + 1 = 5 ^ Nat.card ↥(Work.ThmF.ChV3.Sig H t P) ∨
       Nat.card ↥(Work.ThmF.ChV3.CQ Q P) + 1 = 9 ^ Nat.card ↥(Work.ThmF.ChV3.Sig H t P)) := by
  classical
  -- ## `C_Q(P)` is commutative: step (5) says that `¬` commutative forces `O_{2'}(Q) = 1`.
  have hcomm : IsMulCommutative ↥(Work.ThmF.ChV3.CQ Q P) := by
    by_contra hnc
    exact hQ1 (h15.h5 hnc).2
  -- ## `Σ = C_W(P)` is non-trivial, so it has a non-identity element and odd order.
  obtain ⟨w0, hw0⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hSig
  have hw0G : (w0 : G) ≠ 1 := fun h => hw0 (Subtype.ext h)
  have hDodd : Odd (Nat.card ↥(Submission.Blueprint.twoPoint H t)) :=
    c.split.stronglyEmbedded.2.2 t c.split.not_mem
  have hSigW : Work.ThmF.ChV3.Sig H t P ≤ Work.ThmF.W H t := inf_le_left
  have hSigD : Work.ThmF.ChV3.Sig H t P ≤ Submission.Blueprint.twoPoint H t :=
    hSigW.trans ((Work.ThmF.W_le_centD H t).trans
      (inf_le_left : Submission.Blueprint.centD H t ≤ Submission.Blueprint.twoPoint H t))
  have hSigOdd : Odd (Nat.card ↥(Work.ThmF.ChV3.Sig H t P)) :=
    hDodd.of_dvd_nat (Subgroup.card_dvd_of_le hSigD)
  have hSigGt1 : 1 < Nat.card ↥(Work.ThmF.ChV3.Sig H t P) :=
    (Subgroup.one_lt_card_iff_ne_bot _).mpr hSig
  -- ## `f = o(st) ∈ {3, 5}` (`sigLemma2c` at the non-identity element `w0`).
  have hf35 : orderOf (s * t) = 3 ∨ orderOf (s * t) = 5 :=
    (sigLemma2c hC4 hnil c h15.hQ0 (w := (w0 : G)) w0.2 hw0G).2
  -- ## App. XI Prop. 1 (2)b: the near-field is a field on which `Σ` acts.
  obtain ⟨F, hField, hFint, hCharP, hFact, act, hFcard, hinj, hfix⟩ :=
    hNFF c h15.hm h15.hcq hcomm
  letI := hField
  letI := hFint
  haveI : CharP F (orderOf (s * t)) := hCharP
  haveI : Fact (orderOf (s * t)).Prime := hFact
  -- ## `w ≠ 1` fixes `2^b + 1` elements: `C_{C_Q(P)}(w)` is a subgroup of the `2`-group
  -- `Q ⊓ C_G(w)` (`sigLemma2c`), hence a power of `2` in order.
  have h2 : ∀ w : ↥(Work.ThmF.ChV3.Sig H t P), w ≠ 1 →
      ∃ b : ℕ, Nat.card (Function.fixedPoints (act w)) = 2 ^ b + 1 := by
    intro w hw
    have hwG : (w : G) ≠ 1 := fun h => hw (Subtype.ext h)
    obtain ⟨hgrp, -⟩ := sigLemma2c hC4 hnil c h15.hQ0 (w := (w : G)) w.2 hwG
    have hle : Work.ThmF.ChV3.CQ Q P ⊓ Subgroup.centralizer ({(w : G)} : Set G) ≤
        Q ⊓ Subgroup.centralizer ({(w : G)} : Set G) := by
      intro x hx
      rw [Subgroup.mem_inf] at hx ⊢
      exact ⟨hx.1.1, hx.2⟩
    have hP2 : IsPGroup 2 ↥(Work.ThmF.ChV3.CQ Q P ⊓
        Subgroup.centralizer ({(w : G)} : Set G)) := hgrp.to_le hle
    obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hP2
    exact ⟨b, by rw [hfix w hw, hb]⟩
  -- ## The field arithmetic of step (8).
  obtain ⟨hprime, hcases⟩ :=
    fieldStep8 hA (orderOf (s * t)) hf35 hSigOdd hSigGt1 act hinj h2
  have hcardF : Nat.card F = Nat.card ↥(Work.ThmF.ChV3.CQ Q P) + 1 := by
    rw [hFcard, ← h15.hcq]
  refine ⟨hprime, ?_⟩
  rcases hcases with h | h | h
  · exact Or.inl (by rw [← hcardF, h])
  · exact Or.inr (Or.inl (by rw [← hcardF, h]))
  · exact Or.inr (Or.inr (by rw [← hcardF, h]))

end Work.ThmF.Prove
