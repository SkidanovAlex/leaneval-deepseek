import Submission.Work.Step7Comm.Defs
import Submission.Work.Step7Comm.Basic
import Submission.Work.Step7Comm.isElementaryAbelianTwo_Q0sub
import Submission.Work.Step7Comm.isPGroup_two_CQ_of_mem_SigCQ
import Submission.Work.Step7Comm.commCQCase_of_arithmetic
import Submission.Work.Step7Comm.trichotomy_at_mem_W
import Submission.Work.Step7Comm.false_of_commCQCase
import Submission.Work.ThmF.ChV12.L6basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Step7Comm.sig_inf_centralizer_CQ_eq_bot_of_comm`

**Peterfalvi II, Ch. V §3, step (7), commutative branch, directly from the arithmetic input.**

In the standing context `CtxF H Q t s r P` of §3, with `Q` nilpotent, `C_Q(P)` abelian, and the
steps (1)–(5) of the chain in hand (`h15 : Chain15`), the arithmetic input `ArithmeticNineTwoSeven`
([HB] IX (2-7)) gives

`Σ ⊓ C_G(C_Q(P)) = 1`,  where `Σ = C_W(P)`.

This is the direct substitute for App. XI Prop. 1 (2)b) in the design's step (7)
(`Prove/step7DirectComm.lean`, which *assumes* `NearFieldFieldProp` — the very statement being
proved).  See `Defs.lean` for the case analysis; the pieces it is assembled from are
`isPGroup_two_CQ_of_mem_SigCQ`, `commCQCase_of_arithmetic`, `trichotomy_at_mem_W` and
`false_of_commCQCase`.

`hFT` is part of the interface (the caller threads it); step (1) already enters through `h15`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

open Classical LeanEval.GroupTheory.Defs Submission.Blueprint

namespace Work.Step7Comm

open Work.ThmF.ChV3 Work.ThmF

/-- **Peterfalvi II, Ch. V §3, step (7): the commutative branch of the crux `Σ ⊓ C_G(C_Q(P))`,
proved from the arithmetic input `ArithmeticNineTwoSeven` — no near-field/App. XI input.** -/
theorem sig_inf_centralizer_CQ_eq_bot_of_comm {G : Type} [Group G] [Finite G]
    {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (hA : Work.ThmF.ArithmeticNineTwoSeven) (hFT : FeitThompsonProp)
    (hC4 : ChIIFourProp) (hnil : Group.IsNilpotent ↥Q)
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) (h15 : Work.ThmF.ChV3.Chain15 H Q t s r P)
    (hcomm : IsMulCommutative ↥(Work.ThmF.ChV3.CQ Q P)) :
    Work.ThmF.ChV3.Sig H t P ⊓
      Subgroup.centralizer ((Work.ThmF.ChV3.CQ Q P : Subgroup G) : Set G) = ⊥ := by
  classical
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  by_contra hx1
  -- `K = Σ ⊓ C_G(C_Q(P))` is nontrivial, hence contains an element of prime order.
  have hKne : SigCQ H t Q P ≠ ⊥ := by
    intro hbot
    exact hx1 (by
      have hmem : x ∈ (⊥ : Subgroup G) := hbot ▸ hx
      exact Subgroup.mem_bot.mp hmem)
  have hcardK : Nat.card ↥(SigCQ H t Q P) ≠ 1 := fun h1 =>
    hKne (Subgroup.card_eq_one.mp h1)
  obtain ⟨p, hpprime, hpdvd⟩ := Nat.exists_prime_and_dvd hcardK
  haveI : Fact p.Prime := ⟨hpprime⟩
  haveI : Fintype ↥(SigCQ H t Q P) := Fintype.ofFinite _
  have hpdvd' : p ∣ Fintype.card ↥(SigCQ H t Q P) := by
    rwa [← Nat.card_eq_fintype_card]
  obtain ⟨g, hgorder⟩ := exists_prime_orderOf_dvd_card p hpdvd'
  set w : G := (g : G) with hwdef
  have hw : w ∈ SigCQ H t Q P := g.2
  have hworder : orderOf w = p := (Subgroup.orderOf_coe g).trans hgorder
  have hwprime : (orderOf w).Prime := by rw [hworder]; exact hpprime
  have hw1 : w ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hworder
    exact hpprime.ne_one hworder.symm
  have hwSig : w ∈ Work.ThmF.ChV3.Sig H t P := (Subgroup.mem_inf.mp hw).1
  have hwW : w ∈ Work.ThmF.W H t := (Subgroup.mem_inf.mp hwSig).1
  have hwC : w ∈ Subgroup.centralizer
      ((Work.ThmF.ChV3.CQ Q P : Subgroup G) : Set G) := (Subgroup.mem_inf.mp hw).2
  -- step (7), first move: `C_Q(P)` is a `2`-group and `f = o(st) ∈ {3,5}`.
  obtain ⟨hCQ2, hf35⟩ := isPGroup_two_CQ_of_mem_SigCQ hC4 hnil c h15.hQ0 (w := w) hw hw1
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨b, hCQcard⟩ := hCQ2.exists_card_eq
  -- the arithmetic lemma on `f^m = |C_Q(P)| + 1 = 2^b + 1`.
  have hcases : CommCQCase (orderOf (s * t)) (Nat.card ↥(Work.ThmF.ChV3.CQ Q P)) :=
    commCQCase_of_arithmetic hA h15.hm hf35 h15.hcq hCQcard
  -- `Q` is a `2`-group (step (4)).
  have hQ2 : IsPGroup 2 ↥Q := by
    refine IsPGroup.of_card (n := b * Nat.card P) ?_
    rw [h15.h4, hCQcard, pow_mul]
  -- §2 Lemma 2 (c) at the prime-order subgroup `⟨w⟩`.
  have htri := trichotomy_at_mem_W hC4 c hQ2 h15.hQ0 (w := w) hwW hwprime
  -- the structural inputs of the case analysis
  have hQ0leC := Q0sub_le_centralizer_singleton_of_mem_W c hC4 hwW
  have hQ0leQ : Work.ThmF.Q0sub H ≤ Q := Work.ThmF.ChV12.Q0sub_le_Q c.split
  have helQ0 : IsElementaryAbelianTwo (Work.ThmF.Q0sub H) :=
    isElementaryAbelianTwo_Q0sub c hC4
  exact false_of_commCQCase c h15 hcomm hwW hw1 hwC hQ0leC hQ0leQ helQ0 hcases htri

/-- The same statement in the area's own notation (`SigCQ`). -/
theorem SigCQ_eq_bot_of_comm {G : Type} [Group G] [Finite G]
    {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (hA : Work.ThmF.ArithmeticNineTwoSeven) (hFT : FeitThompsonProp)
    (hC4 : ChIIFourProp) (hnil : Group.IsNilpotent ↥Q)
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) (h15 : Work.ThmF.ChV3.Chain15 H Q t s r P)
    (hcomm : IsMulCommutative ↥(Work.ThmF.ChV3.CQ Q P)) :
    SigCQ H t Q P = ⊥ :=
  sig_inf_centralizer_CQ_eq_bot_of_comm hA hFT hC4 hnil c h15 hcomm

end Work.Step7Comm
