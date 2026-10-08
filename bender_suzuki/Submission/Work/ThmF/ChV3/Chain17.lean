import Submission.Work.ThmF.ChV3.Chain15
import Submission.Work.ThmF.Prove.step6
import Submission.Work.ThmF.Prove.step7Direct

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV3.Chain17` — the chain through §3 steps (6) and (7)

`ChV3/Chain15.lean` assembles steps (1)–(5).  This module adds the two consequences of steps
(6) and (7) that the rest of §3 consumes:

* `ker_eq_P_of_chain15` — **step (7)**, `Ker H Q P t = P`, proved by `Prove/step7Direct`
  directly from the near-field *field* input `NearFieldFieldProp` (App. XI Prop. 1 (2)b) — this
  is the lemma that breaks the (6)⇄(7) circularity recorded in `NOTES.md` §8.2: it does not use
  step (6)'s conclusion.
* `step6_of_chain15` — **step (6)**'s conclusion, `Prove/step6` applied with `h7` supplied by
  `ker_eq_P_of_chain15`.  Its hypotheses are those of `Prove/step6`, in particular the case
  assumption `oddPart Q = ⊥`.

Both are axiom-clean (only Mathlib axioms).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ThmF.ChV3

open Classical LeanEval.GroupTheory.Defs Submission.Blueprint

variable {G : Type} [Group G] [Finite G]

/-- **§3 step (7)** from the chain (1)–(5) and the near-field field input. -/
theorem ker_eq_P_of_chain15 {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (hFT : FeitThompsonProp) (hTh : ThompsonFrobeniusProp)
    (hNF : NearFieldAppXIProp) (hNFF : NearFieldFieldProp) (hC4 : ChIIFourProp)
    (hnil : Group.IsNilpotent ↥Q)
    (c : CtxF H Q t s r P) (h15 : Chain15 H Q t s r P) :
    Ker H Q P t = P :=
  Work.ThmF.Prove.step7Direct hFT hTh hNF hNFF hC4 hnil c h15.h1e
    ⟨h15.m, h15.R, h15.hm, h15.hf, h15.hNR, h15.hRc, h15.hRn, h15.hcardR, h15.hcq, h15.hfpf⟩
    h15.h4 h15.h5 h15.hm h15.hcq

/-- **§3 step (6)** from the chain (1)–(5), the case assumption `oddPart Q = ⊥`, and step (7). -/
theorem step6_of_chain15 (hA : Work.ThmF.ArithmeticNineTwoSeven) (hFT : FeitThompsonProp)
    (hTh : ThompsonFrobeniusProp) (hNF : NearFieldAppXIProp) (hC4 : ChIIFourProp)
    {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (c : CtxF H Q t s r P) (h15 : Chain15 H Q t s r P)
    (hQ1 : Work.ThmF.oddPart Q = ⊥) (h7 : Ker H Q P t = P) :
    (¬ IsMulCommutative ↥(CQ Q P) → Nat.card ↥(Sig H t P) = 1 ∨ Nat.card ↥(Sig H t P) = 3) ∧
    (IsMulCommutative ↥(CQ Q P) →
      (Nat.card ↥(CQ Q P) + 1 = orderOf (s * t) ∨ Nat.card ↥(CQ Q P) + 1 = 9) ∧
        Sig H t P = ⊥) :=
  Work.ThmF.Prove.step6 hA hFT hTh hNF hC4 c h15.h4 h15.h5 hQ1 h15.hf
    ⟨h15.m, h15.hm, h15.hcq⟩ h7

end Work.ThmF.ChV3
