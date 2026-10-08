import Mathlib
import Submission.Work.ThmF.ChV3.Step16Step12
import Submission.Work.ThmF.ChV3.Step16Step17

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV3.Step16ChainTail` — the (10-1)/(10-2) dichotomy closes §3

The lead's pass-16 design (`ThmF/_design16/ThmF16.lean`, `chain_tail`): given the chain's outputs up
to step (11) and step (10)'s dichotomy, the context is contradictory — (10-1) by `step12`, (10-2)
by `step17`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs Submission.Blueprint

namespace Work.ThmF.ChV3

open Work.ThmF

variable {G : Type} [Group G] [Finite G]

/-- **The (12)/(17) split.** -/
theorem chain_tail (hFT : FeitThompsonProp) (hC4 : ChIIFourProp) (hHW : HallWielandtProp)
    {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (c : CtxF H Q t s r P) (h15 : Chain15 H Q t s r P) (h7 : Ker H Q P t = P)
    (hpf : Nat.card P = orderOf (s * t)) {T : Subgroup G} (h11 : Step11Out H Q t P h15.R T)
    (h6 : oddPart Q = ⊥ → IsMulCommutative ↥(CQ Q P) → Sig H t P = ⊥)
    (h8 : oddPart Q ≠ ⊥ → Work.ThmF.Prove.Step8Out H Q t P)
    (hH : Nat.card ↥H = Nat.card Q * Nat.card ↥(twoPoint H t))
    (hD : Nat.card ↥(twoPoint H t) = (2 ^ Nat.card P - 1) * Nat.card ↥(W H t) * Nat.card P)
    (hQ : ¬ Nat.card P ∣ Nat.card Q)
    (hSigW : ¬ Nat.card P ∣ Nat.card ↥(Sig H t P) → ¬ Nat.card P ∣ Nat.card ↥(W H t))
    (hWcyc : Nat.card P ∣ Nat.card ↥(Sig H t P) → IsCyclic ↥(W H t))
    (h10 : Case101 H t P h15.m ∨
      (Nat.card P = 3 ∧ Nat.card ↥(Sig H t P) = 3 ∧ Nat.card ↥(CQ Q P) = 8 ∧
        (Nat.card ↥(W H t) = 3 ∨ Nat.card ↥(W H t) = 9) ∧
        pPart 3 (Nat.card G) = 3 ^ 4 * Nat.card ↥(W H t))) : False := by
  rcases h10 with h101 | ⟨hp3, hs3, hc8, hW, hG3⟩
  · exact step12 hFT hC4 hHW c h15 h7 hpf h11 h6 h8 hH hD hQ hSigW h101
  · refine step17 hFT hC4 hHW c h15 h7 hpf h11
      ⟨hp3, hs3, hc8, hW, hG3, by rw [← hpf, hp3], hWcyc (by rw [hp3, hs3])⟩

end Work.ThmF.ChV3
