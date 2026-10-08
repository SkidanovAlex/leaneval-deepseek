import Mathlib
import Submission.Work.ThmG.Defs
import Submission.Work.FeitSibley.ThmGBridge.vanishesOffProp_of_fsdata
import Submission.Work.ThmG.nilpotent_of_K_ne_one
import Submission.Work.ThmG.nilpotent_two_odd_split
import Submission.Work.ThmG.rankOne_isTI
import Submission.Work.ThreePoints.BenderPrelim

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.BSIntegrate.vanishesOffProp`

Peterfalvi II, Appendice XII, Lemme 2 (a) — field 8 (`Work.ThmG.VanishesOffProp`) of the split
rank-one structure: every `χ ∈ 𝒮 = {χ ∈ Irr H | O_{2'}(Q) ⊄ ker χ}` vanishes outside `Q` — in
the form in which the assembly of Theorem G consumes it.

The hypotheses of the request are exactly the area `Prop`s already available:
`ChIIFourProp` (Peterfalvi I Ch. II §4) and `ThompsonFrobeniusProp` are used to obtain the
nilpotency of `Q` (Ch. V §1 Prop. 1 b), `FpfOddPartProp` is the fixed-point-freeness of `D`
on `O_{2'}(Q)` (Ch. V §2 Lemma 2 c) and `CoprimeDQProp` is `(|D|,|Q|) = 1` (Ch. I).

The degenerate case `O_{2'}(Q) = ⊥` is vacuous: `excludingKernel H ⊥` is empty
(`𝒮` needs a `χ` which is non-trivial on a non-trivial element of `O_{2'}(Q)`), cf. the audit
item **D1** (`Submission/Work/_audit/DegreeFalse1008.lean`).  In the remaining case the
Feit–Sibley bridge `Work.FeitSibley.ThmGBridge.vanishesOffProp_of_fsdata` applies with

* `Q` T.I. (`Work.ThmG.rankOne_isTI`, from the 2-transitivity of the split rank-one
  situation),
* `D = H ⊓ Hᵗ` of odd order (definition of strong embeddedness, `t ∉ H`),
* `Q` nilpotent (`Work.ThmG.nilpotent_of_K_ne_one` with `K = J(D,t) ≠ 1`,
  `Work.ThreePoints.kNeOneProp`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Work.BSIntegrate

open Submission.Blueprint

theorem vanishesOffProp (hC4 : Submission.Blueprint.ChIIFourProp) (hTh : Submission.Blueprint.ThompsonFrobeniusProp) (hFpf : Work.ThmG.FpfOddPartProp) (hCop : Work.ThmG.CoprimeDQProp) : Work.ThmG.VanishesOffProp := by
  intro G _ _ H Q t hh chi hchi h hQ
  -- the split rank-one datum underlying `hh`
  have hsplit : Submission.Blueprint.IsSplitRankOne H Q t := hh.2.2.1
  by_cases hQ1 : Work.ThmG.oddPart Q = ⊥
  · -- `O_{2'}(Q) = 1`: the set `𝒮` is empty
    rw [hQ1, Submission.Blueprint.excludingKernel, Finset.mem_filter] at hchi
    rcases hchi with ⟨-, x, hx, hxne⟩
    rw [Subgroup.mem_bot] at hx
    exact (hxne (by rw [show x = (1 : ↥H) from Subtype.ext hx])).elim
  · -- `Q` is T.I. (from the 2-transitivity of the split rank-one situation)
    have hQT : ∀ x : G, x ∉ H → Q ⊓ Submission.Blueprint.conj x Q = ⊥ :=
      Work.ThmG.rankOne_isTI hsplit
    -- `D = H ⊓ Hᵗ` has odd order (strong embeddedness, `t ∉ H`)
    have hDodd : Odd (Nat.card (Submission.Blueprint.twoPoint H t)) :=
      hsplit.stronglyEmbedded.2.2 t hsplit.not_mem
    -- `Q` is nilpotent: Ch. V §1 Prop. 1 b) with `K = J(D,t) ≠ 1`
    have hQnil : Group.IsNilpotent Q :=
      Work.ThmG.nilpotent_of_K_ne_one hh.1 hC4 hTh hsplit
        (Work.ThreePoints.kNeOneProp G H Q t hh)
    -- Feit–Sibley, Appendice XII Lemme 2 (a)
    exact Work.FeitSibley.ThmGBridge.vanishesOffProp_of_fsdata H Q t hh hQT hDodd hQnil hQ1
      (hFpf G H Q t hh) (hCop G H Q t hh) chi hchi h hQ

end Work.BSIntegrate
