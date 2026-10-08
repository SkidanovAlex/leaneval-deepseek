import Mathlib
import Submission.Work.PSU3.StageA.caseWbot_setup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.PSU3.StageA.BranchTwo.sq_mem_Q0sub`

Squares of elements of `Q` lie in `Q₀ = Q0sub H = ⟨Inv H⟩`.

## Route

The whole content is Peterfalvi II Ch. V §1, Corollary of Prop. 2: since `K = J(D,t)` is cyclic
(this is `Work.ThmF.ChV12.Ksub_cyclic_normal`, which consumes the odd order theorem
`FeitThompsonProp` for the solvable odd-order group `D`) and acts transitively on
`Inv H = Z(Q)♯`, the `2`-group `Q` is a **Suzuki `2`-group** — this is
`Work.PSU3.StageA.caseWbot_isSuzukiTwoGroup`, which needs only `PSU3Hyp`, `FeitThompsonProp`,
`ChIIFourProp` and `¬ IsAbelianSubgroup Q` (in particular *no* hypothesis on `W = C_V(K)`, so it
applies in every branch of the Ch. VI §1 case analysis).

Higman's Theorem 1 (`Work.Higman.higmanProp`) then gives that in a Suzuki `2`-group every square
is central, and that the centre is `Ω₁`; `Work.PSU3.StageA.caseWbot_center_subgroupOf` identifies
`Z(Q)` with `Q₀ = Q0sub H` (through Peterfalvi II Ch. V §1 Prop. 1 (c), i.e.
`Q0sub = {x ∈ Q | x² = 1}`, `caseC_Q0sub_subgroupOf_iff_sq`).

Note this argument makes no use of the Ch. VI §1 dichotomy `|Q| = q²` or `q³`: it holds in
*every* non-abelian branch. (The abelian case `Q = Q₀` is excluded by the hypothesis `hnab`; the
statement as requested does not cover it, and there it would be immediate anyway from
`Q0sub_elementary`.)
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.PSU3.StageA.BranchTwo

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

theorem sq_mem_Q0sub {G : Type} [Group G] [Finite G]
    {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hFT : Submission.Blueprint.FeitThompsonProp)
    (hnab : ¬ Submission.Blueprint.IsAbelianSubgroup Q) :
    ∀ x ∈ Q, x ^ 2 ∈ Work.ThmF.Q0sub H := by
  -- `Q` is a Suzuki `2`-group (Ch. V §1 Cor. of Prop. 2, using the odd order theorem)
  have hSuz : Submission.Blueprint.IsSuzukiTwoGroup ↥Q :=
    Work.PSU3.StageA.caseWbot_isSuzukiTwoGroup hS hFT hC4 hnab
  -- Higman: in a Suzuki `2`-group every square is central
  have hsq : ∀ x : ↥Q, x ^ 2 ∈ Subgroup.center ↥Q :=
    (Work.Higman.higmanProp ↥Q hSuz).2.1
  -- and the centre of `Q` is `Q0sub H`
  have hc : Subgroup.center ↥Q = (Work.ThmF.Q0sub H).subgroupOf Q :=
    Work.PSU3.StageA.caseWbot_center_subgroupOf hS hFT hC4 hnab
  intro x hx
  have hx' : ((⟨x, hx⟩ : ↥Q) ^ 2) ∈ (Work.ThmF.Q0sub H).subgroupOf Q := by
    rw [← hc]
    exact hsq ⟨x, hx⟩
  have h2 := Subgroup.mem_subgroupOf.mp hx'
  simpa [Subgroup.coe_pow, pow_two] using h2

end Work.PSU3.StageA.BranchTwo
