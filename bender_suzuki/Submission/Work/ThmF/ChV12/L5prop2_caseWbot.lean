import Mathlib
import Submission.Work.ThmF.ChV12.Lemma5Defs
import Submission.Work.ThmF.ChV12.L5Base
import Submission.Work.ThmF.ChV12.Ksub_cyclic_normal

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV12.L5prop2_caseWbot` — Ch. V §1 Prop. 2 in the case `V ≠ 1`, `W = 1`

Peterfalvi II Ch. V §1 Prop. 2 says that `K = J(D,t) = Kset H t` is a (cyclic, normal) subgroup
of `D = twoPoint H t`.  This file records the branch `V = centD H t ≠ ⊥`, `W = C_V(K) = ⊥` of
the proposition.

**Corrected 2026-10-05.**  The branch was previously requested *without* `FeitThompsonProp`; the
reviewers and the prover recorded that the source's route in this branch is

* `D̄ = D/W = D`, `A = F(D̄)`, App. X: `A` cyclic, fixed-point-free on `Q₀`, `D̄/A` abelian;
* Fitting's self-centralisation `C_D(A) = A`;

and that both need `D` of odd order to be **solvable**, i.e. `FeitThompsonProp`
(`Work.ThmF.Tools.appX`).  `ChIIFourProp` handles the two other branches
(`V = ⊥`: `L5prop2.Ksub_eq_Kset_of_centD_bot`; `W ≠ ⊥`: `L5prop2.Ksub_eq_Kset_of_W_ne_bot`), and
in the branch `V ≠ ⊥`, `W = ⊥` its P3 clause is unusable (taking `X = W` is impossible since
`W = ⊥`), as the reviewer's argument shows.

With `hFT` the branch is immediate from `Work.ThmF.ChV12.Ksub_cyclic_normal`.
`Work.ThmF.ChV12.L5prop2` no longer routes through this file (it calls `Ksub_cyclic_normal`
directly), so it is kept only for the consumers that import it (`PSU3/StageA/not_caseA.lean`),
which therefore also have to thread `FeitThompsonProp` — they have it, being given it by the
assembly.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ThmF.ChV12

theorem L5prop2_caseWbot {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s : G}
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC4 : Submission.Blueprint.ChIIFourProp)
    (h : Work.ThmF.Lemma5.Hyp5 H Q t s) (hV : Submission.Blueprint.centD H t ≠ ⊥)
    (hW : Work.ThmF.W H t = ⊥) :
    (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t :=
  (Work.ThmF.ChV12.Ksub_cyclic_normal hFT hC4 h.sit h.split).2.1

end Work.ThmF.ChV12
