import Submission.Work.ZassenhausSuzuki.QSZPrelim

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `|D| + 1 = |Z(Q)|`

Second half of L2 (`twoPoint_cyclic`) of the lead's design note
`NOTES_LEAD_probe1630.md`, in the form in which it is used:

* `twoPoint_card_eq_involutions` (`|D| = #Inv(Q)`, Suzuki Prop. 3) supplies the left-hand side;
* `HigmanProp` supplies `Z(Q) = {z | z ^ 2 = 1}`, i.e. `Z(Q) = {1} ∪ Inv(Q)`.

Hence `|D| + 1 = |Z(Q)|`; with `Q ≅ A(n,θ)` this reads `|D| = 2ⁿ - 1`, which is the
cardinality input of Suzuki 1962, Lemma 6 (`SuzukiLemma6Prop`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausSuzuki

-- The canonical (and stronger) form of `|D| + 1 = |Z(Q)|` — without the `HigmanProp`
-- hypothesis, via `Work.Higman.Invol` — is
-- `Work.ZassenhausSuzuki.twoPoint_card_add_one_eq_center_card` in `QSZPrelim.lean`.

end Work.ZassenhausSuzuki
