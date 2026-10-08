/-
Copyright (c) 2024. All rights reserved.

# Area `Higman` — public interface

One import for everything another area needs from Higman (1963), *Suzuki 2-groups*,
`REFS/higman_suzuki2groups.md`.

```lean
import Submission.Work.Higman.Interface
```

## The deliverable

* `Work.Higman.higmanProp : Submission.Blueprint.HigmanProp`
  — the blueprint `Prop` itself, with **no side hypothesis**.
  Shape used by the other areas: `Work.Higman.higman (hFT : FeitThompsonProp) : HigmanProp`
  (`hFT` is unused; this area does not need the odd order theorem).
* `Work.Higman.higmanQ3Prop : Work.Higman.HigmanQ3Prop`
  — **the order-`q³` extension**: Higman's Theorem 1, types `B`/`C`/`D`, in the vocabulary of
  `Submission.Blueprint.IsSuzukiTwoGroup`.  (The blueprint `HigmanProp` stops at
  `|P| ∈ {q², q³}` plus the `q²`-case `A(n,θ)`; `HigmanQ3Prop` is the missing column.)
* `Work.Higman.higmanClass : Work.Higman.HigmanClassProp` where
  `HigmanClassProp = Submission.Blueprint.HigmanProp ∧ HigmanQ3Prop`
  (`Submission/Work/Higman/Class.lean`), with
  `Work.Higman.higmanProp_of_classProp : HigmanClassProp → Submission.Blueprint.HigmanProp`.

All of these are axiom-clean — `Submission/Work/Higman/Verify.lean` prints
`[propext, Classical.choice, Quot.sound]` for each (and fixes their types by `example`s).

## The six clauses of `Submission.Blueprint.HigmanProp`, by module

| clause | name | module |
|---|---|---|
| A1 `Z(P) = Ω₁(P)` | `Work.Higman.center_eq_omega1_new` | `Submission.Work.Higman.center_eq_omega1_new` |
| A2 `∀ x, x² ∈ Z(P)` | `Work.Higman.sq_mem_center` | `Submission.Work.Higman.sq_mem_center` |
| A3 `P' = Z(P)` | `Work.Higman.commutator_eq_center` | `Submission.Work.Higman.commutator_eq_center` |
| A4 `|P| = q² ∨ q³` | `Work.Higman.card_eq_sq_or_cube` | `Submission.Work.Higman.card_eq_sq_or_cube` |
| A5 `|P| = q² ⇒ A(n,θ)` | `Work.Higman.type_A_classification` | `Submission.Work.Higman.type_A_classification` |
| A6 `|P| = q³ ⇒ B/C/D` | `Work.Higman.type_B_C_D_classification` | `Submission.Work.Higman.type_B_C_D_classification` |

## Other public results

* **Models**: `Work.Higman.AType_isSuzukiTwoGroup`, `AType_center`, `AType_omega1`
  (`A(n,θ)` really is a Suzuki 2-group).
* **Type-`B` layer criterion** (ThmF Ch. V §2 Lemma 6, PSU3's A6): definitions
  `Work.Higman.IsXiLayer`, `IsTypeB`, `FpfXi` (`Submission/Work/Higman/typeB.lean`) and
  `Work.Higman.layers_card_dichotomy` (D1), `Work.Higman.typeB_scalar` (D2),
  `Work.Higman.typeB_of_odd_fpf` (D3).
* **Higman's Lemma 8** (the `C₄` exclusion core): `Work.Higman.higman_lemma8`,
  `Work.Higman.MSA.lemma8_clean`.
* **Higman's Lemma 9/13**: `Work.Higman.lemma9_maximal_abelian`,
  `Work.Higman.NSM.higmanLemma13` (`|P| ≤ |Z(P)|³`),
  `Work.Higman.NSM.noSquareMaximal`, `Work.Higman.NSM.deepSquareCase`.
* **Cocycles of the four types**: `Work.Higman.Family.aCocycle`/`bCocycle`/`cCocycle`/`dCocycle`
  and `AType`/`BType`/`CType`/`DType`.
-/

import Submission.Work.Higman.Main
import Submission.Work.Higman.typeB
import Submission.Work.Higman.typeB_of_odd_fpf
import Submission.Work.Higman.layers_card_dichotomy
import Submission.Work.Higman.typeB_scalar

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end
