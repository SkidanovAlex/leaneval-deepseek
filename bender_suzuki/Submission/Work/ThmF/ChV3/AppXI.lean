import Submission.Work.ThmF.ChV3.NearField

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV3.AppXI` — the Appendix XI inputs of Ch. V §3

Peterfalvi II Ch. V §3 quotes Appendix XI (pp. 284–286) twice:

* **Prop. 1** (the near-field): `(C_G(P), C_H(P)) ∈ 𝓕` has a kernel `N` and
  `C_G(P)/N = (F ⋊ C_Q(P)) ⋊ Σ` for a near-field `F`, `C_Q(P) ≅ F^*`.  Only its group-theoretic
  and numeric shadow is used by the rest of §3; it is recorded as `NearFieldAppXIProp`
  (`ChV3/NearField.lean`), the input of step (2).

* **Prop. 2** (the structure of the near-field `F`): if `F^*` has a cyclic subgroup of index `2`,
  then `F` is isomorphic to the Dickson near-field `F_{r²,2}`.  Step (5) reads off from it (and
  from the previously established structure of `C_Q(P)` as a Frobenius complement) that when
  `C_Q(P)` is **non-abelian** one has `|C_Q(P)| = 8` — equivalently `F ≅ F_{9,2}`, `r = 3`.

Since no near-field is built in this workspace (per the project lead, Appendices X–XI are not to be
proved yet), Prop. 2 is recorded here as the named input `AppXIProp2` **in the exact form step (5)
consumes**: for the standing context of §3, a non-abelian `C_Q(P)` has order `8`.

The proof (source, p. 249): `Q` is nilpotent and `C_S(P)` is a non-abelian Sylow `2`-subgroup of
`C_Q(P)` with 2-rank `1`, hence quaternion of order `8`; `C_Q(P) ≅ F^*` then has a cyclic subgroup
of index `2`, so `F ≅ F_{r²,2}` and `|Z(F^*)| = r - 1` (App. XI Prop. 2); from the structure of
`C_Q(P)`, `|F^*/Z(F^*)| = 4 = r + 1`, hence `r = 3` and `|C_Q(P)| = |F^*| = 8`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ThmF.ChV3

open Submission.Blueprint

/-- **App. XI Prop. 2, in the form Ch. V §3 step (5) consumes it.**  In the standing context of
§3, a non-abelian `C_Q(P)` has order `8` (i.e. the near-field is `F_{9,2}`). -/
def AppXIProp2 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G},
    CtxF H Q t s r P → ¬ IsMulCommutative ↥(CQ Q P) → Nat.card ↥(CQ Q P) = 8

end Work.ThmF.ChV3
