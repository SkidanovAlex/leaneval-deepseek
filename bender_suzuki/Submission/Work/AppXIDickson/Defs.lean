import Submission.Work.ThmF.ChV3.AppXI
import Submission.Work.ThmF.ChV3.NearField
import Submission.Work.ThmF.ChV3.Ctx

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.AppXIDickson.Defs` — the vocabulary of Appendix XI Prop. 2 (BS pass 17, Brief 6)

This is the *Dickson* area of the App. XI reduction: the arithmetic half of Appendix XI Prop. 2
(a finite field with an involutive automorphism `σ ≠ 1` whose unit group has a `σ`-fixed subgroup
of odd order `c` with `|K| = 8c + 1` has `c = 1`), the structure of a non-abelian `C_Q(P)`
(`C_Q(P) = T × C`, `T` of order `8`, `C` odd cyclic) and the assembly
`AppXIProp2` from those two (Peterfalvi II Ch. V §3 step (5)).

The two `Prop`s of the standing context are *copied verbatim* from the lead's pass-17 design file
`Submission/Work/_design17/ThmF17_AppXI.lean` (namespace `Design17.XI`), so that this area is
self-contained: modules of this directory import only delivered fleet files, never the design file.

* `NearFieldAppXIPropPlus` (design `Design17.XI.NearFieldAppXIPropPlus`) — App. III (2) plus
  `[R,R] ≤ N`; the input of the whole App. XI reduction.
* `NearFieldAppXIProp` (delivered, `Work.ThmF.ChV3.NearFieldAppXIProp`) — the step-(2) shadow,
  which is a conjunct-for-conjunct *weakening* of `NearFieldAppXIPropPlus`; the bridge is
  `NearFieldAppXIPropPlus.toShadow` below.
* `AppXIProp2` (delivered, `Work.ThmF.ChV3.AppXIProp2`) — the target of this area: in the standing
  context of §3, a non-abelian `C_Q(P)` has order `8`.

Statements of the area (all in namespace `Work.AppXIDickson`):

| module | name |
|---|---|
| `AppXIDickson.CardEqOne` | `card_eq_one_of_dickson` (B1) |
| `AppXIDickson.CqNoncommStructure` | `cq_noncomm_structure` (B2) |
| `AppXIDickson.FieldOfFreeCommAction` | `field_of_free_comm_action` (L0) |
| `AppXIDickson.DicksonStep` | `dickson_step` (L0 + B1) |
| `AppXIDickson.NearFieldQuotient` | `nearField_quotient_data` (`V = R/N`) |
| `AppXIDickson.AppXI2` | **`appXIProp2_of`** (the deliverable) |
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.AppXIDickson

open Classical LeanEval.GroupTheory.Defs Submission.Blueprint

open Work.ThmF.ChV3 (CtxF CQ Ker NearFieldAppXIProp)

/-- **App. III (2) + `[R,R] ≤ N`.**  The step-(2) shadow plus the clause that the preimage `R` of
the near-field is abelian modulo `N`; this is the part of App. III (2) that App. XI Prop. 2 (and
hence `AppXIProp2`) consumes (`V = R/N` must be an abelian group).  Verbatim copy of
`Design17.XI.NearFieldAppXIPropPlus`. -/
def NearFieldAppXIPropPlus : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H Q : Subgroup G) (t s r : G) (P : Subgroup G),
    CtxF H Q t s r P →
    ∃ (m : ℕ) (R N : Subgroup G), N = Ker H Q P t ∧
      1 ≤ m ∧ (orderOf (s * t)).Prime ∧ N ≤ R ∧
      R ≤ Subgroup.centralizer (P : Set G) ∧
      Subgroup.centralizer (P : Set G) ≤ Subgroup.normalizer (R : Set G) ∧
      Subgroup.centralizer (P : Set G) ≤ Subgroup.normalizer (N : Set G) ∧
      Nat.card R = Nat.card N * orderOf (s * t) ^ m ∧
      Nat.card ↥(CQ Q P) + 1 = orderOf (s * t) ^ m ∧
      (∀ x ∈ R, x ∉ N → ∀ y ∈ CQ Q P, y * x * y⁻¹ * x⁻¹ ∈ N → y = 1) ∧
      (∀ x ∈ R, ∀ y ∈ R, x * y * x⁻¹ * y⁻¹ ∈ N)

/-- `NearFieldAppXIPropPlus` is a strengthening of the delivered step-(2) shadow: drop the
commutator clause. -/
theorem NearFieldAppXIPropPlus.toShadow (h : NearFieldAppXIPropPlus) : NearFieldAppXIProp := by
  intro G _ _ H Q t s r P c
  obtain ⟨m, R, N, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, -⟩ := h G H Q t s r P c
  exact ⟨m, R, N, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

end Work.AppXIDickson
