/-
# `Work.ThreePoints.ThmC.hAprereq` — prerequisite `Prop`s for the §3 argument (`hAexists`)

`hAexists` (Peterfalvi I Ch. II §3, Steps 1–3) is proved from four hypotheses, each of which is
its own area theorem (`app4`, Ch. II §2 Lemma 1, Ch. II §2 Lemma 3, Ch. I §6 Prop. 2).  To let the
pieces of the argument be stated in separate modules (which cannot import `hAexists.lean` itself,
since the latter imports them), the four `Prop`s are named here.

They are verbatim the hypothesis types written in the statement of
`Work.ThreePoints.ThmC.hAexists` (file `hAexists.lean`), so a value of the former can be passed
where the latter is expected definitionally.
-/
import Mathlib
import Submission.Work.ThreePoints.ThmC.Defs
import Submission.Blueprint.Interfaces

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Work.ThreePoints.ThmC

open Submission.Blueprint

/-- Peterfalvi Appendix IV (Thompson–Bender), solvable form (hypothesis of `hAexists`). -/
abbrev App4Hyp : Prop :=
  ∀ (M : Type) [Group M] [Finite M] {p : ℕ}, p.Prime → p ≠ 2 → Group.IsSolvable M →
    ∀ {P X : Subgroup M}, IsPGroup p P →
      (∀ x : M, x ∈ Subgroup.centralizer (P : Set M) → orderOf x = p → x ∈ P) →
      Nat.Coprime (Nat.card X) p → P ≤ Subgroup.normalizer (X : Set M) →
      X ≤ Submission.Blueprint.pPrimeCore p M

/-- Peterfalvi I Ch. II §2 Lemma 1 (hypothesis of `hAexists`). -/
abbrev Lem1Hyp : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {H : Subgroup G},
    LeanEval.GroupTheory.Defs.IsStronglyEmbedded H → Submission.Blueprint.IsTwoTransitiveOn H →
    Submission.Blueprint.BrauerSuzukiProp → Submission.Blueprint.FeitThompsonProp →
    ∀ {g u : G}, g ∉ H → u ∈ Submission.Blueprint.involutions (H : Set G) →
    ∀ {p : ℕ} {P : Subgroup G}, p.Prime → p ≠ 2 →
    Work.ThreePoints.ThmC.IsSylowOf p P (Submission.Blueprint.twoPoint H g ⊓
      Submission.Blueprint.conj u (Submission.Blueprint.twoPoint H g)) →
    u ∈ Subgroup.normalizer (P : Set G) →
    Work.ThreePoints.ThmC.IsMaxP3 H p P ∧
    (Work.DoubleTransitivity.IsTwoTransitiveOnSub (Subgroup.normalizer (P : Set G))
        (Submission.Blueprint.fixedPts H P) ∧
      ∀ g₁ : G, P ≤ Submission.Blueprint.conj g₁ H →
        LeanEval.GroupTheory.Defs.IsStronglyEmbedded
          ((Subgroup.normalizer (P : Set G) ⊓ Submission.Blueprint.conj g₁ H).subgroupOf
            (Subgroup.normalizer (P : Set G)))) ∧
    (¬ Submission.Blueprint.HasFourGroup (Subgroup.normalizer (P : Set G)) →
      Work.ThreePoints.ThmC.IsSylowOf p P (Submission.Blueprint.twoPoint H g)) ∧
    (¬ Work.ThreePoints.ThmC.IsSylowOf p P
        (P ⊔ (Subgroup.centralizer (P : Set G) ⊓ Submission.Blueprint.twoPoint H g)) →
      ∀ x ∈ P, u * x = x * u)

/-- Peterfalvi I Ch. II §2 Lemma 3 (hypothesis of `hAexists`). -/
abbrev Lem3Hyp : Prop :=
  ∀ {F : Type} [Group F] [Finite F], Submission.Blueprint.FeitThompsonProp →
    Submission.Blueprint.GlaubermanZJProp → Submission.Blueprint.HasFourGroup F →
    ∀ {H : Subgroup F}, LeanEval.GroupTheory.Defs.IsStronglyEmbedded H →
    (∀ u v : F, u ∈ Submission.Blueprint.involutions (H : Set F) →
      v ∈ Submission.Blueprint.involutions (H : Set F) →
      u * v * u⁻¹ * v⁻¹ ∈ Submission.Blueprint.oddCore F) →
    ∀ {t : F}, orderOf t = 2 → t ∉ H → ∀ {p : ℕ} {R : Subgroup F}, p.Prime → p ≠ 2 →
    Work.ThreePoints.ThmC.IsSylowOf p R (Submission.Blueprint.twoPoint H t) →
    Submission.Blueprint.pPrimeCore p (Submission.Blueprint.twoPoint H t) = ⊥ →
    (∃ Q : Subgroup F, Q ≤ Submission.Blueprint.twoPoint H t ∧ IsPGroup p Q ∧
      ∃ u ∈ Submission.Blueprint.involutions (H : Set F),
        u ∈ Subgroup.normalizer (Q : Set F) ∧ ¬ ∀ x ∈ Q, u * x = x * u) →
    Submission.Blueprint.involutions (H : Set F) ⊆
      (Subgroup.normalizer (Submission.Blueprint.ZJ R : Set F) : Set F)

/-- Peterfalvi I Ch. I §6 Proposition 2 (hypothesis of `hAexists`). -/
abbrev Sec6Hyp : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {H : Subgroup G},
    LeanEval.GroupTheory.Defs.IsStronglyEmbedded H → Submission.Blueprint.FeitThompsonProp →
    Submission.Blueprint.ThmAProp → Submission.Blueprint.BrauerSuzukiProp →
    Submission.Blueprint.HasFourGroup G →
    ∀ {p : ℕ} {P : Subgroup G}, p.Prime → p ≠ 2 → Work.ThreePoints.ThmC.IsMaxP3 H p P →
    P ≤ H → ∀ {u : G}, u ∈ Submission.Blueprint.involutions (H : Set G) →
    u ∈ Subgroup.normalizer (P : Set G) → (∃ x ∈ P, u * x ≠ x * u) →
    ∃ s : G, orderOf s = 2 ∧ s ∉ H ∧ ∀ ω : G ⧸ H, s • ω = ω →
      Work.ThreePoints.ThmC.pPrimeCoreSub p (H ⊓ Submission.Blueprint.conj s H) ≤
        Work.ThreePoints.ThmC.pPrimeCoreSub p
          (MulAction.stabilizer G ω ⊓ H ⊓ Submission.Blueprint.conj s H)

end Work.ThreePoints.ThmC
