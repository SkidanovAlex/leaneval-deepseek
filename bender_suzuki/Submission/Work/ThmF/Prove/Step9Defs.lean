import Submission.Work.ThmF.ChV3.Ctx
import Submission.Work.ThmF.Tools.External

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.Prove.Step9Defs` — step (9)'s input/output abbreviations

The lead's pass-13 design (`Submission/Work/NOTES_LEAD_bs_pass13.md`,
`ThmF/_design13/ThmF13Step9.lean`) records step (3)'s and step (8)'s outputs as the named `Prop`s
`Step3Out` and `Step8Out`, so that the leaves of step (9) can be stated against them.  They are
verbatim `Prove.step3`'s and `Prove.step8`'s conclusions.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs Submission.Blueprint

namespace Work.ThmF.Prove

/-- Step (3)'s output (`Work.ThmF.Prove.step3`), verbatim. -/
def Step3Out {G : Type} [Group G] (Q P : Subgroup G) : Prop :=
  ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ Nat.card ↥(Work.ThmF.oddPart Q) →
    (∃ i < Nat.card P, ℓ ≡ 2 ^ i [MOD 2 ^ Nat.card P - 1]) ∧ ℓ ≠ Nat.card P

/-- Step (8)'s output (`Work.ThmF.Prove.step8`), verbatim (`h8` of `Prove/step9Divisibility`). -/
def Step8Out {G : Type} [Group G] (H Q : Subgroup G) (t : G) (P : Subgroup G) : Prop :=
  Work.ThmF.ChV3.Sig H t P ≠ ⊥ → (Nat.card ↥(Work.ThmF.ChV3.Sig H t P)).Prime ∧
    (Nat.card ↥(Work.ThmF.ChV3.CQ Q P) + 1 = 3 ^ Nat.card ↥(Work.ThmF.ChV3.Sig H t P) ∨
     Nat.card ↥(Work.ThmF.ChV3.CQ Q P) + 1 = 5 ^ Nat.card ↥(Work.ThmF.ChV3.Sig H t P) ∨
     Nat.card ↥(Work.ThmF.ChV3.CQ Q P) + 1 = 9 ^ Nat.card ↥(Work.ThmF.ChV3.Sig H t P))

end Work.ThmF.Prove
