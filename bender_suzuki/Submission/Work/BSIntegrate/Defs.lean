import Submission.Work.ThmG2.Defs
import Submission.Blueprint.Interfaces
import Submission.Work.ThmF.Tools.External
import Submission.Work.BSHallW.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.BSIntegrate` — integration of the Bender–Suzuki areas: vocabulary

This area owns the **end-to-end composition** of the Bender–Suzuki proof: one module that imports
every area and states the challenge from `FeitThompsonProp` plus the remaining named inputs.  See
`Submission/Work/_audit/AUDIT_bs_chain_1008.md` (the end-to-end chain audit) and
`Submission/Work/BSIntegrate/Composed.lean` for the composition itself.

## The audit's ten unproduced inputs

`bender_suzuki_composed` (`Composed.lean`) takes exactly the inputs below.  The two marked
*corrected* are the D1/D2 restatements of the audit: the on-disk statements
`Work.ThmG.DegreeProp` (D1) and `Work.ThmF.HallWielandtProp` (D2) are **false as stated**, and the
corrected forms are the ones that will be proved.

| input | statement | producer |
|---|---|---|
| `Work.ThmF.WielandtFixedPoint` | Huppert–Blackburn XI (12.4), fixed-point form | literature (BSLit) |
| `Work.BSHallW.HallWielandtOddProp` | *corrected* (D2) Hall–Wielandt, `p ≠ 2` | `BSHallW` |
| `Work.ThmF.ArithmeticNineTwoSeven` | Huppert–Blackburn IX (2-7) | literature (BSLit) |
| `Work.ThmF.ChV3.NearFieldFullAppXIProp` | App. XI Prop. 1 (+ exponent clause) | literature (BSLit) |
| `Work.ThmF.ChV3.AppXIProp2` | App. XI Prop. 2 | literature (BSLit) |
| `Work.ThmF.ChV3.NearFieldFieldProp` | App. XI, near-field is a field | literature (BSLit) |
| `Submission.Blueprint.BenderModelFacts2Prop` | Peterfalvi I §5, model facts (2) | `Models` |
| `Work.ThmG2.ExistsLinearV2Prop` | Ch. VI §1, a linear `λ` with `QK ⊆ ker λ` | `ThmF`/`FeitSibley` |
| `Work.BSIntegrate.DegreeProp'` | *corrected* (D1) App. XII (3)–(4) | `FeitSibley` |
| `Work.ThmG.VanishesOffProp` | App. XII Lemma 2 (a) | `FeitSibley` |

**D1.**  `Work.ThmG.DegreeProp` quantifies over every `RankOneHyp` instance, but the premise holds
for `PSU(3,2ⁿ)` with its Borel, where `oddPart Q = ⊥` and `excludingKernel H ⊥ = ∅`: no `χ`
exists.  The honest statement (and the one App. XII (3)–(4) gives) carries the extra hypothesis
`¬ IsPGroup 2 Q`; that is `DegreeProp'` below.  The assembly of Theorem G that *consumes*
`DegreeProp'` is `Work.BSIntegrate.thmG3` (`ThmG3.lean`): it builds the rank-one structure `after`
the `by_contra hnotp : ¬ IsPGroup 2 Q`, exactly as `Work.ThmG2.thmG2` does.

**D2.**  `Work.ThmF.HallWielandtProp` is false at `p = 2` (`G = PSL(2,7)`, `A = C₄ ≤ S = D₈`
abelian and weakly closed, but `G` has no normal subgroup of index `2` while `N_G(A) ≅ S₄` does).
The corrected form is `Work.BSHallW.HallWielandtOddProp` (area `BSHallW`), which adds `p ≠ 2`;
every use in the ThmF chain is at an odd prime (`p ∣ |V|`, `V ≤ D` odd).

## What to import

`Submission.Work.BSIntegrate.Composed` (and hence `Work.BSIntegrate.bender_suzuki_composed`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Work.BSIntegrate

open Submission.Blueprint

/-- **D1-corrected Field 7 of `RankOneStructure2`** (Peterfalvi, App. XII (3)–(4)).

`Work.ThmG.DegreeProp` with the extra hypothesis `¬ IsPGroup 2 Q`.  This is necessary: for
`G = PSU(3,2ⁿ)` with its Borel `H = Q ⋊ D` (an instance of `RankOneHyp`) the subgroup `Q` is a
`2`-group, `oddPart Q = ⊥`, and `excludingKernel H ⊥` is empty, so no character `χ` can exist
(`Submission/Work/_audit/DegreeFalse1008.lean`).

The conclusion is unchanged: `𝒮 = excludingKernel H (Work.ThmF.oddPart Q)` contains a character
`χ` of
degree `|D|` (`D = twoPoint H t`) and every degree in `𝒮` is a multiple of `χ 1`. -/
def DegreeProp' : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (H Q : Subgroup G) (t : G),
    Work.ThmG.RankOneHyp G H Q t → ¬ IsPGroup 2 Q →
    ∃ χ ∈ excludingKernel H (Work.ThmF.oddPart Q), χ 1 = (Nat.card (twoPoint H t) : ℂ) ∧
      ∀ ψ ∈ excludingKernel H (Work.ThmF.oddPart Q), ∃ a : ℕ, ψ 1 = (a : ℂ) * χ 1

/-- The *uncorrected* `Work.ThmG.DegreeProp` implies the corrected `DegreeProp'` (weaken the
hypotheses).  The converse is false (D1), so this is the only direction available; it is recorded
so that a caller who has the (false, but usable if derived from something else) uncorrected
statement can still feed `thmG3`. -/
theorem degreeProp'_of_degreeProp (h : Work.ThmG.DegreeProp) : DegreeProp' :=
  fun G _ _ H Q t hh _ => h G H Q t hh

/-- **D2-corrected Hall–Wielandt** (M. Hall §14.4, Theorem 14.4.2, honest form).

`Work.ThmF.HallWielandtProp` with the extra hypothesis `p ≠ 2`: let `S` be a Sylow `p`-subgroup of
a finite group `G` with `p` an *odd* prime, and `A ≤ S` a subgroup that is weakly closed in `S`
with respect to `G` (`A^g ≤ S ⟹ A^g = A`).  If `A` is abelian, then
`G/O^p(G) ≅ N_G(A)/O^p(N_G(A))`; equivalently `G` has a normal subgroup of index `p` if and only
if `N_G(A)` does.

This is a standalone copy of the definition that area `BSHallW` (`Work.BSHallW.HallWielandtOddProp`,
`Submission/Work/BSHallW/Defs.lean`) uses, so that this area does not depend on that module; the two
definitions have literally the same body, so either can be passed where the other is expected
(`hallWielandtOddProp_of_BSHallW` / `…_iff_…` below). -/
def HallWielandtOddProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → p ≠ 2 →
    ∀ (S : Sylow p G) (A : Subgroup G), A ≤ (S : Subgroup G) →
      (∀ g : G, A.map (MulAut.conj g).toMonoidHom ≤ (S : Subgroup G) →
        A.map (MulAut.conj g).toMonoidHom = A) →
      (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) →
      (Work.ThmF.HasNormalIndexP p G ↔
        Work.ThmF.HasNormalIndexP p ↥(Subgroup.normalizer (A : Set G)))

/-- The two copies of the corrected Hall–Wielandt statement are the same, hence interchangeable. -/
theorem hallWielandtOddProp_iff_BSHallW :
    HallWielandtOddProp ↔ Work.BSHallW.HallWielandtOddProp :=
  Iff.rfl

/-- The corrected statement is *weaker* than the uncorrected one: `HallWielandtProp` implies
`HallWielandtOddProp` (the reverse implication fails at `p = 2`, D2). -/
theorem hallWielandtOddProp_of_hallWielandtProp (h : Work.ThmF.HallWielandtProp) :
    HallWielandtOddProp :=
  fun G _ _ p hp _ => h G p hp

end Work.BSIntegrate
