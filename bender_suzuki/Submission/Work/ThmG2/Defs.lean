import Mathlib
import Submission.Work.ThmG.Defs
import Submission.Work.ThmG.DNeBot

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Area `ThmG2`: Théorème G with the CORRECTED rank-one inputs — vocabulary

This is the continuation of area `ThmG` (`Submission/Work/ThmG/`) announced in
`ThmG/NOTES_LEAD_probe1330.md`.  Two of the eight inputs of `Work.ThmG.RankOneStructure` are
**false as stated**, so `Work.ThmG.thmG` is vacuous:

* `Work.ThmG.ExistsLinearProp` only requires `Q ⊆ ker λ`; the paper (Peterfalvi II, Ch. VI §1,
  p. 258) requires `QK ⊆ ker λ`, where `K = J(D,t) = invertedBy (twoPoint H t) t`;
* `Work.ThmG.IndTwoProp` only requires `Q ⊆ ker λ`, whereas Mackey's formula gives
  `‖Ind_H^G λ‖² = 1 + ⟪λ|_D, λᵗ|_D⟫_D`, and this equals `2` **iff** `λ` is trivial on `K`
  (GAP counterexample in `PSU(3,4)`: the linear `λ` of order 3 are trivial on `Q` but not on `K`,
  and `Ind λ` is irreducible).

`ExistsLinearProp` is true but too weak; it has to be strengthened to `ExistsLinearV2Prop`
(`QK ⊆ ker λ`).  This file fixes the corrected structure; its fields 1–4, 7 and 8 — and their
standalone `Prop`s `KNeOneProp`, `CoprimeDQProp`, `FpfOddPartProp`, `DegreeProp`,
`VanishesOffProp`, and the hypothesis context `RankOneHyp` — are **reused verbatim** from
`Work.ThmG` and are not copied here.

Notation of the paper: `D = H ∩ Hᵗ = twoPoint H t`, `V = C_D(t) = centD H t`,
`K = J(D,t) = invertedBy (twoPoint H t) t` (definitionally `Work.ThmF.Kset H t`).

## Main results of this module

* `Work.ThmG2.RankOneStructure2` / `Work.ThmG2.RankOneStructure2Prop` — the corrected bundle;
* `Work.ThmG2.ExistsLinearV2Prop`, `Work.ThmG2.IndTwoV2Prop` — the corrected fields 5 and 6;
* `Work.ThmG2.rankOneStructure2_of` — the eight inputs (field 2 discharged internally by
  `Work.ThmG.dNeBotProp`), hence seven external inputs, give `RankOneStructure2Prop`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

open Classical
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ThmG2

open Work.ThmG

/-- **The corrected structural inputs of Theorem G.**  Identical to
`Work.ThmG.RankOneStructure` except that fields 5 and 6 require `QK ⊆ ker λ` (equivalently:
triviality on `Q` **and** on `K = J(D,t)`), which is the paper's hypothesis on p. 258.

The fields are in bijection with the eight inputs:
`K_ne_one` (`KNeOneProp`, area `ThreePoints`), `D_ne_bot` (`DNeBotProp`, proved in area `ThmG`),
`coprime` (`CoprimeDQProp`, area `DoubleTransitivity`), `fpf_oddPart` (`FpfOddPartProp`, area
`ThmF`), `exists_linear` (`ExistsLinearV2Prop`, area `ThmF`), `ind_two` (`IndTwoV2Prop`, area
`ThmF`), `degree` (`DegreeProp`, area `FeitSibley`), `vanishes_off` (`VanishesOffProp`, area
`FeitSibley`). -/
structure RankOneStructure2 (G : Type) [Group G] [Fintype G] (H Q : Subgroup G) (t : G) : Prop where
  /-- Field 1, unchanged: `K = J(D,t) ≠ 1` (`|K| = |Inv H| > 1`). -/
  K_ne_one : ∃ x ∈ invertedBy (twoPoint H t) t, x ≠ 1
  /-- Field 2, unchanged: `D = H ∩ Hᵗ ≠ 1`. -/
  D_ne_bot : twoPoint H t ≠ ⊥
  /-- Field 3, unchanged: `(|D|, |Q|) = 1`. -/
  coprime : Nat.Coprime (Nat.card (twoPoint H t)) (Nat.card Q)
  /-- Field 4, unchanged: `D` acts fixed-point-freely on `Q₁ = O_{2'}(Q)`. -/
  fpf_oddPart : ∀ d ∈ twoPoint H t, d ≠ 1 → ∀ x ∈ oddPart Q, d * x * d⁻¹ = x → x = 1
  /-- **Field 5, corrected** (Ch. VI §1, p. 258): a linear character `lam ≠ 1_H` of `H` trivial
  on `Q` **and on `K = J(D,t)`** (the paper's `QK ⊆ ker lam`). -/
  exists_linear : ∃ lam : H → ℂ, lam ∈ Work.CharCore.Irr H ∧ lam 1 = 1 ∧
    lam ≠ (fun _ : H => (1 : ℂ)) ∧ (∀ x : H, (x : G) ∈ Q → lam x = 1) ∧
    (∀ x : H, (x : G) ∈ invertedBy (twoPoint H t) t → lam x = 1)
  /-- **Field 6, corrected** (Ch. VI §1, p. 258): for such a `lam` (trivial on `QK`),
  `Ind_H^G lam` is the sum of two distinct irreducible characters of `G`. -/
  ind_two : ∀ lam : H → ℂ, lam ∈ Work.CharCore.Irr H → lam 1 = 1 →
    lam ≠ (fun _ : H => (1 : ℂ)) → (∀ x : H, (x : G) ∈ Q → lam x = 1) →
    (∀ x : H, (x : G) ∈ invertedBy (twoPoint H t) t → lam x = 1) →
    ∃ f₁ ∈ Work.CharCore.Irr G, ∃ f₂ ∈ Work.CharCore.Irr G, f₁ ≠ f₂ ∧
      Work.Induction.indFun H lam = f₁ + f₂
  /-- Field 7, unchanged (App. XII (3)–(4)). -/
  degree : ∃ χ ∈ excludingKernel H (oddPart Q), χ 1 = (Nat.card (twoPoint H t) : ℂ) ∧
    ∀ ψ ∈ excludingKernel H (oddPart Q), ∃ a : ℕ, ψ 1 = (a : ℂ) * χ 1
  /-- Field 8, unchanged (App. XII Lemma 2 (a)). -/
  vanishes_off : ∀ χ ∈ excludingKernel H (oddPart Q), ∀ h : H, (h : G) ∉ Q → χ h = 0

/-- The corrected structural inputs of `RankOneStructure2`, as one `Prop` mirroring the shape of
`Work.ThmG.RankOneStructureProp` (so that `Work.ThmG2.thmG2` can take them as a hypothesis). -/
def RankOneStructure2Prop : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (H Q : Subgroup G) (t : G),
    RankOneHyp G H Q t → @RankOneStructure2 G _ _ H Q t

/-- **Field 5, corrected** (the `Ch. V §1–2` export of `ThmF`, Ch. VI §1 p. 258): a linear
character `lam ≠ 1_H` of `H` trivial on `Q` and on `K = J(D,t)` (`QK ⊆ ker lam`).

Owner: area `ThmF` (`Work.ThmF.ChV12.exists_linear_v2`, with the auxiliary input
`centD H t ≠ ⊥` obtained from `¬ IsZassenhaus H` by `zassenhaus_iff_centD_bot`). -/
def ExistsLinearV2Prop : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (H Q : Subgroup G) (t : G),
    RankOneHyp G H Q t → ∃ lam : H → ℂ, lam ∈ Work.CharCore.Irr H ∧ lam 1 = 1 ∧
      lam ≠ (fun _ : H => (1 : ℂ)) ∧ (∀ x : H, (x : G) ∈ Q → lam x = 1) ∧
      (∀ x : H, (x : G) ∈ invertedBy (twoPoint H t) t → lam x = 1)

/-- **Field 6, corrected** (the `Ch. V §1–2` export of `ThmF`, Ch. VI §1 p. 258): for a linear
`lam` trivial on `QK`, `Ind_H^G lam` has norm `2`, i.e. is the sum of two distinct irreducible
characters of `G` (Mackey on the two double cosets `H`, `H t H`).

**Proved in this area**: `Work.ThmG2.indTwoV2Prop` (`Submission/Work/ThmG2/IndTwoV2Proof.lean`),
via the self-contained Mackey formula `Work.ThmG2.cfInner_indFun_self_twoDoubleCoset` and
`Work.CharCore.isChar_norm_two`.  The route through area `ThmF` (`Work.ThmF.ChV12.ind_two_v2`) is
also available as a hypothesis of `Work.ThmG2.IndTwoV2Statement`. -/
def IndTwoV2Prop : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (H Q : Subgroup G) (t : G),
    RankOneHyp G H Q t → ∀ lam : H → ℂ, lam ∈ Work.CharCore.Irr H → lam 1 = 1 →
      lam ≠ (fun _ : H => (1 : ℂ)) → (∀ x : H, (x : G) ∈ Q → lam x = 1) →
      (∀ x : H, (x : G) ∈ invertedBy (twoPoint H t) t → lam x = 1) →
      ∃ f₁ ∈ Work.CharCore.Irr G, ∃ f₂ ∈ Work.CharCore.Irr G, f₁ ≠ f₂ ∧
        Work.Induction.indFun H lam = f₁ + f₂

/-- **Wiring**: the corrected structural inputs give `RankOneStructure2Prop`, i.e. they discharge
the hypothesis of `Work.ThmG2.thmG2`.

Field 2 (`D ≠ 1`) is discharged internally by `Work.ThmG.dNeBotProp` (Ch. II §4 Prop. 2 (b) with
p. 236), so **seven** external inputs suffice — exactly as in
`Work.ThmG.rankOneStructure_of_seven`. -/
theorem rankOneStructure2_of (h1 : KNeOneProp) (h3 : CoprimeDQProp) (h4 : FpfOddPartProp)
    (h5 : ExistsLinearV2Prop) (h6 : IndTwoV2Prop) (h7 : DegreeProp) (h8 : VanishesOffProp) :
    RankOneStructure2Prop := by
  intro G _ _ H Q t hh
  exact ⟨h1 G H Q t hh, dNeBotProp G H Q t hh, h3 G H Q t hh, h4 G H Q t hh, h5 G H Q t hh,
    h6 G H Q t hh, h7 G H Q t hh, h8 G H Q t hh⟩

/-- `rankOneStructure2_of` with the two `ThmF` inputs bundled: `ExistsLinearV2Prop` and
`IndTwoV2Prop` together with the four other external inputs give `RankOneStructure2Prop`. -/
theorem rankOneStructure2_of_six (h1 : KNeOneProp) (h3 : CoprimeDQProp) (h4 : FpfOddPartProp)
    (h5 : ExistsLinearV2Prop) (h6 : IndTwoV2Prop)
    (h78 : DegreeProp ∧ VanishesOffProp) : RankOneStructure2Prop :=
  rankOneStructure2_of h1 h3 h4 h5 h6 h78.1 h78.2

end Work.ThmG2
