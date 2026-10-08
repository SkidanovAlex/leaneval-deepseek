/-
Copyright (c) 2024. All rights reserved.

# Type `B`, `C`, `D` (Higman 1963, Lemma 12): the two-step model

Higman, *Suzuki 2-groups*, Illinois J. Math. **7** (1963), 79--96, Lemma 12.

A Suzuki 2-group `P` of order `q ^ 3` (`q = |Z(P)|`) has class `2` and exponent `4`, its
Frattini subgroup and its commutator subgroup both equal its centre.  It is therefore a
*two-step* group: with `V = P / Z(P)` and `W = Z(P)` there are a biadditive cocycle
`b : V → V → W` and an isomorphism `P ≃* TwoStep V W b` (`Submission.Work.Higman.Model`).
The squaring map `Q v = b v v` is then an anisotropic quadratic map with non-degenerate polar
form `B u v = b u v + b v u`.

This file collects the vocabulary of that reduction:

* `TwoStepModel P` -- the two-step model of a finite group `P`;
* elementary facts about `TwoStep` used by the reduction.

The classification itself -- Higman's Lemma 12 in the form used by the reduction, i.e. the
statement that the cocycle of a Suzuki-like two-step group of order `q ^ 3` is, up to a
coboundary and additive coordinate changes, one of the three Column V laws -- is
`Work.Higman.cocycle_normal_form`.
-/

import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.Model
import Submission.Work.Higman.Family
import Submission.Work.Higman.Class

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Work.Higman

/-! ## The two-step model of a finite group -/

/-- A two-step model of a finite group `P`: an additive group `V` with `|V| = |P / Z(P)|`, an
additive group `W` with `|W| = |Z(P)|`, a biadditive cocycle `b : V → V → W`, and an
isomorphism `P ≃* TwoStep V W b`.

For a Suzuki 2-group of order `q ^ 3` such a model exists, with `V ≅ (𝔽₂)^{2n}` and
`W ≅ (𝔽₂)^n` (`V = P / Z(P)`, `W = Z(P)`); it exhibits `P` as an extension of `W` by `V`. -/
structure TwoStepModel (P : Type*) [Group P] [Finite P] where
  /-- the "quotient" coordinates, `≅ P / Z(P)`. -/
  V : Type*
  /-- the "central" coordinates, `≅ Z(P)`. -/
  W : Type*
  [addCommGroup_V : AddCommGroup V]
  [addExpTwo_V : AddExpTwo V]
  [addCommGroup_W : AddCommGroup W]
  [addExpTwo_W : AddExpTwo W]
  /-- the cocycle. -/
  b : V → V → W
  [biadd_b : Biadd b]
  /-- `V` has the cardinality of `P / Z(P)`. -/
  card_V : Nat.card V = Nat.card (P ⧸ Subgroup.center P)
  /-- `W` has the cardinality of `Z(P)`. -/
  card_W : Nat.card W = Nat.card ↥(Subgroup.center P)
  /-- the isomorphism with the two-step group. -/
  iso : P ≃* TwoStep V W b

attribute [instance] TwoStepModel.addCommGroup_V TwoStepModel.addExpTwo_V
  TwoStepModel.addCommGroup_W TwoStepModel.addExpTwo_W TwoStepModel.biadd_b

/-! ## Elementary facts about `TwoStep` -/

namespace TwoStep

variable {A Z : Type*} [AddCommGroup A] [AddCommGroup Z] {b : A → A → Z}
variable [Biadd b] [AddExpTwo A] [AddExpTwo Z]

/-- An element of a `TwoStep` group is an involution exactly when its `A`-coordinate is
"isotropic", i.e. `b v v = 0`. -/
theorem sq_eq_one_iff_invol (x : TwoStep A Z b) : x ^ 2 = 1 ↔ b x.fst x.fst = 0 :=
  sq_eq_one_iff x

/-- The elements with trivial `A`-coordinate are involutions. -/
theorem sq_eq_one_of_mem_kerFst {x : TwoStep A Z b} (hx : x ∈ kerFst) : x ^ 2 = 1 := by
  rw [sq_eq_one_iff_invol]
  rw [mem_kerFst] at hx
  rw [hx]
  exact Biadd.zero_left (0 : A)

/-- `kerFst` has the cardinality of the central coordinates. -/
theorem card_kerFst : Nat.card ↥(kerFst (A := A) (Z := Z) (b := b)) = Nat.card Z := by
  refine Nat.card_congr ?_
  refine
    { toFun := fun x => x.1.snd
      invFun := fun z => ⟨⟨0, z⟩, rfl⟩
      left_inv := fun x => by
        refine Subtype.ext ?_
        ext
        · exact x.2.symm
        · rfl
      right_inv := fun z => rfl }

end TwoStep

end Work.Higman
