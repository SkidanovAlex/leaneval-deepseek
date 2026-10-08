import Mathlib
import Submission.Work.DoubleTransitivity.Sec4.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.DoubleTransitivity.Sec4.RpDefs` — `p`-regular intersections and Ch. I §4 Lemma 2

Peterfalvi I, Ch. I §4 (pp. 154–157).  Fix a finite group `G` with a strongly embedded subgroup
`H` (so `Ω = G ⧸ H` is the class of conjugates of `H`, acted on by left translation) and an odd
prime `p`.

* `Rp p H` is the statement `𝓡_p ≠ ∅` of the source: there are distinct points `ω₁ ≠ ω₂` of `Ω`
  and a `p`-Sylow `P` of the two-point stabiliser `Stab ω₁ ⊓ Stab ω₂` whose normaliser *in the
  point stabiliser* `Stab ω₁` has even order (Ch. I §4 Lemma 1 (c)).

* `TwoPointSylowData p H Q` says that `Q` contains a `p`-Sylow of a two-point stabiliser
  ("`P` contains a `p`-Sylow of an element of `𝓓`", the hypothesis of Ch. I §4 Lemma 2).

* `Sec4Lemma2Part1 p H` is the *conditional* half of Ch. I §4 Lemma 2: if `Q` is maximal among
  the `p`-subgroups of `G` with at least three fixed points, `Q` contains a `p`-Sylow of a
  two-point stabiliser, `ω₁ ≠ ω₂` are two fixed points of `Q` and moreover
  `|N_G(Q) ⊓ Stab ω₁|` is even, then `Q` **is** a `p`-Sylow of `Stab ω₁ ⊓ Stab ω₂`.

* `Sec4Lemma2 p H` is the full Ch. I §4 Lemma 2: under the same hypotheses (without the extra
  evenness assumption), for every pair `ω₁ ≠ ω₂` of fixed points of `Q` the subgroup `Q` is a
  `p`-Sylow of `Stab ω₁ ⊓ Stab ω₂` and some `p`-Sylow `P` of that intersection has
  `|N_G(P) ⊓ Stab ω₁|` even.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.DoubleTransitivity.Sec4

variable {G : Type} [Group G]

/-- Peterfalvi I Ch. I §4: `𝓡_p ≠ ∅`.  There are distinct points of `Ω` whose two-point
stabiliser has a `p`-Sylow with an even-order normaliser in one of the two point stabilisers. -/
def Rp (p : ℕ) (H : Subgroup G) : Prop :=
  ∃ ω₁ ω₂ : Omega H, ω₂ ≠ ω₁ ∧ ∃ P : Subgroup G,
    IsSylowSubgroupOf p P (MulAction.stabilizer G ω₁ ⊓ MulAction.stabilizer G ω₂) ∧
    Even (Nat.card ↥(Subgroup.normalizer (P : Set G) ⊓ MulAction.stabilizer G ω₁))

/-- `Q` contains a `p`-Sylow of a two-point stabiliser (`Q` contains a `p`-Sylow of an element
of `𝓓`, the hypothesis of Ch. I §4 Lemma 2). -/
def TwoPointSylowData (p : ℕ) (H : Subgroup G) (Q : Subgroup G) : Prop :=
  ∃ ω₁ ω₂ : Omega H, ω₂ ≠ ω₁ ∧ ∃ Q₀ : Subgroup G,
    IsSylowSubgroupOf p Q₀ (MulAction.stabilizer G ω₁ ⊓ MulAction.stabilizer G ω₂) ∧ Q₀ ≤ Q

/-- Ch. I §4 Lemma 2, part 1: maximality plus evenness at one fixed point forces `Q` to be a
`p`-Sylow of the two-point stabiliser. -/
def Sec4Lemma2Part1 (p : ℕ) (H : Subgroup G) : Prop :=
  ∀ Q : Subgroup G, MaxFixesThree p H Q → TwoPointSylowData p H Q →
    ∀ ω₁ ω₂ : Omega H, ω₂ ≠ ω₁ → Q ≤ MulAction.stabilizer G ω₁ →
      Q ≤ MulAction.stabilizer G ω₂ →
      Even (Nat.card ↥(Subgroup.normalizer (Q : Set G) ⊓ MulAction.stabilizer G ω₁)) →
      IsSylowSubgroupOf p Q (MulAction.stabilizer G ω₁ ⊓ MulAction.stabilizer G ω₂)

/-- Ch. I §4 Lemma 2 (p. 155–156).  Let `Q` be maximal among the `p`-subgroups of `G` with at
least three fixed points, and suppose that `Q` contains a `p`-Sylow of an element of `𝓓`.  Then
for distinct fixed points `ω₁, ω₂` of `Q`: `Q` is a `p`-Sylow of `Stab ω₁ ⊓ Stab ω₂` and some
`p`-Sylow `P` of `Stab ω₁ ⊓ Stab ω₂` has `|N_G(P) ⊓ Stab ω₁|` even. -/
def Sec4Lemma2 (p : ℕ) (H : Subgroup G) : Prop :=
  ∀ Q : Subgroup G, MaxFixesThree p H Q → TwoPointSylowData p H Q →
    ∀ ω₁ ω₂ : Omega H, ω₂ ≠ ω₁ → Q ≤ MulAction.stabilizer G ω₁ →
      Q ≤ MulAction.stabilizer G ω₂ →
      IsSylowSubgroupOf p Q (MulAction.stabilizer G ω₁ ⊓ MulAction.stabilizer G ω₂) ∧
      ∃ P : Subgroup G, IsSylowSubgroupOf p P
          (MulAction.stabilizer G ω₁ ⊓ MulAction.stabilizer G ω₂) ∧
        Even (Nat.card ↥(Subgroup.normalizer (P : Set G) ⊓ MulAction.stabilizer G ω₁))

end Work.DoubleTransitivity.Sec4
