import Submission.Blueprint.Interfaces
import Submission.Work.Fitting.Main
import Submission.Work.CharCore.Main
import Submission.Work.Coherence.All
import Submission.Work.Induction.All

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Area `ZassenhausTwoGroup`: `Q` is a 2-group in a simple Zassenhaus group (Feit 1960)

Target (`Submission.Blueprint.ZassenhausTwoGroupProp`): if `G` is a finite simple group and
`H = Q ⋊ D` is the rank-one data of a Zassenhaus group (`IsSplitRankOne H Q t`,
`IsZassenhaus H`), then `Q` is a `2`-group.

The proof is Feit's, *On a class of doubly transitive permutation groups*, Illinois J. Math. 4
(1960) 170–186 (Theorem 1), in the rank-one reformulation of Peterfalvi II, Appendix XII and
Huppert–Blackburn III XI §6.

## Notation fixed here (all conventions follow the blueprint)

* `twoPoint H t = H ∩ H^t` is Peterfalvi's `D`, the two-point stabiliser; `|D|` is odd
  (strong embedding) and `|D|` is Peterfalvi's/Feit's `q` as well as Sibley's `e`.
* `oddPart Q = O_{2'}(Q)` is Feit's `M₁`, the odd part of `Q`; `twoPart Q = O_2(Q)` is the
  Sylow `2`-subgroup `S` of `Q` when `Q` is nilpotent, and then `Q = S × O_{2'}(Q)`.
* `scriptS H Q₁ = 𝓢 = {χ ∈ Irr H | Q₁ ⊄ ker χ}` (`Submission.Blueprint.excludingKernel`);
  `indLin H = Ind_H^G` as a `ℤ`-linear map on class functions (`Work.Induction.indFun`).

The area splits as:

* `Defs` (this file): notation and the rank-one set-up predicate.
* `Setting.*`: the elementary group theory of the set-up (`|D|` odd, `|Q|` even, `D` acts
  fixed point freely on `Q`, `Q` is T.I., `(|D|,|Q|) = 1`, `Q` nilpotent, `G` has 2-rank `≥ 2`).
* `Coherence.*`: Feit–Sibley (the black box `FeitSibleyProp`) applied to `H = Q ⋊ D`, and the
  exceptional characters extracted from it.
* `Main`: the area theorem.
-/

set_option autoImplicit false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausTwoGroup

variable {G : Type} [Group G]

/-- `D` acts *fixed point freely* on the subgroup `A`: every `1 ≠ d ∈ D` has no non-trivial fixed
point in `A` (conjugation action; `D` need not normalise `A` for the definition). -/
def IsFpfOn (D A : Subgroup G) : Prop :=
  ∀ d ∈ D, d ≠ 1 → ∀ x ∈ A, d * x * d⁻¹ = x → x = 1

/-- `D` has at most `k` orbits on `A#`, in the form `|A| - 1 ≤ k * |D|`; when `D` acts fixed point
freely this is exactly "at most `k` orbits on `A#`". -/
def FewOrbits (D A : Subgroup G) (k : ℕ) : Prop := Nat.card A - 1 ≤ k * Nat.card D


/-! ## Notation -/

/-- `O_{2'}(Q)`, the largest normal subgroup of `Q` of odd order, viewed as a subgroup of `G`.

In the Zassenhaus set-up `Q` is nilpotent, so `Q = O_2(Q) × O_{2'}(Q)` and this is the odd
factor `Q₁` of Peterfalvi II App. XII. -/
def oddPart (Q : Subgroup G) : Subgroup G := (Work.Fitting.pPrimeCore 2 Q).map Q.subtype

/-- `O_2(Q)`, the largest normal `2`-subgroup of `Q`, viewed as a subgroup of `G`.  If `Q` is
nilpotent this is the Sylow `2`-subgroup `S` of `Q`. -/
def twoPart (Q : Subgroup G) : Subgroup G := (Work.Fitting.pCore 2 Q).map Q.subtype

/-- The rank-one Zassenhaus set-up: `IsSplitRankOne` (the split BN-pair of rank one with the
two-point stabiliser `D = H ∩ H^t`) together with `IsZassenhaus` (the pointwise stabiliser of
three points of `Ω = G ⧸ H` is trivial). -/
def IsZassenhausSetup (H Q : Subgroup G) (t : G) : Prop := IsSplitRankOne H Q t ∧ IsZassenhaus H

/-! ## Immediate consequences of the hypotheses -/

section Basic

variable {H Q : Subgroup G} {t : G}

theorem twoPoint_eq (H : Subgroup G) (t : G) : twoPoint H t = H ⊓ conj t H := rfl

theorem odd_card_twoPoint (hse : IsStronglyEmbedded H) (ht : t ∉ H) :
    Odd (Nat.card (twoPoint H t)) := hse.2.2 t ht

theorem even_card_of_stronglyEmbedded (hse : IsStronglyEmbedded H) : Even (Nat.card H) :=
  hse.2.1

theorem ne_top_of_stronglyEmbedded (hse : IsStronglyEmbedded H) : H ≠ ⊤ := hse.1

theorem Q_le_H (h : IsSplitRankOne H Q t) : Q ≤ H := h.le

theorem H_le_normalizer_Q (h : IsSplitRankOne H Q t) : H ≤ Subgroup.normalizer (Q : Set G) :=
  h.normal

theorem twoPoint_le_H (h : IsSplitRankOne H Q t) : twoPoint H t ≤ H := inf_le_left

theorem Q_inf_twoPoint (h : IsSplitRankOne H Q t) : Q ⊓ twoPoint H t = ⊥ := h.inf_eq

theorem Q_sup_twoPoint (h : IsSplitRankOne H Q t) : Q ⊔ twoPoint H t = H := h.sup_eq

theorem t_notMem (h : IsSplitRankOne H Q t) : t ∉ H := h.not_mem

theorem orderOf_t (h : IsSplitRankOne H Q t) : orderOf t = 2 := h.invol

theorem twoTransitive (h : IsSplitRankOne H Q t) : IsTwoTransitiveOn H := h.twoTransitive

theorem stronglyEmbedded (h : IsSplitRankOne H Q t) : IsStronglyEmbedded H := h.stronglyEmbedded

end Basic

/-! ## Character vocabulary (Feit–Sibley form) -/

section Characters

noncomputable section

variable [Fintype G]

open Classical

/-- `𝓢 = {χ ∈ Irr H | Q₁ ⊄ ker χ}`, the set of characters of Peterfalvi II App. XII.  This is
`Submission.Blueprint.excludingKernel`. -/
abbrev scriptS (H Q₁ : Subgroup G) : Finset (H → ℂ) := Submission.Blueprint.excludingKernel H Q₁

/-- `Ind_H^G` as a `ℤ`-linear map on class functions.  This is
`Submission.Blueprint.indLinear`. -/
abbrev indLin (H : Subgroup G) : (H → ℂ) →ₗ[ℤ] (G → ℂ) := Submission.Blueprint.indLinear H

theorem mem_scriptS {H Q₁ : Subgroup G} {χ : H → ℂ} :
    χ ∈ scriptS H Q₁ ↔
      χ ∈ Work.CharCore.Irr H ∧ ∃ x : H, (x : G) ∈ Q₁ ∧ χ x ≠ χ 1 := by
  simp only [scriptS, Submission.Blueprint.excludingKernel, Finset.mem_filter]

theorem indLin_apply (H : Subgroup G) (φ : H → ℂ) : indLin H φ = Work.Induction.indFun H φ := rfl

end

end Characters

end Work.ZassenhausTwoGroup
