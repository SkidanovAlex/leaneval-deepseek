import Mathlib
import Submission.Work.OROneRel.hnnConjSplit

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# Words in the HNN structure attached to a pair `(H, t)`

For a subgroup `H ≤ G` and an element `t : G`, the canonical HNN decomposition of `G` over `H`
with stable letter `t` has associated subgroups `A = hnnEdgeA H t = H ⊓ t⁻¹Ht` and
`B = hnnEdgeB H t = tAt⁻¹ = H ⊓ tHt⁻¹` (see `Submission/Work/OROneRel/hnnConjSplit.lean`).

This file provides the vocabulary used to run Britton's lemma (the normal form of the HNN
extension) against the coset graph `GradedHNN.Coset H t`:

* `hnnEdgeSub H t u` / `hnnEdgeSubBase H t u`: the two associated subgroups, indexed by a sign
  `u : ℤˣ` (`u = 1` gives `A`, `u = -1` gives `B`), as subgroups of `G` and of the base group `↥H`;
* `hnnWord H t L`: the word `h₁ t^{ε₁} h₂ t^{ε₂} ⋯ hₙ t^{εₙ}` attached to `L = [(εᵢ,hᵢ)]`;
* `NoPinch H t L`: the list `L` exhibits no "pinch", i.e. no consecutive pair `(ε,h)`, `(ε',h')`
  can be rewritten by the relation `t^ε h' t^{-ε} ∈ H` of the HNN extension (`h' ∈ toSubgroup ε`
  and `ε' = -ε`).

The relevance to the coset graph is that a *reduced* path in `GradedHNN.Coset H t` lifts to a
pinch-free word (see `Work.OROneRel.noPinch_hnnLiftAux` in
`Submission/Work/OROneRel/isTree_coset_of_hnnConjMap_injective.lean`), while Britton's lemma
(`Work.OROneRel.britton_hnnConjMap_injective`) says that a pinch-free word with letters in `H`
which represents an element of `H` is empty.
-/

namespace Work.OROneRel

universe u

variable {G : Type u} [Group G]

/-- The two associated subgroups `A = H ⊓ t⁻¹Ht` and `B = H ⊓ tHt⁻¹` of the HNN decomposition of
the pair `(H, t)`, indexed by a sign, as subgroups of `G`. -/
def hnnEdgeSub (H : Subgroup G) (t : G) (u : ℤˣ) : Subgroup G :=
  HNNExtension.toSubgroup (hnnEdgeA H t) (hnnEdgeB H t) u

/-- The same two associated subgroups, now as subgroups of the base group `↥H`. -/
def hnnEdgeSubBase (H : Subgroup G) (t : G) (u : ℤˣ) : Subgroup ↥H :=
  HNNExtension.toSubgroup ((hnnEdgeA H t).subgroupOf H) ((hnnEdgeB H t).subgroupOf H) u

@[simp]
theorem hnnEdgeSub_one (H : Subgroup G) (t : G) : hnnEdgeSub H t 1 = hnnEdgeA H t := rfl

@[simp]
theorem hnnEdgeSub_neg_one (H : Subgroup G) (t : G) : hnnEdgeSub H t (-1) = hnnEdgeB H t := rfl

@[simp]
theorem hnnEdgeSubBase_one (H : Subgroup G) (t : G) :
    hnnEdgeSubBase H t 1 = (hnnEdgeA H t).subgroupOf H := rfl

@[simp]
theorem hnnEdgeSubBase_neg_one (H : Subgroup G) (t : G) :
    hnnEdgeSubBase H t (-1) = (hnnEdgeB H t).subgroupOf H := rfl

theorem mem_hnnEdgeSubBase_iff (H : Subgroup G) (t : G) (u : ℤˣ) {x : ↥H} :
    x ∈ hnnEdgeSubBase H t u ↔ (x : G) ∈ hnnEdgeSub H t u := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · exact Subgroup.mem_subgroupOf
  · exact Subgroup.mem_subgroupOf

/-- The word `h₁ t^{ε₁} h₂ t^{ε₂} ⋯ hₙ t^{εₙ}` attached to the list `L = [(εᵢ, hᵢ)]`. -/
def hnnWord (H : Subgroup G) (t : G) (L : List (ℤˣ × ↥H)) : G :=
  (L.map (fun x => (x.2 : G) * t ^ (x.1 : ℤ))).prod

/-- A list of letters is *pinch free* if no consecutive pair `(ε, h)`, `(ε', h')` exhibits a
reduction `t^ε h' t^{-ε}` of the HNN extension, i.e. `h' ∈ toSubgroup ε` and `ε' = -ε`. -/
def NoPinch (H : Subgroup G) (t : G) (L : List (ℤˣ × ↥H)) : Prop :=
  L.IsChain (fun a b => ¬ (b.2 ∈ hnnEdgeSubBase H t a.1 ∧ b.1 = -a.1))

@[simp]
theorem hnnWord_nil (H : Subgroup G) (t : G) : hnnWord H t [] = 1 := rfl

theorem hnnWord_concat (H : Subgroup G) (t : G) (L : List (ℤˣ × ↥H)) (x : ℤˣ × ↥H) :
    hnnWord H t (L ++ [x]) = hnnWord H t L * ((x.2 : G) * t ^ (x.1 : ℤ)) := by
  simp only [hnnWord, List.map_append, List.map_cons, List.map_nil, List.prod_append,
    List.prod_cons, List.prod_nil, mul_one]

@[simp]
theorem hnnWord_singleton (H : Subgroup G) (t : G) (x : ℤˣ × ↥H) :
    hnnWord H t [x] = (x.2 : G) * t ^ (x.1 : ℤ) := by
  rw [← List.nil_append [x], hnnWord_concat, hnnWord_nil, one_mul]

@[simp]
theorem noPinch_nil (H : Subgroup G) (t : G) : NoPinch H t [] := List.isChain_nil

@[simp]
theorem noPinch_singleton (H : Subgroup G) (t : G) (x : ℤˣ × ↥H) : NoPinch H t [x] :=
  List.isChain_singleton x

end Work.OROneRel
