/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The `G`-complexity `Tree_G` of [JZLA20, §4.3]

For `φ : K[G] →+* U` and `D = divisionClosure (Set.range φ) ⊆ U`, the universal morphism
`Φ : Rat(Kˣ × G) →+* D` is *surjective* (`Section6/Phi_surjective.lean`, [JZLA20, Lemma 4.2]),
so every `a ∈ D` is the image of some `α : Rat(Kˣ × G)`.  The **`G`-complexity** of `a` is

`Tree_G a = min {Tree α : Φ α = a}`,

the minimum being taken in the DHS04 well-order of the finite rooted trees; it is the measure of
complexity along which [JZLA20, Theorem 6.1] runs its induction.

This file contains `treeG` and its characteristic property `treeG_spec` (existence of a realising
element and minimality), which is exactly the `treeH_spec` field of the `Prop51Data` interface of
[JZLA20, Proposition 5.1] — instantiated for the division closure of `K[G]` in `U`.
-/
import Mathlib
import Submission.Work.ORHughesFree.Section6.RatStruct
import Submission.Work.ORHughesFree.Section6.Phi_surjective
import Submission.Work.ORHughesFree.Tree.exists_least
import Submission.Work.ORHughesFree.Rat.ratComplexity_model

set_option autoImplicit false

namespace Work.ORHughesFree

variable {K : Type} [Field K] {G : Type} [Group G] {U : Type} [Ring U]

/-- The set of complexities of the elements of `Rat(Kˣ × G)` realising `a`. -/
def complexitySet (φ : MonoidAlgebra K G →+* U) (a : ↥(divisionClosure (Set.range φ))) : Set Tree :=
  {t : Tree | ∃ α : RatU (Kˣ × G), Rat.treeOfRat (Kˣ × G) α = t ∧ Phi φ α = a}

theorem complexitySet_nonempty (φ : MonoidAlgebra K G →+* U)
    (a : ↥(divisionClosure (Set.range φ))) : (complexitySet φ a).Nonempty := by
  obtain ⟨α, hα⟩ := Section6.Phi_surjective φ a
  exact ⟨Rat.treeOfRat (Kˣ × G) α, α, rfl, hα⟩

/-- **The `G`-complexity of [JZLA20, §4.3]**: the minimum of `Tree α` over the `α` with `Φ α = a`. -/
noncomputable def treeG (φ : MonoidAlgebra K G →+* U)
    (a : ↥(divisionClosure (Set.range φ))) : Tree :=
  Classical.choose (Tree.exists_least (complexitySet φ a) (complexitySet_nonempty φ a))

/-- **The characteristic property of the `G`-complexity**: it is realised, and it is the minimum. -/
theorem treeG_spec (φ : MonoidAlgebra K G →+* U)
    (a : ↥(divisionClosure (Set.range φ))) :
    (∃ α : RatU (Kˣ × G), Phi φ α = a ∧ Rat.treeOfRat (Kˣ × G) α = treeG φ a) ∧
      ∀ β : RatU (Kˣ × G), Phi φ β = a →
        Tree.le (treeG φ a) (Rat.treeOfRat (Kˣ × G) β) := by
  obtain ⟨hmem, hmin⟩ :=
    Classical.choose_spec (Tree.exists_least (complexitySet φ a) (complexitySet_nonempty φ a))
  obtain ⟨α, hα, hα'⟩ := hmem
  refine ⟨⟨α, hα', hα⟩, fun β hβ => ?_⟩
  exact hmin _ ⟨β, rfl, hβ⟩

end Work.ORHughesFree
