/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Subgroup complexities: `Tree_H ≤ Tree_G`

[JZLA20, Theorem 6.1] compares the `G`-complexity of an element `b ∈ D_{H,U}` with its
`H`-complexity: since `Rat(Kˣ × H) ⊆ Rat(Kˣ × G)` via `RatU.ofSubgroup`, every `H`-realiser of `b`
is a `G`-realiser, so

`Tree_G(b) ≤ Tree_H(b)`.

This file proves that comparison, together with the basic glue relating the division closures
`D_{H,U} = divisionClosure (Set.range (φ ∘ K[H] ↪ K[G]))` to `D_{G,U}`.
-/
import Mathlib
import Submission.Work.ORHughesFree.Section6.TreeG
import Submission.Work.ORHughesFree.Section6.Reduce

set_option autoImplicit false

namespace Work.ORHughesFree

/-- The image of `K[↥H]` in `K[G]` under the inclusion of group algebras. -/
noncomputable def inducedMapRing {K : Type} [Field K] {G : Type} [Group G] (H : Subgroup G) :
    MonoidAlgebra K ↥H →+* MonoidAlgebra K G :=
  MonoidAlgebra.mapDomainRingHom K H.subtype

theorem range_inducedMapRing_le {K : Type} [Field K] {G : Type} [Group G] {U : Type} [Ring U]
    (φ : MonoidAlgebra K G →+* U) (H : Subgroup G) :
    Set.range (φ.comp (inducedMapRing (K := K) H)) ⊆ Set.range φ := by
  rintro y ⟨x, rfl⟩
  exact ⟨inducedMapRing (K := K) H x, rfl⟩

/-- **`Tree_G ≤ Tree_H`** ([JZLA20, Theorem 6.1]): every `H`-realiser of an element of `D_{G,U}`
is a `G`-realiser, so the `G`-complexity is at most the `H`-complexity. -/
theorem treeG_le_treeOfRat_ofSubgroup {K : Type} [Field K] {G : Type} [Group G] {U : Type} [Ring U]
    (φ : MonoidAlgebra K G →+* U) (H : Subgroup G)
    (β : RatU ↥(unitsTimesSubgroup (K := K) H)) :
    Tree.le (treeG φ ((Phi φ) (RatU.ofSubgroup (unitsTimesSubgroup (K := K) H) β)))
      (Rat.treeOfRat ↥(unitsTimesSubgroup (K := K) H) β) := by
  rw [← Rat.treeOfRat_ofSubgroup (unitsTimesSubgroup (K := K) H) β]
  exact (treeG_spec φ _).2 _ rfl

/-- The `G`-complexity is realised: `treeG φ a ≤ Tree α` for every realiser `α` of `a`. -/
theorem treeG_le_treeOfRat {K : Type} [Field K] {G : Type} [Group G] {U : Type} [Ring U]
    (φ : MonoidAlgebra K G →+* U) (α : RatU (Kˣ × G)) :
    Tree.le (treeG φ (Phi φ α)) (Rat.treeOfRat (Kˣ × G) α) :=
  (treeG_spec φ _).2 α rfl

/-- **The finitely generated reduction, in the form used by [JZLA20, Theorem 6.1].**  For every
`a ∈ D_{G,U}` there is a finitely generated `H ≤ G` and a minimal realiser `α' ∈ Rat(Kˣ × H)` of
`a`, i.e. `Φ_{H,U}(α') = a` and `Tree_{H}(a) = Tree α'`; and `Tree_H(a) = Tree_G(a)`.

The proof takes a `G`-realiser `α` of the `G`-complexity of `a`
(`Section6.treeG_spec`), applies the finitely generated reduction
(`Section6.exists_fg_reduction`, which preserves the complexity by
`Rat.treeOfRat_ofSubgroup`), and compares the two complexities with
`treeG_le_treeOfRat_ofSubgroup`. -/
theorem exists_fg_reduction_realizing {K : Type} [Field K] {G : Type} [Group G] {U : Type} [Ring U]
    (φ : MonoidAlgebra K G →+* U) (a : ↥(divisionClosure (Set.range φ))) :
    ∃ (H : Subgroup G) (α' : RatU ↥(unitsTimesSubgroup (K := K) H)),
      H.FG ∧
      (Phi φ) (RatU.ofSubgroup (unitsTimesSubgroup (K := K) H) α') = a ∧
      Rat.treeOfRat ↥(unitsTimesSubgroup (K := K) H) α' = treeG φ a ∧
      ∀ β : RatU ↥(unitsTimesSubgroup (K := K) H),
        (Phi φ) (RatU.ofSubgroup (unitsTimesSubgroup (K := K) H) β) = a →
        Tree.le (Rat.treeOfRat ↥(unitsTimesSubgroup (K := K) H) α')
          (Rat.treeOfRat ↥(unitsTimesSubgroup (K := K) H) β) := by
  obtain ⟨α, hα, htree⟩ := (treeG_spec φ a).1
  obtain ⟨H, α', hHfg, hα', htree'⟩ := exists_fg_reduction (K := K) α
  refine ⟨H, α', hHfg, ?_, ?_, ?_⟩
  · rw [hα', hα]
  · rw [htree', htree]
  · intro β hβ
    have h1 : Tree.le (treeG φ a) (Rat.treeOfRat ↥(unitsTimesSubgroup (K := K) H) β) := by
      have h2 := treeG_le_treeOfRat φ (RatU.ofSubgroup (unitsTimesSubgroup (K := K) H) β)
      rw [hβ] at h2
      rwa [Rat.treeOfRat_ofSubgroup (unitsTimesSubgroup (K := K) H) β] at h2
    rw [htree', htree]
    exact h1

end Work.ORHughesFree
