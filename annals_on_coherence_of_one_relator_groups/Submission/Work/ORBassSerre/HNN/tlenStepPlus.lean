import Mathlib
import Submission.Work.ORBassSerre.HNN.Defs

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ORBassSerre.HNN

open HNNExtension

/-- Appending the letter `t^ε` after `of m` to a reduced word `w` whose last letter is `(u, x)`
does not cancel, provided the concatenated letter `(u, x * m)` is not "absorbed" by the stable
letter `t^ε`; in that case the `t`-length grows by exactly one.

The whole content is that the list `w.toList` with its last entry `(u, x)` replaced by
`(u, x * m)` and the extra letter `(ε, 1)` appended is again a reduced word representing
`w.prod * of m * t^ε`; hence its length computes the `t`-length. -/
theorem tlenStepPlus {G : Type*} [Group G] {A B : Subgroup G} {φ : A ≃* B}
    (w : Work.ORBassSerre.HNN.RedWord (A := A) (B := B)) (m : G) (ε : ℤˣ)
    (L₁ : List (ℤˣ × G)) (u : ℤˣ) (x : G)
    (hw : w.toList = L₁ ++ [(u, x)])
    (hx : ¬(u = -ε ∧ x * m ∈ HNNExtension.toSubgroup A B u)) :
    Work.ORBassSerre.HNN.tlen (Work.ORBassSerre.HNN.step (Work.ORBassSerre.HNN.redProd φ w) m ε)
      = w.toList.length + 1 := by
  classical
  -- The word `L₁ ++ [(u, x * m), (ε, 1)]` is reduced: the only new adjacency is between
  -- `(u, x * m)` and `(ε, 1)`, and it is controlled by `hx`.
  have hchain : List.IsChain
      (fun a b : ℤˣ × G => a.2 ∈ HNNExtension.toSubgroup A B a.1 → a.1 = b.1)
      (L₁ ++ [(u, x * m), (ε, 1)]) := by
    rw [show L₁ ++ [(u, x * m), (ε, 1)] = (L₁ ++ [(u, x * m)]) ++ [(ε, 1)] from by
      simp [List.append_assoc]]
    have hw_chain : List.IsChain
        (fun a b : ℤˣ × G => a.2 ∈ HNNExtension.toSubgroup A B a.1 → a.1 = b.1)
        (L₁ ++ [(u, x)]) := hw ▸ w.chain
    obtain ⟨hc₁, -, hc₃⟩ := List.isChain_append.mp hw_chain
    refine List.IsChain.append ?_ (List.isChain_singleton _) ?_
    · -- the prefix: `L₁` is already a chain and the last entry gets `x` replaced by `x * m`
      refine List.IsChain.append hc₁ (List.isChain_singleton _) ?_
      intro y hy z hz
      simp only [List.head?_singleton, Option.mem_some_iff] at hz
      subst hz
      exact hc₃ y hy (u, x) (by simp)
    · -- the new adjacency `(u, x * m)` / `(ε, 1)`
      intro y hy z hz
      simp only [List.head?_singleton, Option.mem_some_iff] at hz
      subst hz
      simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or,
        Option.mem_some_iff] at hy
      subst hy
      intro hmem
      have hne : u ≠ -ε := fun h => hx ⟨h, hmem⟩
      rcases Int.units_eq_one_or u with rfl | rfl <;>
        rcases Int.units_eq_one_or ε with rfl | rfl <;> simp_all
  -- the corresponding reduced word, representing `redProd φ w * of m * t^ε`
  let w' : Work.ORBassSerre.HNN.RedWord (A := A) (B := B) :=
    { head := w.head, toList := L₁ ++ [(u, x * m), (ε, 1)], chain := hchain }
  have hprod : NormalWord.ReducedWord.prod φ w' =
      Work.ORBassSerre.HNN.step (Work.ORBassSerre.HNN.redProd φ w) m ε := by
    simp only [w', NormalWord.ReducedWord.prod, Work.ORBassSerre.HNN.step,
      Work.ORBassSerre.HNN.redProd, Work.ORBassSerre.HNN.ofE, Work.ORBassSerre.HNN.tpow,
      Work.ORBassSerre.HNN.tt, hw, List.map_append, List.map_cons, List.map_nil,
      List.prod_append, List.prod_cons, List.prod_nil, mul_one, map_mul, map_one]
    group
  have hlen : w'.toList.length = w.toList.length + 1 := by
    dsimp only [w']
    rw [hw]
    simp [List.length_append]
  rw [← hprod, tlen_prod w', hlen]

end Work.ORBassSerre.HNN
