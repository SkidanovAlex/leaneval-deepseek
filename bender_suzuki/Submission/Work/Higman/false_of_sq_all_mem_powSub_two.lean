/-
Copyright (c) 2024. All rights reserved.

# Suzuki 2-groups: the case `C² ⊆ A²` of the alternating-pairing argument

Higman, *Suzuki 2-groups*, Illinois J. Math. 7 (1963), Lemma 2 (p. 83):

> **LEMMA 2.** If `A` is an abelian normal `X`-subgroup of `G`, which is not `1`, then for no
> element `u` of `G` not in `A` is both `u² ∈ A²` and `[u, A] ⊆ A⁴`.

Here we record the special case needed for the `ξ`-alternating-pairing contradiction in
`Submission/Work/Higman/xi_alt_pairing_false.lean`: if `A` is a `ξ`-invariant abelian normal
subgroup of a Suzuki 2-group with `Ω₁(P) = A² ≠ 1`, if `C` is a subgroup with `A < C`
centralizing `A`, and if *every* element of `C` squares into `A²`, then we get a contradiction.
Indeed any `u ∈ C \ A` then satisfies `u² ∈ A²` and `[u, A] = 1 ⊆ A⁴`, contradicting
`Work.Higman.higman_lemma2`.
-/

import Mathlib
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.higman_lemma2

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped commutatorElement

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.Higman

variable {P : Type} [Group P] [Finite P]

/-- If every element of `C` has its square in `A ^ (2)` and `C` is not `A`, then Higman's
Lemma 2 is contradicted (the case `C ^ (2) ⊆ A ^ (2)` of the alternating-pairing argument). -/
theorem false_of_sq_all_mem_powSub_two (h : Work.Higman.IsSuzuki2Grp P) {A C : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A) (hAC : A ≤ C) (hCA : C ≠ A)
    (hOmega : Work.Higman.omega1 P = Work.Higman.powSub A 2)
    (hA2ne : Work.Higman.powSub A 2 ≠ ⊥)
    (hZ : ∀ c ∈ C, ∀ a ∈ A, c * a = a * c)
    (hSq : ∀ x ∈ C, x ^ 2 ∈ Work.Higman.powSub A 2) : False := by
  have hOm : omega1 P ≤ A := by rw [hOmega]; exact powSub_le (by norm_num)
  have hAne : A ≠ ⊥ := by
    intro hbot
    refine hA2ne (le_bot_iff.mp ?_)
    rw [hbot]
    exact powSub_le (by norm_num)
  have hex : ∃ u : P, u ∈ C ∧ u ∉ A := by
    by_contra hcon
    push Not at hcon
    exact hCA (le_antisymm (fun x hx => hcon x hx) hAC)
  obtain ⟨u, huC, huA⟩ := hex
  refine higman_lemma2 h hA hOm hAne huA ⟨hSq u huC, ?_⟩
  intro a ha
  have h1 : ⁅u, a⁆ = 1 := by
    rw [commutatorElement_def, hZ u huC a ha]
    group
  rw [h1]
  exact (powSub A 4).one_mem

end Work.Higman
