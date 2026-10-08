import Mathlib
import Submission.Work.DoubleTransitivity.Action
import Submission.Work.DoubleTransitivity.App2.app2_3

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Peterfalvi, Appendix II (4): double transitivity without a distinguished point

This file proves `Work.DoubleTransitivity.App2.app2_4`, the formalisation of Peterfalvi,
*Le théorème de Bender–Suzuki I*, Appendix II (4):

> Suppose that for every pair of distinct points `a ≠ b` of `E` there is a `p`-subgroup of `X`
> whose set of fixed points is exactly `{a, b}`, and that `E` has at least `3` elements.  Then
> `X` acts `2`-transitively on `E`.

The statement of Appendix II (3) (`app2_3`) requires a distinguished point `a` of `E` which is
not fixed by all of `X`.  The point of (4) is that such a point can always be produced: pick
distinct `a, b ∈ E`, let `P` be a `p`-subgroup with `E_P = {a, b}`, and let `c` be a third point
of `E`.  Since `c ∉ E_P`, some element of `P` moves `c`, so `X` does not fix `c`; and `(h)` gives,
for every `d ≠ c`, a `p`-subgroup with fixed point set exactly `{c, d}`.  Now `app2_3` applied at
`c` yields the conclusion.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.DoubleTransitivity.App2

open Work.DoubleTransitivity

/-- **Peterfalvi, Appendix II (4)**: if every pair of distinct points is the fixed point set of
a `p`-subgroup of `X` and `E` has at least three points, then `X` acts `2`-transitively on `E`. -/
theorem app2_4 {X E : Type} [Group X] [MulAction X E] [Finite X] [Fintype E]
    {p : ℕ} [Fact p.Prime] (hE : 3 ≤ (Set.univ : Set E).ncard)
    (h : ∀ a b : E, a ≠ b → ∃ P : Subgroup X, IsPGroup p P ∧ fixedBySub P = {a, b}) :
    MulAction.IsMultiplyPretransitive X E 2 := by
  have hcard : 3 ≤ Fintype.card E := by
    have h' := hE
    rw [Set.ncard_univ, Nat.card_eq_fintype_card] at h'
    exact h'
  -- two distinct points of `E`
  have hne : Nonempty E := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨a⟩ := hne
  obtain ⟨b, hba⟩ := Fintype.exists_ne_of_one_lt_card (α := E) (by omega) a
  obtain ⟨P, hPpg, hPfix⟩ := h a b hba.symm
  -- a third point, outside the fixed point set of `P`
  have hnotsub : ¬ (Set.univ : Set E) ⊆ ({a, b} : Set E) := by
    intro hsub
    have hle : (Set.univ : Set E).ncard ≤ ({a, b} : Set E).ncard := Set.ncard_le_ncard hsub
    rw [Set.ncard_pair hba.symm] at hle
    omega
  obtain ⟨c, -, hc⟩ := Set.not_subset.mp hnotsub
  -- `c` is moved by an element of `P`, so not all of `X` fixes `c`
  have hmoved : ¬ ∀ x : X, x • c = c := by
    intro htriv
    refine hc ?_
    rw [← hPfix]
    exact mem_fixedBySub.mpr fun m _ => htriv m
  -- apply Appendix II (3) at the point `c`
  exact app2_3 (X := X) (E := E) (p := p) (a := c)
    (fun d hd =>
      h c d (Ne.symm (by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hd)))
    hmoved

end Work.DoubleTransitivity.App2
