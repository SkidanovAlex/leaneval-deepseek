/-
# The centralizer in `A₇` of an element of order `3` has order at most `36`

Let `x ∈ A₇` be an element of order `3`.  As a permutation of `Fin 7`, every cycle of `x` has
length dividing `3` and at least one cycle has length `3`, so the cycle type of `x` is either
`{3}` (a 3-cycle, with `4` fixed points) or `{3,3}` (a product of two disjoint 3-cycles, with one
fixed point); at most two 3-cycles fit into seven points.

This splits the argument into two cases, computing the centralizer inside the symmetric group
`S₇` (where `Equiv.Perm.nat_card_centralizer` gives its order) and then intersecting with the
index-two subgroup `A₇`:

* cycle type `{3}`: `C_{S₇}(x)` has order `(7 - 3)! · 3 · 1! = 72`.  It is *not* contained in
  `A₇`: that would force (by `Equiv.Perm.centralizer_le_alternating_iff`, whose second condition
  is `Fintype.card α ≤ x.cycleType.sum + 1`) `7 ≤ 3 + 1`.  Hence `A₇ ⊓ C_{S₇}(x)` has index two
  in `C_{S₇}(x)`, of order `72 / 2 = 36`.

* cycle type `{3,3}`: `C_{S₇}(x)` has order `(7 - 6)! · 9 · 2! = 18`, and its intersection with
  `A₇` has order at most `18 ≤ 36`.

Finally `C_{A₇}(x)` is exactly `A₇ ⊓ C_{S₇}(x)` (`Work.AUTA7.A7.nat_card_centralizer_coe`),
which is how the two cardinalities above become statements about `A₇`.
-/
import Mathlib
import Submission.Work.AUTA7.A7.CentralizerOrderThree
import Submission.Work.AUTA7.A7.CardInfMulTwoOfIndexTwo

namespace Work.CORE4

theorem A7OrderThreeCentralizer :
    ∀ x : alternatingGroup (Fin 7), orderOf x = 3 →
      Nat.card ↥(Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 7)))) ≤ 36 := by
  intro x hx
  classical
  -- `C_{A₇}(x)` is the intersection of `A₇` with the centralizer of `x` in `S₇`.
  rw [Work.AUTA7.A7.nat_card_centralizer_coe x]
  -- Abbreviate that `S₇`-centralizer.
  set C : Subgroup (Equiv.Perm (Fin 7)) :=
    Subgroup.centralizer ({(x : Equiv.Perm (Fin 7))} : Set (Equiv.Perm (Fin 7))) with hC
  -- The cycle type of `x` is `{3}` or `{3,3}`.
  rcases Work.AUTA7.A7.cycleType_eq_three_or_three_three hx with hcyc | hcyc
  · -- Case 1: `x` is a 3-cycle.
    -- `C_{S₇}(x) = ⟨x⟩ × S₄` has order `3 · 4! = 72`.
    have hcardC : Nat.card ↥C = 72 := by
      rw [hC, Equiv.Perm.nat_card_centralizer, hcyc]
      norm_num
    -- `C_{S₇}(x)` is not contained in `A₇`.
    have hnotle : ¬ C ≤ (alternatingGroup (Fin 7) : Subgroup (Equiv.Perm (Fin 7))) := by
      intro hle
      rw [hC] at hle
      obtain ⟨-, h2, -⟩ :=
        (Equiv.Perm.centralizer_le_alternating_iff (g := (x : Equiv.Perm (Fin 7)))).mp hle
      rw [hcyc] at h2
      norm_num at h2
    -- Hence `A₇ ⊓ C_{S₇}(x)` has index two in `C_{S₇}(x)`, so order `36`.
    have hmul := Work.AUTA7.A7.CardInfMulTwoOfIndexTwo (alternatingGroup (Fin 7)) C
      (alternatingGroup.index_eq_two (α := Fin 7)) hnotle
    rw [hcardC] at hmul
    have h36 :
        Nat.card ↥((alternatingGroup (Fin 7) : Subgroup (Equiv.Perm (Fin 7))) ⊓ C) = 36 := by
      rw [inf_comm]
      omega
    omega
  · -- Case 2: `x` is a product of two disjoint 3-cycles.
    -- `C_{S₇}(x) = (C₃ × C₃) ⋊ C₂` has order `1! · 9 · 2! = 18`.
    have hcardC : Nat.card ↥C = 18 := by
      rw [hC, Equiv.Perm.nat_card_centralizer, hcyc]
      norm_num
    -- The intersection with `A₇` has at most that order.
    have hle := Subgroup.card_le_of_le
      (H := (alternatingGroup (Fin 7) : Subgroup (Equiv.Perm (Fin 7))) ⊓ C) (K := C) inf_le_right
    rw [hcardC] at hle
    omega

end Work.CORE4
