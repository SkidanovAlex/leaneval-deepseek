import Mathlib
import Submission.Work.BMF.recursion.Defs
import Submission.Work.BMF.recursion.exists_perm_pair
import Submission.Work.BMF.recursion.powerSums_perm
import Submission.Work.BMF.recursion.S2_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The classical bound `S₂ ≤ k⁴ T`

The counting inequality of Wooley, *On Vinogradov's mean value theorem II*, Michigan Math. J.
**40** (1993), 175–180, §2, case (a): the number of matching pairs whose head is *non*-distinct on
both sides is at most `k⁴` times the number of matching pairs whose two first coordinates agree on
each side.

A pair counted by `S2pair S k Q hkS` has a collision `x i = x j` (`i ≠ j`) in the head of the first
tuple and a collision `y i' = y j'` (`i' ≠ j'`) in the head of the second tuple, so

`S2pair ≤ Σ_{i≠j} Σ_{i'≠j'} Tij S k Q hk hkS i j i' j'`

(the set `S2set` of such pairs is contained in the union of the `S2coll i j i' j'` over the
`S2QPairs k`; `Finset.card_le_card`, `Finset.card_biUnion_le`).  For each ordered pair
`((i,j),(i',j'))` of distinct head indices, relabelling the coordinates by permutations `σ`, `τ`
with `σ (i0) = i`, `σ (i1) = j`, `τ (i0) = i'`, `τ (i1) = j'` (`exists_perm_pair`) is a bijection of
the solution set (`powerSums_perm` shows the moment vector, hence the matching condition, is
preserved) which carries the collision conditions to each other, so `Tij ≤ Tdbl`.  Finally there are
`k⁴` ordered pairs of ordered pairs of head indices, giving `S2pair ≤ k⁴ · Tdbl`.
-/

set_option autoImplicit false

namespace Work.BMF.recursion

open Finset
open scoped BigOperators

noncomputable section

/-- **Relabelling a collision.**  For distinct head indices `i ≠ j` on the first side and `i' ≠ j'`
on the second side, the number of matching pairs whose head collides at `(i,j)` on the first side and
at `(i',j')` on the second side is at most the number of matching pairs whose two *distinguished*
first coordinates agree on each side, i.e. `Tij ≤ Tdbl`. -/
theorem S2_Tij_le_Tdbl (S k Q : ℕ) (hk : 2 ≤ k) (hkS : k ≤ S) (i j i' j' : Fin k)
    (hij : i ≠ j) (hi'j' : i' ≠ j') :
    Tij S k Q hk hkS i j i' j' ≤ Tdbl S k Q hk hkS := by
  classical
  have h01 : i0 k hk ≠ i1 k hk := by
    intro h
    have h' := congrArg Fin.val h
    simp only [i0, i1] at h'
    omega
  obtain ⟨σ, hσ0, hσ1⟩ := exists_perm_pair (hIdx hkS (i0 k hk)) (hIdx hkS (i1 k hk))
    (hIdx hkS i) (hIdx hkS j) (hIdx_ne hkS h01) (hIdx_ne hkS hij)
  obtain ⟨τ, hτ0, hτ1⟩ := exists_perm_pair (hIdx hkS (i0 k hk)) (hIdx hkS (i1 k hk))
    (hIdx hkS i') (hIdx hkS j') (hIdx_ne hkS h01) (hIdx_ne hkS hi'j')
  have hmain : (S2coll S k Q hkS i j i' j').card ≤ (S2Tset S k Q hk hkS).card := by
    refine Finset.card_le_card_of_injOn
      (fun p : PairSpace S Q => (fun s => p.1 (σ s), fun s => p.2 (τ s))) ?_ ?_
    · intro p hp
      rw [Finset.mem_coe, mem_S2coll] at hp
      obtain ⟨hpsol, heq1, heq2⟩ := hp
      rw [Finset.mem_coe, mem_S2Tset]
      refine ⟨?_, ?_, ?_⟩
      · simp only [solSet, Finset.mem_filter, Finset.mem_univ, true_and]
        exact Matches_comp_perm σ τ
          (by simpa only [solSet, Finset.mem_filter, Finset.mem_univ, true_and] using hpsol)
      · show p.1 (σ (hIdx hkS (i0 k hk))) = p.1 (σ (hIdx hkS (i1 k hk)))
        rw [hσ0, hσ1]
        exact heq1
      · show p.2 (τ (hIdx hkS (i0 k hk))) = p.2 (τ (hIdx hkS (i1 k hk)))
        rw [hτ0, hτ1]
        exact heq2
    · intro p _ q _ hpq
      have h1 : (fun s => p.1 (σ s)) = (fun s => q.1 (σ s)) := congrArg Prod.fst hpq
      have h2 : (fun s => p.2 (τ s)) = (fun s => q.2 (τ s)) := congrArg Prod.snd hpq
      refine Prod.ext ?_ ?_
      · funext s
        have hs := congrFun h1 (σ.symm s)
        simpa [Equiv.apply_symm_apply] using hs
      · funext s
        have hs := congrFun h2 (τ.symm s)
        simpa [Equiv.apply_symm_apply] using hs
  rwa [S2coll_card_eq_Tij S k Q hk hkS i j i' j', S2Tset_card_eq_Tdbl S k Q hk hkS] at hmain

/-- **Union bound over the collisions.**  A matching pair whose head is non-distinct on both sides
has a collision `x i = x j` with `i ≠ j` in the first head and a collision `y i' = y j'` with
`i' ≠ j'` in the second head, hence `S2pair` is at most the sum of `Tij` over all ordered pairs of
ordered pairs of distinct head indices. -/
theorem S2pair_le_sum_Tij (S k Q : ℕ) (hk : 2 ≤ k) (hkS : k ≤ S) :
    S2pair S k Q hkS ≤ ∑ q ∈ S2QPairs k, Tij S k Q hk hkS q.1.1 q.1.2 q.2.1 q.2.2 := by
  classical
  have hsub : S2set S k Q hkS ⊆
      (S2QPairs k).biUnion (fun q => S2coll S k Q hkS q.1.1 q.1.2 q.2.1 q.2.2) := by
    intro p hp
    rw [mem_S2set] at hp
    obtain ⟨hpsol, h1, h2⟩ := hp
    simp only [HD] at h1 h2
    push Not at h1 h2
    obtain ⟨i, j, hij, heq1⟩ := h1
    obtain ⟨i', j', hi'j', heq2⟩ := h2
    rw [Finset.mem_biUnion]
    refine ⟨((i, j), (i', j')), ?_, ?_⟩
    · rw [mem_S2QPairs]
      exact ⟨hij, hi'j'⟩
    · rw [mem_S2coll]
      exact ⟨hpsol, heq1, heq2⟩
  calc S2pair S k Q hkS = (S2set S k Q hkS).card := (S2set_card_eq_S2pair S k Q hkS).symm
    _ ≤ ((S2QPairs k).biUnion
          (fun q => S2coll S k Q hkS q.1.1 q.1.2 q.2.1 q.2.2)).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ q ∈ S2QPairs k, (S2coll S k Q hkS q.1.1 q.1.2 q.2.1 q.2.2).card :=
        Finset.card_biUnion_le
    _ = ∑ q ∈ S2QPairs k, Tij S k Q hk hkS q.1.1 q.1.2 q.2.1 q.2.2 :=
        Finset.sum_congr rfl
          (fun q _ => S2coll_card_eq_Tij S k Q hk hkS q.1.1 q.1.2 q.2.1 q.2.2)

/-- The number of matching pairs whose head is *non*-distinct on both sides is at most `k⁴` times
the number of matching pairs where the two *first* coordinates agree on each side
(Wooley, Michigan Math. J. **40** (1993), 175–180, §2, case (a); the classical `S₂ ≤ k⁴ T`).

Route.  A pair counted by `S2pair` has a collision `x i = x j` in the head (`i ≠ j`) and a collision
`y i' = y j'`; this gives the union bound
`S2pair ≤ Σ_{i≠j} Σ_{i'≠j'} Tij S k Q hk hkS i j i' j'` (`Finset.card_le_card` for the subset
inclusion into a `Finset.biUnion`, plus `Finset.card_biUnion_le`).  For each pair of index pairs,
`Tij S k Q hk hkS i j i' j' = Tdbl S k Q hk hkS`: by `exists_perm_pair` choose
`σ, τ : Equiv.Perm (Fin S)` with `σ (hIdx hkS (i0 k hk)) = hIdx hkS i`,
`σ (hIdx hkS (i1 k hk)) = hIdx hkS j` and similarly for `τ` and `i', j'`; then
`(x, y) ↦ (x ∘ σ, y ∘ τ)` is a bijection of the solution set (`powerSums_perm` shows the moment
vector, hence the matching condition, is preserved) carrying the collision conditions to each other.
Finally `k(k-1)` ordered pairs on each side give the factor `k²(k-1)² ≤ k⁴`. -/
theorem S2_le_k4_Tdbl (S k Q : ℕ) (hk : 2 ≤ k) (hkS : k ≤ S) :
    (S2pair S k Q hkS : ℝ) ≤ (k : ℝ) ^ 4 * (Tdbl S k Q hk hkS : ℝ) := by
  classical
  have hcard : (S2QPairs k).card ≤ k ^ 4 := by
    rw [S2QPairs]
    calc (Finset.univ.filter
          (fun q : (Fin k × Fin k) × (Fin k × Fin k) => q.1.1 ≠ q.1.2 ∧ q.2.1 ≠ q.2.2)).card
        ≤ (Finset.univ : Finset ((Fin k × Fin k) × (Fin k × Fin k))).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
      _ = k ^ 4 := by
          rw [Finset.card_univ, Fintype.card_prod, Fintype.card_prod, Fintype.card_fin]
          ring
  have hsum : ∑ q ∈ S2QPairs k, Tij S k Q hk hkS q.1.1 q.1.2 q.2.1 q.2.2
      ≤ (S2QPairs k).card * Tdbl S k Q hk hkS := by
    calc ∑ q ∈ S2QPairs k, Tij S k Q hk hkS q.1.1 q.1.2 q.2.1 q.2.2
        ≤ ∑ _q ∈ S2QPairs k, Tdbl S k Q hk hkS := by
          refine Finset.sum_le_sum (fun q hq => ?_)
          rw [mem_S2QPairs] at hq
          exact S2_Tij_le_Tdbl S k Q hk hkS q.1.1 q.1.2 q.2.1 q.2.2 hq.1 hq.2
      _ = (S2QPairs k).card * Tdbl S k Q hk hkS := by
          rw [Finset.sum_const_nat (fun _ _ => rfl)]
  have hnat : S2pair S k Q hkS ≤ k ^ 4 * Tdbl S k Q hk hkS :=
    (S2pair_le_sum_Tij S k Q hk hkS).trans (hsum.trans (Nat.mul_le_mul_right _ hcard))
  calc (S2pair S k Q hkS : ℝ) ≤ ((k ^ 4 * Tdbl S k Q hk hkS : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = (k : ℝ) ^ 4 * (Tdbl S k Q hk hkS : ℝ) := by push_cast; ring

end

end Work.BMF.recursion
