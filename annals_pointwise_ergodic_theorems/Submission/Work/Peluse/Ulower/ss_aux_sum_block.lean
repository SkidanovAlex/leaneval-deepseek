import Mathlib
import Submission.Work.Peluse.Basic

namespace Work.Peluse.Ulower

/-- The interval `[a,c]` splits as `[a,b] ∪ [b+1,c]` as soon as `a ≤ b+1` and `b ≤ c`. -/
private lemma Icc_union_Icc_eq' (a b c : ℕ) (h1 : a ≤ b + 1) (h2 : b ≤ c) :
    Finset.Icc a c = Finset.Icc a b ∪ Finset.Icc (b + 1) c := by
  ext y
  simp only [Finset.mem_Icc, Finset.mem_union]
  omega

/-- Consecutive intervals `[a,b]` and `[b+1,c]` are disjoint. -/
private lemma disjoint_Icc_Icc' (a b c : ℕ) :
    Disjoint (Finset.Icc a b) (Finset.Icc (b + 1) c) := by
  rw [Finset.disjoint_left]
  intro y hy hy'
  simp only [Finset.mem_Icc] at hy hy'
  omega

/-- **Decomposition of `[1,N]` into blocks of length `L` plus a remainder.**  For `L ≥ 1`,
`J · L ≤ N` and `g : ℕ → ℂ`:

`∑_{y ∈ [1,N]} g y = ∑_{j=1}^{J} ∑_{y ∈ [(j−1)L+1, jL]} g y + ∑_{y ∈ [JL+1, N]} g y`.

(This is the block decomposition used by the periodisation/splitting step of Peluse's §9.) -/
theorem ss_aux_sum_block {L J N : ℕ} (hL : 1 ≤ L) (hJ : J * L ≤ N) (g : ℕ → ℂ) :
    ∑ y ∈ Finset.Icc 1 N, g y
      = (∑ j ∈ Finset.Icc 1 J, ∑ y ∈ Finset.Icc ((j - 1) * L + 1) (j * L), g y)
        + ∑ y ∈ Finset.Icc (J * L + 1) N, g y := by
  -- The hypothesis `hL : 1 ≤ L` is not needed by the argument below (the statement also holds for
  -- `L = 0`, where all the blocks are empty), but it is part of the statement.
  have _hL : 1 ≤ L := hL
  -- Induct on the number `J` of full blocks, peeling off the last block at each step.
  induction J with
  | zero => simp
  | succ J ih =>
      -- the induction hypothesis applies with the same `N`
      have hmul : J * L ≤ (J + 1) * L := Nat.mul_le_mul_right L (Nat.le_succ J)
      have hJL : J * L ≤ N := le_trans hmul hJ
      rw [ih hJL]
      -- peel the last term `j = J+1` off the block sum
      rw [Finset.sum_Icc_succ_top (show 1 ≤ J + 1 by omega)]
      -- split the remainder `[J*L+1, N]` at `(J+1)*L`
      have h1 : J * L + 1 ≤ (J + 1) * L + 1 := Nat.succ_le_succ hmul
      rw [Icc_union_Icc_eq' (J * L + 1) ((J + 1) * L) N h1 hJ,
        Finset.sum_union (disjoint_Icc_Icc' (J * L + 1) ((J + 1) * L) N)]
      -- identify the last block with the peeled term and collect
      simp only [Nat.add_sub_cancel]
      ring

end Work.Peluse.Ulower
