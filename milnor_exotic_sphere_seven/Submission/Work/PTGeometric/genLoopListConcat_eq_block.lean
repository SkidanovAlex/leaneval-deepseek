import Mathlib
import Submission.Work.PTGeometric.blockPt
import Submission.Work.PTGeometric.genLoopListConcat_eq_get

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: on the `k`-th dyadic block the concatenation reads `l[k]` at the block point

`Work.PTGeometric.genLoopListConcat i l` is the iterated concatenation of a list of cube loops `l`
along the coordinate `i`, and `Work.PTGeometric.genLoopListConcatStep i l t` computes the block of
the cube point `t`: the index `k` of the element of the list that is consulted, together with the
reparametrised cube point at which it is read (`Work.PTGeometric.genLoopListConcat_eq_get`).

This file identifies that reparametrised point with the block reparametrisation
`Work.PTGeometric.blockPt i k t` on the *interior* of the `k`-th dyadic block: if
`1 < 2 ^ (k+1) * t i` and `2 ^ k * t i < 1` (so that `t i` lies strictly between the two dyadic
boundaries `2 ^ (-(k+1))` and `2 ^ (-k)`), then

`genLoopListConcat i l t = l[k] (blockPt i k t)`.

## Main results

* `Work.PTGeometric.blockPt_update_eq_blockPt` — the bookkeeping that the block
  reparametrisation commutes with passing from the `k`-th block to its first half;
* `Work.PTGeometric.genLoopListConcatStep_eq_block` — the same statement for the block recursion;
* `Work.PTGeometric.genLoopListConcat_eq_block` — the target.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped Topology unitInterval
open Function Set

namespace Work.PTGeometric

noncomputable section

variable {N : Type*} [DecidableEq N] {X : Type} [TopologicalSpace X] {x : X}

/-! ## The block reparametrisation of the first half of a block

Descending from the `k`-th block of the cube into its first half passes from the point `t` to the
point `t' = update t i (projIcc 0 1 _ (2 * t i))`, whose `i`-th coordinate is `2 * t i`.  The block
reparametrisation of the `(k-1)`-st block at `t'` is the block reparametrisation of the `k`-th block
at `t`. -/
lemma blockPt_update_eq_blockPt (i : N) (k' : ℕ) (t : N → Set.Icc (0:ℝ) 1)
    (hc : (t i : ℝ) ≤ 1/2)
    (hlo1 : 1 < (2:ℝ) ^ (k'+1) * (((Function.update t i (Set.projIcc 0 1 (by norm_num) (2 * (t i : ℝ))) i : Set.Icc (0:ℝ) 1)) : ℝ))
    (hhi1 : (2:ℝ) ^ k' * (((Function.update t i (Set.projIcc 0 1 (by norm_num) (2 * (t i : ℝ))) i : Set.Icc (0:ℝ) 1)) : ℝ) < 1)
    (hlo : 1 < (2:ℝ) ^ (k'+1+1) * (t i : ℝ)) (hhi : (2:ℝ) ^ (k'+1) * (t i : ℝ) < 1) :
    blockPt i k' (Function.update t i (Set.projIcc 0 1 (by norm_num) (2 * (t i : ℝ)))) hlo1 hhi1
      = blockPt i (k'+1) t hlo hhi := by
  have hmem2 : 2 * (t i : ℝ) ∈ Set.Icc (0:ℝ) 1 :=
    ⟨by linarith [(t i).2.1], by linarith⟩
  have ht'i : (((Function.update t i (Set.projIcc 0 1 (by norm_num) (2 * (t i : ℝ))) i : Set.Icc (0:ℝ) 1)) : ℝ) = 2 * (t i : ℝ) := by
    rw [Function.update_self, Set.projIcc_of_mem (show (0:ℝ) ≤ 1 by norm_num) hmem2]
  funext m
  apply Subtype.ext
  rw [blockPt_apply_coe, blockPt_apply_coe]
  by_cases hm : m = i
  · rw [if_pos hm, if_pos hm, ht'i]
    congr 1
    rw [pow_succ]
    ring
  · rw [if_neg hm, if_neg hm, Function.update_of_ne hm]

/-! ## The block formula for the block recursion -/

/-- **On the interior of the `k`-th dyadic block the block recursion consults the `k`-th element of
the list at the block reparametrisation `blockPt i k t`.** -/
theorem genLoopListConcatStep_eq_block (i : N) (l : List (GenLoop N X x))
    (t : N → Set.Icc (0 : ℝ) 1) (k : ℕ) (hk : k < l.length)
    (hlo : 1 < (2 : ℝ) ^ (k + 1) * (t i : ℝ)) (hhi : (2 : ℝ) ^ k * (t i : ℝ) < 1) :
    genLoopListConcatStep i l t = (k, blockPt i k t hlo hhi) := by
  induction l generalizing k t with
  | nil => exact absurd hk (Nat.not_lt_zero k)
  | cons g l' ih =>
    rcases k with _ | k'
    · -- the block index is `0`: the coordinate is already in the second half
      have hlo2 : (1:ℝ) < 2 * (t i : ℝ) := by simpa using hlo
      have hc : ¬ (((t i : Set.Icc (0 : ℝ) 1)) : ℝ) ≤ 1/2 := by intro h; linarith
      rw [genLoopListConcatStep_cons_gt i g l' t hc]
      refine Prod.ext rfl ?_
      rw [blockPt_eq]
      rw [show (2:ℝ) ^ ((0:ℕ) + 1) = 2 from by norm_num]
      rfl
    · -- the block index is `k' + 1`: descend into the first half of the cube
      have hc : (((t i : Set.Icc (0 : ℝ) 1)) : ℝ) ≤ 1/2 := by
        have hle : (2:ℝ) ≤ 2 ^ (k' + 1) := by
          rw [pow_succ']
          have : (1:ℝ) ≤ 2 ^ k' := one_le_pow₀ (by norm_num)
          linarith
        have hti : 0 ≤ (t i : ℝ) := (t i).2.1
        have hh : (2:ℝ) ^ (k' + 1) * (t i : ℝ) < 1 := hhi
        nlinarith [hh, hle, hti]
      set t' : N → Set.Icc (0:ℝ) 1 :=
        Function.update t i (Set.projIcc 0 1 (by norm_num) (2 * (t i : ℝ))) with ht'def
      rw [genLoopListConcatStep_cons_le i g l' t hc]
      have hmem2 : 2 * (t i : ℝ) ∈ Set.Icc (0:ℝ) 1 :=
        ⟨by linarith [(t i).2.1], by linarith⟩
      have ht'i : (t' i : ℝ) = 2 * (t i : ℝ) := by
        rw [ht'def, Function.update_self, Set.projIcc_of_mem (show (0:ℝ) ≤ 1 by norm_num) hmem2]
      have hpoweq : (2:ℝ) ^ (Nat.succ k' + 1) = 2 ^ (k'+1) * 2 := by
        rw [show Nat.succ k' + 1 = (k'+1) + 1 from rfl, pow_succ]
      have hlo1 : 1 < (2:ℝ) ^ (k'+1) * (t' i : ℝ) := by
        rw [ht'i]
        have : (2:ℝ)^(k'+1) * (2 * (t i:ℝ)) = 2 ^ (Nat.succ k' + 1) * (t i : ℝ) := by
          rw [hpoweq]; ring
        rw [this]; exact hlo
      have hhi1 : (2:ℝ) ^ k' * (t' i : ℝ) < 1 := by
        rw [ht'i]
        have : (2:ℝ)^k' * (2 * (t i:ℝ)) = 2 ^ (Nat.succ k') * (t i : ℝ) := by
          rw [show Nat.succ k' = k' + 1 from rfl, pow_succ]; ring
        rw [this]; exact hhi
      have hk' : k' < l'.length := by
        simp only [List.length_cons] at hk; omega
      rw [ih t' k' hk' hlo1 hhi1]
      refine Prod.ext rfl ?_
      exact blockPt_update_eq_blockPt i k' t hc hlo1 hhi1 hlo hhi

/-! ## The block formula for the concatenation -/

theorem genLoopListConcat_eq_block {N : Type*} [DecidableEq N] {X : Type} [TopologicalSpace X]
    {x : X} (i : N) (l : List (GenLoop N X x)) (t : N → Set.Icc (0 : ℝ) 1) (k : ℕ)
    (hk : k < l.length) (hlo : 1 < (2 : ℝ) ^ (k + 1) * (t i : ℝ))
    (hhi : (2 : ℝ) ^ k * (t i : ℝ) < 1) :
    Work.PTGeometric.genLoopListConcat i l t
      = l[k] (Work.PTGeometric.blockPt i k t hlo hhi) := by
  rw [genLoopListConcat_eq_get]
  rw [genLoopListConcatStep_eq_block i l t k hk hlo hhi]
  rw [dif_pos hk]
  rfl

end

end Work.PTGeometric
