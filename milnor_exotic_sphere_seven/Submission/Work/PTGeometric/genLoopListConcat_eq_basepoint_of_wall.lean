import Mathlib
import Submission.Work.PTGeometric.SourceFamily

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: the iterated concatenation is the basepoint on the leading dyadic blocks

`Work.PTGeometric.genLoopListConcat i l` is the iterated concatenation of a list of cube loops along
the coordinate `i` (Mathlib's `GenLoop.transAt`, applied from the right, so that its class is the
product of the classes of the list).  The concatenation splits the cube into `l.length` dyadic blocks
in the coordinate `i`: the recursion `Work.PTGeometric.genLoopListConcatStep` descends into the tail
of the list, incrementing the block index, as long as the reparametrised `i`-coordinate is still
`≤ 1/2`, and stops otherwise.  Consequently the concatenation reads the basepoint `x` as soon as the
recursion has run off the end of the list.

This file records the two configurations in which the `i`-coordinate of the input forces the value of
the concatenation to be the basepoint:

* `Work.PTGeometric.pow_le_genLoopListConcat_eq_basepoint` — the coordinate lies in the leading
  dyadic block of length `2 ^ l.length`, i.e. `2 ^ l.length * t i ≤ 1`: all `l.length` descents are
  performed, the recursion runs off the end of the list, and the value is `x`.
* `Work.PTGeometric.pow_eq_one_genLoopListConcat_eq_basepoint` — the coordinate is exactly at the
  *end* of a block, `2 ^ c * t i = 1` for some `c < l.length`: the `c`-th block is consulted at a
  cube point whose `i`-th coordinate is exactly `1`, hence a boundary point, where the `c`-th loop is
  the basepoint by definition.

Both are proved by the same induction on the list, following the recursion
`genLoopListConcatStep`: in the first case the `i`-coordinate is `≤ 1/2` so one descends with the
doubled coordinate; in the second case the block index is decremented, the `c = 0` case being the
boundary case `t i = 1`.

## Main results

* `Work.PTGeometric.pow_le_genLoopListConcat_eq_basepoint`
* `Work.PTGeometric.pow_eq_one_genLoopListConcat_eq_basepoint`
* `Work.PTGeometric.genLoopListConcat_eq_basepoint_of_wall` — the two cases combined.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace Work.PTGeometric

noncomputable section

/-- **The leading dyadic blocks of the iterated concatenation are the basepoint.**  If the
`i`-th coordinate of the cube point is small enough that all `l.length` dyadic blocks are already
spent, `2 ^ l.length * (t i) ≤ 1`, then the recursion has run off the end of the list and the
concatenation is the basepoint.

This is proved by induction on the list along the recursion `genLoopListConcatStep`: on the first half
(`t i ≤ 1/2`) the concatenation descends into the tail of the list at the doubled coordinate, and the
hypothesis survives the doubling. -/
theorem pow_le_genLoopListConcat_eq_basepoint {N : Type*} [DecidableEq N] {X : Type}
    [TopologicalSpace X] {x : X} (i : N) (l : List (GenLoop N X x)) :
    ∀ t : N → Set.Icc (0 : ℝ) 1,
      (2 : ℝ) ^ l.length * (t i : ℝ) ≤ 1 → genLoopListConcat i l t = x := by
  induction l with
  | nil => intro t _; simp
  | cons g l ih =>
    intro t h
    rw [genLoopListConcat_cons]
    rw [List.length_cons] at h
    have hpow : (2 : ℝ) ^ (l.length + 1) = 2 * (2 : ℝ) ^ l.length := by
      rw [pow_succ]; ring
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ l.length := one_le_pow₀ (by norm_num)
    have hti0 : (0 : ℝ) ≤ (t i : ℝ) := (t i).2.1
    have h2 : 2 * (t i : ℝ) ≤ 1 := by
      have hCt : (t i : ℝ) ≤ (2 : ℝ) ^ l.length * (t i : ℝ) := by
        simpa using mul_le_mul_of_nonneg_right h1 hti0
      calc 2 * (t i : ℝ) ≤ 2 * ((2 : ℝ) ^ l.length * (t i : ℝ)) := by linarith
        _ = (2 : ℝ) ^ (l.length + 1) * (t i : ℝ) := by rw [hpow]; ring
        _ ≤ 1 := h
    have hmem : 2 * (t i : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, h2⟩
    have hle : ((t i : Set.Icc (0 : ℝ) 1) : ℝ) ≤ 1 / 2 := by linarith
    rw [genLoop_transAt_apply_of_le i (genLoopListConcat i l) g hle]
    refine ih _ ?_
    rw [Function.update_self, Set.projIcc_of_mem (by norm_num) hmem]
    calc (2 : ℝ) ^ l.length * (2 * (t i : ℝ)) = (2 : ℝ) ^ (l.length + 1) * (t i : ℝ) := by
          rw [hpow]; ring
      _ ≤ 1 := h

/-- **The end of a dyadic block of the iterated concatenation is the basepoint.**  If the `i`-th
coordinate of the cube point is exactly the right end of one of the blocks,
`2 ^ c * (t i) = 1` for some `c < l.length`, then the `c`-th block of the concatenation is consulted
at the cube point whose `i`-th coordinate is exactly `1`; that is a boundary point, so the `c`-th loop
reads the basepoint there.

The induction follows the recursion: for `c = 0` the coordinate is `1`, the recursion stops
immediately and the *first* element of the list is read at a boundary point; for `c = c' + 1` the
coordinate is `≤ 1/2`, the recursion descends into the tail with the doubled coordinate, and the index
drops to `c'`. -/
theorem pow_eq_one_genLoopListConcat_eq_basepoint {N : Type*} [DecidableEq N] {X : Type}
    [TopologicalSpace X] {x : X} (i : N) (l : List (GenLoop N X x)) :
    ∀ t : N → Set.Icc (0 : ℝ) 1,
      (∃ c < l.length, (2 : ℝ) ^ c * (t i : ℝ) = 1) → genLoopListConcat i l t = x := by
  induction l with
  | nil =>
    intro t h
    obtain ⟨c, hc, -⟩ := h
    exact absurd hc (Nat.not_lt_zero c)
  | cons g l ih =>
    intro t h
    rw [genLoopListConcat_cons]
    obtain ⟨c, hc, heq⟩ := h
    rw [List.length_cons] at hc
    rcases c with _ | c'
    · -- the recursion stops at once: the coordinate `i` is `1`
      rw [pow_zero, one_mul] at heq
      have hgt : ¬ (((t i : Set.Icc (0 : ℝ) 1) : ℝ) ≤ 1 / 2) := by rw [heq]; norm_num
      rw [genLoop_transAt_apply_of_gt i (genLoopListConcat i l) g hgt]
      have hb : (Function.update t i (Set.projIcc (0 : ℝ) 1 (by norm_num)
          (2 * (t i : ℝ) - 1))) i = 1 := by
        rw [Function.update_self]
        apply Subtype.ext
        rw [heq, Set.coe_projIcc]
        norm_num
      exact GenLoop.boundary g _ ⟨i, Or.inr hb⟩
    · -- one descent: the index drops to `c'` and the coordinate doubles
      have hc' : c' < l.length := by omega
      have hkey : (2 : ℝ) ^ c' * (2 * (t i : ℝ)) = 1 := by
        have hstep : (2 : ℝ) ^ (c' + 1) * (t i : ℝ) = (2 : ℝ) ^ c' * (2 * (t i : ℝ)) := by
          rw [pow_succ]; ring
        rw [← hstep]; exact heq
      have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ c' := one_le_pow₀ (by norm_num)
      have hti0 : (0 : ℝ) ≤ (t i : ℝ) := (t i).2.1
      have hCt : (t i : ℝ) ≤ (2 : ℝ) ^ c' * (t i : ℝ) := by
        simpa using mul_le_mul_of_nonneg_right h1 hti0
      have h2 : 2 * (t i : ℝ) ≤ 1 := by nlinarith [hCt, hti0, hkey]
      have hmem : 2 * (t i : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, h2⟩
      have hle : ((t i : Set.Icc (0 : ℝ) 1) : ℝ) ≤ 1 / 2 := by linarith
      rw [genLoop_transAt_apply_of_le i (genLoopListConcat i l) g hle]
      refine ih _ ⟨c', hc', ?_⟩
      rw [Function.update_self, Set.projIcc_of_mem (by norm_num) hmem]
      exact hkey

/-- **The iterated concatenation is the basepoint on the "wall" of the cube.**  If either the
`i`-th coordinate of the cube point lies in the leading dyadic block of length
`2 ^ l.length` (`2 ^ l.length * t i ≤ 1`), so that the recursion runs off the end of the list, or it
lies exactly at the right end of one of the blocks (`2 ^ c * t i = 1` for some `c < l.length`), so
that the block is read at the boundary of the cube, then `genLoopListConcat i l t = x`. -/
theorem genLoopListConcat_eq_basepoint_of_wall {N : Type*} [DecidableEq N] {X : Type} [TopologicalSpace X]
    {x : X} (i : N) (l : List (GenLoop N X x)) (t : N → Set.Icc (0 : ℝ) 1)
    (h : (2 : ℝ) ^ l.length * (t i : ℝ) ≤ 1 ∨ ∃ c < l.length, (2 : ℝ) ^ c * (t i : ℝ) = 1) :
    Work.PTGeometric.genLoopListConcat i l t = x := by
  rcases h with h | h
  · exact pow_le_genLoopListConcat_eq_basepoint i l t h
  · exact pow_eq_one_genLoopListConcat_eq_basepoint i l t h

end

end Work.PTGeometric
