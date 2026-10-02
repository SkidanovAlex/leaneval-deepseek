import Mathlib
import Submission.Work.PTGeometric.genLoopListConcat_eq_get

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The block coordinate of the block recursion

`Work.PTGeometric.genLoopListConcatStep i l t` computes the *block* of a cube point `t` in the
iterated concatenation of the list of cube loops `l` along the coordinate `i`: the index `k` of the
element of the list that is consulted, together with the reparametrised cube point `u` at which it
is read (`k = l.length` meaning that the recursion has run off the end of the list).

This file computes the *coordinate* `u i` explicitly.  If the returned index is `k` and
`k < l.length` (so the recursion stopped inside the list, in the `k`-th dyadic block), then

* `u i = 2 ^ (k+1) * t i - 1`,
* `t i` lies in the half-open dyadic block `(2 ^ (-(k+1)), 2 ^ (-k)]`,
* and all the other coordinates of `u` are those of `t`.

The block `k` is *closed on the right* (`t i = 2 ^ (-k)` gives the block `k`, not `k + 1`), which is
why the statement carries `≤ 1 / 2 ^ k` and not the strict inequality of
`Work.PTGeometric.genLoopListConcatStep_eq_block`: at the dyadic boundary `t i = 2 ^ (-k)` (with
`k ≥ 1`) the recursion still descends and the reparametrised coordinate is `1`.
-/

namespace Work.ThomBordism

open Function

theorem genLoopListConcatStep_snd_eq_of_index {N : Type*} [DecidableEq N] {X : Type}
    [TopologicalSpace X] {x : X} (i : N) (l : List (GenLoop N X x))
    (t : N → Set.Icc (0 : ℝ) 1) (k : ℕ)
    (hk : (Work.PTGeometric.genLoopListConcatStep i l t).1 = k) (hk' : k < l.length) :
    (((Work.PTGeometric.genLoopListConcatStep i l t).2 i : ℝ) = (2 : ℝ) ^ (k + 1) * (t i : ℝ) - 1)
      ∧ (1 / (2 : ℝ) ^ (k + 1) < (t i : ℝ) ∧ (t i : ℝ) ≤ 1 / (2 : ℝ) ^ k)
      ∧ (∀ j : N, j ≠ i →
          ((Work.PTGeometric.genLoopListConcatStep i l t).2 j : ℝ) = (t j : ℝ)) := by
  induction l generalizing t k with
  | nil =>
      simp only [List.length_nil] at hk'
      omega
  | cons g l' ih =>
      by_cases hc : ((t i : Set.Icc (0 : ℝ) 1) : ℝ) ≤ 1/2
      · -- the point lies in the first half: descend into the tail and increment the index
        have hstep := Work.PTGeometric.genLoopListConcatStep_cons_le i g l' t hc
        simp only [hstep] at hk ⊢
        set t' : N → Set.Icc (0 : ℝ) 1 :=
          Function.update t i (Set.projIcc 0 1 (by norm_num) (2 * (t i : ℝ))) with ht'def
        have hk1 : (Work.PTGeometric.genLoopListConcatStep i l' t').1 + 1 = k := hk
        have hklt : (Work.PTGeometric.genLoopListConcatStep i l' t').1 < l'.length := by
          simp only [List.length_cons] at hk'
          omega
        obtain ⟨IH1, IH2, IH3⟩ :=
          ih t' ((Work.PTGeometric.genLoopListConcatStep i l' t').1) rfl hklt
        obtain ⟨IH2a, IH2b⟩ := IH2
        have hmem2 : 2 * (t i : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
          ⟨by linarith [(t i).2.1], by linarith⟩
        have ht'i : (t' i : ℝ) = 2 * (t i : ℝ) := by
          rw [ht'def, Function.update_self,
            Set.projIcc_of_mem (show (0 : ℝ) ≤ 1 by norm_num) hmem2]
        refine ⟨?_, ?_, ?_⟩
        · rw [IH1, ht'i, hk1, pow_succ]
          ring
        · constructor
          · rw [div_lt_iff₀ (show (0 : ℝ) < (2 : ℝ) ^ (k+1) by positivity)]
            have h := (div_lt_iff₀ (show (0 : ℝ) < (2 : ℝ) ^
              ((Work.PTGeometric.genLoopListConcatStep i l' t').1 + 1) by positivity)).mp IH2a
            rw [ht'i] at h
            have heq : (t i : ℝ) * (2 : ℝ)^(k+1) =
                (2 * (t i : ℝ)) * (2 : ℝ)^((Work.PTGeometric.genLoopListConcatStep i l' t').1 + 1) := by
              rw [hk1, pow_succ]; ring
            rw [heq]; exact h
          · rw [le_div_iff₀ (show (0 : ℝ) < (2 : ℝ) ^ k by positivity)]
            have h := (le_div_iff₀ (show (0 : ℝ) < (2 : ℝ) ^
              ((Work.PTGeometric.genLoopListConcatStep i l' t').1) by positivity)).mp IH2b
            rw [ht'i] at h
            have heq : (t i : ℝ) * (2 : ℝ)^k =
                (2 * (t i : ℝ)) * (2 : ℝ)^((Work.PTGeometric.genLoopListConcatStep i l' t').1) := by
              rw [← hk1, pow_succ]; ring
            rw [heq]; exact h
        · intro j hj
          rw [IH3 j hj, ht'def, Function.update_of_ne hj]
      · -- the point lies in the second half: stop with index `0`
        have hstep := Work.PTGeometric.genLoopListConcatStep_cons_gt i g l' t hc
        simp only [hstep] at hk ⊢
        have hk0 : k = 0 := hk.symm
        subst hk0
        have hmem : 2 * (t i : ℝ) - 1 ∈ Set.Icc (0 : ℝ) 1 :=
          ⟨by linarith, by linarith [(t i).2.2]⟩
        refine ⟨?_, ?_, ?_⟩
        · rw [Function.update_self, Set.projIcc_of_mem (show (0 : ℝ) ≤ 1 by norm_num) hmem]
          norm_num
        · constructor
          · rw [show (1 : ℝ)/2^(0+1) = 1/2 by norm_num]
            linarith
          · rw [show (1 : ℝ)/2^0 = 1 by norm_num]
            exact (t i).2.2
        · intro j hj
          rw [Function.update_of_ne hj]

end Work.ThomBordism
