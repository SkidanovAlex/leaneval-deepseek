import Mathlib
import Submission.Work.Layout.SortDefs
import Submission.Work.Layout.SortSpecs
import Submission.Work.Layout.Pass2Aux.Pass

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.Layout

open HvdH
open scoped List

/-- permutation invariance of `List.sum` on `ℕ` (used for the `totL` bookkeeping) -/
theorem perm_sum_eq_nat {l₁ l₂ : List ℕ} (h : l₁.Perm l₂) : l₁.sum = l₂.sum := by
  induction h with
  | nil => rfl
  | cons a _ ih => simp only [List.sum_cons, ih]
  | swap a b l => simp only [List.sum_cons]; ac_rfl
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- **The two-pass lemma.** `pass2 pLt pSz X Y C D T1 T2 SA SB F1 F2 t d` = two bottom-up merge
passes (`pass X Y C D …` then `pass C D X Y …`, see `Submission/Work/Layout/SortDefs.lean`).  Given the
runs `ps` on `X` and `qs` on `Y` (`S X = runEncB ps ++ JX`, `S Y = runEncB qs ++ JY`) with
`ps.length = qs.length ∨ ps.length = qs.length + 1`, every run nonempty, every element a record
`Val.cons (Val.int (k:ℤ)) v'` with `k : ℕ`, every run strictly increasing in `pairKey` and all keys of
`ps ++ qs` distinct, and `C`,`D` empty (`S C = runEncB [] ++ JC`, `S D = runEncB [] ++ JD`), the word
ends with `X`,`Y` holding the runs `(pass2R ps qs).1`, `(pass2R ps qs).2` (where `pass2R` is the
abstract two-pass function of `SortDefs.lean`), `C`,`D` again empty, every other stack unchanged, every
run of the result nonempty, the result's elements a permutation of the input's, the length invariant
`(pass2R ps qs).1.length = (pass2R ps qs).2.length ∨ …+1` preserved, and every result run strictly
increasing.  Cost `≤ P2c KLt KSz * (Σ vsz + Σ|r| + 2*(ps.length+qs.length) + 4)` with
`P2c KLt KSz = 20000*(KLt+KSz)+400000`.

The theorem's conclusion is exactly `Work.Layout.Sk.Pass2Spec` (see `SortSpecs.lean`), whose first
hypothesis is `MergePairAll main pLt pSz KLt KSz`, i.e. "`mergePair` is correct at **every** admissible
tuple of distinct stacks" (that is what `mergePair_ev` provides, uniformly in the stacks).  This
genericity is needed: the first pass merges sources `X,Y` into `C`/`D`, the second pass merges sources
`C,D` back into `X`/`Y`, so the two `MergePairSpec` instances required are at *different* stack tuples.

ROUTE.  `pass` = `peek Y rF; loop rF cons (passBody …); peek X rH; ite rH cons (moveRun X C T1 t d) skip`
and `passBody` = `mergePair … T1 C …; peek Y; ite (cons) (mergePair … T2 D …; peek Y rF)
(peek X; ite (cons) (moveRun X D T2 t d) skip; rF := gMark)`.  So the merged runs go alternately to
`C` and `D` (first merge to `C`, second to `D`, …) and the leftover run of a pass goes to `D` when the
in-body branch fires (odd run count) and to `C` after the loop (even count) — this routing is exactly
`passGo`/`passR` (see the `passGo` doc comment and the `ListsSpec` conjuncts about `passR`/`pass2R`,
proved by `sortListFacts`).  Prove the pass by induction on the run list of `Y` in chunks of two, then
apply it twice.  Each `mergePair` call is discharged by `hMPall` applied to the (distinct) stack tuple;
the `i`-th merge's cost is `MPc KLt KSz * (Σ vsz + |r|+|s| + 2)`, and summing over the
`(ps.length+qs.length+1)/2` merges of a pass gives `P2c KLt KSz * (…)` since
`P2c ≥ 2*MPc` and the two passes together halve the run count. -/
theorem pass2_ev2 {main pLt pSz : HvdH.Cmd} {KLt KSz : ℕ} :
    Work.Layout.Sk.Pass2Spec main pLt pSz KLt KSz := by
  intro hMP X Y C D T1 T2 SA SB F1 F2 t d hdis g S ps qs JX JY JC JD
    hX hY hC hD hlen hne hrec hsort hkeys
  -- ============ first pass (sources X,Y into C,D) ============
  have hRec1 : RunsRec (ps ++ qs) := RunsRec.of_flat hrec
  have hKeys1 : PairKeys ps qs := PairKeys.of_flat_nodup hkeys
  obtain ⟨s₁, n₁, hev₁, hn₁, hX₁, hY₁, hC₁, hD₁, hfr₁⟩ :=
    pass_ev hMP hdis ps qs ([] : List (List Val)) ([] : List (List Val)) JX JY JC JD g S
      hlen hX hY hC hD hne hRec1 hsort hKeys1
  -- ============ second pass (sources C,D back into X,Y) ============
  have hperm : ((Sk.passR ps qs).1 ++ (Sk.passR ps qs).2).flatten.Perm ((ps ++ qs).flatten) :=
    passR_perm ps qs hlen
  have hlen₂ : (Sk.passR ps qs).1.length = (Sk.passR ps qs).2.length ∨
      (Sk.passR ps qs).1.length = (Sk.passR ps qs).2.length + 1 := passR_len_inv ps qs hlen
  have hne₂ : RunsNe ((Sk.passR ps qs).1 ++ (Sk.passR ps qs).2) := passR_ne_nil ps qs hne
  have hsort₂ : RunsSort ((Sk.passR ps qs).1 ++ (Sk.passR ps qs).2) :=
    passR_sorted ps qs hsort hKeys1
  have hkeys₂nd : ((((Sk.passR ps qs).1 ++ (Sk.passR ps qs).2).flatten).map pairKey).Nodup :=
    (hperm.map pairKey).nodup_iff.mpr hkeys
  have hkeys₂ : PairKeys (Sk.passR ps qs).1 (Sk.passR ps qs).2 :=
    PairKeys.of_flat_nodup hkeys₂nd
  have hrec₂ : RunsRec ((Sk.passR ps qs).1 ++ (Sk.passR ps qs).2) :=
    RunsRec.of_flat (fun v hv => hrec v (hperm.mem_iff.mp hv))
  -- the stack tuple of the second pass (sources `C,D`, destinations `X,Y`) is a reordering
  have hdis₂ : ([C, D, X, Y, T1, T2, SA, SB, F1, F2, t, d, 0] : List Stk).Nodup := by
    have h := hdis
    simp only [List.nodup_cons, List.nodup_nil, and_true] at h ⊢
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nodis_mem
  obtain ⟨s₂, n₂, hev₂, hn₂, hC₂, hD₂, hX₂, hY₂, hfr₂⟩ :=
    pass_ev (X := C) (Y := D) (C := X) (D := Y) hMP hdis₂
      (Sk.passR ps qs).1 (Sk.passR ps qs).2 ([] : List (List Val)) ([] : List (List Val))
      JC JD JX JY s₁.reg s₁.stk hlen₂ hC₁ hD₁ hX₁ hY₁ hne₂ hrec₂ hsort₂ hkeys₂
  -- ============ the cost bound ============
  have hM : 4000 ≤ Sk.MPc KLt KSz := by simp only [Sk.MPc]; omega
  have htot : totL ((Sk.passR ps qs).1 ++ (Sk.passR ps qs).2) = totL (ps ++ qs) := by
    simp only [totL]
    rw [hperm.length_eq, perm_sum_eq_nat (hperm.map vsz)]
  have hlen_le : (Sk.passR ps qs).1.length + (Sk.passR ps qs).2.length ≤ ps.length + qs.length :=
    passR_len_le ps qs hlen
  have hb1 : n₁ ≤ 50 * Sk.MPc KLt KSz * (totL (ps ++ qs) + 2 * (ps.length + qs.length) + 4) :=
    le_trans hn₁ (passWBound hM ps qs)
  have hb2 : n₂ ≤ 50 * Sk.MPc KLt KSz *
      (totL ((Sk.passR ps qs).1 ++ (Sk.passR ps qs).2)
        + 2 * ((Sk.passR ps qs).1.length + (Sk.passR ps qs).2.length) + 4) :=
    le_trans hn₂ (passWBound hM _ _)
  have hYX : totL ((Sk.passR ps qs).1 ++ (Sk.passR ps qs).2)
      + 2 * ((Sk.passR ps qs).1.length + (Sk.passR ps qs).2.length) + 4
      ≤ totL (ps ++ qs) + 2 * (ps.length + qs.length) + 4 := by
    rw [htot]; omega
  have hb2' : n₂ ≤ 50 * Sk.MPc KLt KSz * (totL (ps ++ qs) + 2 * (ps.length + qs.length) + 4) :=
    le_trans hb2 (Nat.mul_le_mul_left _ hYX)
  have hP2c : Sk.P2c KLt KSz = 100 * Sk.MPc KLt KSz := by simp only [Sk.P2c, Sk.MPc]; ring
  have hfin : n₁ + n₂ ≤ Sk.P2c KLt KSz *
      (totL (ps ++ qs) + 2 * (ps.length + qs.length) + 4) := by
    rw [hP2c]
    calc n₁ + n₂
        ≤ 50 * Sk.MPc KLt KSz * (totL (ps ++ qs) + 2 * (ps.length + qs.length) + 4)
          + 50 * Sk.MPc KLt KSz * (totL (ps ++ qs) + 2 * (ps.length + qs.length) + 4) :=
          add_le_add hb1 hb2'
      _ = 100 * Sk.MPc KLt KSz * (totL (ps ++ qs) + 2 * (ps.length + qs.length) + 4) := by
          ring
  have hP2R : Sk.pass2R ps qs = Sk.passR (Sk.passR ps qs).1 (Sk.passR ps qs).2 := rfl
  -- ============ conclusion ============
  refine ⟨s₂, n₁ + n₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Sk.pass2
    exact Ev.seq hev₁ hev₂
  · exact hfin
  · rw [hP2R]; exact hX₂
  · rw [hP2R]; exact hY₂
  · exact hC₂
  · exact hD₂
  · intro k hkX hkY hkC hkD
    exact (hfr₂ k hkC hkD hkX hkY).trans (hfr₁ k hkX hkY hkC hkD)
  · rw [hP2R]
    exact passR_ne_nil (Sk.passR ps qs).1 (Sk.passR ps qs).2 hne₂
  · rw [hP2R]
    exact (passR_perm (Sk.passR ps qs).1 (Sk.passR ps qs).2 hlen₂).trans hperm
  · rw [hP2R]
    exact passR_len_inv (Sk.passR ps qs).1 (Sk.passR ps qs).2 hlen₂
  · rw [hP2R]
    exact passR_sorted (Sk.passR ps qs).1 (Sk.passR ps qs).2 hsort₂ hkeys₂

end Work.Layout
