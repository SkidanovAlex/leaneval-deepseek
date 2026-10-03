-- **Namespaced copy** (`Work.OROneRel.NC`) of a colleague's module, made so that the
-- window-data pipeline can be imported *together with* the Freiheitssatz pipeline:
-- `Work.OROneRel.decor_replicate_true` (declared in `Submission.Work.OROneRel.decor_wordOf_zpow_of`)
-- clashes with the declaration of the same name in
-- `Submission.Work.OROneRel.twoLetter_cycle_decor`, so no module can import both
-- `exists_window_support_data_cycred` and `bandFreiheitssatz_of_windowData`.  The copy lives in
-- the namespace `Work.OROneRel.NC`, where `decor_replicate_true` is `Work.OROneRel.NC.decor_replicate_true`
-- and no longer clashes.  Nothing here is new mathematics.
/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# The decoration of a power of a generator

`decor c i L` is the running-weight decoration of a word `L` (see `MagnusGenDefs`), and
`wordOf (FreeGroup.of z ^ n)` for `n : ℤ` is the word `z z ... z` (`n ≥ 0`) or the reduced word
`z⁻¹ z⁻¹ ... z⁻¹` (`n < 0`).  This file computes the decoration of that power at level `0`, in the
two forms that the `τ`-frame bookkeeping needs:

* `n ≥ 0`: the symbols `((z, j * c z), true)` for `0 ≤ j < n`;
* `n < 0`: the symbols `((z, -((j + 1) * c z)), false)` for `0 ≤ j < -n`.

The two computational cores are the running-level formulas `decor_replicate_true` and
`decor_replicate_false` for a constant letter repeated `k` times, which are pure inductions on `k`
(the running level advances by `c z` at each `(z, true)` and drops by `c z` at each `(z, false)`).
-/
import Mathlib
import Submission.Work.OROneRel.wordOfDefs
import Submission.Work.OROneRel.MagnusGenDefs

namespace Work.OROneRel.NC

universe u

/-- **The decoration of `k` copies of the positive letter `(z, true)`.**  Reading `(z, true)` at
running level `i` produces the symbol `((z, i), true)` and moves the level to `i + c z`; hence the
`j`-th copy is decorated at level `i + j * c z`. -/
lemma decor_replicate_true {α : Type u} (c : α → ℤ) (z : α) :
    ∀ (i : ℤ) (k : ℕ),
      Work.OROneRel.decor c i (List.replicate k (z, true)) =
        (List.range k).map (fun j : ℕ => ((z, i + (j : ℤ) * c z), true)) := by
  intro i k
  induction k generalizing i with
  | zero => simp [Work.OROneRel.decor]
  | succ k ih =>
    rw [List.replicate_succ, Work.OROneRel.decor, ih, List.range_succ_eq_map,
      List.map_cons, List.map_map]
    congr 1
    · simp
    · apply List.map_congr_left
      intro j _
      simp only [Function.comp_apply]
      congr 1
      push_cast
      ring_nf

/-- **The decoration of `k` copies of the negative letter `(z, false)`.**  Reading `(z, false)` at
running level `i` produces the symbol `((z, i - c z), false)` and moves the level to `i - c z`;
hence the `j`-th copy is decorated at level `i - (j + 1) * c z`. -/
lemma decor_replicate_false {α : Type u} (c : α → ℤ) (z : α) :
    ∀ (i : ℤ) (k : ℕ),
      Work.OROneRel.decor c i (List.replicate k (z, false)) =
        (List.range k).map (fun j : ℕ => ((z, i - ((j : ℤ) + 1) * c z), false)) := by
  intro i k
  induction k generalizing i with
  | zero => simp [Work.OROneRel.decor]
  | succ k ih =>
    rw [List.replicate_succ, Work.OROneRel.decor, ih, List.range_succ_eq_map,
      List.map_cons, List.map_map]
    congr 1
    · simp
    · apply List.map_congr_left
      intro j _
      simp only [Function.comp_apply]
      congr 1
      push_cast
      ring_nf

/-- `invRev` of a repeated letter: reversal is invisible on a constant list, so only the boolean is
flipped. -/
lemma invRev_replicate {α : Type u} (k : ℕ) (x : α × Bool) :
    FreeGroup.invRev (List.replicate k x) = List.replicate k (x.1, !x.2) := by
  simp [FreeGroup.invRev, List.map_replicate, List.reverse_replicate]

theorem decor_wordOf_zpow_of {α : Type u} (c : α → ℤ) (z : α) (n : ℤ) :
    Work.OROneRel.decor c 0 (Work.OROneRel.wordOf (FreeGroup.of z ^ n)) =
      (if 0 ≤ n then (List.range n.toNat).map (fun j : ℕ => ((z, (j : ℤ) * c z), true))
        else (List.range (-n).toNat).map (fun j : ℕ => ((z, -(((j : ℤ) + 1) * c z)), false))) := by
  classical
  by_cases hn : 0 ≤ n
  · -- `n ≥ 0`: the word of `z ^ n` is `(z, true)` repeated `n.toNat` times.
    rw [if_pos hn]
    have h1 : ((n.toNat : ℤ)) = n := Int.toNat_of_nonneg hn
    have hz : FreeGroup.of z ^ n = FreeGroup.of z ^ n.toNat := by
      rw [← zpow_natCast (FreeGroup.of z) n.toNat, h1]
    rw [hz, Work.OROneRel.wordOf, FreeGroup.toWord_of_pow, decor_replicate_true c z 0 n.toNat]
    apply List.map_congr_left
    intro j _
    simp
  · -- `n < 0`: the word of `z ^ n` is the inverse of `z ^ (-n).toNat`, i.e. `(z, false)` repeated.
    rw [if_neg hn]
    have hm : n = -(((-n).toNat : ℤ)) := by
      have h : (((-n).toNat : ℤ)) = -n := Int.toNat_of_nonneg (by omega)
      omega
    have hz : FreeGroup.of z ^ n = (FreeGroup.of z ^ (-n).toNat)⁻¹ := by
      conv_lhs => rw [hm]
      rw [zpow_neg, zpow_natCast]
    rw [hz, Work.OROneRel.wordOf, FreeGroup.toWord_inv, FreeGroup.toWord_of_pow,
      invRev_replicate]
    simp only [Bool.not_true]
    rw [decor_replicate_false c z 0 (-n).toNat]
    apply List.map_congr_left
    intro j _
    simp

end Work.OROneRel.NC
