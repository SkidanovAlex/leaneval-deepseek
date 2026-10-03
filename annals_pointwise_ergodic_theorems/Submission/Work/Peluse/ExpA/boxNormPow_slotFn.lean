/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.Work.Peluse.ExpA.Defs
import Submission.Work.Peluse.BoxNorm.boxNormPow_shift
import Submission.Work.Peluse.Pairing.boxSumPow_star

/-!
# The box norm power is unchanged by the slot functions

The slot functions of Lemma 4.10 (`Work.Peluse.ExpA.slotFn`) are the translated, conjugated copies
`slotFn b u f j = (star^[|slotIdx j|]) ∘ T_{dotB (slotIdx j) b u} f` of `f`.  Both operations leave
the `2^t`-th power of the Gowers box norm `Work.Peluse.boxNormPow` unchanged:

* translation, `Work.Peluse.BoxNorm.boxNormPow_shift` (proved by reindexing the unconditional
  `tsum` over `ℤ`);
* complex conjugation, `Work.Peluse.Pairing.boxSumPow_star` (conjugating `f` conjugates the whole
  cube average, and `‖star z‖ = ‖z‖`).

Hence

`Work.Peluse.ExpA.boxNormPow_slotFn : ‖slotFn s b u f j‖_{□^t_Q(S)}^{2^t} = ‖f‖_{□^t_Q(S)}^{2^t}`.

The elementary consequences of `boxSumPow_star` used here are isolated as
`boxNormPow_star_apply` (one conjugation) and `boxNormPow_star_iterate` (any fixed number of
conjugations), so that the final statement is a two-line composition of the two invariances.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.ExpA

open Work.Peluse

/-- Conjugating the values of `g` does not change the `2^t`-th power of its box norm.  This is
`Work.Peluse.Pairing.boxSumPow_star` together with `‖star z‖ = ‖z‖`. -/
lemma boxNormPow_star_apply {t : ℕ} (Q : Fin t → Finset ℤ) (S : Finset ℤ) (g : ℤ → ℂ) :
    boxNormPow t Q S (fun x => star (g x)) = boxNormPow t Q S g := by
  simp only [boxNormPow, Pairing.boxSumPow_star, norm_star]

/-- Iterating the conjugation any fixed number of times does not change the `2^t`-th power of the
box norm. -/
lemma boxNormPow_star_iterate {t : ℕ} (Q : Fin t → Finset ℤ) (S : Finset ℤ) (k : ℕ)
    (g : ℤ → ℂ) :
    boxNormPow t Q S ((star^[k]) ∘ g) = boxNormPow t Q S g := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h : (star^[k + 1]) ∘ g = fun x => star (((star^[k]) ∘ g) x) := by
      funext x
      simp only [Function.comp_apply, Function.iterate_succ_apply']
    rw [h, boxNormPow_star_apply, ih]

/-- The slot functions of Lemma 4.10 are isometries of the box-norm power: translating `f` and
conjugating it any number of times does not change `‖f‖_{□^t_Q(S)}^{2^t}`. -/
theorem boxNormPow_slotFn {t : ℕ} (Q : Fin t → Finset ℤ) (S : Finset ℤ) {s : ℕ} (b u : Fin s → ℤ)
    {f : ℤ → ℂ} (hfin : Work.Peluse.FinSuppZ f) (j : Fin (2 ^ s - 1 + 1)) :
    Work.Peluse.boxNormPow t Q S (Work.Peluse.ExpA.slotFn s b u f j)
      = Work.Peluse.boxNormPow t Q S f := by
  rw [slotFn, boxNormPow_star_iterate]
  exact BoxNorm.boxNormPow_shift t Q S f (dotB (slotIdx s j) b u) hfin

end Work.Peluse.ExpA
