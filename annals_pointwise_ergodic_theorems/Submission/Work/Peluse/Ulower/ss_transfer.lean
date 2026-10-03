/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team.
-/
import Mathlib
import Submission.Work.Peluse.Ulower.ss_defs
import Submission.Work.Peluse.Ulower.Defs

/-!
# Changing the support box in the `U^s`-norm: the transfer `ss_transfer`

The Gowers box norm `‖f‖_{□^t_Q(S)}` of `Work.Peluse.boxNormPow` depends on the ambient box `S`
only through the normalising factor `|S|⁻¹` (the inner sum over `x` never mentions `S`); this is
`Work.Peluse.Ulower.boxNormPow_eq_mul_card`.  Consequently the `U^s`-norm at two different boxes
is proportional:

`uNormPow s Q S₁ F = (|S₀| / |S₁|) · uNormPow s Q S₀ F`.

`ss_transfer` is the only consequence of this fact that the `U`-lowering assembly needs: a lower
bound `δ` for the norm at the box `S₀` transfers to the box `S₁` with the loss `|S₀|/|S₁|`.  This
is the mechanism by which the declared support range can be changed in the assembly of
`PeluseULowering` (see `Ulower/NOTES.md`).
-/

set_option autoImplicit false

open scoped BigOperators
open Polynomial

namespace Work.Peluse.Ulower

noncomputable section

open Work.Peluse

/-- **Transfer of a lower bound for the `U^s`-norm between two support boxes.**  If `δ` is a
lower bound for `‖F‖_{U^s_Q(S₀)}` and both boxes are nonempty, then `δ·|S₀|/|S₁|` is a lower bound
for `‖F‖_{U^s_Q(S₁)}`. -/
theorem ss_transfer {P : Polynomial ℤ} {s : ℕ} {N N₀ Ns : ℕ} {Q : Finset ℤ} {F : ℤ → ℂ} {δ : ℝ}
    (hS₀ : 0 < (Work.Peluse.symIcc (Work.Peluse.dSup P N₀ N)).card)
    (hS₁ : 0 < (Work.Peluse.symIcc (Work.Peluse.dSup P Ns N)).card)
    (hδ : δ ≤ Work.Peluse.uNormPow s Q (Work.Peluse.symIcc (Work.Peluse.dSup P N₀ N)) F) :
    δ * (((Work.Peluse.symIcc (Work.Peluse.dSup P N₀ N)).card : ℝ) /
        ((Work.Peluse.symIcc (Work.Peluse.dSup P Ns N)).card : ℝ)) ≤
      Work.Peluse.uNormPow s Q (Work.Peluse.symIcc (Work.Peluse.dSup P Ns N)) F := by
  set S₀ : Finset ℤ := Work.Peluse.symIcc (Work.Peluse.dSup P N₀ N) with hS₀def
  set S₁ : Finset ℤ := Work.Peluse.symIcc (Work.Peluse.dSup P Ns N) with hS₁def
  have hne₁ : S₁.Nonempty := Finset.card_pos.mp hS₁
  have hne₀ : S₀.Nonempty := Finset.card_pos.mp hS₀
  have hc₁ : (S₁.card : ℝ) ≠ 0 := by
    have : S₁.card ≠ 0 := Finset.card_ne_zero.mpr hne₁
    exact_mod_cast this
  have hc₀ : (S₀.card : ℝ) ≠ 0 := by
    have : S₀.card ≠ 0 := Finset.card_ne_zero.mpr hne₀
    exact_mod_cast this
  -- the two box norms differ exactly by the ratio of the cardinalities
  have hkey := boxNormPow_eq_mul_card s (fun _ : Fin s => Q) S₀ S₁ F hne₁
  have h₁ : Work.Peluse.uNormPow s Q S₁ F =
      ((S₀.card : ℝ) / (S₁.card : ℝ)) * Work.Peluse.uNormPow s Q S₀ F := by
    rw [Work.Peluse.uNormPow, Work.Peluse.uNormPow, hkey]
    field_simp
  rw [h₁]
  have hnn : 0 ≤ (S₀.card : ℝ) / (S₁.card : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  calc δ * ((S₀.card : ℝ) / (S₁.card : ℝ))
      ≤ Work.Peluse.uNormPow s Q S₀ F * ((S₀.card : ℝ) / (S₁.card : ℝ)) :=
        mul_le_mul_of_nonneg_right hδ hnn
    _ = ((S₀.card : ℝ) / (S₁.card : ℝ)) * Work.Peluse.uNormPow s Q S₀ F := by ring

end

end Work.Peluse.Ulower
