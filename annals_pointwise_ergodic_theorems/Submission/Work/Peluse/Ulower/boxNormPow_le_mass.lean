/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Mathlib
import Submission.Work.Peluse.Ulower.boxNormPow_le_L1

/-!
# `‖F‖_{□^t_Q(S)}^{2^t} ≤ ‖F‖_{ℓ¹} / |S|` for a `1`-bounded finitely supported `F`

The crude half of the "box norm `≤` `L¹`" inequality (Gowers–Cauchy–Schwarz in its crudest form:
in the cube average for fixed shifts `h, h'` the corner `ω = 0` carries the whole modulus, while the
remaining `2^t - 1` corners contribute at most `1` each because `‖F‖_∞ ≤ 1`):

`Work.Peluse.boxNormPow t Q S F ≤ (∑'_x ‖F x‖) · |S|⁻¹`

for `1 ≤ t`, `F` finitely supported with `‖F‖_∞ ≤ 1`, and *no* hypothesis on the shift sets `Q` or
the support box `S` -- in particular `S` may be empty, in which case both sides vanish.

This is the statement requested by `Work.Peluse.Ulower.mass_bound`, where it is applied to the dual
function `F₂ = dualFn N P f₀ f₁` (which is `1`-bounded when `f₀, f₁` are, see
`mass_bound.dualFn_norm_le_one`) to turn a lower bound `δ^K ≤ ‖F₂‖_{U²}` for the Gowers norm into a
lower bound `δ^K · |S| ≤ ∑'_x ‖f₁ x‖` for the `ℓ¹`-mass of `f₁`; the `ℓ¹`-mass of `F₂` is in turn
bounded by that of `f₁` (`Work.Peluse.Ulower.dualFn_tsum_le`).

## Proof

With `M = 1`, the general interpolation bound
`Work.Peluse.Ulower.boxNormPow_le_L1` (`≤ M ^ (2 ^ t - 1) · ‖F‖_{ℓ¹} / |S|`) immediately gives the
claim when `S` is nonempty, because `1 ^ (2 ^ t - 1) = 1`.  If `S = ∅` then `boxSumPow t Q S F`
carries the factor `((S.card : ℂ))⁻¹ = 0`, hence the box norm vanishes and so does the right-hand
side.

The hypothesis `1 ≤ t` is inherited from `boxNormPow_le_L1`; as noted there, it is not needed.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.Ulower

noncomputable section

open Work.Peluse

/-- The box norm's `tsum`-free input: `FinSuppZ` gives a finite set off which `F` vanishes. -/
private lemma exists_finset_supportIn {F : ℤ → ℂ} (h : Work.Peluse.FinSuppZ F) :
    ∃ s : Finset ℤ, ∀ x : ℤ, x ∉ s → F x = 0 := by
  obtain ⟨N, hN⟩ := h
  refine ⟨Finset.Icc (-(N : ℤ)) (N : ℤ), fun x hx => hN x ?_⟩
  have key : ∀ y : ℤ, y.natAbs ≤ N → y ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    intro y hy
    rw [Finset.mem_Icc]
    have h1 : (y.natAbs : ℤ) ≤ (N : ℤ) := by exact_mod_cast hy
    rw [Int.natCast_natAbs] at h1
    exact abs_le.mp h1
  exact Nat.lt_of_not_le (fun hc => hx (key x hc))

theorem boxNormPow_le_mass {t : ℕ} (ht : 1 ≤ t) (Q : Fin t → Finset ℤ) (S : Finset ℤ)
    (F : ℤ → ℂ) (hF : ∀ x : ℤ, ‖F x‖ ≤ 1) (hfin : Work.Peluse.FinSuppZ F) :
    Work.Peluse.boxNormPow t Q S F ≤ (∑' x : ℤ, ‖F x‖) * ((S.card : ℝ))⁻¹ := by
  rcases eq_or_lt_of_le (Nat.cast_nonneg S.card : (0 : ℝ) ≤ (S.card : ℝ)) with h0 | hpos
  · -- `S = ∅`: the box sum carries the factor `((S.card : ℂ))⁻¹ = 0`
    have hS0 : S.card = 0 := Nat.cast_eq_zero.mp h0.symm
    have hbox : boxNormPow t Q S F = 0 := by
      rw [boxNormPow, boxSumPow, prodCubeSum_eq]
      simp [hS0]
    rw [hbox, h0.symm, inv_zero, mul_zero]
  · -- `S ≠ ∅`: apply the general interpolation bound with `M = 1`
    have hS : 0 < S.card := by exact_mod_cast hpos
    have hsupp : ∃ s : Finset ℤ, ∀ x : ℤ, x ∉ s → F x = 0 := exists_finset_supportIn hfin
    have h := boxNormPow_le_L1 (t := t) ht Q S F (M := 1) zero_le_one hF hsupp hS
    simpa [div_eq_mul_inv] using h

end

end Work.Peluse.Ulower
