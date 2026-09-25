import Mathlib
import Submission.Work.BourgainPlan.Maximal.mstG_gauss

namespace Work.BourgainPlan.Maximal

open Work.BourgainPlan.IonescuWainger

set_option autoImplicit false

/-!
# The uniform Gauss decay of `mstG` (no side condition on `s`)

`mstG_gauss` proves the Gauss/Weyl decay `‖mstG P β‖ ≤ C (s^l)^{-δ}` on the annulus
`mstU l (s+1) ∖ mstU l s`, but only under the side condition `2^{iwK (mstRho l)} ≤ s^l`, which makes
the Farey fractions of denominator `≤ s^l` sit inside `mstU l s`.  Downstream arguments (MST §5,
`probe_mstG_gauss_uniform`) want the *unconditional* statement, with the decay measured against
`(s+1)^{-δ l}` instead of `(s^l)^{-δ}`.

That is what this file supplies, from `mstG_gauss` plus nothing but the trivial bound
`‖mstG P β‖ ≤ 1` (`mstG_norm_le_one`):

* for `s^l ≥ 2^{iwK (mstRho l)}` the decay `mstG_gauss` applies, and
  `(s^l)^{-δ} = s^{-δ l} ≤ 2^{δ l} (s+1)^{-δ l}` for `s ≥ 1`
  (`rpow_neg_le_two_mul_rpow_neg`, which is `1/s ≤ 2/(s+1) ⟺ s+1 ≤ 2s`);
* for `s^l < 2^{iwK (mstRho l)}` the trivial bound `1` applies, and
  `(s+1)^{δ l} ≤ (2^{iwK (mstRho l)}+1)^{δ l}` because `s < 2^{iwK (mstRho l)}`.

Both constants are absorbed into the single `D` (a sum, so that no case analysis on `max` is
needed).  Note that `l` is a parameter of the statement, so a constant depending on `l` — as
`2^{δ l}` does — is harmless.
-/

/-! ## An elementary real-power estimate -/

/-- **Trade a smaller base for a slightly larger constant.**  For `a ≥ 1` and `x ≥ 0`,
`a ^ (-x) ≤ 2 ^ x * (a + 1) ^ (-x)`; equivalently `(a+1)^x ≤ (2a)^x`.  This is the loss incurred by
replacing `s` with `s+1` in the Gauss exponent. -/
lemma rpow_neg_le_two_mul_rpow_neg {a x : ℝ} (ha : 1 ≤ a) (hx : 0 ≤ x) :
    a ^ (-x) ≤ 2 ^ x * (a + 1) ^ (-x) := by
  have hapos : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have ha1pos : (0 : ℝ) < a + 1 := by linarith
  have h1 : a⁻¹ ≤ 2 * (a + 1)⁻¹ := by
    have h2 : (2 : ℝ) * (a + 1)⁻¹ = 2 / (a + 1) := by rw [div_eq_mul_inv]
    rw [inv_eq_one_div, h2, div_le_div_iff₀ hapos ha1pos]
    linarith
  calc a ^ (-x) = (a ^ x)⁻¹ := Real.rpow_neg hapos.le x
    _ = (a⁻¹) ^ x := (Real.inv_rpow hapos.le x).symm
    _ ≤ (2 * (a + 1)⁻¹) ^ x := Real.rpow_le_rpow (inv_nonneg.mpr hapos.le) h1 hx
    _ = 2 ^ x * (a + 1) ^ (-x) := by
        rw [Real.mul_rpow (by norm_num) (inv_nonneg.mpr ha1pos.le), Real.inv_rpow ha1pos.le,
          Real.rpow_neg ha1pos.le]

/-! ## The uniform decay -/

theorem mstG_gauss_uniform (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (hc : 0 < P.leadingCoeff)
    (l : ℕ) (hl : 1 ≤ l) :
    ∃ (δ D : ℝ), 0 < δ ∧ 0 < D ∧
      ∀ (s : ℕ) (β : Work.BourgainPlan.IonescuWainger.Circle),
        β ∈ Work.BourgainPlan.Maximal.mstU l (s + 1) \ Work.BourgainPlan.Maximal.mstU l s →
        ‖Work.BourgainPlan.Maximal.mstG P β‖ ≤ D * ((s : ℝ) + 1) ^ (-(δ * l)) := by
  obtain ⟨δ, C, hδpos, hCpos, hbound⟩ := mstG_gauss P hd hc l hl
  have hlne : l ≠ 0 := by omega
  have hδl : 0 < δ * (l : ℝ) := mul_pos hδpos (by exact_mod_cast hl)
  set N : ℕ := 2 ^ iwK (mstRho l) with hN
  have hN1 : 1 ≤ N := by rw [hN]; exact Nat.one_le_two_pow
  set D : ℝ := C * (2 : ℝ) ^ (δ * (l : ℝ)) + (((N : ℕ) : ℝ) + 1) ^ (δ * (l : ℝ)) with hD
  have hDpos : 0 < D := by
    rw [hD]
    exact add_pos (mul_pos hCpos (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _))
      (Real.rpow_pos_of_pos (by positivity) _)
  refine ⟨δ, D, hδpos, hDpos, ?_⟩
  intro s β hβ
  have hsnn : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
  have hpos1 : (0 : ℝ) < (s : ℝ) + 1 := by linarith
  rcases le_or_gt N (s ^ l) with hge | hlt
  · -- decay regime: `mstG_gauss` applies
    have hs1 : 1 ≤ s := by
      refine Nat.one_le_iff_ne_zero.mpr ?_
      intro h0
      rw [h0, zero_pow hlne] at hge
      omega
    have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs1
    have hgeR : (2 : ℝ) ^ ((iwK (mstRho l) : ℕ) : ℝ) ≤ (s : ℝ) ^ l := by
      rw [Real.rpow_natCast]
      have hnat : 2 ^ iwK (mstRho l) ≤ s ^ l := by rw [← hN]; exact hge
      exact_mod_cast hnat
    have hbs := hbound s β hgeR hβ
    have hs1R : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs1
    have hdecay : ((s : ℝ) ^ l) ^ (-δ) = (s : ℝ) ^ (-(δ * (l : ℝ))) := by
      rw [← Real.rpow_natCast (s : ℝ) l, ← Real.rpow_mul hsR.le (l : ℝ) (-δ)]
      congr 1
      ring
    have hkey := rpow_neg_le_two_mul_rpow_neg (a := (s : ℝ)) (x := δ * (l : ℝ)) hs1R hδl.le
    have hDle : C * (2 : ℝ) ^ (δ * (l : ℝ)) ≤ D := by
      rw [hD]
      exact le_add_of_nonneg_right (Real.rpow_nonneg (by positivity) _)
    calc ‖mstG P β‖
        ≤ C * ((s : ℝ) ^ l) ^ (-δ) := hbs
      _ = C * (s : ℝ) ^ (-(δ * (l : ℝ))) := by rw [hdecay]
      _ ≤ C * (2 ^ (δ * (l : ℝ)) * ((s : ℝ) + 1) ^ (-(δ * (l : ℝ)))) :=
          mul_le_mul_of_nonneg_left hkey hCpos.le
      _ = (C * 2 ^ (δ * (l : ℝ))) * ((s : ℝ) + 1) ^ (-(δ * (l : ℝ))) := by ring
      _ ≤ D * ((s : ℝ) + 1) ^ (-(δ * (l : ℝ))) :=
          mul_le_mul_of_nonneg_right hDle (Real.rpow_nonneg hpos1.le _)
  · -- trivial regime: `‖mstG‖ ≤ 1`
    have hsN : s < N := by
      rcases Nat.eq_zero_or_pos s with h0 | hpos
      · rw [h0]; exact lt_of_lt_of_le Nat.zero_lt_one hN1
      · exact lt_of_le_of_lt (Nat.le_self_pow hlne s) hlt
    have hsN' : (s : ℝ) + 1 ≤ (N : ℝ) + 1 := by
      have hnat : s + 1 ≤ N + 1 := Nat.succ_le_succ (le_of_lt hsN)
      exact_mod_cast hnat
    have hcle : ((s : ℝ) + 1) ^ (δ * (l : ℝ)) ≤ ((N : ℝ) + 1) ^ (δ * (l : ℝ)) :=
      Real.rpow_le_rpow (by positivity) hsN' hδl.le
    have hDle : ((N : ℝ) + 1) ^ (δ * (l : ℝ)) ≤ D := by
      rw [hD]
      exact le_add_of_nonneg_left
        (mul_nonneg hCpos.le (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _))
    have hxne : ((s : ℝ) + 1) ^ (δ * (l : ℝ)) ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos hpos1 _)
    have hone : (1 : ℝ) ≤ D * ((s : ℝ) + 1) ^ (-(δ * (l : ℝ))) := by
      calc (1 : ℝ)
          = ((s : ℝ) + 1) ^ (δ * (l : ℝ)) * (((s : ℝ) + 1) ^ (δ * (l : ℝ)))⁻¹ := by
            rw [mul_inv_cancel₀ hxne]
        _ ≤ D * (((s : ℝ) + 1) ^ (δ * (l : ℝ)))⁻¹ :=
            mul_le_mul_of_nonneg_right (le_trans hcle hDle)
              (inv_nonneg.mpr (Real.rpow_nonneg hpos1.le _))
        _ = D * ((s : ℝ) + 1) ^ (-(δ * (l : ℝ))) := by
            rw [Real.rpow_neg hpos1.le]
    exact le_trans (mstG_norm_le_one P β) hone

end Work.BourgainPlan.Maximal
