import Mathlib

/-!
# The `q`-clause arithmetic of the `D`-lossy gap case (pure real arithmetic).

See `NOTES_small_shift_GAP_SESSION.md`.
-/

set_option autoImplicit false

namespace Work.Peluse.Ulower

theorem ss_gap_q_arith {k : ℕ} {c0 C0 A0 D M Ns del delc gac A' q : ℝ}
    (hc00 : 0 < c0) (hd0 : 0 < del) (hd1 : del ≤ 1) (hgac0 : 0 < gac) (hdelc0 : 0 < delc)
    (hD0 : 0 < D) (hDM : D ≤ M) (hNs0 : 0 ≤ Ns) (hNsM : Ns ≤ A0 * M) (hA00 : 0 ≤ A0)
    (hC00 : 0 ≤ C0) (hA'1 : 1 ≤ A') (hlam : del ^ 3 / c0 ≤ delc * gac)
    (hq : q ≤ C0 * (delc⁻¹) ^ k * (gac⁻¹) ^ k * (Ns / D) ^ k) :
    q ≤ (C0 * c0 ^ k * A0 ^ k) * (A' ^ (3 * k) * (M / D) ^ (3 * k) * (del⁻¹) ^ (3 * k)) := by
  have hdcg0 : 0 < delc * gac := mul_pos hdelc0 hgac0
  have hd3c0 : 0 < del ^ 3 / c0 := by positivity
  have hinv : (delc * gac)⁻¹ ≤ (del ^ 3 / c0)⁻¹ := inv_anti₀ hd3c0 hlam
  have hpow : ((delc * gac)⁻¹) ^ k ≤ ((del ^ 3 / c0)⁻¹) ^ k :=
    pow_le_pow_left₀ (by positivity) hinv k
  have hrew1 : (del ^ 3 / c0)⁻¹ = c0 * (del⁻¹) ^ 3 := by
    rw [inv_div, inv_pow]; ring
  have hrew : ((del ^ 3 / c0)⁻¹) ^ k = c0 ^ k * (del⁻¹) ^ (3 * k) := by
    rw [hrew1, mul_pow, ← pow_mul]
  have h1 : (delc⁻¹) ^ k * (gac⁻¹) ^ k ≤ c0 ^ k * (del⁻¹) ^ (3 * k) := by
    rw [← mul_pow, ← mul_inv, ← hrew]
    exact hpow
  have hNsD : Ns / D ≤ A0 * (M / D) := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right hNsM hD0.le
  have h2 : (Ns / D) ^ k ≤ A0 ^ k * (M / D) ^ k := by
    have := pow_le_pow_left₀ (by positivity) hNsD k
    rwa [mul_pow] at this
  have hq2 : q ≤ C0 * (c0 ^ k * (del⁻¹) ^ (3 * k)) * (A0 ^ k * (M / D) ^ k) := by
    calc q ≤ C0 * (delc⁻¹) ^ k * (gac⁻¹) ^ k * (Ns / D) ^ k := hq
      _ = C0 * ((delc⁻¹) ^ k * (gac⁻¹) ^ k) * (Ns / D) ^ k := by ring
      _ ≤ C0 * (c0 ^ k * (del⁻¹) ^ (3 * k)) * (Ns / D) ^ k := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left h1 hC00) (by positivity)
      _ ≤ C0 * (c0 ^ k * (del⁻¹) ^ (3 * k)) * (A0 ^ k * (M / D) ^ k) := by
            exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have hA'k : 1 ≤ A' ^ (3 * k) := one_le_pow₀ hA'1
  have hMD1 : 1 ≤ M / D := (one_le_div hD0).mpr hDM
  have hMDk : (M / D) ^ k ≤ (M / D) ^ (3 * k) := pow_le_pow_right₀ hMD1 (by omega)
  have hdelk : 0 ≤ (del⁻¹) ^ (3 * k) := by positivity
  have h3 : C0 * (c0 ^ k * (del⁻¹) ^ (3 * k)) * (A0 ^ k * (M / D) ^ k)
      ≤ (C0 * c0 ^ k * A0 ^ k) * (A' ^ (3 * k) * (M / D) ^ (3 * k) * (del⁻¹) ^ (3 * k)) := by
    have hX : 0 ≤ (del⁻¹) ^ (3 * k) * (M / D) ^ k := by positivity
    calc C0 * (c0 ^ k * (del⁻¹) ^ (3 * k)) * (A0 ^ k * (M / D) ^ k)
        = (C0 * c0 ^ k * A0 ^ k) * ((del⁻¹) ^ (3 * k) * (M / D) ^ k) := by ring
      _ ≤ (C0 * c0 ^ k * A0 ^ k) * ((del⁻¹) ^ (3 * k) * (M / D) ^ (3 * k)) := by
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hMDk hdelk) (by positivity)
      _ ≤ (C0 * c0 ^ k * A0 ^ k) * (A' ^ (3 * k) * ((M / D) ^ (3 * k) * (del⁻¹) ^ (3 * k))) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            have hX' : (0:ℝ) ≤ (M / D) ^ (3 * k) * (del⁻¹) ^ (3 * k) := by positivity
            calc (del⁻¹) ^ (3 * k) * (M / D) ^ (3 * k)
                = 1 * ((M / D) ^ (3 * k) * (del⁻¹) ^ (3 * k)) := by ring
              _ ≤ A' ^ (3 * k) * ((M / D) ^ (3 * k) * (del⁻¹) ^ (3 * k)) :=
                  mul_le_mul_of_nonneg_right hA'k hX'
      _ = (C0 * c0 ^ k * A0 ^ k) * (A' ^ (3 * k) * (M / D) ^ (3 * k) * (del⁻¹) ^ (3 * k)) := by ring
  exact le_trans hq2 h3



/-- **The sharp `q`-clause** (the intermediate of `ss_gap_q_arith`): the `A'`-factor is kept out. -/
theorem ss_gap_q_arith_sharp {k : ℕ} {c0 C0 A0 D M Ns del delc gac q : ℝ}
    (hc00 : 0 < c0) (hd0 : 0 < del) (hd1 : del ≤ 1) (hgac0 : 0 < gac) (hdelc0 : 0 < delc)
    (hD0 : 0 < D) (hDM : D ≤ M) (hNs0 : 0 ≤ Ns) (hNsM : Ns ≤ A0 * M) (hA00 : 0 ≤ A0)
    (hC00 : 0 ≤ C0) (hlam : del ^ 3 / c0 ≤ delc * gac)
    (hq : q ≤ C0 * (delc⁻¹) ^ k * (gac⁻¹) ^ k * (Ns / D) ^ k) :
    q ≤ C0 * c0 ^ k * A0 ^ k * (del⁻¹) ^ (3 * k) * (M / D) ^ k := by
  have hd3c0 : 0 < del ^ 3 / c0 := by positivity
  have hinv : (delc * gac)⁻¹ ≤ (del ^ 3 / c0)⁻¹ := inv_anti₀ hd3c0 hlam
  have hpow : ((delc * gac)⁻¹) ^ k ≤ ((del ^ 3 / c0)⁻¹) ^ k :=
    pow_le_pow_left₀ (by positivity) hinv k
  have hrew1 : (del ^ 3 / c0)⁻¹ = c0 * (del⁻¹) ^ 3 := by
    rw [inv_div, inv_pow]; ring
  have hrew : ((del ^ 3 / c0)⁻¹) ^ k = c0 ^ k * (del⁻¹) ^ (3 * k) := by
    rw [hrew1, mul_pow, ← pow_mul]
  have h1 : (delc⁻¹) ^ k * (gac⁻¹) ^ k ≤ c0 ^ k * (del⁻¹) ^ (3 * k) := by
    rw [← mul_pow, ← mul_inv, ← hrew]
    exact hpow
  have hNsD : Ns / D ≤ A0 * (M / D) := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right hNsM hD0.le
  have h2 : (Ns / D) ^ k ≤ A0 ^ k * (M / D) ^ k := by
    have := pow_le_pow_left₀ (by positivity) hNsD k
    rwa [mul_pow] at this
  calc q ≤ C0 * (delc⁻¹) ^ k * (gac⁻¹) ^ k * (Ns / D) ^ k := hq
    _ = C0 * ((delc⁻¹) ^ k * (gac⁻¹) ^ k) * (Ns / D) ^ k := by ring
    _ ≤ C0 * (c0 ^ k * (del⁻¹) ^ (3 * k)) * (A0 ^ k * (M / D) ^ k) := by
          have h1' : C0 * ((delc⁻¹) ^ k * (gac⁻¹) ^ k) ≤ C0 * (c0 ^ k * (del⁻¹) ^ (3 * k)) :=
            mul_le_mul_of_nonneg_left h1 hC00
          exact mul_le_mul h1' h2 (by positivity) (by positivity)
    _ = C0 * c0 ^ k * A0 ^ k * (del⁻¹) ^ (3 * k) * (M / D) ^ k := by ring

end Work.Peluse.Ulower
