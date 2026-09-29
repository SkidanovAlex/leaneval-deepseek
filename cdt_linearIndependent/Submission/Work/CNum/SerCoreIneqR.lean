import Mathlib
import Submission.Work.CNum.SerCorePlan

/-!
# `Work.CNum.SerCoreIneqR` — the elementary route to the `serUp` core inequality

We prove

  `∑_{J=1}^{44} max (A_J) (B_J) ≤ R^90/(2(1-R²)) - R^135/(3(1-R³))`,  `R = c + ρ`,

for `0 < c`, `0 < ρ`, `ρ < c`, `R < 1`, `R ≤ 4/5`, `ρ ≤ 1/1000`, where

  `A_J = log (1 - c^J + (R^J - c^J)) - log (1 - c^J + (45-J) R^{J-1} ρ)`,
  `B_J = log (1 + c^J + (R^J - c^J)) - log (1 + c^J + (45-J) R^{J-1} ρ)`.

The right-hand side is non-negative for `0 < R < 1`, so it suffices to show that the left-hand
side is `≤ 0`.  This is done by a first-order pairing:

* With `Δ_J = (2J-45) R^{J-1} ρ` and `Φ_J = R^J - c^J - (45-J) R^{J-1} ρ` one has
  `Φ_J ≤ Δ_J` (geometric bound `R^J - c^J ≤ J R^{J-1} ρ`), and `log x - log y ≤ (x-y)/y`, so
  each of `A_J`, `B_J` is at most `Φ_J` divided by its own denominator.
* For `J ≤ 22` (`Δ_J ≤ 0`) both denominators are `≤ 1 + R^J + 45ρ`, giving
  `max (A_J) (B_J) ≤ Δ_J/(1 + R^J + 45ρ)`; for `J ≥ 23` (`Δ_J ≥ 0`) both are `≥ 1 - R^J`,
  giving `max (A_J) (B_J) ≤ Δ_J/(1 - R^J)`.
* Summing and reindexing `J ↦ 45 - J` over `23 ≤ J ≤ 44`, the total is
  `∑_{J=1}^{22} (45-2J) ρ [ R^{44-J}/(1-R^{45-J}) - R^{J-1}/(1+R^J+45ρ) ]`,
  and every bracket is `≤ 0` because `R^{45-2J}(1 + R^J + 45ρ) ≤ 1 - R^{45-J}`
  (from `R ≤ 4/5`, `ρ ≤ 1/1000`).

All numerical inputs are `norm_num`-checkable rational inequalities.
-/

namespace Work.CNum

open Finset

/-! ## Elementary analytic helpers -/

/-- `log x - log y ≤ (x - y)/y` for `x, y > 0`. -/
lemma log_sub_log_le_div {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.log x - Real.log y ≤ (x - y) / y := by
  have h := Real.log_le_sub_one_of_pos (div_pos hx hy)
  rw [Real.log_div (ne_of_gt hx) (ne_of_gt hy)] at h
  have h2 : x / y - 1 = (x - y) / y := by rw [sub_div, div_self (ne_of_gt hy)]
  linarith

/-- `R ^ J - c ^ J ≤ J · R ^ (J-1) · (R - c)` for `0 ≤ c ≤ R`. -/
lemma pow_sub_pow_le_geom {c R : ℝ} (hc : 0 ≤ c) (hcR : c ≤ R) (J : ℕ) :
    R ^ J - c ^ J ≤ (J : ℝ) * R ^ (J - 1) * (R - c) := by
  have hR0 : 0 ≤ R := le_trans hc hcR
  rcases Nat.eq_zero_or_pos J with hJ | hJ
  · subst hJ; simp
  have hgeo := geom_sum₂_mul R c J
  have hnonneg : 0 ≤ R - c := by linarith
  have hterm : ∀ i ∈ Finset.range J, R ^ i * c ^ (J - 1 - i) ≤ R ^ (J - 1) := by
    intro i hi
    have hiJ : i < J := Finset.mem_range.mp hi
    have hile : i ≤ J - 1 := Nat.le_sub_one_of_lt hiJ
    have hci : c ^ (J - 1 - i) ≤ R ^ (J - 1 - i) := pow_le_pow_left₀ hc hcR _
    have hpi : 0 ≤ R ^ i := pow_nonneg hR0 i
    calc R ^ i * c ^ (J - 1 - i) ≤ R ^ i * R ^ (J - 1 - i) :=
          mul_le_mul_of_nonneg_left hci hpi
      _ = R ^ (i + (J - 1 - i)) := (pow_add R i (J - 1 - i)).symm
      _ = R ^ (J - 1) := by rw [Nat.add_sub_cancel' hile]
  have hsum : (∑ i ∈ Finset.range J, R ^ i * c ^ (J - 1 - i)) ≤ (J : ℝ) * R ^ (J - 1) := by
    calc (∑ i ∈ Finset.range J, R ^ i * c ^ (J - 1 - i))
        ≤ ∑ i ∈ Finset.range J, R ^ (J - 1) := Finset.sum_le_sum hterm
      _ = (J : ℝ) * R ^ (J - 1) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  calc R ^ J - c ^ J = (∑ i ∈ Finset.range J, R ^ i * c ^ (J - 1 - i)) * (R - c) := hgeo.symm
    _ ≤ ((J : ℝ) * R ^ (J - 1)) * (R - c) := mul_le_mul_of_nonneg_right hsum hnonneg
    _ = (J : ℝ) * R ^ (J - 1) * (R - c) := by ring

/-- If `D ≤ 0` and the denominators are positive and `≤ V`, the max of the two log-differences
is at most `D / V`. -/
lemma max_log_le_of_nonpos {xA vA xB vB D V : ℝ} (hxA : 0 < xA) (hvA : 0 < vA)
    (hxB : 0 < xB) (hvB : 0 < vB) (hV : 0 < V) (hA : xA - vA ≤ D) (hB : xB - vB ≤ D)
    (hD : D ≤ 0) (hAV : vA ≤ V) (hBV : vB ≤ V) :
    max (Real.log xA - Real.log vA) (Real.log xB - Real.log vB) ≤ D / V := by
  refine max_le ?_ ?_
  · have h1 := log_sub_log_le_div hxA hvA
    have h2 : (xA - vA) / vA ≤ D / vA := div_le_div_of_nonneg_right hA (le_of_lt hvA)
    have h3 : D / vA ≤ D / V := by
      rw [div_le_div_iff₀ hvA hV]
      exact mul_le_mul_of_nonpos_left hAV hD
    linarith
  · have h1 := log_sub_log_le_div hxB hvB
    have h2 : (xB - vB) / vB ≤ D / vB := div_le_div_of_nonneg_right hB (le_of_lt hvB)
    have h3 : D / vB ≤ D / V := by
      rw [div_le_div_iff₀ hvB hV]
      exact mul_le_mul_of_nonpos_left hBV hD
    linarith

/-- If `D ≥ 0` and the denominators are positive and `≥ W`, the max of the two log-differences
is at most `D / W`. -/
lemma max_log_le_of_nonneg {xA vA xB vB D W : ℝ} (hxA : 0 < xA) (hvA : 0 < vA)
    (hxB : 0 < xB) (hvB : 0 < vB) (hW : 0 < W) (hA : xA - vA ≤ D) (hB : xB - vB ≤ D)
    (hD : 0 ≤ D) (hWA : W ≤ vA) (hWB : W ≤ vB) :
    max (Real.log xA - Real.log vA) (Real.log xB - Real.log vB) ≤ D / W := by
  refine max_le ?_ ?_
  · have h1 := log_sub_log_le_div hxA hvA
    have h2 : (xA - vA) / vA ≤ D / vA := div_le_div_of_nonneg_right hA (le_of_lt hvA)
    have h3 : D / vA ≤ D / W := by
      rw [div_le_div_iff₀ hvA hW]
      exact mul_le_mul_of_nonneg_left hWA hD
    linarith
  · have h1 := log_sub_log_le_div hxB hvB
    have h2 : (xB - vB) / vB ≤ D / vB := div_le_div_of_nonneg_right hB (le_of_lt hvB)
    have h3 : D / vB ≤ D / W := by
      rw [div_le_div_iff₀ hvB hW]
      exact mul_le_mul_of_nonneg_left hWB hD
    linarith

/-! ## The two per-term estimates -/

/-- Per-term estimate for `1 ≤ J ≤ 22` (`Δ_J ≤ 0`). -/
lemma serCoreTermLe22 {c ρ : ℝ} (hc : 0 < c) (hρ : 0 < ρ) (hR1 : c + ρ < 1)
    {J : ℕ} (hJ1 : 1 ≤ J) (hJ22 : J ≤ 22) :
    max (Real.log (1 - c ^ J + ((c + ρ) ^ J - c ^ J))
          - Real.log (1 - c ^ J + ((45 - J : ℕ) : ℝ) * (c + ρ) ^ (J - 1) * ρ))
        (Real.log (1 + c ^ J + ((c + ρ) ^ J - c ^ J))
          - Real.log (1 + c ^ J + ((45 - J : ℕ) : ℝ) * (c + ρ) ^ (J - 1) * ρ))
      ≤ ((2 * (J : ℝ) - 45) * (c + ρ) ^ (J - 1) * ρ) / (1 + (c + ρ) ^ J + 45 * ρ) := by
  set R := c + ρ with hRdef
  have hRpos : 0 < R := by rw [hRdef]; linarith
  have hRlt1 : R < 1 := by rw [hRdef]; linarith
  have hc0 : 0 ≤ c := le_of_lt hc
  have hcR : c ≤ R := by rw [hRdef]; linarith
  have hc1 : c < 1 := lt_of_le_of_lt hcR hRlt1
  have hJne : J ≠ 0 := by omega
  have hcJ1 : c ^ J < 1 := pow_lt_one₀ hc0 hc1 hJne
  have hcJ0 : 0 ≤ c ^ J := pow_nonneg hc0 J
  have hcJle : c ^ J ≤ R ^ J := pow_le_pow_left₀ hc0 hcR J
  have hRcJ : 0 ≤ R ^ J - c ^ J := sub_nonneg.mpr hcJle
  have hRc : R - c = ρ := by rw [hRdef]; ring
  have hδ : R ^ J - c ^ J ≤ (J : ℝ) * R ^ (J - 1) * ρ := by
    have h := pow_sub_pow_le_geom hc0 hcR J
    rwa [hRc] at h
  have hcast : ((45 - J : ℕ) : ℝ) = 45 - (J : ℝ) := by
    rw [Nat.cast_sub (by omega : J ≤ 45)]
    norm_num
  have hX0 : 0 ≤ ((45 - J : ℕ) : ℝ) * R ^ (J - 1) * ρ :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (le_of_lt hRpos) _)) (le_of_lt hρ)
  have hX45 : ((45 - J : ℕ) : ℝ) * R ^ (J - 1) * ρ ≤ 45 * ρ := by
    have h45 : ((45 - J : ℕ) : ℝ) ≤ 45 := by
      have h : (45 - J : ℕ) ≤ 45 := Nat.sub_le _ _
      exact_mod_cast h
    have hRp : R ^ (J - 1) ≤ 1 := pow_le_one₀ (le_of_lt hRpos) (le_of_lt hRlt1)
    have hRp0 : 0 ≤ R ^ (J - 1) := pow_nonneg (le_of_lt hRpos) _
    calc ((45 - J : ℕ) : ℝ) * R ^ (J - 1) * ρ
        = ((45 - J : ℕ) : ℝ) * (R ^ (J - 1) * ρ) := by ring
      _ ≤ 45 * (R ^ (J - 1) * ρ) := mul_le_mul_of_nonneg_right h45 (mul_nonneg hRp0 (le_of_lt hρ))
      _ ≤ 45 * (1 * ρ) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact mul_le_mul_of_nonneg_right hRp (le_of_lt hρ)
      _ = 45 * ρ := by ring
  have hDle : (2 * (J : ℝ) - 45) * R ^ (J - 1) * ρ ≤ 0 := by
    have h2 : (2 * (J : ℝ) - 45) ≤ 0 := by
      have : (J : ℝ) ≤ 22 := by exact_mod_cast hJ22
      linarith
    calc (2 * (J : ℝ) - 45) * R ^ (J - 1) * ρ
        = (2 * (J : ℝ) - 45) * (R ^ (J - 1) * ρ) := by ring
      _ ≤ 0 * (R ^ (J - 1) * ρ) := mul_le_mul_of_nonneg_right h2 (mul_nonneg (pow_nonneg (le_of_lt hRpos) _) (le_of_lt hρ))
      _ = 0 := by ring
  have hkey : (R ^ J - c ^ J) - ((45 - J : ℕ) : ℝ) * R ^ (J - 1) * ρ
      ≤ (2 * (J : ℝ) - 45) * R ^ (J - 1) * ρ := by
    have h1 : (R ^ J - c ^ J) - ((45 - J : ℕ) : ℝ) * R ^ (J - 1) * ρ
        ≤ (J : ℝ) * R ^ (J - 1) * ρ - ((45 - J : ℕ) : ℝ) * R ^ (J - 1) * ρ := by
      linarith
    have h2 : (J : ℝ) * R ^ (J - 1) * ρ - ((45 - J : ℕ) : ℝ) * R ^ (J - 1) * ρ
        = (2 * (J : ℝ) - 45) * R ^ (J - 1) * ρ := by
      rw [hcast]; ring
    linarith [h1, h2]
  have hkeyA : (1 - c ^ J + (R ^ J - c ^ J)) - (1 - c ^ J + ((45 - J : ℕ) : ℝ) * R ^ (J - 1) * ρ)
      ≤ (2 * (J : ℝ) - 45) * R ^ (J - 1) * ρ := by
    have : (1 - c ^ J + (R ^ J - c ^ J)) - (1 - c ^ J + ((45 - J : ℕ) : ℝ) * R ^ (J - 1) * ρ)
        = (R ^ J - c ^ J) - ((45 - J : ℕ) : ℝ) * R ^ (J - 1) * ρ := by ring
    rw [this]; exact hkey
  have hkeyB : (1 + c ^ J + (R ^ J - c ^ J)) - (1 + c ^ J + ((45 - J : ℕ) : ℝ) * R ^ (J - 1) * ρ)
      ≤ (2 * (J : ℝ) - 45) * R ^ (J - 1) * ρ := by
    have : (1 + c ^ J + (R ^ J - c ^ J)) - (1 + c ^ J + ((45 - J : ℕ) : ℝ) * R ^ (J - 1) * ρ)
        = (R ^ J - c ^ J) - ((45 - J : ℕ) : ℝ) * R ^ (J - 1) * ρ := by ring
    rw [this]; exact hkey
  refine max_log_le_of_nonpos ?_ ?_ ?_ ?_ ?_ hkeyA hkeyB hDle ?_ ?_
  · linarith
  · linarith
  · linarith
  · linarith
  · have hRJ0 : 0 ≤ R ^ J := pow_nonneg (le_of_lt hRpos) J
    linarith
  · linarith
  · linarith

/-- Per-term estimate for `23 ≤ J ≤ 44` (`Δ_J ≥ 0`). -/
lemma serCoreTermLe23 {c ρ : ℝ} (hc : 0 < c) (hρ : 0 < ρ) (hR1 : c + ρ < 1)
    {J : ℕ} (hJ23 : 23 ≤ J) (hJ44 : J ≤ 44) :
    max (Real.log (1 - c ^ J + ((c + ρ) ^ J - c ^ J))
          - Real.log (1 - c ^ J + ((45 - J : ℕ) : ℝ) * (c + ρ) ^ (J - 1) * ρ))
        (Real.log (1 + c ^ J + ((c + ρ) ^ J - c ^ J))
          - Real.log (1 + c ^ J + ((45 - J : ℕ) : ℝ) * (c + ρ) ^ (J - 1) * ρ))
      ≤ ((2 * (J : ℝ) - 45) * (c + ρ) ^ (J - 1) * ρ) / (1 - (c + ρ) ^ J) := by
  set R := c + ρ with hRdef
  have hRpos : 0 < R := by rw [hRdef]; linarith
  have hRlt1 : R < 1 := by rw [hRdef]; linarith
  have hc0 : 0 ≤ c := le_of_lt hc
  have hcR : c ≤ R := by rw [hRdef]; linarith
  have hc1 : c < 1 := lt_of_le_of_lt hcR hRlt1
  have hJne : J ≠ 0 := by omega
  have hcJ1 : c ^ J < 1 := pow_lt_one₀ hc0 hc1 hJne
  have hcJ0 : 0 ≤ c ^ J := pow_nonneg hc0 J
  have hcJle : c ^ J ≤ R ^ J := pow_le_pow_left₀ hc0 hcR J
  have hRcJ : 0 ≤ R ^ J - c ^ J := sub_nonneg.mpr hcJle
  have hRJ1 : R ^ J < 1 := pow_lt_one₀ (le_of_lt hRpos) hRlt1 hJne
  have hRc : R - c = ρ := by rw [hRdef]; ring
  have hδ : R ^ J - c ^ J ≤ (J : ℝ) * R ^ (J - 1) * ρ := by
    have h := pow_sub_pow_le_geom hc0 hcR J
    rwa [hRc] at h
  have hX0 : 0 ≤ ((45 - J : ℕ) : ℝ) * R ^ (J - 1) * ρ :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (le_of_lt hRpos) _)) (le_of_lt hρ)
  have hDge : 0 ≤ (2 * (J : ℝ) - 45) * R ^ (J - 1) * ρ := by
    have h2 : (0 : ℝ) ≤ 2 * (J : ℝ) - 45 := by
      have : (23 : ℝ) ≤ (J : ℝ) := by exact_mod_cast hJ23
      linarith
    exact mul_nonneg (mul_nonneg h2 (pow_nonneg (le_of_lt hRpos) _)) (le_of_lt hρ)
  have hcast : ((45 - J : ℕ) : ℝ) = 45 - (J : ℝ) := by
    rw [Nat.cast_sub (by omega : J ≤ 45)]
    norm_num
  have hkey : (R ^ J - c ^ J) - ((45 - J : ℕ) : ℝ) * R ^ (J - 1) * ρ
      ≤ (2 * (J : ℝ) - 45) * R ^ (J - 1) * ρ := by
    have h1 : (R ^ J - c ^ J) - ((45 - J : ℕ) : ℝ) * R ^ (J - 1) * ρ
        ≤ (J : ℝ) * R ^ (J - 1) * ρ - ((45 - J : ℕ) : ℝ) * R ^ (J - 1) * ρ := by
      linarith
    have h2 : (J : ℝ) * R ^ (J - 1) * ρ - ((45 - J : ℕ) : ℝ) * R ^ (J - 1) * ρ
        = (2 * (J : ℝ) - 45) * R ^ (J - 1) * ρ := by
      rw [hcast]; ring
    linarith [h1, h2]
  have hkeyA : (1 - c ^ J + (R ^ J - c ^ J)) - (1 - c ^ J + ((45 - J : ℕ) : ℝ) * R ^ (J - 1) * ρ)
      ≤ (2 * (J : ℝ) - 45) * R ^ (J - 1) * ρ := by
    have : (1 - c ^ J + (R ^ J - c ^ J)) - (1 - c ^ J + ((45 - J : ℕ) : ℝ) * R ^ (J - 1) * ρ)
        = (R ^ J - c ^ J) - ((45 - J : ℕ) : ℝ) * R ^ (J - 1) * ρ := by ring
    rw [this]; exact hkey
  have hkeyB : (1 + c ^ J + (R ^ J - c ^ J)) - (1 + c ^ J + ((45 - J : ℕ) : ℝ) * R ^ (J - 1) * ρ)
      ≤ (2 * (J : ℝ) - 45) * R ^ (J - 1) * ρ := by
    have : (1 + c ^ J + (R ^ J - c ^ J)) - (1 + c ^ J + ((45 - J : ℕ) : ℝ) * R ^ (J - 1) * ρ)
        = (R ^ J - c ^ J) - ((45 - J : ℕ) : ℝ) * R ^ (J - 1) * ρ := by ring
    rw [this]; exact hkey
  refine max_log_le_of_nonneg ?_ ?_ ?_ ?_ ?_ hkeyA hkeyB hDge ?_ ?_
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith

/-! ## The right-hand side is non-negative -/

lemma serCoreRHS_nonneg {R : ℝ} (hR0 : 0 < R) (hR1 : R < 1) :
    0 ≤ R ^ (2 * 45) / (2 * (1 - R ^ 2)) - R ^ (3 * 45) / (3 * (1 - R ^ 3)) := by
  have hR0' : 0 ≤ R := le_of_lt hR0
  have h1R : 0 < 1 - R := by linarith
  have h1R2 : 0 < 1 - R ^ 2 := by nlinarith [mul_pos h1R (by linarith : (0:ℝ) < 1 + R)]
  have h1R3 : 0 < 1 - R ^ 3 := by
    nlinarith [mul_pos h1R (by nlinarith [sq_nonneg R] : (0:ℝ) < 1 + R + R^2)]
  have hR45 : R ^ 45 ≤ 1 := pow_le_one₀ hR0' (le_of_lt hR1)
  have hnum : 0 ≤ R ^ 90 * (3 * (1 - R ^ 3) - 2 * R ^ 45 * (1 - R ^ 2)) := by
    apply mul_nonneg (pow_nonneg hR0' 90)
    have hfac : 3 * (1 - R ^ 3) - 2 * R ^ 45 * (1 - R ^ 2)
        = (1 - R) * (3 * (1 + R + R ^ 2) - 2 * R ^ 45 * (1 + R)) := by ring
    rw [hfac]
    apply mul_nonneg (le_of_lt h1R)
    nlinarith [hR45, hR0', sq_nonneg R]
  have hmain : R ^ (2*45) / (2 * (1 - R ^ 2)) - R ^ (3*45) / (3 * (1 - R ^ 3))
      = R ^ 90 * (3 * (1 - R ^ 3) - 2 * R ^ 45 * (1 - R ^ 2))
        / (6 * (1 - R ^ 2) * (1 - R ^ 3)) := by
    rw [show (2*45 : ℕ) = 90 from rfl, show (3*45 : ℕ) = 135 from rfl]
    rw [show (135:ℕ) = 90 + 45 from rfl, pow_add]
    field_simp
    ring
  rw [hmain]
  exact div_nonneg hnum (by positivity)

/-! ## The pairing inequality -/

/-- The numerator bound `R ^ (45 - 2J) * (1 + R^J + 45ρ) ≤ 1 - R ^ (45 - J)`. -/
lemma serCoreNumPair {R ρ : ℝ} (hR0 : 0 < R) (hR8 : R ≤ 4 / 5) (hρ0 : 0 < ρ)
    (hρs : ρ ≤ 1 / 1000) {J : ℕ} (hJ1 : 1 ≤ J) (hJ22 : J ≤ 22) :
    R ^ (45 - 2 * J) * (1 + R ^ J + 45 * ρ) ≤ 1 - R ^ (45 - J) := by
  have hR0' : 0 ≤ R := le_of_lt hR0
  set n := 45 - 2 * J with hn
  have hn1 : 1 ≤ n := by omega
  have hnj : n + J = 45 - J := by omega
  have hRn : R ^ n ≤ 4 / 5 := by
    calc R ^ n ≤ (4/5) ^ n := pow_le_pow_left₀ hR0' hR8 n
      _ ≤ (4/5) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hn1
      _ = 4/5 := by norm_num
  have hRnJ : R ^ (n + J) ≤ (4/5) ^ 23 := by
    calc R ^ (n + J) ≤ (4/5) ^ (n + J) := pow_le_pow_left₀ hR0' hR8 _
      _ ≤ (4/5) ^ 23 := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have h45rho : 45 * ρ ≤ 9 / 200 := by
    have : (45:ℝ) * ρ ≤ 45 * (1/1000) := by linarith
    linarith
  have hbound : R ^ n + R ^ (n + J) + 45 * ρ * R ^ n ≤ 4/5 + (4/5)^23 + 9/250 := by
    have h3 : 45 * ρ * R ^ n ≤ 9/200 * (4/5) := by
      calc 45 * ρ * R ^ n ≤ 9/200 * R ^ n := mul_le_mul_of_nonneg_right h45rho (pow_nonneg hR0' n)
        _ ≤ 9/200 * (4/5) := mul_le_mul_of_nonneg_left hRn (by norm_num)
    have h4 : (9:ℝ)/200 * (4/5) = 9/250 := by norm_num
    linarith
  have hfinal : (4:ℝ)/5 + (4/5)^23 + 9/250 ≤ 1 - (4/5)^23 := by norm_num
  calc R ^ n * (1 + R ^ J + 45 * ρ)
      = R ^ n + R ^ n * R ^ J + R ^ n * (45 * ρ) := by ring
    _ = R ^ n + R ^ (n + J) + 45 * ρ * R ^ n := by rw [pow_add]; ring
    _ ≤ 4/5 + (4/5)^23 + 9/250 := hbound
    _ ≤ 1 - (4/5)^23 := hfinal
    _ ≤ 1 - R ^ (n + J) := by linarith
    _ = 1 - R ^ (45 - J) := by rw [hnj]

/-- The two summands `G_J`, `H_J` used in the assembly. -/
noncomputable def serCoreG (R ρ : ℝ) (J : ℕ) : ℝ :=
  ((2 * (J : ℝ) - 45) * R ^ (J - 1) * ρ) / (1 + R ^ J + 45 * ρ)

/-- The second summand, evaluated at the reflected index. -/
noncomputable def serCoreH (R ρ : ℝ) (J : ℕ) : ℝ :=
  ((2 * (J : ℝ) - 45) * R ^ (J - 1) * ρ) / (1 - R ^ J)

/-- Each reflected pair of summands is non-positive. -/
lemma serCoreNumPair_nonpos {R ρ : ℝ} (hR0 : 0 < R) (hR8 : R ≤ 4 / 5) (hρ0 : 0 < ρ)
    (hρs : ρ ≤ 1 / 1000) {J : ℕ} (hJ1 : 1 ≤ J) (hJ22 : J ≤ 22) :
    serCoreG R ρ J + serCoreH R ρ (45 - J) ≤ 0 := by
  have hR1 : R < 1 := by linarith
  simp only [serCoreG, serCoreH]
  have hcast : ((45 - J : ℕ) : ℝ) = 45 - (J : ℝ) := by
    rw [Nat.cast_sub (by omega : J ≤ 45)]
    norm_num
  have hexp : (45 - J) - 1 = 44 - J := by omega
  have hcoef2 : 2 * ((45 - J : ℕ) : ℝ) - 45 = 45 - 2 * (J : ℝ) := by rw [hcast]; ring
  have hrew : ((2 * ((45 - J : ℕ) : ℝ) - 45) * R ^ ((45 - J) - 1) * ρ) / (1 - R ^ (45 - J))
      = ((45 - 2 * (J : ℝ)) * R ^ (44 - J) * ρ) / (1 - R ^ (45 - J)) := by
    rw [hcoef2, hexp]
  rw [hrew]
  have hB : 0 < 1 + R ^ J + 45 * ρ := by
    have h1 : 0 ≤ R ^ J := pow_nonneg (le_of_lt hR0) J
    nlinarith [h1, hρ0]
  have hA : 0 < 1 - R ^ (45 - J) := by
    have h1 : R ^ (45 - J) < 1 := pow_lt_one₀ (le_of_lt hR0) hR1 (by omega)
    linarith
  have hpow : R ^ (44 - J) = R ^ (J - 1) * R ^ (45 - 2 * J) := by
    rw [← pow_add]
    congr 1
    omega
  have hkey : R ^ (44 - J) * (1 + R ^ J + 45 * ρ) ≤ R ^ (J - 1) * (1 - R ^ (45 - J)) := by
    have hp := serCoreNumPair hR0 hR8 hρ0 hρs hJ1 hJ22
    rw [hpow]
    calc R ^ (J - 1) * R ^ (45 - 2 * J) * (1 + R ^ J + 45 * ρ)
        = R ^ (J - 1) * (R ^ (45 - 2 * J) * (1 + R ^ J + 45 * ρ)) := by ring
      _ ≤ R ^ (J - 1) * (1 - R ^ (45 - J)) :=
          mul_le_mul_of_nonneg_left hp (pow_nonneg (le_of_lt hR0) (J - 1))
  have hvu : R ^ (44 - J) / (1 - R ^ (45 - J)) ≤ R ^ (J - 1) / (1 + R ^ J + 45 * ρ) := by
    rw [div_le_div_iff₀ hA hB]
    exact hkey
  have hcoef : 0 ≤ (45 - 2 * (J : ℝ)) * ρ := by
    have h1 : (0:ℝ) ≤ 45 - 2 * (J:ℝ) := by
      have : (J:ℝ) ≤ 22 := by exact_mod_cast hJ22
      linarith
    exact mul_nonneg h1 (le_of_lt hρ0)
  have hEq : ((2 * (J : ℝ) - 45) * R ^ (J - 1) * ρ) / (1 + R ^ J + 45 * ρ)
      + ((45 - 2 * (J : ℝ)) * R ^ (44 - J) * ρ) / (1 - R ^ (45 - J))
      = (45 - 2 * (J : ℝ)) * ρ
        * (R ^ (44 - J) / (1 - R ^ (45 - J)) - R ^ (J - 1) / (1 + R ^ J + 45 * ρ)) := by
    field_simp
    ring
  rw [hEq]
  exact mul_nonpos_of_nonneg_of_nonpos hcoef (by linarith)

/-- Splitting the `Icc 1 44` sum at `22`. -/
lemma sum_Icc_one_44_split (f : ℕ → ℝ) :
    (∑ J ∈ Finset.Icc 1 44, f J) = (∑ J ∈ Finset.Icc 1 22, f J) + ∑ J ∈ Finset.Icc 23 44, f J := by
  rw [show (Finset.Icc 1 44 : Finset ℕ) = Finset.Icc 1 22 ∪ Finset.Icc 23 44 from by
    ext x; simp only [Finset.mem_Icc, Finset.mem_union]; omega]
  rw [Finset.sum_union]
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  simp only [Finset.mem_Icc] at hx1 hx2
  omega

/-- Reflection of the `Icc 23 44` sum. -/
lemma sum_Icc_reflect_23_44 (g : ℕ → ℝ) :
    (∑ J ∈ Finset.Icc 23 44, g J) = ∑ K ∈ Finset.Icc 1 22, g (45 - K) := by
  refine Finset.sum_bij (fun J _ => 45 - J) ?_ ?_ ?_ ?_
  · intro J hJ; simp only [Finset.mem_Icc] at hJ ⊢; omega
  · intro J1 hJ1 J2 hJ2 h; simp only [Finset.mem_Icc] at hJ1 hJ2; omega
  · intro K hK; simp only [Finset.mem_Icc] at hK
    exact ⟨45 - K, by simp only [Finset.mem_Icc]; omega, by omega⟩
  · intro J hJ; simp only [Finset.mem_Icc] at hJ; congr 1; omega

theorem SerCoreIneqR {c ρ : ℝ} (hc : 0 < c) (hρ : 0 < ρ) (hρc : ρ < c) (hR1 : c + ρ < 1) (hR8 : c + ρ ≤ 4 / 5) (hρs : ρ ≤ 1 / 1000) : (∑ J ∈ Finset.Icc (1 : ℕ) 44, max (Real.log (1 - c ^ J + ((c + ρ) ^ J - c ^ J)) - Real.log (1 - c ^ J + ((45 - J : ℕ) : ℝ) * (c + ρ) ^ (J - 1) * ρ)) (Real.log (1 + c ^ J + ((c + ρ) ^ J - c ^ J)) - Real.log (1 + c ^ J + ((45 - J : ℕ) : ℝ) * (c + ρ) ^ (J - 1) * ρ))) ≤ ((c + ρ) ^ (2 * 45) / (2 * (1 - (c + ρ) ^ 2)) - (c + ρ) ^ (3 * 45) / (3 * (1 - (c + ρ) ^ 3))) := by
  have hRpos : 0 < c + ρ := by linarith
  have hRlt : c + ρ < 1 := hR1
  set A : ℕ → ℝ := fun J => Real.log (1 - c ^ J + ((c + ρ) ^ J - c ^ J))
      - Real.log (1 - c ^ J + ((45 - J : ℕ) : ℝ) * (c + ρ) ^ (J - 1) * ρ) with hA
  set B : ℕ → ℝ := fun J => Real.log (1 + c ^ J + ((c + ρ) ^ J - c ^ J))
      - Real.log (1 + c ^ J + ((45 - J : ℕ) : ℝ) * (c + ρ) ^ (J - 1) * ρ) with hB
  have h22 : ∀ J ∈ Finset.Icc 1 22, max (A J) (B J) ≤ serCoreG (c + ρ) ρ J := by
    intro J hJ
    rw [Finset.mem_Icc] at hJ
    simp only [hA, hB, serCoreG]
    exact serCoreTermLe22 hc hρ hR1 hJ.1 hJ.2
  have h23 : ∀ J ∈ Finset.Icc 23 44, max (A J) (B J) ≤ serCoreH (c + ρ) ρ J := by
    intro J hJ
    rw [Finset.mem_Icc] at hJ
    simp only [hA, hB, serCoreH]
    exact serCoreTermLe23 hc hρ hR1 hJ.1 hJ.2
  have hpair : ∀ K ∈ Finset.Icc 1 22, serCoreG (c + ρ) ρ K + serCoreH (c + ρ) ρ (45 - K) ≤ 0 := by
    intro K hK
    rw [Finset.mem_Icc] at hK
    exact serCoreNumPair_nonpos hRpos hR8 hρ hρs hK.1 hK.2
  have hzero : (∑ J ∈ Finset.Icc 1 22, serCoreG (c + ρ) ρ J)
      + ∑ J ∈ Finset.Icc 23 44, serCoreH (c + ρ) ρ J ≤ 0 := by
    rw [sum_Icc_reflect_23_44 (serCoreH (c + ρ) ρ), ← Finset.sum_add_distrib]
    exact Finset.sum_nonpos hpair
  calc (∑ J ∈ Finset.Icc 1 44, max (A J) (B J))
      = (∑ J ∈ Finset.Icc 1 22, max (A J) (B J)) + ∑ J ∈ Finset.Icc 23 44, max (A J) (B J) :=
        sum_Icc_one_44_split _
    _ ≤ (∑ J ∈ Finset.Icc 1 22, serCoreG (c + ρ) ρ J) + ∑ J ∈ Finset.Icc 23 44, serCoreH (c + ρ) ρ J :=
        add_le_add (Finset.sum_le_sum h22) (Finset.sum_le_sum h23)
    _ ≤ 0 := hzero
    _ ≤ (c + ρ) ^ (2 * 45) / (2 * (1 - (c + ρ) ^ 2)) - (c + ρ) ^ (3 * 45) / (3 * (1 - (c + ρ) ^ 3)) :=
        serCoreRHS_nonneg hRpos hRlt

end Work.CNum
