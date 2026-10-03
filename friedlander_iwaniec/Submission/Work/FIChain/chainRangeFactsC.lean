/-
# `Submission.Work.FIChain.chainRangeFactsC` — the range facts of the `B`-dependent family

The eight range facts about the family `(sc, Yc, Zc, Deltac, Dc, Mc, d2c)` of
`Submission/Work/FIChain/Defs.lean` that the §3–§6 chain consumes:

* `1 ≤ sc x B` and the exact product identity `sc x B · Yc x B = √x/(log x)^{B+2}`;
* `0 < Yc x B` and `Zc x B ≤ √x` (from `sc·(log x)^{B+2} ≥ 1`, no asymptotics needed);
* `Deltac x ≤ x` and `3 ≤ Deltac x`;
* the §6 level comparisons `Deltac x · (Mc x B · d2c x B) ≤ Dc x` and
  `x/(sc x B · Yc x B) ≤ Mc x B`.

The only asymptotic input is `(log x)^{3B+6} ≤ (1/24)·x^{71/400}`, since
`24·(log x)^{3B+6} ≤ x^{71/400}` is exactly what is needed to compare
`12·x^{51/100}·(log x)^{3B+6}` with `x^{11/16}/2` (`51/100 + 71/400 = 11/16`).
-/
import Mathlib
import Submission.Work.FIChain.Defs
import Submission.Work.FIChain.scale_factsC
import Submission.Work.FIChain.window_marginsC

set_option autoImplicit false

namespace Work.FIChain

open Filter

noncomputable section

theorem chainRangeFactsC (B : ℝ) (hB : 0 < B) :
    ∀ᶠ x : ℕ in Filter.atTop,
      1 ≤ Work.FIChain.sc x B ∧
      Work.FIChain.sc x B * Work.FIChain.Yc x B
        = Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ (B + 2) ∧
      0 < Work.FIChain.Yc x B ∧
      (Work.FIChain.Zc x B : ℝ) ≤ Real.sqrt (x : ℝ) ∧
      Work.FIChain.Deltac x ≤ x ∧
      3 ≤ Work.FIChain.Deltac x ∧
      Work.FIChain.Deltac x * (Work.FIChain.Mc x B * Work.FIChain.d2c x B) ≤ Work.FIChain.Dc x ∧
      (x : ℝ) / (Work.FIChain.sc x B * Work.FIChain.Yc x B) ≤ (Work.FIChain.Mc x B : ℝ) := by
  have _ : (0 : ℝ) < B := hB
  filter_upwards [eventually_ge_atTop 2, Work.FITop.FI_ev_log_ge_nat 1,
    Work.FITop.FI_ev_Delta1_le_two_Lam1, Work.FITop.FI_ev_Lam1_ge_one,
    Work.FITop.FI_ev_Dcut_lower,
    Work.FITop.FI_ev_rpow_ge_nat ((1 : ℝ) / 100) (by norm_num) 3,
    Work.FITop.FI_ev_rpow_ge_nat ((99 : ℝ) / 100) (by norm_num) 2,
    Work.FITop.FI_ev_log_rpow_le_nat (b := 3 * B + 6) (ε := (71 : ℝ) / 400)
      (C := 1 / 24) (by norm_num) (by norm_num)]
    with x hx2 hL1 hD2 hLam hDcut hx3 hx99 hlogb
  have hx1 : (1 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 1 < x)
  have hxpos : (0 : ℝ) < x := by linarith
  have hx0 : (0 : ℝ) ≤ x := hxpos.le
  have hLpos : 0 < Real.log (x : ℝ) := lt_of_lt_of_le zero_lt_one hL1
  have hLp_pos : 0 < (Real.log (x : ℝ)) ^ (B + 2) := Real.rpow_pos_of_pos hLpos _
  have hLp_one : 1 ≤ (Real.log (x : ℝ)) ^ (B + 2) := Real.one_le_rpow hL1 (by linarith)
  have hLq_one : 1 ≤ (Real.log (x : ℝ)) ^ (2 * B + 4) := Real.one_le_rpow hL1 (by linarith)
  have hsc_one : 1 ≤ sc x B := by rw [sc]; exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hsc_pos : 0 < sc x B := lt_of_lt_of_le zero_lt_one hsc_one
  -- (2) the exact product identity
  have hprod : sc x B * Yc x B = Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ (B + 2) := by
    rw [Yc]
    have hsc_ne : sc x B ≠ 0 := ne_of_gt hsc_pos
    have hLp_ne : (Real.log (x : ℝ)) ^ (B + 2) ≠ 0 := ne_of_gt hLp_pos
    field_simp
  -- (3) positivity
  have hYpos : 0 < Yc x B := by
    rw [Yc]
    exact div_pos (Real.sqrt_pos.mpr hxpos) (mul_pos hsc_pos hLp_pos)
  -- (4) `Zc ≤ √x`
  have hYle : Yc x B ≤ Real.sqrt (x : ℝ) := by
    rw [Yc]
    have hscLp : (1 : ℝ) ≤ sc x B * (Real.log (x : ℝ)) ^ (B + 2) := by
      have h := mul_le_mul hsc_one hLp_one zero_le_one (le_trans zero_le_one hsc_one)
      simpa using h
    calc Real.sqrt (x : ℝ) / (sc x B * (Real.log (x : ℝ)) ^ (B + 2))
        ≤ Real.sqrt (x : ℝ) / 1 :=
          div_le_div_of_nonneg_left (Real.sqrt_nonneg _) one_pos hscLp
      _ = Real.sqrt (x : ℝ) := div_one _
  have hZc : (Zc x B : ℝ) ≤ Real.sqrt (x : ℝ) := by
    show (⌊Yc x B⌋₊ : ℝ) ≤ Real.sqrt (x : ℝ)
    exact le_trans (Nat.floor_le hYpos.le) hYle
  -- (5) `Deltac x ≤ x`
  have hD2' : (Deltac x : ℝ) ≤ 2 * (x : ℝ) ^ ((1 : ℝ) / 100) := by
    simpa only [Deltac, Work.FITop.Lam1] using hD2
  have hDx : Deltac x ≤ x := by
    have h2 : 2 * (x : ℝ) ^ ((1 : ℝ) / 100) ≤ (x : ℝ) := by
      have h := mul_le_mul_of_nonneg_right hx99 (Real.rpow_nonneg hx0 ((1 : ℝ) / 100))
      rw [← Real.rpow_add hxpos, show (99 : ℝ) / 100 + 1 / 100 = 1 by norm_num,
        Real.rpow_one] at h
      exact h
    have hreal : ((Deltac x : ℕ) : ℝ) ≤ (x : ℝ) := le_trans hD2' h2
    exact_mod_cast hreal
  -- (6) `3 ≤ Deltac x`
  have hD3real : (3 : ℝ) ≤ (Deltac x : ℝ) :=
    le_trans hx3 (Work.FITop.FI_Lam1_le_Delta1 x)
  have hD3 : 3 ≤ Deltac x := by exact_mod_cast hD3real
  -- (7) `Deltac x · (Mc x B · d2c x B) ≤ Dc x`
  have hMc_bound : (Mc x B : ℝ) ≤ 2 * (Real.sqrt (x : ℝ) * (Real.log (x : ℝ)) ^ (B + 2)) := by
    have hsx1 : (1 : ℝ) ≤ Real.sqrt (x : ℝ) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by exact_mod_cast (by omega : 1 ≤ x))
    have ha1 : (1 : ℝ) ≤ Real.sqrt (x : ℝ) * (Real.log (x : ℝ)) ^ (B + 2) := by
      have h := mul_le_mul hsx1 hLp_one zero_le_one (le_trans zero_le_one hsx1)
      simpa using h
    have hlt : (Mc x B : ℝ) < Real.sqrt (x : ℝ) * (Real.log (x : ℝ)) ^ (B + 2) + 1 :=
      Nat.ceil_lt_add_one (le_trans zero_le_one ha1)
    linarith
  have hdc_bound : (d2c x B : ℝ) ≤ 3 * (Real.log (x : ℝ)) ^ (2 * B + 4) := by
    have hlt : (d2c x B : ℝ) < 2 * (Real.log (x : ℝ)) ^ (2 * B + 4) + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    linarith
  have h7real : (Deltac x : ℝ) * ((Mc x B : ℝ) * (d2c x B : ℝ))
      ≤ (x : ℝ) ^ ((11 : ℝ) / 16) / 2 := by
    have h1 : (Deltac x : ℝ) * ((Mc x B : ℝ) * (d2c x B : ℝ))
        ≤ (2 * (x : ℝ) ^ ((1 : ℝ) / 100))
          * ((2 * (Real.sqrt (x : ℝ) * (Real.log (x : ℝ)) ^ (B + 2)))
            * (3 * (Real.log (x : ℝ)) ^ (2 * B + 4))) :=
      mul_le_mul hD2' (mul_le_mul hMc_bound hdc_bound (by positivity) (by positivity))
        (by positivity) (by positivity)
    have h2 : (2 * (x : ℝ) ^ ((1 : ℝ) / 100))
          * ((2 * (Real.sqrt (x : ℝ) * (Real.log (x : ℝ)) ^ (B + 2)))
            * (3 * (Real.log (x : ℝ)) ^ (2 * B + 4)))
        = 12 * ((x : ℝ) ^ ((1 : ℝ) / 100) * Real.sqrt (x : ℝ))
          * ((Real.log (x : ℝ)) ^ (B + 2) * (Real.log (x : ℝ)) ^ (2 * B + 4)) := by ring
    have h3 : (x : ℝ) ^ ((1 : ℝ) / 100) * Real.sqrt (x : ℝ) = (x : ℝ) ^ ((51 : ℝ) / 100) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hxpos]
      norm_num
    have h4 : (Real.log (x : ℝ)) ^ (B + 2) * (Real.log (x : ℝ)) ^ (2 * B + 4)
        = (Real.log (x : ℝ)) ^ (3 * B + 6) := by
      rw [← Real.rpow_add hLpos]
      congr 1
      ring
    have h5 : 12 * (x : ℝ) ^ ((51 : ℝ) / 100) * (Real.log (x : ℝ)) ^ (3 * B + 6)
        ≤ (x : ℝ) ^ ((11 : ℝ) / 16) / 2 := by
      have hx51 : (0 : ℝ) ≤ (x : ℝ) ^ ((51 : ℝ) / 100) := Real.rpow_nonneg hx0 _
      have h6 : 12 * (x : ℝ) ^ ((51 : ℝ) / 100) * (Real.log (x : ℝ)) ^ (3 * B + 6)
          ≤ 12 * (x : ℝ) ^ ((51 : ℝ) / 100)
            * ((1 / 24) * (x : ℝ) ^ ((71 : ℝ) / 400)) :=
        mul_le_mul_of_nonneg_left hlogb (mul_nonneg (by norm_num) hx51)
      have h7 : 12 * (x : ℝ) ^ ((51 : ℝ) / 100) * ((1 / 24) * (x : ℝ) ^ ((71 : ℝ) / 400))
          = (x : ℝ) ^ ((11 : ℝ) / 16) / 2 := by
        rw [show 12 * (x : ℝ) ^ ((51 : ℝ) / 100) * ((1 / 24) * (x : ℝ) ^ ((71 : ℝ) / 400))
            = (1 / 2) * ((x : ℝ) ^ ((51 : ℝ) / 100) * (x : ℝ) ^ ((71 : ℝ) / 400)) by ring]
        rw [← Real.rpow_add hxpos, show (51 : ℝ) / 100 + 71 / 400 = 11 / 16 by norm_num]
        ring
      linarith [h6, h7]
    calc (Deltac x : ℝ) * ((Mc x B : ℝ) * (d2c x B : ℝ))
        ≤ _ := h1
      _ = 12 * ((x : ℝ) ^ ((1 : ℝ) / 100) * Real.sqrt (x : ℝ))
            * ((Real.log (x : ℝ)) ^ (B + 2) * (Real.log (x : ℝ)) ^ (2 * B + 4)) := h2
      _ = 12 * (x : ℝ) ^ ((51 : ℝ) / 100) * (Real.log (x : ℝ)) ^ (3 * B + 6) := by rw [h3, h4]
      _ ≤ (x : ℝ) ^ ((11 : ℝ) / 16) / 2 := h5
  have h7 : Deltac x * (Mc x B * d2c x B) ≤ Dc x := by
    have hcast : ((Deltac x * (Mc x B * d2c x B) : ℕ) : ℝ)
        = (Deltac x : ℝ) * ((Mc x B : ℝ) * (d2c x B : ℝ)) := by push_cast; ring
    have hgoal : ((Deltac x * (Mc x B * d2c x B) : ℕ) : ℝ) ≤ (Dc x : ℝ) := by
      rw [hcast]
      exact le_trans h7real hDcut
    exact_mod_cast hgoal
  -- (8) `x/(sc·Yc) ≤ Mc x B`
  have h8 : (x : ℝ) / (sc x B * Yc x B) ≤ (Mc x B : ℝ) := by
    have hMc_ge : Real.sqrt (x : ℝ) * (Real.log (x : ℝ)) ^ (B + 2) ≤ (Mc x B : ℝ) :=
      Nat.le_ceil _
    have hsx : (x : ℝ) / Real.sqrt (x : ℝ) = Real.sqrt (x : ℝ) := by
      rw [div_eq_iff (ne_of_gt (Real.sqrt_pos.mpr hxpos))]
      rw [← pow_two, Real.sq_sqrt hx0]
    have heq : (x : ℝ) / (Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ (B + 2))
        = Real.sqrt (x : ℝ) * (Real.log (x : ℝ)) ^ (B + 2) := by
      rw [div_div_eq_mul_div]
      rw [show (x : ℝ) * (Real.log (x : ℝ)) ^ (B + 2) / Real.sqrt (x : ℝ)
          = ((x : ℝ) / Real.sqrt (x : ℝ)) * (Real.log (x : ℝ)) ^ (B + 2) by ring]
      rw [hsx]
    rw [hprod, heq]
    exact hMc_ge
  exact ⟨hsc_one, hprod, hYpos, hZc, hDx, hD3, h7, h8⟩

end

end Work.FIChain
