/-
# `Submission.Work.FIChain.window_margin_sharp`

The **sharp bottom margin** of the `B`-dependent window of `Submission/Work/FIChain/Defs.lean`:
for every `B > 0`, `κ > 0` and `0 < η < 3/32` one has eventually

  `(x^{1/4 + η/2} + 2) * Dpi x κ < Yc x B / Deltac x`.

This refines `window_marginsC` (which proves `x^{1/4+η} + 2 < Yc/Δ` for `η < 1/32`) in two
directions needed by the Rankin layer: the exponent `1/4 + η/2` is compared against the full
strength of `Yc`, and the extra factor `Dpi x κ = ⌈exp(κ (loglog x)^3)⌉` is absorbed.

The content is elementary: with `a = 1/4 + η/2` and `d = (21/400 - η/2)/2` one has
`a + 2 d = 121/400`, and

* `Dpi x κ ≤ 2 x^d` eventually (`exp` of a subpolynomial is dominated by every `x^d`);
* `Yc x B > x^{5/16}` and `Deltac x ≤ 2 x^{1/100}`, hence `Yc x B / Deltac x ≥ (1/2) x^{121/400}`;
* `12 ≤ x^d` eventually, which upgrades `6 x^{a+d} ≤ (1/2) x^{a+2d}`.

Since `121/400 = 5/16 - 1/100` and `a + 2d = 121/400 > 1/4 + 3/64 ≥ 1/4 + η/2` (for `η < 3/32`),
the subpolynomial factor `Dpi` fits into the gap.

Everything below is proved; no `sorry`, no `axiom`.
-/
import Mathlib
import Submission.Work.FIChain.BpWinDefs
import Submission.Work.FITop.RCPrelude

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIChain

open Filter

noncomputable section

/-! ## 1. The `Dpi` bound: `Dpi x κ ≤ 2 x^d` for every `d > 0` -/

private lemma Dpi_le_two_rpow (κ δ : ℝ) (hκ : 0 < κ) (hδ : 0 < δ) :
    ∀ᶠ x : ℕ in Filter.atTop, (Dpi x κ : ℝ) ≤ 2 * (x : ℝ) ^ δ := by
  have h := Work.FITop.FI_ev_loglog_rpow_le_nat (b := (3 : ℝ)) (ε := (1 : ℝ))
    (C := δ / κ) (by positivity) (by norm_num)
  filter_upwards [h, Filter.eventually_ge_atTop 1] with x hx hx1
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hx1' : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx1
  have hloglog : (Real.log (Real.log (x : ℝ))) ^ (3 : ℝ) ≤ (δ / κ) * Real.log (x : ℝ) := by
    have h' := hx
    rwa [Real.rpow_one] at h'
  have hkey : κ * (Real.log (Real.log (x : ℝ))) ^ 3 ≤ Real.log (x : ℝ) * δ := by
    have h2 : (Real.log (Real.log (x : ℝ))) ^ (3 : ℝ) = (Real.log (Real.log (x : ℝ))) ^ 3 := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have h3 : (Real.log (Real.log (x : ℝ))) ^ 3 ≤ (δ / κ) * Real.log (x : ℝ) := by
      rw [← h2]; exact hloglog
    have h4 := mul_le_mul_of_nonneg_left h3 hκ.le
    have h5 : κ * ((δ / κ) * Real.log (x : ℝ)) = Real.log (x : ℝ) * δ := by field_simp
    rw [h5] at h4
    exact h4
  have hexp : Real.exp (κ * (Real.log (Real.log (x : ℝ))) ^ 3) ≤ (x : ℝ) ^ δ := by
    rw [Real.rpow_def_of_pos hxpos]
    exact Real.exp_le_exp.mpr hkey
  have hDpi_lt : (Dpi x κ : ℝ) < Real.exp (κ * (Real.log (Real.log (x : ℝ))) ^ 3) + 1 := by
    rw [Dpi]; exact Nat.ceil_lt_add_one (Real.exp_nonneg _)
  have h2x : (1 : ℝ) ≤ (x : ℝ) ^ δ := Real.one_le_rpow hx1' hδ.le
  linarith

/-! ## 2. The dyadic sandwich for `sc` and the lower bound `x^{5/16} < Yc x B`

This is the standard chain: `sc x B = 2^{Jc x B}` with `Jc` the ceiling of
`log(x^{1/4-2η_c}/(2(log x)^{B+2}))/log 2`, so `sc·(log x)^{B+2}` lies between `x^{3/16}/2` and
`x^{3/16}`; dividing `√x` by it gives `x^{5/16} < Yc x B`.  (`η_c = 1/32`, so
`1/4 - 2η_c = 3/16`.) -/

private lemma etac_val : (1 : ℝ) / 4 - 2 * etac = 3 / 16 := by norm_num [etac]

private lemma sc_mul_lt (x : ℕ) (B : ℝ) (hx1 : 1 < (x : ℝ))
    (hu : 1 ≤ (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) / (2 * (Real.log (x : ℝ)) ^ (B + 2))) :
    sc x B * (Real.log (x : ℝ)) ^ (B + 2) < (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) := by
  have hxpos : (0 : ℝ) < x := by linarith
  have hLpos : 0 < Real.log (x : ℝ) := Real.log_pos hx1
  have hLp_pos : 0 < (Real.log (x : ℝ)) ^ (B + 2) := Real.rpow_pos_of_pos hLpos _
  have hupos : 0 < (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) / (2 * (Real.log (x : ℝ)) ^ (B + 2)) :=
    lt_of_lt_of_le zero_lt_one hu
  have ht0 : 0 ≤ Real.log ((x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) / (2 * (Real.log (x : ℝ)) ^ (B + 2)))
      / Real.log 2 :=
    div_nonneg (Real.log_nonneg hu) (Real.log_pos (by norm_num)).le
  have hJlt : (Jc x B : ℝ) <
      Real.log ((x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) / (2 * (Real.log (x : ℝ)) ^ (B + 2)))
        / Real.log 2 + 1 := by
    rw [Jc]; exact Nat.ceil_lt_add_one ht0
  have hpow : (2 : ℝ) ^ (Real.log ((x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac)
      / (2 * (Real.log (x : ℝ)) ^ (B + 2))) / Real.log 2)
      = (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) / (2 * (Real.log (x : ℝ)) ^ (B + 2)) :=
    Work.FITop.FI_two_rpow_log_div_log _ hupos
  have hlt : (2 : ℝ) ^ (Jc x B) < 2 * ((x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac)
      / (2 * (Real.log (x : ℝ)) ^ (B + 2))) := by
    calc (2 : ℝ) ^ (Jc x B) = (2 : ℝ) ^ ((Jc x B : ℝ)) := (Real.rpow_natCast 2 (Jc x B)).symm
      _ < (2 : ℝ) ^ (Real.log ((x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac)
            / (2 * (Real.log (x : ℝ)) ^ (B + 2))) / Real.log 2 + 1) :=
          Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hJlt
      _ = 2 * ((x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) / (2 * (Real.log (x : ℝ)) ^ (B + 2))) := by
          rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one, hpow]; ring
  calc sc x B * (Real.log (x : ℝ)) ^ (B + 2)
      = (2 : ℝ) ^ (Jc x B) * (Real.log (x : ℝ)) ^ (B + 2) := rfl
    _ < (2 * ((x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) / (2 * (Real.log (x : ℝ)) ^ (B + 2))))
          * (Real.log (x : ℝ)) ^ (B + 2) := mul_lt_mul_of_pos_right hlt hLp_pos
    _ = (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) := by field_simp

private lemma Yc_lower (x : ℕ) (B : ℝ) (hx1 : 1 < (x : ℝ))
    (hu : 1 ≤ (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) / (2 * (Real.log (x : ℝ)) ^ (B + 2))) :
    (x : ℝ) ^ ((5 : ℝ) / 16) < Yc x B := by
  have hxpos : (0 : ℝ) < x := by linarith
  have hLpos : 0 < Real.log (x : ℝ) := Real.log_pos hx1
  have hLp_pos : 0 < (Real.log (x : ℝ)) ^ (B + 2) := Real.rpow_pos_of_pos hLpos _
  have hsc_pos : 0 < sc x B := by rw [sc]; positivity
  have hden_pos : 0 < sc x B * (Real.log (x : ℝ)) ^ (B + 2) := mul_pos hsc_pos hLp_pos
  have hsc_lt := sc_mul_lt x B hx1 hu
  have hmain : Real.sqrt (x : ℝ) / (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac)
      < Real.sqrt (x : ℝ) / (sc x B * (Real.log (x : ℝ)) ^ (B + 2)) :=
    div_lt_div_of_pos_left (Real.sqrt_pos.mpr hxpos) hden_pos hsc_lt
  have heq : Real.sqrt (x : ℝ) / (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) = (x : ℝ) ^ ((5 : ℝ) / 16) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hxpos]
    congr 1
    norm_num [etac]
  calc (x : ℝ) ^ ((5 : ℝ) / 16)
      = Real.sqrt (x : ℝ) / (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) := heq.symm
    _ < Real.sqrt (x : ℝ) / (sc x B * (Real.log (x : ℝ)) ^ (B + 2)) := hmain
    _ = Yc x B := rfl

private lemma ev_u_ge_one (B : ℝ) :
    ∀ᶠ x : ℕ in Filter.atTop,
      1 ≤ (x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac) / (2 * (Real.log (x : ℝ)) ^ (B + 2)) := by
  filter_upwards [Work.FITop.FI_ev_log_rpow_le_nat (b := B + 2) (ε := (3 : ℝ) / 16)
      (C := 1 / 2) (by norm_num) (by norm_num), Filter.eventually_ge_atTop 2] with x hle hx2
  have hx1 : (1 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 1 < x)
  have hLpos : 0 < Real.log (x : ℝ) := Real.log_pos hx1
  rw [etac_val, le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (Real.log (x : ℝ)) ^ (B + 2))]
  linarith

private lemma ev_Yc_gt (B : ℝ) :
    ∀ᶠ x : ℕ in Filter.atTop, (x : ℝ) ^ ((5 : ℝ) / 16) < Yc x B := by
  filter_upwards [ev_u_ge_one B, Filter.eventually_ge_atTop 2] with x hu hx2
  have hx1 : (1 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 1 < x)
  exact Yc_lower x B hx1 hu

/-! ## 3. The sharp margin, parametric in `(a, d)` with `a + 2d ≤ 121/400` -/

private lemma window_margin_aux (B κ a d : ℝ) (hκ : 0 < κ)
    (ha : 0 ≤ a) (hd : 0 < d) (hsum : a + 2 * d ≤ 121 / 400) :
    ∀ᶠ x : ℕ in Filter.atTop,
      ((x : ℝ) ^ a + 2) * (Dpi x κ : ℝ) < Yc x B / (Deltac x : ℝ) := by
  have hDpi := Dpi_le_two_rpow κ d hκ hd
  have hYc := ev_Yc_gt B
  have hxδ := Work.FITop.FI_ev_rpow_ge_nat d hd 12
  filter_upwards [hDpi, hYc, Work.FITop.FI_ev_Delta1_le_two_Lam1,
      Work.FITop.FI_ev_Lam1_ge_one, hxδ, Filter.eventually_ge_atTop 2]
    with x hDpi_x hYc_x hDel_x hLam1ge_x hxδ_x hx2
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 1 ≤ x)
  have hxa : 1 ≤ (x : ℝ) ^ a := Real.one_le_rpow hx1 ha
  have hDeltapos : 0 < (Deltac x : ℝ) := by
    have h := Work.FITop.FI_Lam1_le_Delta1 x
    simp only [Deltac]
    linarith
  have hDel_le : (Deltac x : ℝ) ≤ 2 * (x : ℝ) ^ ((1 : ℝ) / 100) := by
    have h := hDel_x
    rw [Work.FITop.Lam1] at h
    simpa only [Deltac] using h
  have hstep1 : ((x : ℝ) ^ a + 2) * (Dpi x κ : ℝ) ≤ 6 * (x : ℝ) ^ (a + d) := by
    have hAC : (x : ℝ) ^ a + 2 ≤ 3 * (x : ℝ) ^ a := by linarith
    have hmul := mul_le_mul hAC hDpi_x (Nat.cast_nonneg (Dpi x κ))
      (by positivity : (0 : ℝ) ≤ 3 * (x : ℝ) ^ a)
    calc ((x : ℝ) ^ a + 2) * (Dpi x κ : ℝ)
        ≤ (3 * (x : ℝ) ^ a) * (2 * (x : ℝ) ^ d) := hmul
      _ = 6 * ((x : ℝ) ^ a * (x : ℝ) ^ d) := by ring
      _ = 6 * (x : ℝ) ^ (a + d) := by rw [Real.rpow_add hxpos]
  have hA : (x : ℝ) ^ (a + 2 * d) = (x : ℝ) ^ (a + d) * (x : ℝ) ^ d := by
    have hh : a + 2 * d = (a + d) + d := by ring
    rw [hh]
    exact Real.rpow_add hxpos (a + d) d
  have hstep2 : 6 * (x : ℝ) ^ (a + d) ≤ (1 / 2) * (x : ℝ) ^ (a + 2 * d) := by
    rw [hA]
    have hh : 6 * (x : ℝ) ^ (a + d) ≤ (1 / 2) * (x : ℝ) ^ (a + d) * (x : ℝ) ^ d := by
      have h2 := mul_le_mul_of_nonneg_left hxδ_x
        (by positivity : (0 : ℝ) ≤ (1 / 2) * (x : ℝ) ^ (a + d))
      have h3 : (1 / 2) * (x : ℝ) ^ (a + d) * 12 = 6 * (x : ℝ) ^ (a + d) := by ring
      linarith [h2, h3]
    calc 6 * (x : ℝ) ^ (a + d) ≤ (1 / 2) * (x : ℝ) ^ (a + d) * (x : ℝ) ^ d := hh
      _ = (1 / 2) * ((x : ℝ) ^ (a + d) * (x : ℝ) ^ d) := by ring
  have hstep3 : (1 / 2) * (x : ℝ) ^ (a + 2 * d) ≤ (1 / 2) * (x : ℝ) ^ ((121 : ℝ) / 400) :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx1 hsum) (by norm_num)
  have hRHS : (1 / 2) * (x : ℝ) ^ ((121 : ℝ) / 400) < Yc x B / (Deltac x : ℝ) := by
    have hmain : (x : ℝ) ^ ((5 : ℝ) / 16) / (2 * (x : ℝ) ^ ((1 : ℝ) / 100))
        = (1 / 2) * (x : ℝ) ^ ((121 : ℝ) / 400) := by
      rw [show (x : ℝ) ^ ((5 : ℝ) / 16) / (2 * (x : ℝ) ^ ((1 : ℝ) / 100))
            = (1 / 2) * ((x : ℝ) ^ ((5 : ℝ) / 16) / (x : ℝ) ^ ((1 : ℝ) / 100)) by ring]
      rw [← Real.rpow_sub hxpos]
      congr 1
      norm_num
    rw [← hmain]
    exact lt_of_le_of_lt
      (div_le_div_of_nonneg_left (Real.rpow_nonneg hxpos.le _) hDeltapos hDel_le)
      (div_lt_div_of_pos_right hYc_x hDeltapos)
  exact lt_of_le_of_lt (le_trans hstep1 (le_trans hstep2 hstep3)) hRHS

/-! ## 4. The requested lemma -/

theorem window_margin_sharp (B κ : ℝ) (hB : 0 < B) (hκ : 0 < κ) (η : ℝ) (hη : 0 < η) (hη32 : η < 3 / 32) :
    ∀ᶠ x : ℕ in Filter.atTop,
      ((x : ℝ) ^ ((1 : ℝ) / 4 + η / 2) + 2) * (Work.FIChain.Dpi x κ : ℝ)
        < Work.FIChain.Yc x B / (Work.FIChain.Deltac x : ℝ) := by
  have _hB : (0 : ℝ) < B := hB
  have hd : 0 < ((21 : ℝ) / 400 - η / 2) / 2 := by
    have h1 : η / 2 < 3 / 64 := by linarith
    linarith
  have ha : (0 : ℝ) ≤ (1 : ℝ) / 4 + η / 2 := by linarith
  have hsum : (1 : ℝ) / 4 + η / 2 + 2 * (((21 : ℝ) / 400 - η / 2) / 2) = 121 / 400 := by ring
  exact window_margin_aux B κ ((1 : ℝ) / 4 + η / 2) (((21 : ℝ) / 400 - η / 2) / 2) hκ ha hd
    (le_of_eq hsum)

end

end Work.FIChain
