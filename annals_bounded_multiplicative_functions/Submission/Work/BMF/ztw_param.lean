import Mathlib
import Submission.Work.BMF.ztw_defs
import Submission.Work.BMF.ztw_asym
import Submission.Work.BMF.N4chain.ztNumeric_eventually_21

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open Filter
open scoped Real Topology

set_option maxHeartbeats 4000000

noncomputable section

/-! ## Bounds for the `6/7`-shaped Perron parameter package -/

/-- Height/logarithm/D bounds for the `6/7`-shaped twisted Perron parameters:
`log (2 * twT L u + 3)` and `log (|u| + twT L u + 3)` are `≤ 2 L^{21/20}`, the
denominator `twD L u` lies between `L^{1/12}` and `2 L^{11/12}`, uniformly for
`|u| ≤ exp (L^{21/20})` and eventually in `L`. -/
lemma ztw_param_twD_bounds :
    ∀ᶠ L : ℝ in Filter.atTop, ∀ u : ℝ, |u| ≤ Real.exp (L ^ (21 / 20 : ℝ)) →
      Real.log (2 * twT L u + 3) ≤ 2 * L ^ (21 / 20 : ℝ) ∧
      Real.log (|u| + twT L u + 3) ≤ 2 * L ^ (21 / 20 : ℝ) ∧
      twD L u ≤ 2 * L ^ (11 / 12 : ℝ) ∧
      L ^ (1 / 12 : ℝ) ≤ twD L u := by
  have hnum := N4chain.ztNumeric_eventually_21.1
  have hlog3 := N4chain.ztNumeric_eventually_21.2.1
  have hlog6 := N4chain.ztNumeric_eventually_21.2.2.1
  have hlogL : ∀ᶠ L : ℝ in Filter.atTop, 2 * Real.log L ≤ L ^ (1 / 60 : ℝ) :=
    ztw_log_le_rpow 2 (1 / 60) (by norm_num)
  have hL1 : ∀ᶠ L : ℝ in Filter.atTop, (1 : ℝ) ≤ L := eventually_ge_atTop 1
  filter_upwards [hnum, hlog3, hlog6, hlogL, hL1] with L hnum hlog3 hlog6 hlogL hL1
  intro u hu
  have hLpos : 0 < L := by linarith
  have hLnn : 0 ≤ L := hLpos.le
  have h2T : 2 * twT L u + 3 ≤ 3 * Real.exp (L ^ (21 / 20 : ℝ)) := by
    rw [twT]; linarith [abs_nonneg u, hu, hnum]
  have hT3 : |u| + twT L u + 3 ≤ 3 * Real.exp (L ^ (21 / 20 : ℝ)) := by
    have h := abs_lt_twT L u; linarith
  have hlogT : Real.log (2 * twT L u + 3) ≤ 2 * L ^ (21 / 20 : ℝ) := by
    have hpos : 0 < 2 * twT L u + 3 := by have := twT_pos L u; linarith
    calc Real.log (2 * twT L u + 3) ≤ Real.log (3 * Real.exp (L ^ (21 / 20 : ℝ))) :=
          Real.log_le_log hpos h2T
      _ = Real.log 3 + L ^ (21 / 20 : ℝ) := by
          rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp]
      _ ≤ 2 * L ^ (21 / 20 : ℝ) := by linarith
  have hlogu : Real.log (|u| + twT L u + 3) ≤ 2 * L ^ (21 / 20 : ℝ) := by
    have hpos : 0 < |u| + twT L u + 3 := by
      have := twT_pos L u; have := abs_nonneg u; linarith
    calc Real.log (|u| + twT L u + 3) ≤ Real.log (3 * Real.exp (L ^ (21 / 20 : ℝ))) :=
          Real.log_le_log hpos hT3
      _ = Real.log 3 + L ^ (21 / 20 : ℝ) := by
          rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp]
      _ ≤ 2 * L ^ (21 / 20 : ℝ) := by linarith
  have hlog1 : (1 : ℝ) ≤ Real.log (2 * twT L u + 3) := by
    have h17 : (3 : ℝ) ≤ 2 * twT L u + 3 := by have := seven_le_twT L u; linarith
    exact le_trans one_le_log_three (Real.log_le_log (by norm_num) h17)
  have hA0 : 0 ≤ Real.log (2 * twT L u + 3) := le_trans zero_le_one hlog1
  have hpow_le : (Real.log (2 * twT L u + 3)) ^ (6 / 7 : ℝ) ≤ 2 * L ^ (9 / 10 : ℝ) := by
    have h1 := Real.rpow_le_rpow hA0 hlogT (by norm_num : (0 : ℝ) ≤ 6 / 7)
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Real.rpow_nonneg hLnn _)] at h1
    have hLp : (L ^ (21 / 20 : ℝ)) ^ (6 / 7 : ℝ) = L ^ (9 / 10 : ℝ) := by
      rw [← Real.rpow_mul hLnn]; norm_num
    rw [hLp] at h1
    have h2 : (2 : ℝ) ^ (6 / 7 : ℝ) ≤ 2 := by
      calc (2 : ℝ) ^ (6 / 7 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    calc (Real.log (2 * twT L u + 3)) ^ (6 / 7 : ℝ)
        ≤ (2 : ℝ) ^ (6 / 7 : ℝ) * L ^ (9 / 10 : ℝ) := h1
      _ ≤ 2 * L ^ (9 / 10 : ℝ) := mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hLnn _)
  have hB_le : Real.log 3 + Real.log (Real.log (2 * twT L u + 3)) ≤ 2 * Real.log L := by
    have hpos : 0 < Real.log (2 * twT L u + 3) := by linarith
    have h1 : Real.log (Real.log (2 * twT L u + 3)) ≤ Real.log (2 * L ^ (21 / 20 : ℝ)) :=
      Real.log_le_log hpos hlogT
    have h2 : Real.log (2 * L ^ (21 / 20 : ℝ)) = Real.log 2 + (21 / 20) * Real.log L := by
      rw [Real.log_mul (by norm_num) (ne_of_gt (Real.rpow_pos_of_pos hLpos _)), Real.log_rpow hLpos]
    have h3 : Real.log 6 = Real.log 3 + Real.log 2 := by
      rw [show (6 : ℝ) = 3 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    linarith [h1, h2 ▸ h1, h3 ▸ hlog6]
  have hB_nonneg : 0 ≤ Real.log 3 + Real.log (Real.log (2 * twT L u + 3)) := by
    have h4 : 0 ≤ Real.log (Real.log (2 * twT L u + 3)) := Real.log_nonneg hlog1
    have h5 : 0 < Real.log 3 := Real.log_pos (by norm_num)
    linarith
  have hDle : twD L u ≤ 2 * L ^ (11 / 12 : ℝ) := by
    have hLp : L ^ (9 / 10 : ℝ) * L ^ (1 / 60 : ℝ) = L ^ (11 / 12 : ℝ) := by
      rw [← Real.rpow_add hLpos]; norm_num
    rw [twD, ztD]
    calc (Real.log (2 * twT L u + 3)) ^ (6 / 7 : ℝ) *
            (Real.log 3 + Real.log (Real.log (2 * twT L u + 3)))
        ≤ (2 * L ^ (9 / 10 : ℝ)) * (2 * Real.log L) :=
          mul_le_mul hpow_le hB_le hB_nonneg (by positivity)
      _ = 2 * L ^ (9 / 10 : ℝ) * (2 * Real.log L) := by ring
      _ ≤ 2 * L ^ (9 / 10 : ℝ) * L ^ (1 / 60 : ℝ) :=
          mul_le_mul_of_nonneg_left hlogL (by positivity)
      _ = 2 * L ^ (11 / 12 : ℝ) := by rw [mul_assoc, hLp]
  have hDge : L ^ (1 / 12 : ℝ) ≤ twD L u := by
    have hexp_le : Real.exp (L ^ (1 / 10 : ℝ)) ≤ 2 * twT L u + 3 := by
      have h1' : (1 : ℝ) ≤ 2 * L ^ 2 := by nlinarith [hL1, sq_nonneg L]
      have h1 : Real.exp (L ^ (1 / 10 : ℝ)) ≤ 2 * L ^ 2 * Real.exp (L ^ (1 / 10 : ℝ)) := by
        calc Real.exp (L ^ (1 / 10 : ℝ)) = 1 * Real.exp (L ^ (1 / 10 : ℝ)) := by ring
          _ ≤ (2 * L ^ 2) * Real.exp (L ^ (1 / 10 : ℝ)) :=
              mul_le_mul_of_nonneg_right h1' (Real.exp_pos _).le
      have h2 : 2 * L ^ 2 * Real.exp (L ^ (1 / 10 : ℝ)) + 17 ≤ 2 * twT L u + 3 := by
        rw [twT]; linarith [abs_nonneg u]
      linarith
    have hA_ge : L ^ (1 / 10 : ℝ) ≤ Real.log (2 * twT L u + 3) := by
      have h := Real.log_le_log (Real.exp_pos _) hexp_le
      rwa [Real.log_exp] at h
    have hpow_ge : L ^ (1 / 12 : ℝ) ≤ (Real.log (2 * twT L u + 3)) ^ (6 / 7 : ℝ) := by
      have h := Real.rpow_le_rpow (Real.rpow_nonneg hLnn _) hA_ge (by norm_num : (0 : ℝ) ≤ 6 / 7)
      rw [← Real.rpow_mul hLnn] at h
      have h35 : (1 / 10 : ℝ) * (6 / 7) = 3 / 35 := by norm_num
      rw [h35] at h
      have hle : L ^ (1 / 12 : ℝ) ≤ L ^ (3 / 35 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
      linarith
    have hB_ge : (1 : ℝ) ≤ Real.log 3 + Real.log (Real.log (2 * twT L u + 3)) := by
      have h4 : 0 ≤ Real.log (Real.log (2 * twT L u + 3)) := Real.log_nonneg hlog1
      linarith [one_le_log_three]
    rw [twD, ztD]
    calc L ^ (1 / 12 : ℝ) = L ^ (1 / 12 : ℝ) * 1 := by ring
      _ ≤ (Real.log (2 * twT L u + 3)) ^ (6 / 7 : ℝ) *
            (Real.log 3 + Real.log (Real.log (2 * twT L u + 3))) :=
          mul_le_mul hpow_ge hB_ge (by norm_num) (Real.rpow_nonneg hA0 _)
  exact ⟨hlogT, hlogu, hDle, hDge⟩

/-! ## Exponential absorption inequalities -/

/-- The three pure-`L` inequalities absorbing all remaining polynomial factors against the
exponentials `exp (∓(κ/16) L^{1/12})` / `exp (-L^{1/10})`. -/
lemma ztw_param_exp_le (κ C₅ C Ctr : ℝ) (hκ : 0 < κ) (hC₅ : 0 < C₅) (hC : 0 < C)
    (hCtr : 0 < Ctr) :
    (∀ᶠ L : ℝ in Filter.atTop,
      Ctr * (Real.exp L * Real.exp (-(L ^ (1 / 10 : ℝ))) + L) ≤
        (1 / 8) * (Real.exp L * Real.exp (-((κ / 16) * L ^ (1 / 12 : ℝ))))) ∧
    (∀ᶠ L : ℝ in Filter.atTop,
      32 * (4 * C + C₅ + 8 / κ) * (κ / 4 + 1) * L ^ (127 / 60 : ℝ) *
          Real.exp (-(L ^ (1 / 10 : ℝ))) ≤
        (1 / 8) * Real.exp (-((κ / 16) * L ^ (1 / 12 : ℝ)))) ∧
    (∀ᶠ L : ℝ in Filter.atTop,
      64 * Real.sqrt 2 * (4 * C + C₅ + 8 / κ) * L ^ (21 / 4 : ℝ) ≤
        (1 / 8) * Real.exp ((κ / 16) * L ^ (1 / 12 : ℝ))) := by
  have hM0 : 0 < 4 * C + C₅ + 8 / κ := by positivity
  have hIa : ∀ᶠ L : ℝ in Filter.atTop,
      Ctr * L ^ (0 : ℝ) * Real.exp (-(1 * L ^ (1 / 10 : ℝ) - (κ / 16) * L ^ (1 / 12 : ℝ))) ≤
        1 / 16 :=
    ztw_rpow_mul_exp_sub_le Ctr 0 1 (κ / 16) (1 / 10) (1 / 12) (1 / 16) hCtr.le
      (by norm_num) (by positivity) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hIb : ∀ᶠ L : ℝ in Filter.atTop,
      16 * Ctr * L ^ (1 : ℝ) * Real.exp (-(1 * L ^ (1 : ℝ) - (κ / 16) * L ^ (1 / 12 : ℝ))) ≤
        1 :=
    ztw_rpow_mul_exp_sub_le (16 * Ctr) 1 1 (κ / 16) 1 (1 / 12) 1 (by positivity)
      (by norm_num) (by positivity) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hII : ∀ᶠ L : ℝ in Filter.atTop,
      32 * (4 * C + C₅ + 8 / κ) * (κ / 4 + 1) * L ^ (127 / 60 : ℝ) *
          Real.exp (-(1 * L ^ (1 / 10 : ℝ) - (κ / 16) * L ^ (1 / 12 : ℝ))) ≤ 1 / 8 :=
    ztw_rpow_mul_exp_sub_le (32 * (4 * C + C₅ + 8 / κ) * (κ / 4 + 1)) (127 / 60) 1 (κ / 16)
      (1 / 10) (1 / 12) (1 / 8) (by positivity) (by norm_num) (by positivity) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  have hIII : ∀ᶠ L : ℝ in Filter.atTop,
      64 * Real.sqrt 2 * (4 * C + C₅ + 8 / κ) * L ^ (21 / 4 : ℝ) *
          Real.exp (-((κ / 16) * L ^ (1 / 12 : ℝ))) ≤ 1 / 8 :=
    ztw_rpow_mul_exp_neg_le (64 * Real.sqrt 2 * (4 * C + C₅ + 8 / κ)) (21 / 4) (κ / 16) (1 / 12)
      (1 / 8) (by positivity) (by positivity) (by norm_num) (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hIa, hIb] with L hIa hIb
    rw [Real.rpow_zero, mul_one, one_mul] at hIa
    rw [Real.rpow_one, one_mul] at hIb
    have hterm1 : Ctr * (Real.exp L * Real.exp (-(L ^ (1 / 10 : ℝ)))) ≤
        (1 / 16) * (Real.exp L * Real.exp (-((κ / 16) * L ^ (1 / 12 : ℝ)))) := by
      have hsplit : Real.exp (-(L ^ (1 / 10 : ℝ))) =
          Real.exp (-((κ / 16) * L ^ (1 / 12 : ℝ))) *
            Real.exp (-(L ^ (1 / 10 : ℝ) - (κ / 16) * L ^ (1 / 12 : ℝ))) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [hsplit]
      calc Ctr * (Real.exp L * (Real.exp (-((κ / 16) * L ^ (1 / 12 : ℝ))) *
              Real.exp (-(L ^ (1 / 10 : ℝ) - (κ / 16) * L ^ (1 / 12 : ℝ)))))
          = Real.exp L * Real.exp (-((κ / 16) * L ^ (1 / 12 : ℝ))) *
              (Ctr * Real.exp (-(L ^ (1 / 10 : ℝ) - (κ / 16) * L ^ (1 / 12 : ℝ)))) := by ring
        _ ≤ Real.exp L * Real.exp (-((κ / 16) * L ^ (1 / 12 : ℝ))) * (1 / 16) :=
            mul_le_mul_of_nonneg_left hIa (by positivity)
        _ = (1 / 16) * (Real.exp L * Real.exp (-((κ / 16) * L ^ (1 / 12 : ℝ)))) := by ring
    have hterm2 : Ctr * L ≤
        (1 / 16) * (Real.exp L * Real.exp (-((κ / 16) * L ^ (1 / 12 : ℝ)))) := by
      have hg : L - (κ / 16) * L ^ (1 / 12 : ℝ) = L + (-((κ / 16) * L ^ (1 / 12 : ℝ))) := by ring
      have heq : Real.exp (-(L - (κ / 16) * L ^ (1 / 12 : ℝ))) * Real.exp (L - (κ / 16) * L ^ (1 / 12 : ℝ)) = 1 := by
        rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
      have h : 16 * Ctr * L ≤ Real.exp (L - (κ / 16) * L ^ (1 / 12 : ℝ)) := by
        have hexppos : 0 < Real.exp (L - (κ / 16) * L ^ (1 / 12 : ℝ)) := Real.exp_pos _
        have h2 := mul_le_mul_of_nonneg_right hIb hexppos.le
        calc 16 * Ctr * L ≤ (16 * Ctr * L * Real.exp (-(L - (κ / 16) * L ^ (1 / 12 : ℝ)))) *
              Real.exp (L - (κ / 16) * L ^ (1 / 12 : ℝ)) := by
              rw [show (16 * Ctr * L * Real.exp (-(L - (κ / 16) * L ^ (1 / 12 : ℝ)))) *
                    Real.exp (L - (κ / 16) * L ^ (1 / 12 : ℝ))
                  = 16 * Ctr * L * (Real.exp (-(L - (κ / 16) * L ^ (1 / 12 : ℝ))) *
                    Real.exp (L - (κ / 16) * L ^ (1 / 12 : ℝ))) by ring]
              rw [heq, mul_one]
          _ ≤ 1 * Real.exp (L - (κ / 16) * L ^ (1 / 12 : ℝ)) := h2
          _ = Real.exp (L - (κ / 16) * L ^ (1 / 12 : ℝ)) := one_mul _
      have hsplit : Real.exp (L - (κ / 16) * L ^ (1 / 12 : ℝ)) =
          Real.exp L * Real.exp (-((κ / 16) * L ^ (1 / 12 : ℝ))) := by
        rw [hg, Real.exp_add]
      have hfinal : Ctr * L ≤ (1 / 16) * Real.exp (L - (κ / 16) * L ^ (1 / 12 : ℝ)) := by
        linarith
      rw [hsplit] at hfinal
      exact hfinal
    calc Ctr * (Real.exp L * Real.exp (-(L ^ (1 / 10 : ℝ))) + L)
        = Ctr * (Real.exp L * Real.exp (-(L ^ (1 / 10 : ℝ)))) + Ctr * L := by ring
      _ ≤ (1 / 16) * (Real.exp L * Real.exp (-((κ / 16) * L ^ (1 / 12 : ℝ)))) +
            (1 / 16) * (Real.exp L * Real.exp (-((κ / 16) * L ^ (1 / 12 : ℝ)))) :=
          add_le_add hterm1 hterm2
      _ = (1 / 8) * (Real.exp L * Real.exp (-((κ / 16) * L ^ (1 / 12 : ℝ)))) := by ring
  · filter_upwards [hII] with L hII
    rw [one_mul] at hII
    have heq : Real.exp (-(L ^ (1 / 10 : ℝ))) =
        Real.exp (-(L ^ (1 / 10 : ℝ) - (κ / 16) * L ^ (1 / 12 : ℝ))) *
          Real.exp (-((κ / 16) * L ^ (1 / 12 : ℝ))) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [heq]
    have h := mul_le_mul_of_nonneg_right hII (Real.exp_pos (-((κ / 16) * L ^ (1 / 12 : ℝ)))).le
    calc 32 * (4 * C + C₅ + 8 / κ) * (κ / 4 + 1) * L ^ (127 / 60 : ℝ) *
          (Real.exp (-(L ^ (1 / 10 : ℝ) - (κ / 16) * L ^ (1 / 12 : ℝ))) *
            Real.exp (-((κ / 16) * L ^ (1 / 12 : ℝ))))
        = (32 * (4 * C + C₅ + 8 / κ) * (κ / 4 + 1) * L ^ (127 / 60 : ℝ) *
            Real.exp (-(L ^ (1 / 10 : ℝ) - (κ / 16) * L ^ (1 / 12 : ℝ)))) *
              Real.exp (-((κ / 16) * L ^ (1 / 12 : ℝ))) := by ring
      _ ≤ (1 / 8) * Real.exp (-((κ / 16) * L ^ (1 / 12 : ℝ))) := h
  · filter_upwards [hIII] with L hIII
    have h := mul_le_mul_of_nonneg_right hIII (Real.exp_pos ((κ / 16) * L ^ (1 / 12 : ℝ))).le
    calc 64 * Real.sqrt 2 * (4 * C + C₅ + 8 / κ) * L ^ (21 / 4 : ℝ)
        = (64 * Real.sqrt 2 * (4 * C + C₅ + 8 / κ) * L ^ (21 / 4 : ℝ) *
            Real.exp (-((κ / 16) * L ^ (1 / 12 : ℝ)))) *
              Real.exp ((κ / 16) * L ^ (1 / 12 : ℝ)) := by
          conv_rhs => rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
      _ ≤ (1 / 8) * Real.exp ((κ / 16) * L ^ (1 / 12 : ℝ)) := h

/-- **The eventual parameter package of the `6/7`-shaped twisted Perron argument.**

For every `L` large enough and every `u` with `|u| ≤ exp (L^{21/20})`, writing `T = twT L u`,
`D = twD L u = ztD (2T)` and `δ = twδ κ L u = κ/(4D)`: `log (2T+3) ≤ 2 L^{21/20}`;
`D ≤ 2 L^{11/12}`; `δ ≤ min δ₅ (1/4)`; the truncation term is small; and the horizontal- and
left-edge factors are dominated by `exp(∓(κ/16) L^{1/12})`. -/
theorem ztw_param (κ δ₅ C₅ C Ctr : ℝ) (hκ : 0 < κ) (hδ₅ : 0 < δ₅) (hC₅ : 0 < C₅)
    (hC : 0 < C) (hCtr : 0 < Ctr) :
    ∀ᶠ L : ℝ in Filter.atTop, ∀ u : ℝ, |u| ≤ Real.exp (L ^ (21 / 20 : ℝ)) →
      Real.log (2 * Work.BMF.twT L u + 3) ≤ 2 * L ^ (21 / 20 : ℝ) ∧
      Work.BMF.twD L u ≤ 2 * L ^ (11 / 12 : ℝ) ∧
      Work.BMF.twδ κ L u ≤ min δ₅ (1 / 4) ∧
      Ctr * (Real.exp L * L ^ 2 / Work.BMF.twT L u + L) ≤
        (1 / 8) * (Real.exp L * Real.exp (-((κ / 16) * L ^ (1 / 12 : ℝ)))) ∧
      8 * (max (C * (Real.log (2 * Work.BMF.twT L u + 3)) ^ 2) (C₅ + 1 / Work.BMF.twδ κ L u)) *
          (Real.log (|u| + Work.BMF.twT L u + 3)) ^ 2 *
            ((Work.BMF.twδ κ L u + 1 / L) / Work.BMF.twT L u) ≤
        (1 / 8) * Real.exp (-((κ / 16) * L ^ (1 / 12 : ℝ))) ∧
      4 * (max (C * (Real.log (2 * Work.BMF.twT L u + 3)) ^ 2) (C₅ + 1 / Work.BMF.twδ κ L u)) *
          (Real.log (|u| + Work.BMF.twT L u + 3)) ^ 2 *
          (2 * Real.sqrt 2 * Real.log (1 + Work.BMF.twT L u / Work.BMF.twσ κ L u)) ≤
        (1 / 8) * Real.exp ((κ / 16) * L ^ (1 / 12 : ℝ)) := by
  obtain ⟨hA, hB, hCexp⟩ := ztw_param_exp_le κ C₅ C Ctr hκ hC₅ hC hCtr
  have hthr : ∀ᶠ L : ℝ in Filter.atTop, max κ (κ / (4 * min δ₅ (1 / 4))) ≤ L ^ (1 / 12 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 12)).eventually_ge_atTop _
  have hL1f : ∀ᶠ L : ℝ in Filter.atTop, (1 : ℝ) ≤ L := eventually_ge_atTop 1
  have hnum : ∀ᶠ L : ℝ in Filter.atTop,
      L ^ 2 * Real.exp (L ^ (1 / 10 : ℝ)) + 7 ≤ Real.exp (L ^ (21 / 20 : ℝ)) := by
    filter_upwards [N4chain.ztNumeric_eventually_21.1] with L hL
    have hep : 0 < Real.exp (L ^ (21 / 20 : ℝ)) := Real.exp_pos _
    linarith
  have hlog6le : ∀ᶠ L : ℝ in Filter.atTop, Real.log 6 ≤ L ^ (21 / 20 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 21 / 20)).eventually_ge_atTop (Real.log 6)
  filter_upwards [ztw_param_twD_bounds, hA, hB, hCexp, hthr, hL1f, hnum, hlog6le]
    with L hb hA hB hCexp hthr hL1 hnum hlog6le
  intro u hu
  obtain ⟨hlogT, hlogu, hDle, hDge⟩ := hb u hu
  have hLpos : 0 < L := by linarith
  have hLnn : 0 ≤ L := hLpos.le
  have hTpos : 0 < twT L u := twT_pos L u
  have hTge : L ^ 2 * Real.exp (L ^ (1 / 10 : ℝ)) ≤ twT L u := le_twT L u
  have hDpos : 0 < twD L u := twD_pos L u
  have hδpos : 0 < twδ κ L u := twδ_pos hκ
  have hlog1 : (1 : ℝ) ≤ Real.log (2 * twT L u + 3) := by
    have h17 : (3 : ℝ) ≤ 2 * twT L u + 3 := by have := seven_le_twT L u; linarith
    exact le_trans one_le_log_three (Real.log_le_log (by norm_num) h17)
  set A := max (C * (Real.log (2 * twT L u + 3)) ^ 2) (C₅ + 1 / twδ κ L u) with hAdef
  set Lu2 := (Real.log (|u| + twT L u + 3)) ^ 2 with hLudef
  set Fr := (twδ κ L u + 1 / L) / twT L u with hFrdef
  have hA0 : 0 ≤ A := by
    rw [hAdef]; exact le_trans (mul_nonneg hC.le (sq_nonneg _)) (le_max_left _ _)
  have hLu2ge : 0 ≤ Lu2 := by rw [hLudef]; exact sq_nonneg _
  have hFrge : 0 ≤ Fr := by
    rw [hFrdef]
    exact div_nonneg (by linarith [hδpos.le, one_div_pos.mpr hLpos]) hTpos.le
  have hκle : κ ≤ L ^ (1 / 12 : ℝ) := le_trans (le_max_left _ _) hthr
  have hκδle : κ / (4 * min δ₅ (1 / 4)) ≤ L ^ (1 / 12 : ℝ) := le_trans (le_max_right _ _) hthr
  have hδ14 : twδ κ L u ≤ 1 / 4 := by
    rw [twδ, div_le_iff₀ (by positivity : (0 : ℝ) < 4 * twD L u)]
    have : (1 / 4) * (4 * twD L u) = twD L u := by ring
    linarith [hκle, hDge, this]
  have hδδ₅ : twδ κ L u ≤ δ₅ := by
    have hm : min δ₅ (1 / 4) ≤ δ₅ := min_le_left _ _
    have h2 : κ / (4 * δ₅) ≤ κ / (4 * min δ₅ (1 / 4)) := by
      apply div_le_div_of_nonneg_left hκ.le (by positivity)
      nlinarith [hm]
    have h3 : κ / (4 * δ₅) ≤ twD L u := le_trans h2 (le_trans hκδle hDge)
    rw [twδ, div_le_iff₀ (by positivity : (0 : ℝ) < 4 * twD L u)]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * δ₅)] at h3
    have hr : δ₅ * (4 * twD L u) = twD L u * (4 * δ₅) := by ring
    linarith [h3, hr]
  have hδle : twδ κ L u ≤ min δ₅ (1 / 4) := le_min hδδ₅ hδ14
  have hδhalf : twδ κ L u ≤ 1 / 2 := by linarith [hδ14]
  -- squared logarithms
  have hlogT_sq : (Real.log (2 * twT L u + 3)) ^ 2 ≤ 4 * L ^ (21 / 10 : ℝ) := by
    have hnn : 0 ≤ Real.log (2 * twT L u + 3) := le_trans zero_le_one hlog1
    have hXnn : 0 ≤ 2 * L ^ (21 / 20 : ℝ) := by positivity
    have h2 : (2 * L ^ (21 / 20 : ℝ)) ^ 2 = 4 * L ^ (21 / 10 : ℝ) := by
      have hp : (L ^ (21 / 20 : ℝ)) ^ 2 = L ^ (21 / 10 : ℝ) := by
        rw [← Real.rpow_natCast (L ^ (21 / 20 : ℝ)) 2, ← Real.rpow_mul hLnn]; norm_num
      rw [mul_pow, hp]; norm_num
    calc (Real.log (2 * twT L u + 3)) ^ 2 ≤ (2 * L ^ (21 / 20 : ℝ)) ^ 2 := by
          nlinarith [hlogT, hnn, hXnn]
      _ = 4 * L ^ (21 / 10 : ℝ) := h2
  have hlogu_sq : Lu2 ≤ 4 * L ^ (21 / 10 : ℝ) := by
    rw [hLudef]
    have hnn : 0 ≤ Real.log (|u| + twT L u + 3) :=
      Real.log_nonneg (by have := seven_le_twT L u; have := abs_nonneg u; linarith)
    have hXnn : 0 ≤ 2 * L ^ (21 / 20 : ℝ) := by positivity
    have h2 : (2 * L ^ (21 / 20 : ℝ)) ^ 2 = 4 * L ^ (21 / 10 : ℝ) := by
      have hp : (L ^ (21 / 20 : ℝ)) ^ 2 = L ^ (21 / 10 : ℝ) := by
        rw [← Real.rpow_natCast (L ^ (21 / 20 : ℝ)) 2, ← Real.rpow_mul hLnn]; norm_num
      rw [mul_pow, hp]; norm_num
    calc (Real.log (|u| + twT L u + 3)) ^ 2 ≤ (2 * L ^ (21 / 20 : ℝ)) ^ 2 := by
          nlinarith [hlogu, hnn, hXnn]
      _ = 4 * L ^ (21 / 10 : ℝ) := h2
  -- the auxiliary maximum
  have hM : A ≤ (4 * C + C₅ + 8 / κ) * L ^ (21 / 10 : ℝ) := by
    rw [hAdef]
    have hlt : C * (Real.log (2 * twT L u + 3)) ^ 2 ≤ 4 * C * L ^ (21 / 10 : ℝ) := by
      have := mul_le_mul_of_nonneg_left hlogT_sq hC.le
      linarith [this]
    have hLt1 : (1 : ℝ) ≤ L ^ (21 / 10 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
    have h1δ : C₅ + 1 / twδ κ L u ≤ (C₅ + 8 / κ) * L ^ (21 / 10 : ℝ) := by
      have hLP : L ^ (11 / 12 : ℝ) ≤ L ^ (21 / 10 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
      have h1 : 1 / twδ κ L u ≤ (8 / κ) * L ^ (11 / 12 : ℝ) := by
        have hDl : 4 * twD L u / κ ≤ 8 * L ^ (11 / 12 : ℝ) / κ := by
          apply div_le_div_of_nonneg_right _ hκ.le
          linarith [hDle]
        rw [show 1 / twδ κ L u = 4 * twD L u / κ by rw [twδ, one_div_div]]
        calc 4 * twD L u / κ ≤ 8 * L ^ (11 / 12 : ℝ) / κ := hDl
          _ = (8 / κ) * L ^ (11 / 12 : ℝ) := by ring
      have h2 : (8 / κ) * L ^ (11 / 12 : ℝ) ≤ (8 / κ) * L ^ (21 / 10 : ℝ) :=
        mul_le_mul_of_nonneg_left hLP (by positivity)
      have h3 : C₅ ≤ C₅ * L ^ (21 / 10 : ℝ) := le_mul_of_one_le_right hC₅.le hLt1
      have hr : (8 / κ) * L ^ (21 / 10 : ℝ) + C₅ * L ^ (21 / 10 : ℝ) =
          (C₅ + 8 / κ) * L ^ (21 / 10 : ℝ) := by ring
      linarith [h1, h2, h3, hr]
    have hp1 : 0 ≤ (C₅ + 8 / κ) * L ^ (21 / 10 : ℝ) := by positivity
    have hp2 : 0 ≤ 4 * C * L ^ (21 / 10 : ℝ) := by positivity
    have hmax : max (C * (Real.log (2 * twT L u + 3)) ^ 2) (C₅ + 1 / twδ κ L u) ≤
        4 * C * L ^ (21 / 10 : ℝ) + (C₅ + 8 / κ) * L ^ (21 / 10 : ℝ) :=
      max_le (by linarith [hlt, hp1]) (by linarith [h1δ, hp2])
    have hr : 4 * C * L ^ (21 / 10 : ℝ) + (C₅ + 8 / κ) * L ^ (21 / 10 : ℝ) =
        (4 * C + C₅ + 8 / κ) * L ^ (21 / 10 : ℝ) := by ring
    linarith [hmax, hr]
  refine ⟨hlogT, hDle, hδle, ?_, ?_, ?_⟩
  · -- clause 4
    have hterm : Real.exp L * L ^ 2 / twT L u ≤ Real.exp L * Real.exp (-(L ^ (1 / 10 : ℝ))) := by
      rw [div_le_iff₀ hTpos]
      have h1 : Real.exp L * Real.exp (-(L ^ (1 / 10 : ℝ))) * (L ^ 2 * Real.exp (L ^ (1 / 10 : ℝ))) ≤
          Real.exp L * Real.exp (-(L ^ (1 / 10 : ℝ))) * twT L u :=
        mul_le_mul_of_nonneg_left hTge (by positivity)
      have heq : Real.exp L * Real.exp (-(L ^ (1 / 10 : ℝ))) *
            (L ^ 2 * Real.exp (L ^ (1 / 10 : ℝ))) = Real.exp L * L ^ 2 := by
        have hxx : Real.exp (-(L ^ (1 / 10 : ℝ))) * Real.exp (L ^ (1 / 10 : ℝ)) = 1 := by
          rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
        calc Real.exp L * Real.exp (-(L ^ (1 / 10 : ℝ))) * (L ^ 2 * Real.exp (L ^ (1 / 10 : ℝ)))
            = (Real.exp L * L ^ 2) *
                (Real.exp (-(L ^ (1 / 10 : ℝ))) * Real.exp (L ^ (1 / 10 : ℝ))) := by ring
          _ = (Real.exp L * L ^ 2) * 1 := by rw [hxx]
          _ = Real.exp L * L ^ 2 := by ring
      rw [heq] at h1
      exact h1
    calc Ctr * (Real.exp L * L ^ 2 / twT L u + L)
        ≤ Ctr * (Real.exp L * Real.exp (-(L ^ (1 / 10 : ℝ))) + L) := by
          apply mul_le_mul_of_nonneg_left _ hCtr.le
          linarith [hterm]
      _ ≤ (1 / 8) * (Real.exp L * Real.exp (-((κ / 16) * L ^ (1 / 12 : ℝ)))) := hA
  · -- clause 5
    have hLp5 : L ^ (21 / 10 : ℝ) * L ^ (21 / 10 : ℝ) * L ^ (-(1 / 12) : ℝ) *
        L ^ (-(2) : ℝ) = L ^ (127 / 60 : ℝ) := by
      rw [← Real.rpow_add hLpos, ← Real.rpow_add hLpos, ← Real.rpow_add hLpos]
      norm_num
    have hδk : twδ κ L u ≤ (κ / 4) * L ^ (-(1 / 12) : ℝ) := by
      have h4D : 4 * L ^ (1 / 12 : ℝ) ≤ 4 * twD L u := by linarith [hDge]
      have h0 : 0 < 4 * L ^ (1 / 12 : ℝ) := by positivity
      have h1 : κ / (4 * twD L u) ≤ κ / (4 * L ^ (1 / 12 : ℝ)) :=
        div_le_div_of_nonneg_left hκ.le h0 h4D
      have h2 : κ / (4 * L ^ (1 / 12 : ℝ)) = (κ / 4) * L ^ (-(1 / 12) : ℝ) := by
        have hneg : L ^ (-(1 / 12) : ℝ) = (L ^ (1 / 12 : ℝ))⁻¹ := Real.rpow_neg hLnn (1 / 12)
        rw [hneg, div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev]
        ring
      rw [twδ]
      linarith [h1, h2]
    have hL1inv : 1 / L ≤ L ^ (-(1 / 12) : ℝ) := by
      have h := Real.rpow_le_rpow_of_exponent_le hL1 (show (-1 : ℝ) ≤ -(1 / 12) by norm_num)
      rw [Real.rpow_neg_one] at h
      simpa [one_div] using h
    have hsum : twδ κ L u + 1 / L ≤ (κ / 4 + 1) * L ^ (-(1 / 12) : ℝ) := by
      calc twδ κ L u + 1 / L ≤ (κ / 4) * L ^ (-(1 / 12) : ℝ) + L ^ (-(1 / 12) : ℝ) :=
            add_le_add hδk hL1inv
        _ = (κ / 4 + 1) * L ^ (-(1 / 12) : ℝ) := by ring
    have hTinv : 1 / twT L u ≤ L ^ (-(2) : ℝ) * Real.exp (-(L ^ (1 / 10 : ℝ))) := by
      have h0 : 0 < L ^ 2 * Real.exp (L ^ (1 / 10 : ℝ)) := by positivity
      have h1 : 1 / twT L u ≤ 1 / (L ^ 2 * Real.exp (L ^ (1 / 10 : ℝ))) :=
        one_div_le_one_div_of_le h0 hTge
      have h2 : 1 / (L ^ 2 * Real.exp (L ^ (1 / 10 : ℝ))) =
          L ^ (-(2) : ℝ) * Real.exp (-(L ^ (1 / 10 : ℝ))) := by
        have e1 : (L ^ 2)⁻¹ = L ^ (-(2) : ℝ) := by
          have h22 : L ^ 2 = L ^ (2 : ℝ) := (Real.rpow_natCast L 2).symm
          rw [h22, ← Real.rpow_neg hLnn (2 : ℝ)]
        have e2 : (Real.exp (L ^ (1 / 10 : ℝ)))⁻¹ = Real.exp (-(L ^ (1 / 10 : ℝ))) :=
          (Real.exp_neg _).symm
        rw [one_div, mul_inv_rev, e1, e2]
        ring
      linarith [h1, h2]
    have hfrac : Fr ≤ (κ / 4 + 1) * L ^ (-(1 / 12) : ℝ) *
        (L ^ (-(2) : ℝ) * Real.exp (-(L ^ (1 / 10 : ℝ)))) := by
      rw [hFrdef, div_eq_mul_one_div]
      exact mul_le_mul hsum hTinv (by positivity) (by positivity)
    have hstep : 8 * A * Lu2 * Fr ≤
        32 * (4 * C + C₅ + 8 / κ) * (κ / 4 + 1) * L ^ (127 / 60 : ℝ) *
          Real.exp (-(L ^ (1 / 10 : ℝ))) := by
      have h1 : 8 * A ≤ 8 * ((4 * C + C₅ + 8 / κ) * L ^ (21 / 10 : ℝ)) :=
        mul_le_mul_of_nonneg_left hM (by norm_num)
      have hcomb : 8 * A * Lu2 ≤
          (8 * ((4 * C + C₅ + 8 / κ) * L ^ (21 / 10 : ℝ))) * (4 * L ^ (21 / 10 : ℝ)) :=
        mul_le_mul h1 hlogu_sq hLu2ge (by positivity)
      have hcomb2 := mul_le_mul hcomb hfrac hFrge (by positivity)
      refine le_trans hcomb2 ?_
      have hrw : (8 * ((4 * C + C₅ + 8 / κ) * L ^ (21 / 10 : ℝ))) * (4 * L ^ (21 / 10 : ℝ)) *
            ((κ / 4 + 1) * L ^ (-(1 / 12) : ℝ) * (L ^ (-(2) : ℝ) * Real.exp (-(L ^ (1 / 10 : ℝ))))) =
          32 * (4 * C + C₅ + 8 / κ) * (κ / 4 + 1) *
            (L ^ (21 / 10 : ℝ) * L ^ (21 / 10 : ℝ) * L ^ (-(1 / 12) : ℝ) * L ^ (-(2) : ℝ)) *
              Real.exp (-(L ^ (1 / 10 : ℝ))) := by ring
      rw [hrw, hLp5]
    calc 8 * A * Lu2 * Fr ≤ 32 * (4 * C + C₅ + 8 / κ) * (κ / 4 + 1) * L ^ (127 / 60 : ℝ) *
          Real.exp (-(L ^ (1 / 10 : ℝ))) := hstep
      _ ≤ (1 / 8) * Real.exp (-((κ / 16) * L ^ (1 / 12 : ℝ))) := hB
  · -- clause 6
    have hσhalf : 1 / 2 ≤ twσ κ L u := by rw [twσ]; linarith [hδhalf]
    have hTle2 : twT L u ≤ 2 * Real.exp (L ^ (21 / 20 : ℝ)) := by
      have h := abs_nonneg u
      rw [twT]; linarith [hu, hnum]
    have hlogσ : Real.log (1 + twT L u / twσ κ L u) ≤ 2 * L ^ (21 / 20 : ℝ) := by
      have hσpos : 0 < twσ κ L u := by linarith [hσhalf]
      have h1 : twT L u / twσ κ L u ≤ 2 * twT L u := by
        rw [div_le_iff₀ hσpos]
        nlinarith [hσhalf, hTpos]
      have h2 : 1 + twT L u / twσ κ L u ≤ 3 * twT L u := by
        have := seven_le_twT L u; linarith
      have h3 : 3 * twT L u ≤ 3 * (2 * Real.exp (L ^ (21 / 20 : ℝ))) := by linarith [hTle2]
      have h4 : Real.log (1 + twT L u / twσ κ L u) ≤
          Real.log (3 * (2 * Real.exp (L ^ (21 / 20 : ℝ)))) :=
        Real.log_le_log (by have h : 0 < twT L u / twσ κ L u := div_pos hTpos hσpos; linarith)
          (le_trans h2 h3)
      have h5 : Real.log (3 * (2 * Real.exp (L ^ (21 / 20 : ℝ)))) = Real.log 6 + L ^ (21 / 20 : ℝ) := by
        rw [show (3 : ℝ) * (2 * Real.exp (L ^ (21 / 20 : ℝ))) = 6 * Real.exp (L ^ (21 / 20 : ℝ)) by ring,
          Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp]
      rw [h5] at h4
      linarith [h4, hlog6le]
    have hLp6 : L ^ (21 / 10 : ℝ) * L ^ (21 / 10 : ℝ) * L ^ (21 / 20 : ℝ) = L ^ (21 / 4 : ℝ) := by
      rw [← Real.rpow_add hLpos, ← Real.rpow_add hLpos]
      norm_num
    calc 4 * A * Lu2 * (2 * Real.sqrt 2 * Real.log (1 + twT L u / twσ κ L u))
        ≤ 4 * ((4 * C + C₅ + 8 / κ) * L ^ (21 / 10 : ℝ)) * (4 * L ^ (21 / 10 : ℝ)) *
            (2 * Real.sqrt 2 * (2 * L ^ (21 / 20 : ℝ))) := by
          have h1 : 4 * A ≤ 4 * ((4 * C + C₅ + 8 / κ) * L ^ (21 / 10 : ℝ)) :=
            mul_le_mul_of_nonneg_left hM (by norm_num)
          have h3 : 2 * Real.sqrt 2 * Real.log (1 + twT L u / twσ κ L u) ≤
              2 * Real.sqrt 2 * (2 * L ^ (21 / 20 : ℝ)) :=
            mul_le_mul_of_nonneg_left hlogσ (by positivity)
          have hc1 : 4 * A * Lu2 ≤
              (4 * ((4 * C + C₅ + 8 / κ) * L ^ (21 / 10 : ℝ))) * (4 * L ^ (21 / 10 : ℝ)) :=
            mul_le_mul h1 hlogu_sq hLu2ge (by positivity)
          have h3nn : 0 ≤ 2 * Real.sqrt 2 * Real.log (1 + twT L u / twσ κ L u) := by
            have hl : 0 ≤ Real.log (1 + twT L u / twσ κ L u) :=
              Real.log_nonneg (by
                have h : 0 ≤ twT L u / twσ κ L u :=
                  div_nonneg hTpos.le (by linarith [hσhalf])
                linarith)
            exact mul_nonneg (by positivity) hl
          exact mul_le_mul hc1 h3 h3nn (by positivity)
      _ = 64 * Real.sqrt 2 * (4 * C + C₅ + 8 / κ) * L ^ (21 / 4 : ℝ) := by
          rw [show 4 * ((4 * C + C₅ + 8 / κ) * L ^ (21 / 10 : ℝ)) * (4 * L ^ (21 / 10 : ℝ)) *
                (2 * Real.sqrt 2 * (2 * L ^ (21 / 20 : ℝ))) =
              64 * Real.sqrt 2 * (4 * C + C₅ + 8 / κ) *
                (L ^ (21 / 10 : ℝ) * L ^ (21 / 10 : ℝ) * L ^ (21 / 20 : ℝ)) by ring,
            hLp6]
      _ ≤ (1 / 8) * Real.exp ((κ / 16) * L ^ (1 / 12 : ℝ)) := hCexp

end

end Work.BMF
