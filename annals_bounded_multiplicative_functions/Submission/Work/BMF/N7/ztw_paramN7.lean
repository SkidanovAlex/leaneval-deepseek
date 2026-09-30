import Mathlib
import Submission.Work.BMF.ztw_defs
import Submission.Work.BMF.ztw_asym
import Submission.Work.BMF.N7.twD_uniform_ge
import Submission.Work.BMF.N7.ztw_D_exp_bound
import Submission.Work.BMF.N7.ztw_truncN7

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.N7

open Filter
open scoped Real Topology

noncomputable section

/-! ## The parameter package of the `6/7`-shaped twisted Perron argument

Conjuncts (1) `log (2T+3) ≤ 2L^{21/20}`, (2) `twD ≤ 2L^{11/12}` (using the arithmetic core
`Work.BMF.N7.ztw_D_exp_bound`), (3) `twδ ≤ min δ₅ (1/4)` (using the uniform lower bound
`Work.BMF.N7.twD_uniform_ge`), (4), (5) and (6) are proved here; conjunct (4) also appears as
`Work.BMF.N7.ztw_truncN7`. -/

lemma ztw_rpow_le_exp_sub (K a b₁ b₂ c₁ c₂ ε : ℝ) (hK : 0 ≤ K) (hb₁ : 0 < b₁)
    (hb₂ : 0 ≤ b₂) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hcc : c₂ < c₁) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in Filter.atTop, K * L ^ a ≤ ε * Real.exp (b₁ * L ^ c₁ - b₂ * L ^ c₂) := by
  have h := Work.BMF.ztw_rpow_mul_exp_sub_le K a b₁ b₂ c₁ c₂ ε hK hb₁ hb₂ hc₁ hc₂ hcc hε
  filter_upwards [h] with L hL
  have hX : 0 < Real.exp (b₁ * L ^ c₁ - b₂ * L ^ c₂) := Real.exp_pos _
  have hh := mul_le_mul_of_nonneg_right hL hX.le
  have heq : (K * L ^ a * Real.exp (-(b₁ * L ^ c₁ - b₂ * L ^ c₂)))
      * Real.exp (b₁ * L ^ c₁ - b₂ * L ^ c₂) = K * L ^ a := by
    rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
  rw [heq] at hh
  exact hh

/-- `K L^a exp(-(b₁ L^{c₁})) ≤ ε exp(-(b₂ L^{c₂}))` eventually (`0 < c₂ < c₁`). -/
lemma ztw_rpow_mul_exp_sub' (K a b₁ b₂ c₁ c₂ ε : ℝ) (hK : 0 ≤ K) (hb₁ : 0 < b₁)
    (hb₂ : 0 ≤ b₂) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hcc : c₂ < c₁) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in Filter.atTop,
      K * L ^ a * Real.exp (-(b₁ * L ^ c₁)) ≤ ε * Real.exp (-(b₂ * L ^ c₂)) := by
  have h := ztw_rpow_le_exp_sub K a b₁ b₂ c₁ c₂ ε hK hb₁ hb₂ hc₁ hc₂ hcc hε
  filter_upwards [h] with L hL
  have hX : 0 < Real.exp (-(b₁ * L ^ c₁)) := Real.exp_pos _
  have hh := mul_le_mul_of_nonneg_right hL hX.le
  have hR : (ε * Real.exp (b₁ * L ^ c₁ - b₂ * L ^ c₂)) * Real.exp (-(b₁ * L ^ c₁))
      = ε * Real.exp (-(b₂ * L ^ c₂)) := by
    rw [mul_assoc, ← Real.exp_add]
    congr 1
    ring
  rw [hR] at hh
  exact hh

lemma ztw_eventually_log3 : ∀ᶠ L : ℝ in Filter.atTop, Real.log 3 ≤ L ^ (21 / 20 : ℝ) :=
  (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 21 / 20)).eventually_ge_atTop (Real.log 3)

lemma ztw_eventually_log4 : ∀ᶠ L : ℝ in Filter.atTop, Real.log 4 ≤ L ^ (21 / 20 : ℝ) :=
  (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 21 / 20)).eventually_ge_atTop (Real.log 4)

lemma ztw_eventually_two_rpowA : ∀ᶠ L : ℝ in Filter.atTop, (1:ℝ) ≤ 2 * L ^ (21 / 20 : ℝ) := by
  filter_upwards [(tendsto_rpow_atTop (by norm_num : (0:ℝ) < 21 / 20)).eventually_ge_atTop (1:ℝ)]
    with L hL
  linarith

lemma ztw_eventually_expA : ∀ᶠ L : ℝ in Filter.atTop,
    2 * L ^ 2 * Real.exp (L ^ (1/10 : ℝ)) + 17 ≤ Real.exp (L ^ (21/20 : ℝ)) := by
  have h2 : ∀ᶠ L : ℝ in Filter.atTop,
      2 * L ^ 2 ≤ (1/2) * Real.exp (1 * L ^ (21/20 : ℝ) - 1 * L ^ (1/10 : ℝ)) := by
    have h := ztw_rpow_le_exp_sub (2:ℝ) (2:ℝ) 1 1 (21/20) (1/10) (1/2) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    filter_upwards [h] with L hL
    rw [Real.rpow_two] at hL
    exact hL
  have h17 : ∀ᶠ L : ℝ in Filter.atTop,
      (17:ℝ) ≤ (1/2) * Real.exp (1 * L ^ (21/20 : ℝ) - 1 * L ^ (1/10 : ℝ)) := by
    have h := ztw_rpow_le_exp_sub (17:ℝ) (0:ℝ) 1 1 (21/20) (1/10) (1/2) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    filter_upwards [h] with L hL
    rw [Real.rpow_zero, mul_one] at hL
    exact hL
  filter_upwards [h2, h17, eventually_ge_atTop (0:ℝ)] with L h2L h17L hL0
  have hEpos : 0 < Real.exp (L ^ (1/10 : ℝ)) := Real.exp_pos _
  have hE1 : (1:ℝ) ≤ Real.exp (L ^ (1/10 : ℝ)) := by
    rw [← Real.exp_zero, Real.exp_le_exp]
    exact Real.rpow_nonneg hL0 _
  have hXE : Real.exp (1 * L ^ (21/20 : ℝ) - 1 * L ^ (1/10 : ℝ)) * Real.exp (L ^ (1/10 : ℝ))
      = Real.exp (L ^ (21/20 : ℝ)) := by
    rw [← Real.exp_add]; congr 1; ring
  have he : (1/2) * Real.exp (1 * L ^ (21/20 : ℝ) - 1 * L ^ (1/10 : ℝ))
      * Real.exp (L ^ (1/10 : ℝ)) = (1/2) * Real.exp (L ^ (21/20 : ℝ)) := by
    rw [mul_assoc, hXE]
  have hA1 : 2 * L ^ 2 * Real.exp (L ^ (1/10 : ℝ)) ≤ (1/2) * Real.exp (L ^ (21/20 : ℝ)) := by
    have h := mul_le_mul_of_nonneg_right h2L hEpos.le
    rw [he] at h
    exact h
  have hA17 : (17:ℝ) * Real.exp (L ^ (1/10 : ℝ)) ≤ (1/2) * Real.exp (L ^ (21/20 : ℝ)) := by
    have h := mul_le_mul_of_nonneg_right h17L hEpos.le
    rw [he] at h
    exact h
  have h17le : (17:ℝ) ≤ 17 * Real.exp (L ^ (1/10 : ℝ)) := by nlinarith [hE1]
  linarith [hA1, hA17, h17le]

lemma ztw_conj1 : ∀ᶠ L : ℝ in Filter.atTop, ∀ u : ℝ, |u| ≤ Real.exp (L ^ (21/20 : ℝ)) →
    Real.log (2 * Work.BMF.twT L u + 3) ≤ 2 * L ^ (21/20 : ℝ) := by
  filter_upwards [ztw_eventually_expA, ztw_eventually_log3] with L hexpA hlog3
  intro u hu
  have hT : Work.BMF.twT L u ≤ Real.exp (L ^ (21/20 : ℝ)) + L^2 * Real.exp (L ^ (1/10 : ℝ)) + 7 := by
    rw [Work.BMF.twT]; linarith
  have h23 : 2 * Work.BMF.twT L u + 3 ≤ 3 * Real.exp (L ^ (21/20 : ℝ)) := by linarith
  have h3 : (3:ℝ) ≤ Real.exp (L ^ (21/20 : ℝ)) := by
    have h := Real.exp_le_exp.mpr hlog3
    rwa [Real.exp_log (by norm_num : (0:ℝ) < 3)] at h
  have h3e : 3 * Real.exp (L ^ (21/20 : ℝ)) ≤ Real.exp (2 * L ^ (21/20 : ℝ)) := by
    calc 3 * Real.exp (L ^ (21/20 : ℝ))
        ≤ Real.exp (L ^ (21/20 : ℝ)) * Real.exp (L ^ (21/20 : ℝ)) :=
          mul_le_mul_of_nonneg_right h3 (Real.exp_pos (L ^ (21/20 : ℝ))).le
      _ = Real.exp (2 * L ^ (21/20 : ℝ)) := by rw [← Real.exp_add, ← two_mul]
  have hpos : (0:ℝ) < 2 * Work.BMF.twT L u + 3 := by
    have := Work.BMF.seven_le_twT L u; linarith
  calc Real.log (2 * Work.BMF.twT L u + 3)
      ≤ Real.log (Real.exp (2 * L ^ (21/20 : ℝ))) := Real.log_le_log hpos (le_trans h23 h3e)
    _ = 2 * L ^ (21/20 : ℝ) := Real.log_exp _

lemma ztw_conj2 : ∀ᶠ L : ℝ in Filter.atTop, ∀ u : ℝ, |u| ≤ Real.exp (L ^ (21/20 : ℝ)) →
    Work.BMF.twD L u ≤ 2 * L ^ (11/12 : ℝ) := by
  filter_upwards [ztw_conj1, ztw_D_exp_bound, ztw_eventually_two_rpowA] with L h1 hD' hA1
  intro u hu
  have hlog := h1 u hu
  have h4 : (4:ℝ) ≤ 2 * Work.BMF.twT L u := by
    have := Work.BMF.seven_le_twT L u; linarith
  have hzt := Work.BMF.ztD_le_of_log_le h4 hA1 hlog
  calc Work.BMF.twD L u = Work.BMF.ztD (2 * Work.BMF.twT L u) := rfl
    _ ≤ (2 * L ^ (21/20 : ℝ)) ^ (6/7 : ℝ) * (Real.log 3 + Real.log (2 * L ^ (21/20 : ℝ))) := hzt
    _ ≤ 2 * L ^ (11/12 : ℝ) := hD'

lemma ztw_conj3 (κ δ₅ : ℝ) (hκ : 0 < κ) (hδ₅ : 0 < δ₅) :
    ∀ᶠ L : ℝ in Filter.atTop, ∀ u : ℝ, Work.BMF.twδ κ L u ≤ min δ₅ (1/4) := by
  have hD := twD_uniform_ge (max (κ/(4*δ₅)) κ)
  filter_upwards [hD] with L hD'
  intro u
  have hDu : max (κ/(4*δ₅)) κ ≤ Work.BMF.twD L u := hD' u
  have hDpos : 0 < Work.BMF.twD L u := Work.BMF.twD_pos L u
  have h1 : Work.BMF.twδ κ L u ≤ δ₅ := by
    rw [Work.BMF.twδ, div_le_iff₀ (by positivity : (0:ℝ) < 4 * Work.BMF.twD L u)]
    have hK : κ / (4*δ₅) ≤ Work.BMF.twD L u := le_trans (le_max_left _ _) hDu
    have h4δ : 0 < 4 * δ₅ := by positivity
    have h2 : κ ≤ (4*δ₅) * Work.BMF.twD L u := by
      have h := mul_le_mul_of_nonneg_left hK h4δ.le
      have h' : (4*δ₅) * (κ/(4*δ₅)) = κ := by
        rw [mul_comm]; exact div_mul_cancel₀ κ (ne_of_gt h4δ)
      linarith [h, h']
    nlinarith [h2]
  have h2 : Work.BMF.twδ κ L u ≤ 1/4 := by
    rw [Work.BMF.twδ, div_le_iff₀ (by positivity : (0:ℝ) < 4 * Work.BMF.twD L u)]
    have hK : κ ≤ Work.BMF.twD L u := le_trans (le_max_right _ _) hDu
    nlinarith [hK]
  exact le_min h1 h2

lemma ztw_conj3' (κ : ℝ) (hκ : 0 < κ) :
    ∀ᶠ L : ℝ in Filter.atTop, ∀ u : ℝ, Work.BMF.twδ κ L u ≤ 1/4 := by
  have h := ztw_conj3 κ 1 hκ one_pos
  filter_upwards [h] with L hL
  intro u
  exact le_trans (hL u) (min_le_right _ _)

/-! ## shared pieces -/

lemma ztw_pieces (κ C₅ C : ℝ) (hκ : 0 < κ) (hC₅ : 0 < C₅) (hC : 0 < C) :
    ∀ᶠ L : ℝ in Filter.atTop, ∀ u : ℝ, |u| ≤ Real.exp (L ^ (21/20 : ℝ)) →
      max (C * (Real.log (2 * Work.BMF.twT L u + 3)) ^ 2) (C₅ + 1 / Work.BMF.twδ κ L u)
          ≤ (4 * C + C₅ + 8 / κ) * L ^ (21/10 : ℝ) ∧
      (Real.log (|u| + Work.BMF.twT L u + 3)) ^ 2 ≤ 4 * L ^ (21/10 : ℝ) ∧
      Work.BMF.twT L u ≤ 2 * Real.exp (L ^ (21/20 : ℝ)) ∧
      (3/4 : ℝ) ≤ Work.BMF.twσ κ L u := by
  filter_upwards [ztw_conj1, ztw_conj2, ztw_conj3' κ hκ, ztw_eventually_expA,
    eventually_ge_atTop (1:ℝ)] with L hc1 hc2 hc3 hexpA hL1
  have hL0 : (0:ℝ) ≤ L := le_trans zero_le_one hL1
  intro u hu
  have hlog2T : Real.log (2 * Work.BMF.twT L u + 3) ≤ 2 * L ^ (21/20 : ℝ) := hc1 u hu
  have hlog2T_nn : 0 ≤ Real.log (2 * Work.BMF.twT L u + 3) := by
    apply Real.log_nonneg
    have := Work.BMF.seven_le_twT L u; linarith
  have hDle : Work.BMF.twD L u ≤ 2 * L ^ (11/12 : ℝ) := hc2 u hu
  have hdel : Work.BMF.twδ κ L u ≤ 1/4 := hc3 u
  have hTpos : 0 < Work.BMF.twT L u := Work.BMF.twT_pos L u
  -- `(2 L^{21/20})^2 = 4 L^{21/10}`
  have h2pow : (2 * L ^ (21/20 : ℝ)) ^ 2 = 4 * L ^ (21/10 : ℝ) := by
    rw [mul_pow]
    have h3 : (L ^ (21/20 : ℝ)) ^ 2 = L ^ (21/10 : ℝ) := by
      rw [← Real.rpow_two, ← Real.rpow_mul hL0]
      norm_num
    rw [h3]; norm_num
  have hsq_le : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → a ^ 2 ≤ b ^ 2 := by
    intro a b ha hab
    have h := mul_self_le_mul_self ha hab
    simpa [pow_two] using h
  -- first term of the `max`
  have hA1 : C * (Real.log (2 * Work.BMF.twT L u + 3)) ^ 2 ≤ 4 * C * L ^ (21/10 : ℝ) := by
    have hsq : (Real.log (2 * Work.BMF.twT L u + 3)) ^ 2 ≤ (2 * L ^ (21/20 : ℝ)) ^ 2 :=
      hsq_le hlog2T_nn hlog2T
    calc C * (Real.log (2 * Work.BMF.twT L u + 3)) ^ 2
        ≤ C * (2 * L ^ (21/20 : ℝ)) ^ 2 := mul_le_mul_of_nonneg_left hsq hC.le
      _ = 4 * C * L ^ (21/10 : ℝ) := by rw [h2pow]; ring
  -- second term of the `max`
  have hA2 : C₅ + 1 / Work.BMF.twδ κ L u ≤ (C₅ + 8/κ) * L ^ (21/10 : ℝ) := by
    have hδpos : 0 < Work.BMF.twδ κ L u := Work.BMF.twδ_pos hκ
    have hinv : 1 / Work.BMF.twδ κ L u = 4 * Work.BMF.twD L u / κ := by
      rw [Work.BMF.twδ, one_div, inv_div]
    have hLpow : L ^ (11/12 : ℝ) ≤ L ^ (21/10 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    have h1 : 4 * Work.BMF.twD L u / κ ≤ 8 * L ^ (21/10 : ℝ) / κ := by
      have h3 : 4 * Work.BMF.twD L u ≤ 8 * L ^ (21/10 : ℝ) := by linarith
      exact div_le_div_of_nonneg_right h3 hκ.le
    have h4 : C₅ ≤ C₅ * L ^ (21/10 : ℝ) := by
      have hone : (1:ℝ) ≤ L ^ (21/10 : ℝ) := by
        have h := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num : (0:ℝ) ≤ 21/10)
        simpa using h
      nlinarith [hC₅]
    calc C₅ + 1 / Work.BMF.twδ κ L u = C₅ + 4 * Work.BMF.twD L u / κ := by rw [hinv]
      _ ≤ C₅ + 8 * L ^ (21/10 : ℝ) / κ := by linarith
      _ = C₅ + (8/κ) * L ^ (21/10 : ℝ) := by congr 1; ring
      _ ≤ C₅ * L ^ (21/10 : ℝ) + (8/κ) * L ^ (21/10 : ℝ) := by linarith
      _ = (C₅ + 8/κ) * L ^ (21/10 : ℝ) := by ring
  have hmax : max (C * (Real.log (2 * Work.BMF.twT L u + 3)) ^ 2) (C₅ + 1 / Work.BMF.twδ κ L u)
      ≤ (4 * C + C₅ + 8 / κ) * L ^ (21/10 : ℝ) := by
    have hA1nn : 0 ≤ C * (Real.log (2 * Work.BMF.twT L u + 3)) ^ 2 :=
      mul_nonneg hC.le (sq_nonneg _)
    have hA2nn : 0 ≤ C₅ + 1 / Work.BMF.twδ κ L u :=
      add_nonneg hC₅.le (div_nonneg zero_le_one (Work.BMF.twδ_pos hκ).le)
    have hm := max_le_add_of_nonneg hA1nn hA2nn
    linarith [hm, hA1, hA2]
  -- the `log^2` factor
  have hls : (Real.log (|u| + Work.BMF.twT L u + 3)) ^ 2 ≤ 4 * L ^ (21/10 : ℝ) := by
    have hle : |u| + Work.BMF.twT L u + 3 ≤ 2 * Work.BMF.twT L u + 3 := by
      have := Work.BMF.abs_lt_twT L u; linarith
    have hpos1 : 0 < |u| + Work.BMF.twT L u + 3 := by
      have := abs_nonneg u; have := Work.BMF.seven_le_twT L u; linarith
    have hpos2 : 0 < 2 * Work.BMF.twT L u + 3 := by
      have := Work.BMF.seven_le_twT L u; linarith
    have hlog_le : Real.log (|u| + Work.BMF.twT L u + 3)
        ≤ Real.log (2 * Work.BMF.twT L u + 3) := Real.log_le_log hpos1 hle
    have hnn : 0 ≤ Real.log (|u| + Work.BMF.twT L u + 3) :=
      Real.log_nonneg (by linarith [abs_nonneg u, Work.BMF.seven_le_twT L u])
    calc (Real.log (|u| + Work.BMF.twT L u + 3)) ^ 2
        ≤ (2 * L ^ (21/20 : ℝ)) ^ 2 := hsq_le hnn (le_trans hlog_le hlog2T)
      _ = 4 * L ^ (21/10 : ℝ) := h2pow
  -- `T ≤ 2 exp (L^{21/20})`
  have hTup : Work.BMF.twT L u ≤ 2 * Real.exp (L ^ (21/20 : ℝ)) := by
    have h1 : Work.BMF.twT L u
        ≤ Real.exp (L ^ (21/20 : ℝ)) + L^2 * Real.exp (L ^ (1/10 : ℝ)) + 7 := by
      rw [Work.BMF.twT]; linarith
    have h2 : L^2 * Real.exp (L ^ (1/10 : ℝ)) + 7 ≤ Real.exp (L ^ (21/20 : ℝ)) := by
      linarith
    linarith
  have hσ : (3/4 : ℝ) ≤ Work.BMF.twσ κ L u := by
    rw [Work.BMF.twσ]; linarith
  exact ⟨hmax, hls, hTup, hσ⟩

/-! ## numeric endgames -/

lemma ztw_num5 (K c : ℝ) (hK : 0 ≤ K) (hc : 0 < c) :
    ∀ᶠ L : ℝ in Filter.atTop,
      8 * (K * L ^ (21/10:ℝ)) * (4 * L ^ (21/10:ℝ))
        * ((5/4) / (L^2 * Real.exp (L ^ (1/10:ℝ))))
      ≤ (1/8) * Real.exp (-(c * L ^ (1/12:ℝ))) := by
  have h := ztw_rpow_le_exp_sub (320 * K) (11/5) 1 c (1/10) (1/12) 1
      (by positivity) one_pos hc.le (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  filter_upwards [h, eventually_gt_atTop (0:ℝ)] with L hL hLpos
  have hB : 320 * K * L ^ (11/5:ℝ) ≤ Real.exp (L ^ (1/10:ℝ) - c * L ^ (1/12:ℝ)) := by
    simpa using hL
  have hQ : 0 < L^2 * Real.exp (L^(1/10:ℝ)) := by positivity
  rw [← mul_div_assoc, div_le_iff₀ hQ]
  have hA : 8 * (K * L ^ (21/10:ℝ)) * (4 * L ^ (21/10:ℝ)) * (5/4)
      = 40 * K * L ^ (21/5:ℝ) := by
    have hPP : L ^ (21/10:ℝ) * L ^ (21/10:ℝ) = L ^ (21/5:ℝ) := by
      rw [← Real.rpow_add hLpos]; norm_num
    calc 8 * (K * L ^ (21/10:ℝ)) * (4 * L ^ (21/10:ℝ)) * (5/4)
        = 40 * K * (L ^ (21/10:ℝ) * L ^ (21/10:ℝ)) := by ring
      _ = 40 * K * L ^ (21/5:ℝ) := by rw [hPP]
  have hYQ : ((1/8) * Real.exp (-(c * L ^ (1/12:ℝ)))) * (L^2 * Real.exp (L ^ (1/10:ℝ)))
      = (1/8) * L^2 * Real.exp (L ^ (1/10:ℝ) - c * L ^ (1/12:ℝ)) := by
    calc ((1/8) * Real.exp (-(c * L ^ (1/12:ℝ)))) * (L^2 * Real.exp (L ^ (1/10:ℝ)))
        = (1/8) * L^2 * (Real.exp (-(c * L ^ (1/12:ℝ))) * Real.exp (L ^ (1/10:ℝ))) := by ring
      _ = (1/8) * L^2 * Real.exp (-(c * L ^ (1/12:ℝ)) + L ^ (1/10:ℝ)) := by rw [Real.exp_add]
      _ = (1/8) * L^2 * Real.exp (L ^ (1/10:ℝ) - c * L ^ (1/12:ℝ)) := by
            congr 1; ring
  have h3 : (1/8) * L^2 * (320 * K * L ^ (11/5:ℝ))
      ≤ (1/8) * L^2 * Real.exp (L ^ (1/10:ℝ) - c * L ^ (1/12:ℝ)) :=
    mul_le_mul_of_nonneg_left hB (by positivity)
  have h3' : 40 * K * L ^ (21/5:ℝ)
      ≤ (1/8) * L^2 * Real.exp (L ^ (1/10:ℝ) - c * L ^ (1/12:ℝ)) := by
    have heq : (1/8) * L^2 * (320 * K * L ^ (11/5:ℝ)) = 40 * K * L ^ (21/5:ℝ) := by
      have hP : L^2 * L ^ (11/5:ℝ) = L ^ (21/5:ℝ) := by
        rw [← Real.rpow_two, ← Real.rpow_add hLpos]; norm_num
      calc (1/8) * L^2 * (320 * K * L ^ (11/5:ℝ)) = 40 * K * (L^2 * L ^ (11/5:ℝ)) := by ring
        _ = 40 * K * L ^ (21/5:ℝ) := by rw [hP]
    linarith [h3, heq.le, heq.ge]
  rw [hA, hYQ]
  exact h3'

lemma ztw_num6 (K c : ℝ) (hK : 0 ≤ K) (hc : 0 < c) :
    ∀ᶠ L : ℝ in Filter.atTop,
      (4 * (K * L ^ (21/10:ℝ))) * (4 * L ^ (21/10:ℝ))
        * (4 * Real.sqrt 2 * L ^ (21/20:ℝ))
      ≤ (1/8) * Real.exp (c * L ^ (1/12:ℝ)) := by
  have h := ztw_rpow_le_exp_sub (512 * Real.sqrt 2 * K) (21/4) c 0 (1/12) (1/100) 1
      (by positivity) hc (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  filter_upwards [h, eventually_gt_atTop (0:ℝ)] with L hL hLpos
  have hB : 512 * Real.sqrt 2 * K * L ^ (21/4:ℝ) ≤ Real.exp (c * L ^ (1/12:ℝ)) := by
    simpa using hL
  have hPPQ : L ^ (21/10:ℝ) * L ^ (21/10:ℝ) * L ^ (21/20:ℝ) = L ^ (21/4:ℝ) := by
    rw [← Real.rpow_add hLpos, ← Real.rpow_add hLpos]
    norm_num
  have h8 : 8 * ((4 * (K * L ^ (21/10:ℝ))) * (4 * L ^ (21/10:ℝ))
      * (4 * Real.sqrt 2 * L ^ (21/20:ℝ)))
      = 512 * Real.sqrt 2 * K * L ^ (21/4:ℝ) := by
    calc 8 * ((4 * (K * L ^ (21/10:ℝ))) * (4 * L ^ (21/10:ℝ))
          * (4 * Real.sqrt 2 * L ^ (21/20:ℝ)))
        = 512 * Real.sqrt 2 * K * (L ^ (21/10:ℝ) * L ^ (21/10:ℝ) * L ^ (21/20:ℝ)) := by ring
      _ = 512 * Real.sqrt 2 * K * L ^ (21/4:ℝ) := by rw [hPPQ]
  have hmul := mul_le_mul_of_nonneg_left hB (by norm_num : (0:ℝ) ≤ 1/8)
  have hLHS : (4 * (K * L ^ (21/10:ℝ))) * (4 * L ^ (21/10:ℝ))
      * (4 * Real.sqrt 2 * L ^ (21/20:ℝ))
      = (1/8) * (512 * Real.sqrt 2 * K * L ^ (21/4:ℝ)) := by
    rw [← h8]; ring
  rw [hLHS]
  exact hmul

/-! ## the horizontal and left-edge conjuncts -/

lemma ztw_horizN7_own (κ C₅ C : ℝ) (hκ : 0 < κ) (hC₅ : 0 < C₅) (hC : 0 < C) :
    ∀ᶠ L : ℝ in Filter.atTop, ∀ u : ℝ, |u| ≤ Real.exp (L ^ (21 / 20 : ℝ)) →
      8 * (max (C * (Real.log (2 * Work.BMF.twT L u + 3)) ^ 2) (C₅ + 1 / Work.BMF.twδ κ L u)) *
          (Real.log (|u| + Work.BMF.twT L u + 3)) ^ 2 *
            ((Work.BMF.twδ κ L u + 1 / L) / Work.BMF.twT L u) ≤
        (1 / 8) * Real.exp (-((κ / 16) * L ^ (1 / 12 : ℝ))) := by
  have hK : 0 ≤ 4 * C + C₅ + 8 / κ := by positivity
  have hKc : 0 < κ / 16 := by positivity
  filter_upwards [ztw_pieces κ C₅ C hκ hC₅ hC, ztw_num5 (4 * C + C₅ + 8 / κ) (κ/16) hK hKc,
    eventually_ge_atTop (1:ℝ)] with L hP hnum hL1
  have hLpos : 0 < L := by linarith
  have hKnn : 0 ≤ (4 * C + C₅ + 8 / κ) * L ^ (21/10 : ℝ) :=
    mul_nonneg hK (Real.rpow_nonneg hLpos.le _)
  have h8Knn : 0 ≤ 8 * ((4 * C + C₅ + 8 / κ) * L ^ (21/10 : ℝ)) :=
    mul_nonneg (by norm_num) hKnn
  have h42nn : 0 ≤ (8 * ((4 * C + C₅ + 8 / κ) * L ^ (21/10 : ℝ))) * (4 * L ^ (21/10 : ℝ)) :=
    mul_nonneg h8Knn (mul_nonneg (by norm_num) (Real.rpow_nonneg hLpos.le _))
  intro u hu
  obtain ⟨hmax, hls, hTup, hσ⟩ := hP u hu
  have hTpos : 0 < Work.BMF.twT L u := Work.BMF.twT_pos L u
  have hδpos : 0 < Work.BMF.twδ κ L u := Work.BMF.twδ_pos hκ
  have hdel : Work.BMF.twδ κ L u ≤ 1/4 := by
    have h := hσ
    rw [Work.BMF.twσ] at h
    linarith
  have h1L : 1 / L ≤ 1 := by
    rw [div_le_iff₀ hLpos]
    linarith
  have hnum2 : Work.BMF.twδ κ L u + 1 / L ≤ 5/4 := by linarith
  have hδT : (Work.BMF.twδ κ L u + 1 / L) / Work.BMF.twT L u
      ≤ (5/4) / (L^2 * Real.exp (L ^ (1/10:ℝ))) := by
    have hQpos : 0 < L^2 * Real.exp (L ^ (1/10:ℝ)) := by positivity
    calc (Work.BMF.twδ κ L u + 1 / L) / Work.BMF.twT L u
        ≤ (5/4) / Work.BMF.twT L u := div_le_div_of_nonneg_right hnum2 hTpos.le
      _ ≤ (5/4) / (L^2 * Real.exp (L ^ (1/10:ℝ))) :=
          div_le_div_of_nonneg_left (by norm_num) hQpos (Work.BMF.le_twT L u)
  have hls_nn : 0 ≤ (Real.log (|u| + Work.BMF.twT L u + 3)) ^ 2 := sq_nonneg _
  have hlast_nn : 0 ≤ (Work.BMF.twδ κ L u + 1 / L) / Work.BMF.twT L u :=
    div_nonneg (add_nonneg hδpos.le (div_nonneg zero_le_one hLpos.le)) hTpos.le
  have step1 : 8 * max (C * (Real.log (2 * Work.BMF.twT L u + 3)) ^ 2)
        (C₅ + 1 / Work.BMF.twδ κ L u)
      ≤ 8 * ((4 * C + C₅ + 8 / κ) * L ^ (21/10 : ℝ)) :=
    mul_le_mul_of_nonneg_left hmax (by norm_num)
  have step2 : 8 * max (C * (Real.log (2 * Work.BMF.twT L u + 3)) ^ 2)
        (C₅ + 1 / Work.BMF.twδ κ L u) * (Real.log (|u| + Work.BMF.twT L u + 3)) ^ 2
      ≤ (8 * ((4 * C + C₅ + 8 / κ) * L ^ (21/10 : ℝ))) * (4 * L ^ (21/10 : ℝ)) :=
    mul_le_mul step1 hls hls_nn h8Knn
  have step3 : 8 * max (C * (Real.log (2 * Work.BMF.twT L u + 3)) ^ 2)
        (C₅ + 1 / Work.BMF.twδ κ L u) * (Real.log (|u| + Work.BMF.twT L u + 3)) ^ 2
        * ((Work.BMF.twδ κ L u + 1 / L) / Work.BMF.twT L u)
      ≤ ((8 * ((4 * C + C₅ + 8 / κ) * L ^ (21/10 : ℝ))) * (4 * L ^ (21/10 : ℝ)))
        * ((5/4) / (L^2 * Real.exp (L ^ (1/10:ℝ)))) :=
    mul_le_mul step2 hδT hlast_nn h42nn
  exact le_trans step3 hnum

lemma ztw_leftN7_own (κ C₅ C : ℝ) (hκ : 0 < κ) (hC₅ : 0 < C₅) (hC : 0 < C) :
    ∀ᶠ L : ℝ in Filter.atTop, ∀ u : ℝ, |u| ≤ Real.exp (L ^ (21 / 20 : ℝ)) →
      4 * (max (C * (Real.log (2 * Work.BMF.twT L u + 3)) ^ 2) (C₅ + 1 / Work.BMF.twδ κ L u)) *
          (Real.log (|u| + Work.BMF.twT L u + 3)) ^ 2 *
          (2 * Real.sqrt 2 * Real.log (1 + Work.BMF.twT L u / Work.BMF.twσ κ L u)) ≤
        (1 / 8) * Real.exp ((κ / 16) * L ^ (1 / 12 : ℝ)) := by
  have hK : 0 ≤ 4 * C + C₅ + 8 / κ := by positivity
  have hKc : 0 < κ / 16 := by positivity
  filter_upwards [ztw_pieces κ C₅ C hκ hC₅ hC, ztw_eventually_log4,
    ztw_num6 (4 * C + C₅ + 8 / κ) (κ/16) hK hKc, eventually_ge_atTop (0:ℝ)] with L hP hlog4 hnum hL0
  have hKnn : 0 ≤ (4 * C + C₅ + 8 / κ) * L ^ (21/10 : ℝ) :=
    mul_nonneg hK (Real.rpow_nonneg hL0 _)
  have h4Knn : 0 ≤ 4 * ((4 * C + C₅ + 8 / κ) * L ^ (21/10 : ℝ)) :=
    mul_nonneg (by norm_num) hKnn
  have h44nn : 0 ≤ (4 * ((4 * C + C₅ + 8 / κ) * L ^ (21/10 : ℝ))) * (4 * L ^ (21/10 : ℝ)) :=
    mul_nonneg h4Knn (mul_nonneg (by norm_num) (Real.rpow_nonneg hL0 _))
  intro u hu
  obtain ⟨hmax, hls, hTup, hσ⟩ := hP u hu
  have hTpos : 0 < Work.BMF.twT L u := Work.BMF.twT_pos L u
  have hσpos : 0 < Work.BMF.twσ κ L u := by linarith
  have hTσ_nn : 0 ≤ Work.BMF.twT L u / Work.BMF.twσ κ L u := div_nonneg hTpos.le hσpos.le
  have hlogTσ : Real.log (1 + Work.BMF.twT L u / Work.BMF.twσ κ L u)
      ≤ 2 * L ^ (21/20 : ℝ) := by
    have h1 : Work.BMF.twT L u / Work.BMF.twσ κ L u ≤ (4/3) * Work.BMF.twT L u := by
      rw [div_le_iff₀ hσpos]
      nlinarith [hσ, hTpos]
    have hE1 : (1:ℝ) ≤ Real.exp (L ^ (21/20 : ℝ)) := by
      rw [← Real.exp_zero, Real.exp_le_exp]
      exact Real.rpow_nonneg hL0 _
    have h2 : 1 + (4/3) * Work.BMF.twT L u ≤ 4 * Real.exp (L ^ (21/20 : ℝ)) := by
      linarith
    have harg : 1 + Work.BMF.twT L u / Work.BMF.twσ κ L u ≤ 4 * Real.exp (L ^ (21/20 : ℝ)) := by
      linarith
    have hargpos : 0 < 1 + Work.BMF.twT L u / Work.BMF.twσ κ L u := by linarith
    calc Real.log (1 + Work.BMF.twT L u / Work.BMF.twσ κ L u)
        ≤ Real.log (4 * Real.exp (L ^ (21/20 : ℝ))) := Real.log_le_log hargpos harg
      _ = Real.log 4 + L ^ (21/20 : ℝ) := by
            rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp]
      _ ≤ 2 * L ^ (21/20 : ℝ) := by linarith
  have hlogTσ_nn : 0 ≤ Real.log (1 + Work.BMF.twT L u / Work.BMF.twσ κ L u) := by
    apply Real.log_nonneg
    linarith
  have hll : 2 * Real.sqrt 2 * Real.log (1 + Work.BMF.twT L u / Work.BMF.twσ κ L u)
      ≤ 4 * Real.sqrt 2 * L ^ (21/20 : ℝ) := by
    have h : 2 * Real.sqrt 2 * Real.log (1 + Work.BMF.twT L u / Work.BMF.twσ κ L u)
        ≤ 2 * Real.sqrt 2 * (2 * L ^ (21/20 : ℝ)) :=
      mul_le_mul_of_nonneg_left hlogTσ (mul_nonneg (by norm_num) (Real.sqrt_nonneg 2))
    linarith [h]
  have hls_nn : 0 ≤ (Real.log (|u| + Work.BMF.twT L u + 3)) ^ 2 := sq_nonneg _
  have hll_nn : 0 ≤ 2 * Real.sqrt 2 * Real.log (1 + Work.BMF.twT L u / Work.BMF.twσ κ L u) :=
    mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg 2)) hlogTσ_nn
  have step1 : 4 * max (C * (Real.log (2 * Work.BMF.twT L u + 3)) ^ 2)
        (C₅ + 1 / Work.BMF.twδ κ L u)
      ≤ 4 * ((4 * C + C₅ + 8 / κ) * L ^ (21/10 : ℝ)) :=
    mul_le_mul_of_nonneg_left hmax (by norm_num)
  have step2 : 4 * max (C * (Real.log (2 * Work.BMF.twT L u + 3)) ^ 2)
        (C₅ + 1 / Work.BMF.twδ κ L u) * (Real.log (|u| + Work.BMF.twT L u + 3)) ^ 2
      ≤ (4 * ((4 * C + C₅ + 8 / κ) * L ^ (21/10 : ℝ))) * (4 * L ^ (21/10 : ℝ)) :=
    mul_le_mul step1 hls hls_nn h4Knn
  have step3 : 4 * max (C * (Real.log (2 * Work.BMF.twT L u + 3)) ^ 2)
        (C₅ + 1 / Work.BMF.twδ κ L u) * (Real.log (|u| + Work.BMF.twT L u + 3)) ^ 2
        * (2 * Real.sqrt 2 * Real.log (1 + Work.BMF.twT L u / Work.BMF.twσ κ L u))
      ≤ ((4 * ((4 * C + C₅ + 8 / κ) * L ^ (21/10 : ℝ))) * (4 * L ^ (21/10 : ℝ)))
        * (4 * Real.sqrt 2 * L ^ (21/20 : ℝ)) :=
    mul_le_mul step2 hll hll_nn h44nn
  exact le_trans step3 hnum

/-! ## The target: the full parameter package -/

/-- **The eventual parameter package of the `6/7`-shaped twisted Perron argument**
(same statement as `Work.BMF.ztw_param` in `Submission/Work/BMF/ztw_param.lean`, which is a dead
link — silent owner for four hours — and blocks node V6 `zeta_prime_sum_twist`, hence N10 and N7).

For every `L` large enough and every `u` with `|u| ≤ exp(L^{21/20})`, writing `T = twT L u`,
`D = twD L u = ztD (2T)` and `δ = twδ κ L u = κ/(4D)`:
`log(2T+3) ≤ 2 L^{21/20}`; `D ≤ 2 L^{11/12}`; `δ ≤ min δ₅ (1/4)`; the truncation term is small;
and the horizontal- and left-edge factors are dominated by `exp(∓(κ/16)L^{1/12})`.

All six conjuncts are *eventual* estimates as `L → ∞`, uniform in `u` in the range
`|u| ≤ exp(L^{21/20})`.  Since `twT L u = |u| + L²exp(L^{1/10}) + 7`, one has
`L²exp(L^{1/10}) + 7 ≤ T ≤ exp(L^{21/20}) + L²exp(L^{1/10}) + 7`; the lower bound drives the
truncation conjunct and the upper bound drives the logarithms of the last two.  To prove the sixth
conjunct, `twσ κ L u = 1 - twδ κ L u ≥ 3/4 > 0` is available from the third conjunct.
The elementary helpers in `Submission/Work/BMF/ztw_defs.lean` (`seven_le_twT`, `abs_lt_twT`,
`twT_pos`, `le_twT`, `twD_pos`, `twδ_pos`, `ztD_pos`, `ztD_le_of_log_le`, `one_le_log_three`) are
available; the remaining work is only the asymptotic calculus of `log`, `exp` and `rpow` at
`L → ∞` (e.g. `Filter.eventually_atTop`, `Real.log_le_log`, `Real.rpow_le_rpow`,
`Real.exp_le_exp`, `Real.log_mul`, `div_le_div_of_nonneg_right`, `nlinarith`). -/
theorem ztw_paramN7 (κ δ₅ C₅ C Ctr : ℝ) (hκ : 0 < κ) (hδ₅ : 0 < δ₅) (hC₅ : 0 < C₅)
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
  filter_upwards [ztw_conj1, ztw_conj2, ztw_conj3 κ δ₅ hκ hδ₅, ztw_truncN7 κ Ctr hκ hCtr,
    ztw_horizN7_own κ C₅ C hκ hC₅ hC, ztw_leftN7_own κ C₅ C hκ hC₅ hC] with L h1 h2 h3 h4 h5 h6
  intro u hu
  exact ⟨h1 u hu, h2 u hu, h3 u, h4 u hu, h5 u hu, h6 u hu⟩

end

end Work.BMF.N7
