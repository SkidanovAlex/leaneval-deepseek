import Mathlib
import Submission.Work.BMF.VKdenom
import Submission.Work.BMF.liouville.zeta_tw_perron
import Submission.Work.BMF.liouville.zeta_tw_vk_sum
import Submission.Work.BMF.liouville.zetaTwVKdefs
import Submission.Work.BMF.liouville.zetaTwParam_bounds_proved
import Submission.Work.BMF.liouville.zetaTwLeft_near_far_le
import Submission.Work.BMF.liouville.zetaTwSum_small_x
import Submission.Work.BMF.liouville.cpow_one_sub_I_mul_sub_le
import Submission.Work.BMF.liouville.zeta_logDeriv_near_four
import Submission.Work.BMF.liouville.zetaTwTrunc_absorb
import Submission.Work.BMF.liouville.zetaTwTopEdge_absorb
import Submission.Work.BMF.liouville.zetaTwLeftEdge_absorb

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 0

namespace Work.BMF.liouville

open Complex MeasureTheory Filter
open scoped Real Interval Topology

noncomputable section

/-- `(exp L)^(1/L) = exp 1` for `L > 0`. -/
lemma exp_rpow_inv_self {L : ℝ} (hL : 0 < L) : (Real.exp L) ^ (1 / L) = Real.exp 1 := by
  rw [Real.rpow_def_of_pos (Real.exp_pos L), Real.log_exp, mul_one_div, div_self (ne_of_gt hL)]

/-- For `3 ≤ x ≤ X`, `exp (cf * (log x)^{1/10}) ≤ exp (cf * (log X)^{1/10})`. -/
lemma exp_cf_log_mono {cf x X : ℝ} (hcf : 0 ≤ cf) (h3 : 3 ≤ x) (hxX : x ≤ X) :
    Real.exp (cf * x.log ^ (1 / 10 : ℝ)) ≤ Real.exp (cf * X.log ^ (1 / 10 : ℝ)) := by
  refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ hcf)
  exact Real.rpow_le_rpow (Real.log_pos (by linarith)).le
    (Real.log_le_log (by linarith) hxX) (by norm_num)

/-- Eventually, any fixed polynomial factor in `L` is dominated by `exp (δ L^{1/10})`.
(`L^a = o (exp (δ L^{1/10}))` by `isLittleO_rpow_exp_pos_mul_atTop`, and multiplying by
`K + 1` gives `(K+1) L^a ≤ exp (δ L^{1/10})`, hence `K L^a ≤ exp (δ L^{1/10})`.) -/
lemma zt_eventually_rpow_le_exp (K a δ : ℝ) (hK : 0 ≤ K) (hδ : 0 < δ) :
    ∀ᶠ L in Filter.atTop, K * L ^ a ≤ Real.exp (δ * L ^ (1 / 10 : ℝ)) := by
  have h1 : (fun L : ℝ => L ^ a) =o[Filter.atTop]
      (fun L : ℝ => Real.exp (δ * L ^ (1 / 10 : ℝ))) := by
    have h2 : (fun L : ℝ => (L ^ (1 / 10 : ℝ)) ^ (10 * a)) =o[Filter.atTop]
        (fun L : ℝ => Real.exp (δ * L ^ (1 / 10 : ℝ))) :=
      (isLittleO_rpow_exp_pos_mul_atTop (10 * a) hδ).comp_tendsto
        (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 10 by norm_num))
    refine h2.congr' ?_ Filter.EventuallyEq.rfl
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with L hL
    rw [← Real.rpow_mul hL]
    congr 1
    ring
  have h1' := h1.const_mul_left (K + 1)
  filter_upwards [h1'.eventuallyLE, Filter.eventually_ge_atTop (0 : ℝ)] with L hL hL0
  rw [Real.norm_of_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg hL0 a)),
    Real.norm_of_nonneg (Real.exp_pos _).le] at hL
  nlinarith [hL, hK, Real.rpow_nonneg hL0 a]

/-- `L ≤ exp L * exp (-(c L^{1/10}))` eventually, for `c > 0`
(i.e. `L ≤ exp (L - c L^{1/10})`). -/
lemma zt_eventually_le_exp_mul (c : ℝ) (hc : 0 < c) :
    ∀ᶠ L in Filter.atTop, L ≤ Real.exp L * Real.exp (-(c * L ^ (1 / 10 : ℝ))) := by
  have h1 : ∀ᶠ L in Filter.atTop, L ≤ Real.exp ((1 / 2) * L) := by
    have h := isLittleO_rpow_exp_pos_mul_atTop 1 (show (0 : ℝ) < 1 / 2 by norm_num)
    filter_upwards [h.eventuallyLE, Filter.eventually_ge_atTop (0 : ℝ)] with L hL hL0
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hL0 1),
      Real.norm_of_nonneg (Real.exp_pos _).le, Real.rpow_one] at hL
    exact hL
  have h2 : ∀ᶠ L in Filter.atTop, c * L ^ (1 / 10 : ℝ) ≤ (1 / 2) * L := by
    have h3 : ∀ᶠ L in Filter.atTop, 2 * c ≤ L ^ (9 / 10 : ℝ) :=
      (tendsto_rpow_atTop (show (0 : ℝ) < 9 / 10 by norm_num)).eventually_ge_atTop (2 * c)
    filter_upwards [h3, Filter.eventually_gt_atTop (0 : ℝ)] with L hL hL0
    have hp : 0 < L ^ (1 / 10 : ℝ) := Real.rpow_pos_of_pos hL0 _
    have hmul : (2 * c) * L ^ (1 / 10 : ℝ) ≤ L ^ (9 / 10 : ℝ) * L ^ (1 / 10 : ℝ) :=
      mul_le_mul_of_nonneg_right hL hp.le
    have hsp : L ^ (9 / 10 : ℝ) * L ^ (1 / 10 : ℝ) = L := by
      rw [← Real.rpow_add hL0, show (9 : ℝ) / 10 + 1 / 10 = 1 by norm_num, Real.rpow_one]
    rw [hsp] at hmul
    linarith
  filter_upwards [h1, h2] with L hL1 hL2
  have hA : (1 / 2) * L ≤ L + -(c * L ^ (1 / 10 : ℝ)) := by linarith
  calc L ≤ Real.exp ((1 / 2) * L) := hL1
    _ ≤ Real.exp (L + -(c * L ^ (1 / 10 : ℝ))) := Real.exp_le_exp.mpr hA
    _ = Real.exp L * Real.exp (-(c * L ^ (1 / 10 : ℝ))) := by rw [Real.exp_add]

/-- The engine of `zetaTwSum_sub_main_le`: the twisted Vinogradov–Korobov prime number
theorem for the principal character, in the form needed by the final assembly. -/
theorem zetaTwSum_engine (c₁ c₂ B C₅ δ₅ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hB : 0 < B)
    (hC₅ : 0 < C₅) (hδ₅ : 0 < δ₅)
    (hreg : ∀ t σ : ℝ, 3 ≤ |t| → 1 - c₁ / Work.BMF.VKd (|t| + 3) ≤ σ → σ ≤ 1 →
      riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0)
    (hlog : ∀ t σ : ℝ, 3 ≤ |t| → 1 - c₂ / Work.BMF.VKd (|t| + 3) ≤ σ → σ ≤ 2 →
      ‖deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) /
        riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ B * (Real.log (|t| + 3)) ^ 2)
    (hnearld : ∀ t σ : ℝ, |t| ≤ 4 → σ ≠ 1 → 1 - δ₅ ≤ σ → σ ≤ 2 →
      ‖deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) /
        riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        C₅ + 1 / ‖((σ : ℂ) + (t : ℂ) * Complex.I) - 1‖)
    (hneazz : ∀ t σ : ℝ, |t| ≤ 4 → 1 - δ₅ ≤ σ → σ ≤ 2 →
      riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0)
    (hrect : ∀ u x T σ₁ : ℝ, 1 < x → 0 < T → 0 < σ₁ → σ₁ < 1 →
      σ₁ < 1 + 1 / Real.log x → |u| < T →
      (∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ 1 + 1 / Real.log x → |s.im - u| ≤ T → s ≠ 1 →
        riemannZeta s ≠ 0) →
      zetaTwPerron u x T =
        (x : ℂ) ^ (1 - Complex.I * (u : ℂ)) / (1 - Complex.I * (u : ℂ))
          + zetaTwTop u x T σ₁ - zetaTwBot u x T σ₁ + zetaTwLeft u x T σ₁) :
    ∃ N0 C : ℝ, 0 < C ∧ ∀ y : ℝ, N0 ≤ y → (∀ n : ℕ, (n : ℝ) ≠ y) → ∀ u : ℝ,
      |u| ≤ Real.exp ((Real.log y) ^ (5 / 4 : ℝ)) →
      ‖zetaTwSum u y - (y : ℂ) ^ (1 - Complex.I * (u : ℂ)) / (1 - Complex.I * (u : ℂ))‖
        ≤ C * y * Real.exp (-(ztC c₁ c₂ / 16) * (Real.log y) ^ (1 / 10 : ℝ)) := by
  obtain ⟨C1, hC1pos, htrunc⟩ := Work.BMF.liouville.zetaTwPerron_sub_sum
  set c : ℝ := ztC c₁ c₂ with hcdef
  have hc : 0 < c := by rw [hcdef]; exact ztC_pos hc₁ hc₂
  have hc_le_c1 : c ≤ c₁ := by rw [hcdef]; exact ztC_le_left c₁ c₂
  have hc_le_c2 : c ≤ c₂ := by rw [hcdef]; exact ztC_le_right c₁ c₂
  have hc_le_1 : c ≤ 1 := by rw [hcdef]; exact ztC_le_one c₁ c₂
  have hc8 : c ≤ 8 := by linarith
  have hε : 0 < c / 16 := by positivity
  have hc8pos : 0 < c / 8 := by positivity
  have hη : 0 < min δ₅ (1 / 2 : ℝ) := lt_min hδ₅ (by norm_num)
  obtain ⟨hPb1, hPb2⟩ := zetaTwParam_bounds_proved c₁ c₂
  set KK : ℝ := 96 * Real.sqrt 2 * (B + C₅ + 1 + 4 / c) + 32 * Real.exp 1 * B + 8 * C1 + 4
    with hKKdef
  have hbr : 0 ≤ B + C₅ + 1 + 4 / c := by
    have h4 : 0 ≤ 4 / c := by positivity
    linarith [hB.le, hC₅.le]
  have hKKa : 0 ≤ 96 * Real.sqrt 2 * (B + C₅ + 1 + 4 / c) := mul_nonneg (by positivity) hbr
  have hKKb : 0 ≤ 32 * Real.exp 1 * B := by positivity
  have hKKc : 0 ≤ 8 * C1 := by linarith [hC1pos.le]
  have hKKnonneg : 0 ≤ KK := by rw [hKKdef]; linarith
  have hKK1 : 8 * C1 ≤ KK := by rw [hKKdef]; linarith
  have hKK2 : 32 * Real.exp 1 * B ≤ KK := by rw [hKKdef]; linarith
  have hKK3 : 96 * Real.sqrt 2 * (B + C₅ + 1 + 4 / c) ≤ KK := by rw [hKKdef]; linarith
  have habs : ∀ᶠ L in Filter.atTop,
      KK * L ^ (10 : ℝ) ≤ Real.exp ((c / 16) * L ^ (1 / 10 : ℝ)) :=
    zt_eventually_rpow_le_exp KK 10 (c / 16) hKKnonneg hε
  have hLyall : ∀ᶠ L in Filter.atTop,
      L ≤ Real.exp L * Real.exp (-((c / 8) * L ^ (1 / 10 : ℝ))) :=
    zt_eventually_le_exp_mul (c / 8) hc8pos
  have hAll : ∀ᶠ L in Filter.atTop,
      (∀ u : ℝ, |u| ≤ Real.exp (L ^ (5 / 4 : ℝ)) →
        ztC c₁ c₂ / (4 * ztV L u) ≤ min δ₅ (1 / 2)) ∧
      (∀ u : ℝ, |u| ≤ Real.exp (L ^ (5 / 4 : ℝ)) →
        0 < ztT L u ∧ |u| < ztT L u ∧ 0 < ztV L u ∧ ztV L u ≤ L ^ (9 / 10 : ℝ) ∧
        Real.log (2 * ztT L u + 3) ≤ 2 * L ^ (5 / 4 : ℝ) ∧
        Real.log (|u| + ztT L u + 3) ≤ 2 * L ^ (5 / 4 : ℝ)) ∧
      KK * L ^ (10 : ℝ) ≤ Real.exp ((ztC c₁ c₂ / 16) * L ^ (1 / 10 : ℝ)) ∧
      L ≤ Real.exp L * Real.exp (-((c / 8) * L ^ (1 / 10 : ℝ))) :=
    (hPb1 _ hη).and (hPb2.and (habs.and hLyall))
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp hAll
  refine ⟨Real.exp (max 3 (max 1 N₁)) + 3, 1, one_pos, ?_⟩
  intro y hy hynat u hu
  have hy3 : 3 ≤ y := by
    have := Real.exp_pos (max 3 (max 1 N₁))
    linarith
  have hy1 : 1 < y := by linarith
  have hypos : 0 < y := by linarith
  have hLge : N₁ ≤ Real.log y := by
    have h2 : Real.exp (max 3 (max 1 N₁)) ≤ y := by linarith [hy]
    have h3 : max 3 (max 1 N₁) ≤ Real.log y := (Real.le_log_iff_exp_le hypos).mpr h2
    exact le_trans (le_trans (le_max_right (1 : ℝ) N₁) (le_max_right 3 (max 1 N₁))) h3
  have hLpos : 0 < Real.log y := Real.log_pos hy1
  have hL1 : 1 ≤ Real.log y := by
    have h2 : Real.exp (max 3 (max 1 N₁)) ≤ y := by linarith [hy]
    have h3 : max 3 (max 1 N₁) ≤ Real.log y := (Real.le_log_iff_exp_le hypos).mpr h2
    linarith [le_max_left (3 : ℝ) (max 1 N₁), h3]
  obtain ⟨hA, hBp, hC, hLy⟩ := hN₁ (Real.log y) hLge
  obtain ⟨hTpos0, huT0, hVpos0, hVle0, hlogT0, hloguT0⟩ := hBp u hu
  have hyexp : Real.exp (Real.log y) = y := Real.exp_log hypos
  set T : ℝ := ztT (Real.log y) u with hTdef
  set V : ℝ := ztV (Real.log y) u with hVdef
  set σ₁ : ℝ := ztS c₁ c₂ (Real.log y) u with hσdef
  have hTpos : 0 < T := by rw [hTdef]; exact hTpos0
  have huT : |u| < T := by rw [hTdef]; exact huT0
  have hVpos : 0 < V := by rw [hVdef]; exact hVpos0
  have hVle : V ≤ (Real.log y) ^ (9 / 10 : ℝ) := by rw [hVdef]; exact hVle0
  have hlogT : Real.log (2 * T + 3) ≤ 2 * (Real.log y) ^ (5 / 4 : ℝ) := by
    rw [hTdef]; exact hlogT0
  have hloguT : Real.log (|u| + T + 3) ≤ 2 * (Real.log y) ^ (5 / 4 : ℝ) := by
    rw [hTdef]; exact hloguT0
  have hA' : c / (4 * V) ≤ min δ₅ (1 / 2) := by
    rw [hcdef, hVdef]; exact hA u hu
  have hC' : KK * (Real.log y) ^ (10 : ℝ) ≤ Real.exp ((c / 16) * (Real.log y) ^ (1 / 10 : ℝ)) := by
    rw [hcdef]; exact hC
  have hLy0 : Real.log y ≤ y * Real.exp (-((c / 8) * (Real.log y) ^ (1 / 10 : ℝ))) := by
    rw [hyexp] at hLy; exact hLy
  have hLy' : Real.log y ≤ y * Real.exp (-(c / 8) * (Real.log y) ^ (1 / 10 : ℝ)) := by
    rw [show -((c / 8) * (Real.log y) ^ (1 / 10 : ℝ)) = -(c / 8) * (Real.log y) ^ (1 / 10 : ℝ)
      by ring] at hLy0
    exact hLy0
  have hTge : (Real.log y) ^ 2 * ztE (Real.log y) ≤ T := by
    rw [hTdef, ztT]; have := abs_nonneg u; linarith
  have hσ₁eq : 1 - σ₁ = c / (4 * V) := by
    simp only [hσdef, hcdef, hVdef, ztS]; ring
  have hσ₁pos : 0 < σ₁ := by
    have h1 : c / (4 * V) ≤ 1 / 2 := le_trans hA' (min_le_right _ _)
    linarith
  have hσ₁lt : σ₁ < 1 := by
    have h1 : 0 < c / (4 * V) := by positivity
    linarith
  have hσ₁δ : 1 - δ₅ ≤ σ₁ := by
    have h1 : c / (4 * V) ≤ δ₅ := le_trans hA' (min_le_left _ _)
    linarith
  have hσ₁half : 1 / 2 ≤ σ₁ := by
    have h1 : c / (4 * V) ≤ 1 / 2 := le_trans hA' (min_le_right _ _)
    linarith
  have hσ₁le : σ₁ < 1 + 1 / Real.log y := by
    have h1 : 0 < 1 / Real.log y := by positivity
    linarith
  have hVK_le : ∀ t : ℝ, 3 ≤ |t| → |t| ≤ 2 * T → Work.BMF.VKd (|t| + 3) ≤ V := by
    intro t ht htT
    rw [hVdef]
    refine Work.BMF.VKd_mono (by linarith) ?_
    linarith [htT, hTpos]
  have hlog_at : ∀ t σ : ℝ, 3 ≤ |t| → |t| ≤ 2 * T → σ₁ ≤ σ → σ ≤ 2 →
      ‖deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) /
        riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ B * (Real.log (|t| + 3)) ^ 2 := by
    intro t σ ht3 htT hσ1 hσ2
    have hVK : Work.BMF.VKd (|t| + 3) ≤ V := hVK_le t ht3 htT
    have hVKpos : 0 < Work.BMF.VKd (|t| + 3) := Work.BMF.VKd_pos (by linarith)
    have hdiv : c / (4 * V) ≤ c₂ / Work.BMF.VKd (|t| + 3) := by
      rw [div_le_div_iff₀ (by positivity) hVKpos]
      have h1 : c * Work.BMF.VKd (|t| + 3) ≤ (4 * c₂) * V :=
        mul_le_mul (by linarith : c ≤ 4 * c₂) hVK (Work.BMF.VKd_nonneg (by linarith))
          (by positivity)
      linarith
    have hσ : 1 - c₂ / Work.BMF.VKd (|t| + 3) ≤ σ := by linarith
    exact hlog t σ ht3 hσ hσ2
  -- ** the zero-free region on the contour
  have hZ : ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ 1 + 1 / Real.log y → |s.im - u| ≤ T → s ≠ 1 →
      riemannZeta s ≠ 0 := by
    intro s hs1 hs2 hsim hsne hzero
    have htabs : |s.im| ≤ 2 * T := by
      have h1 : |s.im| ≤ |s.im - u| + |u| := by
        have := abs_sub_abs_le_abs_sub s.im u
        linarith [abs_nonneg u]
      linarith [hsim, huT]
    have hseq : ((s.re : ℂ) + (s.im : ℂ) * Complex.I) = s := Complex.re_add_im s
    by_cases hre : 1 ≤ s.re
    · exact riemannZeta_ne_zero_of_one_le_re hre hzero
    · push_neg at hre
      by_cases h3 : 3 ≤ |s.im|
      · have hVK : Work.BMF.VKd (|s.im| + 3) ≤ V := hVK_le s.im h3 htabs
        have hVKpos : 0 < Work.BMF.VKd (|s.im| + 3) := Work.BMF.VKd_pos (by linarith)
        have hineq : c / (4 * V) ≤ c₁ / Work.BMF.VKd (|s.im| + 3) := by
          rw [div_le_div_iff₀ (by positivity) hVKpos]
          have h1 : c * Work.BMF.VKd (|s.im| + 3) ≤ (4 * c₁) * V :=
            mul_le_mul (by linarith : c ≤ 4 * c₁) hVK (Work.BMF.VKd_nonneg (by linarith))
              (by positivity)
          linarith
        have hσ : 1 - c₁ / Work.BMF.VKd (|s.im| + 3) ≤ s.re := by linarith
        have hz := hreg s.im s.re h3 hσ (le_of_lt hre)
        exact hz (by rw [hseq]; exact hzero)
      · push_neg at h3
        have hz := hneazz s.im s.re (by linarith) (by linarith) (by linarith)
        exact hz (by rw [hseq]; exact hzero)
  -- ** parameter facts for the edges
  have hTpos7 : (Real.log y) ^ 2 * ztE (Real.log y) + 7 ≤ T := by
    rw [hTdef, ztT]; linarith [abs_nonneg u]
  have hL2E1 : 1 ≤ (Real.log y) ^ 2 * ztE (Real.log y) := by
    have hzt : 1 ≤ ztE (Real.log y) := by
      rw [ztE]
      exact Real.one_le_exp_iff.mpr (Real.rpow_nonneg hLpos.le _)
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hL1) hzt
  have hTlo : 3 ≤ T := by linarith [hTpos7, hL2E1]
  have hTdu3 : 3 ≤ T - |u| := by rw [hTdef, ztT]; linarith [hL2E1]
  have hTu : 3 ≤ |T + u| := by
    have h3 : 3 ≤ T + u := by linarith [neg_abs_le u, hTdu3]
    rw [abs_of_pos (by linarith : (0 : ℝ) < T + u)]
    exact h3
  have hmu : 3 ≤ |-T + u| := by
    have h3 : 3 ≤ T - u := by linarith [le_abs_self u, hTdu3]
    have h2 : 0 < T - u := by linarith
    rw [show -T + u = -(T - u) by ring, abs_neg, abs_of_pos h2]
    exact h3
  have hTu2 : |T + u| ≤ 2 * T := by
    have h4 : T + u ≤ 2 * T := by linarith [le_abs_self u, huT]
    rw [abs_of_pos (by linarith [neg_abs_le u, huT, hTlo] : (0 : ℝ) < T + u)]
    exact h4
  have hmu2 : |-T + u| ≤ 2 * T := by
    have h4 : T - u ≤ 2 * T := by linarith [neg_abs_le u, huT]
    have h2 : 0 < T - u := by linarith [le_abs_self u, huT]
    rw [show -T + u = -(T - u) by ring, abs_neg, abs_of_pos h2]
    exact h4
  have hv2 : 1 + 1 / Real.log y ≤ 2 := by
    have h : 1 / Real.log y ≤ 1 := by rw [div_le_one hLpos]; linarith
    linarith
  -- ** the contour shift
  have hmain_eq := hrect u y T σ₁ hy1 hTpos hσ₁pos hσ₁lt hσ₁le huT hZ
  have htr := htrunc u y T hy3 hynat (by linarith : 2 ≤ T)
  -- ** edge data
  have hDtop : ∀ v : ℝ, σ₁ ≤ v → v ≤ 1 + 1 / Real.log y →
      ‖deriv riemannZeta ((v : ℂ) + ((T + u : ℝ) : ℂ) * Complex.I) /
        riemannZeta ((v : ℂ) + ((T + u : ℝ) : ℂ) * Complex.I)‖ ≤
        B * (Real.log (|T + u| + 3)) ^ 2 := by
    intro v hv1 hv2'
    exact hlog_at (T + u) v hTu hTu2 hv1 (le_trans hv2' hv2)
  have hDbot : ∀ v : ℝ, σ₁ ≤ v → v ≤ 1 + 1 / Real.log y →
      ‖deriv riemannZeta ((v : ℂ) + ((-T + u : ℝ) : ℂ) * Complex.I) /
        riemannZeta ((v : ℂ) + ((-T + u : ℝ) : ℂ) * Complex.I)‖ ≤
        B * (Real.log (|-T + u| + 3)) ^ 2 := by
    intro v hv1 hv2'
    exact hlog_at (-T + u) v hmu hmu2 hv1 (le_trans hv2' hv2)
  have hDfar : ∀ t : ℝ, |t| ≤ T → 3 ≤ |t + u| →
      ‖deriv riemannZeta ((σ₁ : ℂ) + ((t + u : ℝ) : ℂ) * Complex.I) /
        riemannZeta ((σ₁ : ℂ) + ((t + u : ℝ) : ℂ) * Complex.I)‖
        ≤ B * (Real.log (|t + u| + 3)) ^ 2 := by
    intro t ht h3
    have ht2 : |t + u| ≤ 2 * T := by
      have h1 : |t + u| ≤ |t| + |u| := abs_add_le t u
      linarith [huT]
    exact hlog_at (t + u) σ₁ h3 ht2 le_rfl (by linarith)
  have hDnear : ∀ t : ℝ, |t + u| ≤ 4 →
      ‖deriv riemannZeta ((σ₁ : ℂ) + ((t + u : ℝ) : ℂ) * Complex.I) /
        riemannZeta ((σ₁ : ℂ) + ((t + u : ℝ) : ℂ) * Complex.I)‖ ≤
        C₅ + 1 / ‖((σ₁ : ℂ) + ((t + u : ℝ) : ℂ) * Complex.I) - 1‖ := by
    intro t ht
    exact hnearld (t + u) σ₁ ht (ne_of_lt hσ₁lt) hσ₁δ (by linarith)
  -- ** raw edge bounds
  have htop1 : ‖zetaTwTop u y T σ₁‖ ≤
      8 * Real.exp 1 * B * (Real.log y) ^ (1 / 2 : ℝ) * y *
        Real.exp (-((Real.log y) ^ (1 / 10 : ℝ))) := by
    have hle : ‖zetaTwTop u y T σ₁‖ ≤ B * (Real.log (|u| + T + 3)) ^ 2 *
        y ^ (1 + 1 / Real.log y) * ((1 + 1 / Real.log y) - σ₁) / T := by
      have hh := norm_horiz_edge_le (u := u) (x := y) (T := T) (σ₁ := σ₁) (B := B) (r := T)
        hy1 hσ₁pos hTpos (le_of_lt hσ₁le) hB.le (abs_of_pos hTpos) hDtop
      simpa only [zetaTwTop] using hh
    exact le_trans hle (zetaTwTopEdge_absorb hB.le hL1 hTpos hTge hyexp.symm hσ₁pos hσ₁lt hloguT)
  have hbot1 : ‖zetaTwBot u y T σ₁‖ ≤
      8 * Real.exp 1 * B * (Real.log y) ^ (1 / 2 : ℝ) * y *
        Real.exp (-((Real.log y) ^ (1 / 10 : ℝ))) := by
    have hh := norm_horiz_edge_le (u := u) (x := y) (T := T) (σ₁ := σ₁) (B := B) (r := -T)
      hy1 hσ₁pos hTpos (le_of_lt hσ₁le) hB.le (by rw [abs_neg, abs_of_pos hTpos]) hDbot
    have hb : (∫ v in σ₁..(1 + 1 / Real.log y),
          zetaTwG u y ((v : ℂ) + (((-T : ℝ) : ℂ)) * Complex.I)) =
        (∫ v in σ₁..(1 + 1 / Real.log y),
          zetaTwG u y ((v : ℂ) - (T : ℂ) * Complex.I)) := by
      apply intervalIntegral.integral_congr
      intro v _
      show zetaTwG u y ((v : ℂ) + (((-T : ℝ) : ℂ)) * Complex.I) =
        zetaTwG u y ((v : ℂ) - (T : ℂ) * Complex.I)
      rw [show (v : ℂ) + (((-T : ℝ) : ℂ)) * Complex.I = (v : ℂ) - (T : ℂ) * Complex.I by
        push_cast
        ring]
    rw [hb] at hh
    have hle : ‖zetaTwBot u y T σ₁‖ ≤ B * (Real.log (|u| + T + 3)) ^ 2 *
        y ^ (1 + 1 / Real.log y) * ((1 + 1 / Real.log y) - σ₁) / T := by
      rw [zetaTwBot]
      exact hh
    exact le_trans hle (zetaTwTopEdge_absorb hB.le hL1 hTpos hTge hyexp.symm hσ₁pos hσ₁lt hloguT)
  have hleft1 : ‖zetaTwLeft u y T σ₁‖ ≤
      (B + C₅ + 1 / (1 - σ₁) + 1) * (Real.log (|u| + T + 3)) ^ 2 * y ^ σ₁ *
        (2 * Real.sqrt 2 * Real.log (1 + T / σ₁)) :=
    zetaTwLeft_near_far_le hy1 hTpos hσ₁pos hσ₁lt hB.le hC₅.le hDfar hDnear
  -- ** packaged edge bounds
  have hE2le : Real.exp (-((Real.log y) ^ (1 / 10 : ℝ))) ≤
      Real.exp (-(c / 8) * (Real.log y) ^ (1 / 10 : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have hnn : 0 ≤ (Real.log y) ^ (1 / 10 : ℝ) := Real.rpow_nonneg hLpos.le _
    nlinarith [hc8]
  have htop_le : ‖zetaTwTop u y T σ₁‖ ≤
      KK * (Real.log y) ^ (10 : ℝ) * y *
        Real.exp (-(c / 8) * (Real.log y) ^ (1 / 10 : ℝ)) / 4 := by
    have h8 : 8 * Real.exp 1 * B ≤ KK / 4 := by linarith [hKK2]
    have hLp : (Real.log y) ^ (1 / 2 : ℝ) ≤ (Real.log y) ^ (10 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    have hEs' : 8 * Real.exp 1 * B * (Real.log y) ^ (1 / 2 : ℝ) ≤
        KK / 4 * (Real.log y) ^ (10 : ℝ) :=
      mul_le_mul h8 hLp (Real.rpow_nonneg hLpos.le _) (by positivity)
    calc ‖zetaTwTop u y T σ₁‖
        ≤ 8 * Real.exp 1 * B * (Real.log y) ^ (1 / 2 : ℝ) * y *
            Real.exp (-((Real.log y) ^ (1 / 10 : ℝ))) := htop1
      _ = (8 * Real.exp 1 * B * (Real.log y) ^ (1 / 2 : ℝ)) *
            (y * Real.exp (-((Real.log y) ^ (1 / 10 : ℝ)))) := by ring
      _ ≤ (KK / 4 * (Real.log y) ^ (10 : ℝ)) *
            (y * Real.exp (-(c / 8) * (Real.log y) ^ (1 / 10 : ℝ))) :=
          mul_le_mul hEs' (mul_le_mul_of_nonneg_left hE2le hypos.le) (by positivity)
            (by positivity)
      _ = KK * (Real.log y) ^ (10 : ℝ) * y *
            Real.exp (-(c / 8) * (Real.log y) ^ (1 / 10 : ℝ)) / 4 := by ring
  have hbot_le : ‖zetaTwBot u y T σ₁‖ ≤
      KK * (Real.log y) ^ (10 : ℝ) * y *
        Real.exp (-(c / 8) * (Real.log y) ^ (1 / 10 : ℝ)) / 4 := by
    have h8 : 8 * Real.exp 1 * B ≤ KK / 4 := by linarith [hKK2]
    have hLp : (Real.log y) ^ (1 / 2 : ℝ) ≤ (Real.log y) ^ (10 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    have hEs' : 8 * Real.exp 1 * B * (Real.log y) ^ (1 / 2 : ℝ) ≤
        KK / 4 * (Real.log y) ^ (10 : ℝ) :=
      mul_le_mul h8 hLp (Real.rpow_nonneg hLpos.le _) (by positivity)
    calc ‖zetaTwBot u y T σ₁‖
        ≤ 8 * Real.exp 1 * B * (Real.log y) ^ (1 / 2 : ℝ) * y *
            Real.exp (-((Real.log y) ^ (1 / 10 : ℝ))) := hbot1
      _ = (8 * Real.exp 1 * B * (Real.log y) ^ (1 / 2 : ℝ)) *
            (y * Real.exp (-((Real.log y) ^ (1 / 10 : ℝ)))) := by ring
      _ ≤ (KK / 4 * (Real.log y) ^ (10 : ℝ)) *
            (y * Real.exp (-(c / 8) * (Real.log y) ^ (1 / 10 : ℝ))) :=
          mul_le_mul hEs' (mul_le_mul_of_nonneg_left hE2le hypos.le) (by positivity)
            (by positivity)
      _ = KK * (Real.log y) ^ (10 : ℝ) * y *
            Real.exp (-(c / 8) * (Real.log y) ^ (1 / 10 : ℝ)) / 4 := by ring
  have hleft_le : ‖zetaTwLeft u y T σ₁‖ ≤
      KK * (Real.log y) ^ (10 : ℝ) * y *
        Real.exp (-(c / 8) * (Real.log y) ^ (1 / 10 : ℝ)) / 4 := by
    have hraw := zetaTwLeftEdge_absorb (c := c) (V := V) (B := B) (C₅ := C₅)
      (L := Real.log y) (T := T) (y := y) (σ₁ := σ₁) (u := u)
      hc hVpos hB.le hC₅.le hL1 hTpos hTge hyexp.symm hσ₁eq hVle hσ₁half hlogT hloguT
    refine le_trans hleft1 (le_trans hraw ?_)
    have h24 : 24 * Real.sqrt 2 * (B + C₅ + 1 + 4 / c) ≤ KK / 4 := by linarith [hKK3]
    calc 24 * Real.sqrt 2 * (B + C₅ + 1 + 4 / c) * (Real.log y) ^ (10 : ℝ) * y *
          Real.exp (-(c / 8) * (Real.log y) ^ (1 / 10 : ℝ))
        = (24 * Real.sqrt 2 * (B + C₅ + 1 + 4 / c) * (Real.log y) ^ (10 : ℝ)) *
            (y * Real.exp (-(c / 8) * (Real.log y) ^ (1 / 10 : ℝ))) := by ring
      _ ≤ (KK / 4 * (Real.log y) ^ (10 : ℝ)) *
            (y * Real.exp (-(c / 8) * (Real.log y) ^ (1 / 10 : ℝ))) :=
          mul_le_mul (mul_le_mul h24 le_rfl (Real.rpow_nonneg hLpos.le _) (by positivity))
            le_rfl (by positivity) (by positivity)
      _ = KK * (Real.log y) ^ (10 : ℝ) * y *
            Real.exp (-(c / 8) * (Real.log y) ^ (1 / 10 : ℝ)) / 4 := by ring
  have htrunc_le : C1 * (y * (Real.log y) ^ 2 / T + Real.log y) ≤
      KK * (Real.log y) ^ (10 : ℝ) * y *
        Real.exp (-(c / 8) * (Real.log y) ^ (1 / 10 : ℝ)) / 4 := by
    have hraw := zetaTwTrunc_absorb (c := c) (C1 := C1) (L := Real.log y) (T := T) (y := y)
      hc hc8 hC1pos.le hL1 hTpos hTge hyexp.symm hLy'
    refine le_trans hraw ?_
    have h2C1 : 2 * C1 ≤ KK / 4 := by linarith [hKK1]
    have hLp : (1 : ℝ) ≤ (Real.log y) ^ (10 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
    calc 2 * C1 * (Real.log y) ^ (10 : ℝ) * y *
          Real.exp (-(c / 8) * (Real.log y) ^ (1 / 10 : ℝ))
        = (2 * C1 * (Real.log y) ^ (10 : ℝ)) *
            (y * Real.exp (-(c / 8) * (Real.log y) ^ (1 / 10 : ℝ))) := by ring
      _ ≤ (KK / 4 * (Real.log y) ^ (10 : ℝ)) *
            (y * Real.exp (-(c / 8) * (Real.log y) ^ (1 / 10 : ℝ))) :=
          mul_le_mul (mul_le_mul h2C1 le_rfl (Real.rpow_nonneg hLpos.le _) (by positivity))
            le_rfl (by positivity) (by positivity)
      _ = KK * (Real.log y) ^ (10 : ℝ) * y *
            Real.exp (-(c / 8) * (Real.log y) ^ (1 / 10 : ℝ)) / 4 := by ring
  -- ** total
  have hTot : ‖zetaTwSum u y - (y : ℂ) ^ (1 - Complex.I * (u : ℂ)) / (1 - Complex.I * (u : ℂ))‖ ≤
      KK * (Real.log y) ^ (10 : ℝ) * y *
        Real.exp (-(c / 8) * (Real.log y) ^ (1 / 10 : ℝ)) := by
    have hkey : zetaTwSum u y - (y : ℂ) ^ (1 - Complex.I * (u : ℂ)) / (1 - Complex.I * (u : ℂ)) =
        (zetaTwSum u y - zetaTwPerron u y T) +
          (zetaTwTop u y T σ₁ - zetaTwBot u y T σ₁ + zetaTwLeft u y T σ₁) := by
      rw [hmain_eq]; ring
    rw [hkey]
    have h1 : ‖(zetaTwSum u y - zetaTwPerron u y T) +
        (zetaTwTop u y T σ₁ - zetaTwBot u y T σ₁ + zetaTwLeft u y T σ₁)‖ ≤
        ‖zetaTwSum u y - zetaTwPerron u y T‖ +
          ‖zetaTwTop u y T σ₁ - zetaTwBot u y T σ₁ + zetaTwLeft u y T σ₁‖ :=
      norm_add_le _ _
    have h2 : ‖zetaTwTop u y T σ₁ - zetaTwBot u y T σ₁ + zetaTwLeft u y T σ₁‖ ≤
        (‖zetaTwTop u y T σ₁‖ + ‖zetaTwBot u y T σ₁‖) + ‖zetaTwLeft u y T σ₁‖ := by
      refine le_trans (norm_add_le _ _) ?_
      exact add_le_add (norm_sub_le _ _) le_rfl
    have h3 : ‖zetaTwSum u y - zetaTwPerron u y T‖ =
        ‖zetaTwPerron u y T - zetaTwSum u y‖ := norm_sub_rev _ _
    have hX4 : KK * (Real.log y) ^ (10 : ℝ) * y *
          Real.exp (-(c / 8) * (Real.log y) ^ (1 / 10 : ℝ)) / 4
        + (KK * (Real.log y) ^ (10 : ℝ) * y *
            Real.exp (-(c / 8) * (Real.log y) ^ (1 / 10 : ℝ)) / 4
        + (KK * (Real.log y) ^ (10 : ℝ) * y *
            Real.exp (-(c / 8) * (Real.log y) ^ (1 / 10 : ℝ)) / 4
        + KK * (Real.log y) ^ (10 : ℝ) * y *
            Real.exp (-(c / 8) * (Real.log y) ^ (1 / 10 : ℝ)) / 4))
        = KK * (Real.log y) ^ (10 : ℝ) * y *
            Real.exp (-(c / 8) * (Real.log y) ^ (1 / 10 : ℝ)) := by ring
    linarith [h1, h2, h3, htrunc_le, htop_le, hbot_le, hleft_le, hX4]
  refine le_trans hTot ?_
  simp only [one_mul]
  calc KK * (Real.log y) ^ (10 : ℝ) * y *
        Real.exp (-(c / 8) * (Real.log y) ^ (1 / 10 : ℝ))
      = (KK * (Real.log y) ^ (10 : ℝ)) *
          (y * Real.exp (-(c / 8) * (Real.log y) ^ (1 / 10 : ℝ))) := by ring
    _ ≤ Real.exp ((c / 16) * (Real.log y) ^ (1 / 10 : ℝ)) *
          (y * Real.exp (-(c / 8) * (Real.log y) ^ (1 / 10 : ℝ))) :=
        mul_le_mul_of_nonneg_right hC' (by positivity)
    _ = y * (Real.exp ((c / 16) * (Real.log y) ^ (1 / 10 : ℝ)) *
          Real.exp (-(c / 8) * (Real.log y) ^ (1 / 10 : ℝ))) := by ring
    _ = y * Real.exp (-(c / 16) * (Real.log y) ^ (1 / 10 : ℝ)) := by
        rw [← Real.exp_add]
        congr 1
        ring

end

end Work.BMF.liouville

namespace Work.BMF.liouville

namespace Work.BMF.liouville

set_option maxHeartbeats 800000

/-- **The Vinogradov–Korobov twisted prime-number asymptotic for the principal character**
(χ = 1), as a bound for `Σ_{n ≤ x} Λ(n) n^{-iu} - x^{1-iu}/(1-iu)`.

Inputs (all standard, to be instantiated from the ζ VK zero-free region + log-derivative bound,
which in turn come from the VK growth bound for ζ):

* `hreg`: the zero-free region `ζ(σ+it) ≠ 0` for `|t| ≥ 3`, `1 - c₁/VKd(|t|+3) ≤ σ ≤ 1`;
* `hlog`: the log-derivative bound `‖ζ′/ζ(σ+it)‖ ≤ B (log(|t|+3))²` in the region
  `|t| ≥ 3`, `1 - c₂/VKd(|t|+3) ≤ σ ≤ 2`;
* `hrect`: the twisted Perron contour-shift identity
  `zetaTwPerron u x T = x^{1-iu}/(1-iu) + zetaTwTop - zetaTwBot + zetaTwLeft`
  (the statement of `Work.BMF.liouville.zetaTwPerron_rect`, whose file
  `Submission/Work/BMF/liouville/zetaTwPerron_rect.lean` is being produced in parallel;
  it is passed as a hypothesis here so that this result is independent of it).

Conclusion: `∃ c > 0, ∃ C ≥ 0` such that for every `x ≥ 3` and every real `u` with
`|u| ≤ exp((log x)^{5/4})`,
`‖Σ_{n ≤ x} Λ(n) n^{-iu} − x^{1-iu}/(1-iu)‖ ≤ C x exp(-c (log x)^{1/10})`. -/
theorem zetaTwSum_sub_main_le
    (hreg : ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ t σ : ℝ, 3 ≤ |t| →
      1 - c₁ / Work.BMF.VKd (|t| + 3) ≤ σ → σ ≤ 1 →
      riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0)
    (hlog : ∃ c₂ B : ℝ, 0 < c₂ ∧ 0 < B ∧ ∀ t σ : ℝ, 3 ≤ |t| →
      1 - c₂ / Work.BMF.VKd (|t| + 3) ≤ σ → σ ≤ 2 →
      ‖deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) /
        riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ B * (Real.log (|t| + 3)) ^ 2)
    (hrect : ∀ u x T σ₁ : ℝ, 1 < x → 0 < T → 0 < σ₁ → σ₁ < 1 →
      σ₁ < 1 + 1 / Real.log x → |u| < T →
      (∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ 1 + 1 / Real.log x → |s.im - u| ≤ T → s ≠ 1 →
        riemannZeta s ≠ 0) →
      zetaTwPerron u x T =
        (x : ℂ) ^ (1 - Complex.I * (u : ℂ)) / (1 - Complex.I * (u : ℂ))
          + zetaTwTop u x T σ₁ - zetaTwBot u x T σ₁ + zetaTwLeft u x T σ₁) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ x : ℝ, 3 ≤ x → ∀ u : ℝ,
      |u| ≤ Real.exp ((Real.log x) ^ (5 / 4 : ℝ)) →
      ‖zetaTwSum u x - (x : ℂ) ^ (1 - Complex.I * (u : ℂ)) / (1 - Complex.I * (u : ℂ))‖
        ≤ C * x * Real.exp (-(c * (Real.log x) ^ (1 / 10 : ℝ))) := by
  obtain ⟨c₁, hc₁, hreg'⟩ := hreg
  obtain ⟨c₂, B, hc₂, hB, hlog'⟩ := hlog
  obtain ⟨C₅, δ₅, hC₅, hδ₅, hnear_ld, hnear_zz⟩ := zeta_logDeriv_near_four
  obtain ⟨N0, Ceng, hCengpos, heng⟩ :=
    zetaTwSum_engine c₁ c₂ B C₅ δ₅ hc₁ hc₂ hB hC₅ hδ₅ hreg' hlog' hnear_ld hnear_zz hrect
  have hCeng : 0 ≤ Ceng := hCengpos.le
  have hzc : 0 < ztC c₁ c₂ := ztC_pos hc₁ hc₂
  set cf : ℝ := ztC c₁ c₂ / 16 with hcfdef
  have hcfpos : 0 < cf := by rw [hcfdef]; exact div_pos hzc (by norm_num)
  set X : ℝ := max N0 3 with hXdef
  have hX3 : 3 ≤ X := le_max_right _ _
  obtain ⟨Csm, hCsmpos, hsm⟩ := zetaTwSum_small_x X hX3
  set Cfin : ℝ := max (Csm * Real.exp (cf * (Real.log X) ^ (1 / 10 : ℝ)))
    (Ceng * (7 / 6) + 1 / 2) with hCfindef
  refine ⟨cf, Cfin, hcfpos, ?_, ?_⟩
  · rw [hCfindef]
    have h1 : 0 ≤ Csm * Real.exp (cf * (Real.log X) ^ (1 / 10 : ℝ)) :=
      mul_nonneg hCsmpos.le (Real.exp_pos _).le
    have h2 : 0 ≤ Ceng * (7 / 6) + 1 / 2 := by linarith
    exact le_max_iff.mpr (Or.inl h1)
  · intro x hx u hu
    by_cases hxX : x ≤ X
    · have h := hsm x hx hxX u
      have hxm := exp_cf_log_mono hcfpos.le hx hxX
      have hle : Csm ≤ Cfin * Real.exp (-(cf * (Real.log x) ^ (1 / 10 : ℝ))) := by
        rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _)]
        exact le_trans (mul_le_mul_of_nonneg_left hxm hCsmpos.le) (le_max_left _ _)
      calc ‖zetaTwSum u x - (x : ℂ) ^ (1 - Complex.I * (u : ℂ)) / (1 - Complex.I * (u : ℂ))‖
          ≤ Csm * x := h
        _ ≤ (Cfin * Real.exp (-(cf * (Real.log x) ^ (1 / 10 : ℝ)))) * x :=
            mul_le_mul_of_nonneg_right hle (by linarith)
        _ = Cfin * x * Real.exp (-(cf * (Real.log x) ^ (1 / 10 : ℝ))) := by ring
    · have hxX' : X < x := not_le.mp hxX
      by_cases hint : ∃ n : ℕ, (n : ℝ) = x
      · obtain ⟨n, hn⟩ := hint
        set y : ℝ := x + 1 / 2 with hydef
        have hyN : N0 ≤ y := by
          have h1 : N0 ≤ X := le_max_left _ _
          rw [hydef]; linarith
        have hfy : ⌊y⌋₊ = n := by
          rw [hydef, ← hn]
          rw [Nat.floor_eq_iff (show (0 : ℝ) ≤ (n : ℝ) + 1 / 2 by positivity)]
          constructor <;> linarith
        have hfx : ⌊x⌋₊ = n := by rw [← hn]; exact Nat.floor_natCast n
        have hynat : ∀ m : ℕ, (m : ℝ) ≠ y := by
          intro m hm
          have h2 : ⌊(m : ℝ)⌋₊ = ⌊y⌋₊ := by rw [hm]
          rw [Nat.floor_natCast, hfy] at h2
          rw [h2, hydef, ← hn] at hm
          linarith
        have hsum_eq : zetaTwSum u y = zetaTwSum u x := by simp only [zetaTwSum, hfy, hfx]
        have hlogxpos : 0 < Real.log x := Real.log_pos (by linarith)
        have hlogy : Real.log x ≤ Real.log y :=
          Real.log_le_log (by linarith) (by rw [hydef]; linarith)
        have hu' : |u| ≤ Real.exp ((Real.log y) ^ (5 / 4 : ℝ)) := by
          refine le_trans hu (Real.exp_le_exp.mpr ?_)
          exact Real.rpow_le_rpow hlogxpos.le hlogy (by norm_num)
        have heng' := heng y hyN hynat u hu'
        have heng'' : ‖zetaTwSum u y - (y : ℂ) ^ (1 - Complex.I * (u : ℂ)) /
            (1 - Complex.I * (u : ℂ))‖ ≤ Ceng * y * Real.exp (-(cf * (Real.log y) ^ (1 / 10 : ℝ))) := by
          refine le_trans heng' ?_
          have h2 : Real.exp (-(ztC c₁ c₂ / 16) * (Real.log y) ^ (1 / 10 : ℝ)) =
              Real.exp (-(cf * (Real.log y) ^ (1 / 10 : ℝ))) := by
            rw [hcfdef]
            congr 1
            ring
          rw [h2]
        have hy7 : y ≤ 7 / 6 * x := by rw [hydef]; linarith
        have hexp_le : Real.exp (-(cf * (Real.log y) ^ (1 / 10 : ℝ))) ≤
            Real.exp (-(cf * (Real.log x) ^ (1 / 10 : ℝ))) := by
          apply Real.exp_le_exp.mpr
          have h1 : -(cf * (Real.log y) ^ (1 / 10 : ℝ)) ≤ -(cf * (Real.log x) ^ (1 / 10 : ℝ)) := by
            have h2 : (Real.log x) ^ (1 / 10 : ℝ) ≤ (Real.log y) ^ (1 / 10 : ℝ) :=
              Real.rpow_le_rpow hlogxpos.le hlogy (by norm_num)
            nlinarith [hcfpos]
          exact h1
        have hxE : 1 ≤ x * Real.exp (-(cf * (Real.log x) ^ (1 / 10 : ℝ))) := by
          have hlogx1 : 1 ≤ Real.log x := by
            have h6 := Real.log_le_log (by norm_num : (0 : ℝ) < 3) hx
            linarith [Work.BMF.one_le_log_three]
          have hxe : Real.exp (Real.log x) = x := Real.exp_log (by linarith)
          have h1 : cf * (Real.log x) ^ (1 / 10 : ℝ) ≤ Real.log x := by
            have h2 : (Real.log x) ^ (1 / 10 : ℝ) ≤ (Real.log x) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hlogx1 (by norm_num)
            rw [Real.rpow_one] at h2
            have h3 : cf ≤ 1 := by rw [hcfdef]; linarith [ztC_le_one c₁ c₂]
            have h4 : 0 ≤ (Real.log x) ^ (1 / 10 : ℝ) := Real.rpow_nonneg hlogxpos.le _
            nlinarith
          have h2 : (0 : ℝ) ≤ Real.log x + -(cf * (Real.log x) ^ (1 / 10 : ℝ)) := by linarith
          calc (1 : ℝ) ≤ Real.exp (Real.log x + -(cf * (Real.log x) ^ (1 / 10 : ℝ))) :=
                Real.one_le_exp_iff.mpr h2
            _ = Real.exp (Real.log x) * Real.exp (-(cf * (Real.log x) ^ (1 / 10 : ℝ))) := by
                rw [Real.exp_add]
            _ = x * Real.exp (-(cf * (Real.log x) ^ (1 / 10 : ℝ))) := by rw [hxe]
        have hmain_diff : ‖(y : ℂ) ^ (1 - Complex.I * (u : ℂ)) / (1 - Complex.I * (u : ℂ)) -
            (x : ℂ) ^ (1 - Complex.I * (u : ℂ)) / (1 - Complex.I * (u : ℂ))‖ ≤ 1 / 2 := by
          rw [← sub_div, norm_div]
          have hden : (0 : ℝ) < ‖(1 : ℂ) - Complex.I * (u : ℂ)‖ := by
            have h := Complex.abs_re_le_norm ((1 : ℂ) - Complex.I * (u : ℂ))
            have hre : ((1 : ℂ) - Complex.I * (u : ℂ)).re = 1 := by simp
            rw [hre] at h
            simp only [abs_one] at h
            linarith
          rw [div_le_iff₀ hden]
          have h1 := cpow_one_sub_I_mul_sub_le (x := x) (y := y) (by linarith)
            (by rw [hydef]; linarith) u
          calc ‖(y : ℂ) ^ (1 - Complex.I * (u : ℂ)) - (x : ℂ) ^ (1 - Complex.I * (u : ℂ))‖
              ≤ ‖(1 : ℂ) - Complex.I * (u : ℂ)‖ * (y - x) := h1
            _ = 1 / 2 * ‖(1 : ℂ) - Complex.I * (u : ℂ)‖ := by rw [hydef]; ring
        have hsplit : Ceng * y * Real.exp (-(cf * (Real.log y) ^ (1 / 10 : ℝ))) + 1 / 2 ≤
            (Ceng * (7 / 6) + 1 / 2) *
              (x * Real.exp (-(cf * (Real.log x) ^ (1 / 10 : ℝ)))) := by
          have ha : Ceng * y * Real.exp (-(cf * (Real.log y) ^ (1 / 10 : ℝ))) ≤
              Ceng * (7 / 6) * (x * Real.exp (-(cf * (Real.log x) ^ (1 / 10 : ℝ)))) := by
            have h2 : Ceng * y ≤ Ceng * (7 / 6) * x := by
              have h3 : Ceng * y ≤ Ceng * (7 / 6 * x) := mul_le_mul_of_nonneg_left hy7 hCeng
              nlinarith
            have h5 : Ceng * y * Real.exp (-(cf * (Real.log y) ^ (1 / 10 : ℝ))) ≤
                (Ceng * (7 / 6) * x) * Real.exp (-(cf * (Real.log x) ^ (1 / 10 : ℝ))) := by
              calc Ceng * y * Real.exp (-(cf * (Real.log y) ^ (1 / 10 : ℝ)))
                  ≤ (Ceng * (7 / 6) * x) *
                      Real.exp (-(cf * (Real.log y) ^ (1 / 10 : ℝ))) :=
                    mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
                _ ≤ (Ceng * (7 / 6) * x) *
                      Real.exp (-(cf * (Real.log x) ^ (1 / 10 : ℝ))) :=
                    mul_le_mul_of_nonneg_left hexp_le
                      (mul_nonneg (mul_nonneg hCeng (by norm_num)) (by linarith))
            calc Ceng * y * Real.exp (-(cf * (Real.log y) ^ (1 / 10 : ℝ)))
                ≤ (Ceng * (7 / 6) * x) * Real.exp (-(cf * (Real.log x) ^ (1 / 10 : ℝ))) := h5
              _ = Ceng * (7 / 6) * (x * Real.exp (-(cf * (Real.log x) ^ (1 / 10 : ℝ)))) := by
                  ring
          have hb : (1 : ℝ) / 2 ≤
              (1 / 2) * (x * Real.exp (-(cf * (Real.log x) ^ (1 / 10 : ℝ)))) := by
            linarith [hxE]
          calc Ceng * y * Real.exp (-(cf * (Real.log y) ^ (1 / 10 : ℝ))) + 1 / 2
              ≤ Ceng * (7 / 6) * (x * Real.exp (-(cf * (Real.log x) ^ (1 / 10 : ℝ)))) +
                (1 / 2) * (x * Real.exp (-(cf * (Real.log x) ^ (1 / 10 : ℝ)))) :=
                add_le_add ha hb
            _ = (Ceng * (7 / 6) + 1 / 2) *
                (x * Real.exp (-(cf * (Real.log x) ^ (1 / 10 : ℝ)))) := by ring
        have hCfin : Ceng * (7 / 6) + 1 / 2 ≤ Cfin := by
          rw [hCfindef]; exact le_max_right _ _
        calc ‖zetaTwSum u x - (x : ℂ) ^ (1 - Complex.I * (u : ℂ)) / (1 - Complex.I * (u : ℂ))‖
            = ‖zetaTwSum u y - (x : ℂ) ^ (1 - Complex.I * (u : ℂ)) /
                (1 - Complex.I * (u : ℂ))‖ := by rw [hsum_eq]
          _ ≤ ‖zetaTwSum u y - (y : ℂ) ^ (1 - Complex.I * (u : ℂ)) /
                (1 - Complex.I * (u : ℂ))‖ +
              ‖(y : ℂ) ^ (1 - Complex.I * (u : ℂ)) / (1 - Complex.I * (u : ℂ)) -
                (x : ℂ) ^ (1 - Complex.I * (u : ℂ)) / (1 - Complex.I * (u : ℂ))‖ := by
              have heq : zetaTwSum u y - (x : ℂ) ^ (1 - Complex.I * (u : ℂ)) /
                    (1 - Complex.I * (u : ℂ)) =
                  (zetaTwSum u y - (y : ℂ) ^ (1 - Complex.I * (u : ℂ)) /
                    (1 - Complex.I * (u : ℂ))) +
                  ((y : ℂ) ^ (1 - Complex.I * (u : ℂ)) / (1 - Complex.I * (u : ℂ)) -
                    (x : ℂ) ^ (1 - Complex.I * (u : ℂ)) / (1 - Complex.I * (u : ℂ))) := by ring
              rw [heq]
              exact norm_add_le _ _
          _ ≤ Ceng * y * Real.exp (-(cf * (Real.log y) ^ (1 / 10 : ℝ))) + 1 / 2 :=
              add_le_add heng'' hmain_diff
          _ ≤ (Ceng * (7 / 6) + 1 / 2) *
                (x * Real.exp (-(cf * (Real.log x) ^ (1 / 10 : ℝ)))) := hsplit
          _ ≤ Cfin * (x * Real.exp (-(cf * (Real.log x) ^ (1 / 10 : ℝ)))) :=
              mul_le_mul_of_nonneg_right hCfin (mul_nonneg (by linarith) (Real.exp_pos _).le)
          _ = Cfin * x * Real.exp (-(cf * (Real.log x) ^ (1 / 10 : ℝ))) := by ring
      · have hint' : ∀ m : ℕ, (m : ℝ) ≠ x := by
          intro m hm; exact hint ⟨m, hm⟩
        have hN0x : N0 ≤ x := le_trans (le_max_left _ _) hxX'.le
        have h0 := heng x hN0x hint' u hu
        have h : ‖zetaTwSum u x - (x : ℂ) ^ (1 - Complex.I * (u : ℂ)) /
            (1 - Complex.I * (u : ℂ))‖ ≤ Ceng * x * Real.exp (-(cf * (Real.log x) ^ (1 / 10 : ℝ))) := by
          refine le_trans h0 ?_
          have h2 : Real.exp (-(ztC c₁ c₂ / 16) * (Real.log x) ^ (1 / 10 : ℝ)) =
              Real.exp (-(cf * (Real.log x) ^ (1 / 10 : ℝ))) := by
            rw [hcfdef]
            congr 1
            ring
          rw [h2]
        refine le_trans h ?_
        have h1 : Ceng ≤ Cfin := by
          have h2 : Ceng * (7 / 6) + 1 / 2 ≤ Cfin := by
            rw [hCfindef]; exact le_max_right _ _
          linarith
        calc Ceng * x * Real.exp (-(cf * (Real.log x) ^ (1 / 10 : ℝ)))
            ≤ Cfin * x * Real.exp (-(cf * (Real.log x) ^ (1 / 10 : ℝ))) := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right h1 (by linarith)) (Real.exp_pos _).le

end Work.BMF.liouville

/-- The canonical-namespace restatement of `Work.BMF.liouville.zetaTwSum_sub_main_le` (the
statement above lives in the doubly nested namespace `Work.BMF.liouville.Work.BMF.liouville`
because the requested statement carried its own `namespace`/`end` pair). -/
theorem zetaTwSum_sub_main_le
    (hreg : ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ t σ : ℝ, 3 ≤ |t| →
      1 - c₁ / Work.BMF.VKd (|t| + 3) ≤ σ → σ ≤ 1 →
      riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0)
    (hlog : ∃ c₂ B : ℝ, 0 < c₂ ∧ 0 < B ∧ ∀ t σ : ℝ, 3 ≤ |t| →
      1 - c₂ / Work.BMF.VKd (|t| + 3) ≤ σ → σ ≤ 2 →
      ‖deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) /
        riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ B * (Real.log (|t| + 3)) ^ 2)
    (hrect : ∀ u x T σ₁ : ℝ, 1 < x → 0 < T → 0 < σ₁ → σ₁ < 1 →
      σ₁ < 1 + 1 / Real.log x → |u| < T →
      (∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ 1 + 1 / Real.log x → |s.im - u| ≤ T → s ≠ 1 →
        riemannZeta s ≠ 0) →
      zetaTwPerron u x T =
        (x : ℂ) ^ (1 - Complex.I * (u : ℂ)) / (1 - Complex.I * (u : ℂ))
          + zetaTwTop u x T σ₁ - zetaTwBot u x T σ₁ + zetaTwLeft u x T σ₁) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ x : ℝ, 3 ≤ x → ∀ u : ℝ,
      |u| ≤ Real.exp ((Real.log x) ^ (5 / 4 : ℝ)) →
      ‖zetaTwSum u x - (x : ℂ) ^ (1 - Complex.I * (u : ℂ)) / (1 - Complex.I * (u : ℂ))‖
        ≤ C * x * Real.exp (-(c * (Real.log x) ^ (1 / 10 : ℝ))) :=
  Work.BMF.liouville.Work.BMF.liouville.zetaTwSum_sub_main_le hreg hlog hrect

end Work.BMF.liouville
