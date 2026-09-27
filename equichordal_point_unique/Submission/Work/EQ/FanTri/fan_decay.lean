import Mathlib
import Submission.Work.EQ.FanTri.DecayDefs
import Submission.Work.EQ.FanTri.radicand_pos
import Submission.Work.EQ.FanTri.analytic_invBranch
import Submission.Work.EQ.FanTri.vis_count
import Submission.Work.EQ.FanTri.Base
import Submission.Work.EQ.FanSep.step_w
import Submission.Work.EQ.FanSep.step_x
import Submission.Work.EQ.FanSep.germ_lip
import Submission.Work.EQ.FanSep.centre_numbers
import Submission.Work.EQ.FanSep.axis_walk
import Submission.Work.EQ.walk_bounds

set_option maxHeartbeats 800000000

namespace Work.EQ.FanTri

open Work.EQ Complex Metric Filter
open scoped Topology

noncomputable section

/-- `‖x / y‖ ≤ c` from `‖x‖ ≤ c * ‖y‖` (no nonvanishing needed). -/
private lemma norm_div_le_of_le_mul {x y : ℂ} {c : ℝ} (hc : 0 ≤ c)
    (h : ‖x‖ ≤ c * ‖y‖) : ‖x / y‖ ≤ c := by
  by_cases hy : y = 0
  · rw [hy, div_zero, norm_zero]; exact hc
  · rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr hy)]
    calc ‖x‖ ≤ c * ‖y‖ := h

/-- `(x·f)/(z·f)` has norm at most `‖x‖/‖z‖`; no hypothesis on `f`. -/
private lemma norm_mul_div_mul_le (x z f : ℂ) : ‖x * f / (z * f)‖ ≤ ‖x‖ / ‖z‖ := by
  by_cases hf : f = 0
  · have hz : x * f / (z * f) = 0 := by rw [hf]; simp
    rw [hz, norm_zero]
    exact div_nonneg (norm_nonneg _) (norm_nonneg _)
  · have hf' : ‖f‖ ≠ 0 := norm_ne_zero_iff.mpr hf
    rw [norm_div, norm_mul, norm_mul]
    rw [mul_div_mul_right _ _ hf']

/-- The exact/`≤` one-step recursion for the semi-projective coordinate. -/
private lemma wFan_cons_le {a : ℝ} {h : ℂ → ℂ} (s : Bool) (ε : List Bool) (v : ℂ)
    (hden : (fan a h ε ((eqLam a : ℂ) * v)).1 - ((a / 2 : ℝ) : ℂ) ≠ 0) :
    ‖wFan a h (s :: ε) v‖ ≤ ‖wFan a h ε ((eqLam a : ℂ) * v)‖ *
      (‖(fan a h ε ((eqLam a : ℂ) * v)).1 - ((a / 2 : ℝ) : ℂ)‖ /
        ‖(fan a h ε ((eqLam a : ℂ) * v)).1 + ((a / 2 : ℝ) : ℂ)‖) := by
  obtain ⟨f, h1, h2⟩ := FanSep.invBranch_mul_sub a s (fan a h ε ((eqLam a : ℂ) * v))
  have e1 : (fan a h (s :: ε) v).2 = (fan a h ε ((eqLam a : ℂ) * v)).2 * f := by
    show (invBranch a s (fan a h ε ((eqLam a : ℂ) * v))).2 = _; exact h2
  have e2 : (fan a h (s :: ε) v).1 - ((a / 2 : ℝ) : ℂ)
      = ((fan a h ε ((eqLam a : ℂ) * v)).1 + ((a / 2 : ℝ) : ℂ)) * f := by
    show (invBranch a s (fan a h ε ((eqLam a : ℂ) * v))).1 - ((a / 2 : ℝ) : ℂ) = _; exact h1
  rw [wFan, wFan, e1, e2]
  have hR : ‖(fan a h ε ((eqLam a : ℂ) * v)).2 /
        ((fan a h ε ((eqLam a : ℂ) * v)).1 - ((a / 2 : ℝ) : ℂ))‖
      * (‖(fan a h ε ((eqLam a : ℂ) * v)).1 - ((a / 2 : ℝ) : ℂ)‖
        / ‖(fan a h ε ((eqLam a : ℂ) * v)).1 + ((a / 2 : ℝ) : ℂ)‖)
      = ‖(fan a h ε ((eqLam a : ℂ) * v)).2‖
        / ‖(fan a h ε ((eqLam a : ℂ) * v)).1 + ((a / 2 : ℝ) : ℂ)‖ := by
    rw [norm_div]
    have hd : ‖(fan a h ε ((eqLam a : ℂ) * v)).1 - ((a / 2 : ℝ) : ℂ)‖ ≠ 0 :=
      norm_ne_zero_iff.mpr hden
    field_simp
  rw [hR]
  exact norm_mul_div_mul_le _ _ _

/-- The fan centre of a word is `A₁` exactly when the level-`0` walk state vanishes. -/
private lemma centre_eq_iff {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hSG : IsStableGerm a h r) (ε : List Bool) :
    ((fan a h ε 0).1 = ((-1 / 2 : ℝ) : ℂ)) ↔ fLvl ε 0 = 0 := by
  have h1 : (fan a h ε 0).1 = ((stCtr (fLvl ε 0) : ℝ) : ℂ) := by
    rw [fan_centre_walk ha0 ha1 hSG ε]; rfl
  rw [h1]
  constructor
  · intro hc
    exact stCtr_eq_iff.mp (Complex.ofReal_injective hc)
  · intro hc
    rw [hc, stCtr_zero]

/-- The per-step gain at a fan centre is at most `tau`. -/
private lemma lam_ratio_le_tau {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hSG : IsStableGerm a h r)
    (hctr : ∀ ε : List Bool, ((fan a h ε 0).1 = ((-1 / 2 : ℝ) : ℂ)) ↔ fLvl ε 0 = 0)
    (ε : List Bool) :
    eqLam a * (‖(fan a h ε 0).1 - ((a / 2 : ℝ) : ℂ)‖ /
      ‖(fan a h ε 0).1 + ((a / 2 : ℝ) : ℂ)‖) ≤ tau a ε := by
  obtain ⟨haxis1, haxis2⟩ := FanSep.axis_walk ha0 ha1 hSG
  obtain ⟨hz, k, hk⟩ := haxis2 ε
  have hx1 : (fan a h ε 0).1 = (((-1 / 2 + 2 * (k : ℝ) : ℝ)) : ℂ) := by
    rw [hk]; push_cast; ring
  rw [hx1, FanSep.norm_ofReal_sub_eq_abs, FanSep.norm_ofReal_add_eq_abs, ← mul_div_assoc]
  rcases eq_or_ne k 0 with hk0 | hk0
  · subst hk0
    have hfl : fLvl ε 0 = 0 := by rw [← hctr ε, hx1]; norm_num
    rw [show tau a ε = 1 from by unfold tau; rw [if_pos hfl]]
    have hcz := centre_ratio_zero a ha0 ha1
    linarith [hcz]
  · have hfl : fLvl ε 0 ≠ 0 := by
      intro hfl
      have h := (hctr ε).mpr hfl
      rw [hx1] at h
      have h2 : (-1 / 2 + 2 * (k : ℝ) : ℝ) = -1 / 2 := Complex.ofReal_injective h
      have h3 : (k : ℝ) = 0 := by linarith
      exact hk0 (by exact_mod_cast h3)
    rw [show tau a ε = fanTh a from by unfold tau; rw [if_neg hfl]]
    exact centre_ratio_le_fanTh ha0 ha1 hk0

/-! ## Closure inequalities of the majorant induction -/

private lemma clos_w {Qc Cw Ke lam w d : ℝ} (hQc : 0 < Qc) (hCw : 0 < Cw) (hKe : 0 < Ke)
    (hlam0 : 0 < lam) (hw0 : 0 ≤ w) (hd0 : 0 ≤ d)
    (hd : d ≤ Ke * lam * w) (hQlw : Qc * (lam * w) ≤ 1)
    (hQbig : 2 * Cw * Ke * lam ≤ Qc * (1 - lam)) :
    (1 + Qc * (lam * w)) * (1 + Cw * d) ≤ 1 + Qc * w := by
  have h2 : Cw * d ≤ Cw * Ke * lam * w := by
    have h := mul_le_mul_of_nonneg_left hd (le_of_lt hCw); linarith
  have h5 : Cw * d * Qc * (lam * w) ≤ Cw * Ke * lam * w := by
    calc Cw * d * Qc * (lam * w) = (Cw * d) * (Qc * (lam * w)) := by ring
      _ ≤ (Cw * Ke * lam * w) * 1 :=
          mul_le_mul h2 hQlw (by positivity) (by nlinarith [hCw, hKe, hlam0, hw0])
      _ = Cw * Ke * lam * w := by ring
  have h3 : Cw * Ke * lam * w ≤ Qc * (1 - lam) * w := by
    have h := mul_le_mul_of_nonneg_right hQbig hw0
    have hnn : 0 ≤ Cw * Ke * lam * w := by positivity
    linarith
  have h4 : (1 + Qc * (lam * w)) * (1 + Cw * d)
      = 1 + Qc * (lam * w) + Cw * d + Cw * d * Qc * (lam * w) := by ring
  rw [h4]
  have h6 : 1 + Qc * (lam * w) + Cw * Ke * lam * w + Cw * Ke * lam * w ≤ 1 + Qc * w := by
    nlinarith [h3, hQc, hlam0, hw0]
  linarith [h2, h5, h6]

private lemma clos_x {Ke Cx Lam F tau lam m w Δ qw : ℝ}
    (hKe : 0 < Ke) (hCx : 0 < Cx) (hLam : 0 < Lam) (hF0 : 0 ≤ F) (hF1 : F ≤ 1)
    (hw0 : 0 ≤ w) (hwΔ : w ≤ Δ) (hqw0 : 0 ≤ qw) (hqw : qw ≤ 4 * Lam * F * w)
    (hδ : 16 * Cx * Lam ^ 2 * Δ ≤ Ke * m) (hm : m ≤ tau - lam) :
    Ke * F * lam * w + Cx * qw ^ 2 ≤ Ke * F * tau * w := by
  have h1 : qw ^ 2 ≤ (4 * Lam * F * w) ^ 2 := pow_le_pow_left₀ hqw0 hqw 2
  have h2 : (4 * Lam * F * w) ^ 2 = 16 * Lam ^ 2 * F ^ 2 * w ^ 2 := by ring
  have hF2 : F ^ 2 ≤ F := by nlinarith [hF0, hF1]
  have hw2 : w ^ 2 ≤ Δ * w := by nlinarith [hw0, hwΔ]
  have h3 : F ^ 2 * w ^ 2 ≤ F * (Δ * w) := by
    have ha : F ^ 2 * w ^ 2 ≤ F * w ^ 2 := mul_le_mul_of_nonneg_right hF2 (by positivity)
    have hb : F * w ^ 2 ≤ F * (Δ * w) := mul_le_mul_of_nonneg_left hw2 hF0
    linarith
  have h4 : qw ^ 2 ≤ 16 * Lam ^ 2 * (F * (Δ * w)) := by
    rw [h2] at h1; nlinarith [h1, h3]
  have h5 : Cx * qw ^ 2 ≤ 16 * Cx * Lam ^ 2 * (F * (Δ * w)) := by nlinarith [h4, hCx]
  have h6 : 16 * Cx * Lam ^ 2 * (F * (Δ * w)) ≤ Ke * m * F * w := by
    have h8 := mul_le_mul_of_nonneg_right hδ (by positivity : (0:ℝ) ≤ F * w)
    nlinarith [h8]
  have h9 : Ke * m * F * w ≤ Ke * (tau - lam) * F * w := by
    have h10 := mul_le_mul_of_nonneg_right hm (by positivity : (0:ℝ) ≤ Ke * F * w)
    nlinarith [h10]
  have h11 : Ke * F * lam * w + Ke * (tau - lam) * F * w = Ke * F * tau * w := by ring
  linarith [h5, h6, h9, h11]

private lemma clos_wfan {Lam F tau lam ratio_c w Qc d : ℝ}
    (hLam : 0 ≤ Lam) (hF0 : 0 ≤ F) (hw0 : 0 ≤ w) (hlam0 : 0 ≤ lam)
    (hQc0 : 0 ≤ Qc) (hrc0 : 0 ≤ ratio_c) (hd0 : 0 ≤ d)
    (hrc : ratio_c * lam ≤ tau) (hτ0 : 0 ≤ tau)
    (hcl : (1 + Qc * (lam * w)) * (1 + d) ≤ 1 + Qc * w) :
    Lam * F * (lam * w) * (1 + Qc * (lam * w)) * ratio_c * (1 + d)
      ≤ Lam * F * tau * w * (1 + Qc * w) := by
  have h1 : lam * ratio_c ≤ tau := by linarith [hrc]
  have h3 : 0 ≤ (1 + Qc * (lam * w)) * (1 + d) := by positivity
  calc Lam * F * (lam * w) * (1 + Qc * (lam * w)) * ratio_c * (1 + d)
      = (Lam * F * w) * ((lam * ratio_c) * ((1 + Qc * (lam * w)) * (1 + d))) := by ring
    _ ≤ (Lam * F * w) * (tau * (1 + Qc * w)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul h1 hcl h3 (by positivity)
    _ = Lam * F * tau * w * (1 + Qc * w) := by ring

private lemma qw_bound {Lam F lam w Qc ratio_c d : ℝ}
    (hLam : 0 ≤ Lam) (hF : 0 ≤ F) (hlam : 0 < lam) (hw : 0 ≤ w) (hQc : 0 ≤ Qc)
    (hrc : ratio_c * lam ≤ 1) (hd0 : 0 ≤ d) (hd : d ≤ 1)
    (hQlw : Qc * (lam * w) ≤ 1) :
    Lam * F * (lam * w) * (1 + Qc * (lam * w)) * ratio_c * (1 + d) ≤ 4 * Lam * F * w := by
  have h1 : 1 + Qc * (lam * w) ≤ 2 := by linarith
  have h2 : 1 + d ≤ 2 := by linarith
  calc Lam * F * (lam * w) * (1 + Qc * (lam * w)) * ratio_c * (1 + d)
      = Lam * F * w * ((lam * ratio_c) * ((1 + Qc * (lam * w)) * (1 + d))) := by ring
    _ ≤ Lam * F * w * (1 * 4) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have h4 : lam * ratio_c ≤ 1 := by linarith [hrc]
        have h5 : 0 ≤ (1 + Qc * (lam * w)) * (1 + d) := by positivity
        calc (lam * ratio_c) * ((1 + Qc * (lam * w)) * (1 + d)) ≤ 1 * 4 :=
              mul_le_mul h4 (by nlinarith [h1, h2]) h5 (by norm_num)
          _ = 1 * 4 := rfl
    _ = 4 * Lam * F * w := by ring

/-- `‖(r : ℂ)‖ = |r|`. -/
private lemma norm_ofReal_abs (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = |r| := RCLike.norm_ofReal r

/-- **Quantitative fan decay (Rychlik Thm 7(1), estimates (99)–(109)).** -/
theorem fan_decay {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) :
    ∃ δ Q : ℝ, 0 < δ ∧ 0 < Q ∧ ∀ ε : List Bool, ∀ u : ℂ, u ∈ Metric.ball (0 : ℂ) δ →
      AnalyticOnNhd ℂ (fan a h ε) (Metric.ball 0 δ) ∧
      ‖wFan a h ε u‖ ≤ Q * ‖u‖ * (fanTh a) ^ (fVis ε) ∧
      ‖(fan a h ε u).1 - (fan a h ε 0).1‖ ≤ Q * ‖u‖ * (fanTh a) ^ (fVis ε) := by
  obtain ⟨hr, han, hh0, hhd, hhr, hhFE⟩ := hh
  have hSG : IsStableGerm a h r := ⟨hr, han, hh0, hhd, hhr, hhFE⟩
  obtain ⟨hth0, hth1, hlam_le_th, hVis_nil, hVis_cons, hVis_le, hfvis_eq, hpow, htau, -⟩ :=
    vis_count ha0 ha1 hSG
  have hctrV : ∀ ε : List Bool, ((fan a h ε 0).1 = ((-1 / 2 : ℝ) : ℂ)) ↔ fLvl ε 0 = 0 :=
    fun ε => centre_eq_iff ha0 ha1 hSG ε
  obtain ⟨δg, pg, qg, hδg, hpg, hqg, hgerm⟩ := FanSep.germ_lip ha0 ha1 hSG
  obtain ⟨ρg, hρg, hgan⟩ := germC_analytic ha0 ha1 hSG
  obtain ⟨δfac, hδfac, hfac⟩ := FanSep.germC_snd_factor ha0 ha1 hSG
  obtain ⟨Cx, hCxpos, hCx⟩ := FanSep.step_x ha0 ha1
  obtain ⟨Cw, hCwpos, hCw⟩ := FanSep.step_w_second_est ha0 ha1
  have hHan : AnalyticAt ℂ h 0 := han 0 (by simpa using hr)
  obtain ⟨δh, ch, hδh, hch, hhlip⟩ := FanSep.analytic_lipschitz hHan hh0
  have hlam0 : 0 < eqLam a := eqLam_pos' ha0 ha1
  have hlam1 : eqLam a < 1 := eqLam_lt_one' ha0 ha1
  have h1mlam : 0 < 1 - eqLam a := by linarith
  have h1a : 0 < 1 - a := by linarith
  have hmpos : 0 < min (1 - eqLam a) (fanTh a - eqLam a) := by
    refine lt_min h1mlam ?_
    have hcont : fanTh a - eqLam a = (1 - a) * (2 * a) / ((1 + a) * (5 - a)) := by
      rw [fanTh, eqLam]
      have h1' : (1 + a) ≠ 0 := by linarith
      have h2' : (5 - a) ≠ 0 := by linarith
      field_simp
      ring
    rw [hcont]
    exact div_pos (mul_pos (by linarith) (by linarith)) (by nlinarith)
  set Ke : ℝ := pg + 1 with hKedef
  have hKe0 : 0 < Ke := by rw [hKedef]; linarith
  have hKepg : pg ≤ Ke := by rw [hKedef]; linarith
  set Lam : ℝ := max qg (ch * eqLam a) + 1 with hLamdef
  have hLam0 : 0 < Lam := by rw [hLamdef]; positivity
  have hLamqg : qg ≤ Lam := by rw [hLamdef]; linarith [le_max_left qg (ch * eqLam a)]
  have hLamch : ch * eqLam a ≤ Lam := by rw [hLamdef]; linarith [le_max_right qg (ch * eqLam a)]
  set Qc : ℝ := 2 * Cw * Ke * eqLam a / (1 - eqLam a) + 1 with hQcdef
  have hQc0 : 0 < Qc := by rw [hQcdef]; positivity
  have hQcbig : 2 * Cw * Ke * eqLam a ≤ Qc * (1 - eqLam a) := by
    rw [hQcdef]
    have h1 : (2 * Cw * Ke * eqLam a / (1 - eqLam a) + 1) * (1 - eqLam a)
        = 2 * Cw * Ke * eqLam a + (1 - eqLam a) := by
      field_simp
    rw [h1]; linarith
  have hD0 : 0 < Ke * min (1 - eqLam a) (fanTh a - eqLam a) * eqLam a
      / (16 * Cx * Lam ^ 2) :=
    div_pos (mul_pos (mul_pos hKe0 hmpos) hlam0) (by positivity)
  set Δ : ℝ := min (1/4) (min δg (min ρg (min ((1 - a) / (16 * Ke)) (min (eqLam a / (16 * Lam)) (min (1 / Qc) (min (Ke * min (1 - eqLam a) (fanTh a - eqLam a) * eqLam a / (16 * Cx * Lam ^ 2)) (min ((1 - a) / (64 * Cx * Lam ^ 2)) (min (1 / (Cw * Ke * eqLam a)) (min δh δfac))))))))) with hΔdef
  have hΔ0 : 0 < Δ := by
    rw [hΔdef]
    refine lt_min (by norm_num) (lt_min hδg (lt_min hρg (lt_min (by positivity) (lt_min (by positivity)
      (lt_min (by positivity) (lt_min hD0 (lt_min (by positivity) (lt_min (by positivity)
      (lt_min hδh hδfac)))))))))
  have hΔ14 : Δ ≤ 1/4 := by rw [hΔdef]; exact min_le_left _ _
  have hΔδg : Δ ≤ δg := by
    rw [hΔdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hΔρg : Δ ≤ ρg := by
    rw [hΔdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hΔA : Δ ≤ (1 - a) / (16 * Ke) := by
    rw [hΔdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hΔB : Δ ≤ eqLam a / (16 * Lam) := by
    rw [hΔdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hΔC : Δ ≤ 1 / Qc := by
    rw [hΔdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_left _ _)))))
  have hΔD : Δ ≤ Ke * min (1 - eqLam a) (fanTh a - eqLam a) * eqLam a
      / (16 * Cx * Lam ^ 2) := by
    rw [hΔdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))))
  have hΔE : Δ ≤ (1 - a) / (64 * Cx * Lam ^ 2) := by
    rw [hΔdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _) (min_le_left _ _)))))))
  have hΔF : Δ ≤ 1 / (Cw * Ke * eqLam a) := by
    rw [hΔdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))))))
  have hΔh : Δ ≤ δh := by
    rw [hΔdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
            (le_trans (min_le_right _ _) (min_le_left _ _)))))))))
  have hΔfac : Δ ≤ δfac := by
    rw [hΔdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
            (le_trans (min_le_right _ _) (min_le_right _ _)))))))))
  -- the derived smallness facts
  have hKeΔ : Ke * Δ ≤ (1 - a) / 16 := by
    have h := mul_le_mul_of_nonneg_left hΔA hKe0.le
    have h4 : Ke * ((1 - a) / (16 * Ke)) = (1 - a) / 16 := by field_simp
    linarith [h, h4.le, h4.ge]
  have hLamΔ : Lam * Δ ≤ eqLam a / 16 := by
    have h := mul_le_mul_of_nonneg_left hΔB hLam0.le
    have h4 : Lam * (eqLam a / (16 * Lam)) = eqLam a / 16 := by field_simp
    linarith [h, h4.le, h4.ge]
  have hQcΔ : Qc * Δ ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hΔC (by positivity : (0:ℝ) ≤ Qc)
    have h4 : Qc * (1 / Qc) = 1 := by field_simp
    exact le_trans h h4.le
  have hCwΔ : Cw * Ke * eqLam a * Δ ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hΔF (by positivity : (0:ℝ) ≤ Cw * Ke * eqLam a)
    have h4 : Cw * Ke * eqLam a * (1 / (Cw * Ke * eqLam a)) = 1 := by field_simp
    linarith [h, h4.le, h4.ge]
  have h16Δ : 16 * Cx * Lam ^ 2 * Δ ≤ Ke * min (1 - eqLam a) (fanTh a - eqLam a) := by
    have h := mul_le_mul_of_nonneg_left hΔD (by positivity : (0:ℝ) ≤ 16 * Cx * Lam ^ 2)
    have h6 : 16 * Cx * Lam ^ 2 * (Ke * min (1 - eqLam a) (fanTh a - eqLam a) * eqLam a
        / (16 * Cx * Lam ^ 2)) = Ke * min (1 - eqLam a) (fanTh a - eqLam a) * eqLam a := by
      field_simp
    have h7 : Ke * min (1 - eqLam a) (fanTh a - eqLam a) * eqLam a
        ≤ Ke * min (1 - eqLam a) (fanTh a - eqLam a) := by
      have h8 : 0 ≤ Ke * min (1 - eqLam a) (fanTh a - eqLam a) := mul_nonneg hKe0.le hmpos.le
      calc Ke * min (1 - eqLam a) (fanTh a - eqLam a) * eqLam a
          = eqLam a * (Ke * min (1 - eqLam a) (fanTh a - eqLam a)) := by ring
        _ ≤ 1 * (Ke * min (1 - eqLam a) (fanTh a - eqLam a)) :=
            mul_le_mul_of_nonneg_right hlam1.le h8
        _ = _ := one_mul _
    linarith [h, h6.le, h6.ge, h7]
  have h64Δ : Cx * (4 * Lam * Δ) ^ 2 ≤ (1 - a) / 16 := by
    have h1 : (4 * Lam * Δ) ^ 2 = 16 * Lam ^ 2 * Δ ^ 2 := by ring
    rw [h1]
    have h2 : 16 * Cx * Lam ^ 2 * Δ ^ 2 ≤ 16 * Cx * Lam ^ 2 * Δ * Δ := by nlinarith [hΔ0.le]
    have h3 : 16 * Cx * Lam ^ 2 * Δ * Δ ≤ (1 - a) / 4 * Δ := by
      have h := mul_le_mul_of_nonneg_right hΔE hΔ0.le
      have h2' : 16 * Cx * Lam ^ 2 * (((1 - a) / (64 * Cx * Lam ^ 2)) * Δ) = (1 - a) / 4 * Δ := by
        field_simp
        norm_num
      have h3' : 16 * Cx * Lam ^ 2 * (Δ * Δ)
          ≤ 16 * Cx * Lam ^ 2 * (((1 - a) / (64 * Cx * Lam ^ 2)) * Δ) :=
        mul_le_mul_of_nonneg_left h (by positivity)
      linarith [h3', h2'.le, h2'.ge]
    have h4 : (1 - a) / 4 * Δ ≤ (1 - a) / 16 := by
      have h := mul_le_mul_of_nonneg_left hΔ14 (by positivity : (0:ℝ) ≤ (1 - a) / 4)
      linarith [h]
    linarith [h2, h3, h4]
  have h16Δ2 : 16 * Cx * Lam ^ 2 * Δ ≤ 16 * Cx * Lam ^ 2 * Δ := le_rfl
  have key : ∀ ε : List Bool, ∀ v : ℂ, ‖v‖ < Δ → FanDecay a h Ke Lam Qc ε v := by
    intro ε
    induction ε with
    | nil =>
      intro v hv
      obtain ⟨hb1, hb2⟩ := hgerm v (lt_of_lt_of_le hv hΔδg)
      have hvρg : v ∈ Metric.ball (0 : ℂ) ρg := by
        rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact lt_of_lt_of_le hv hΔρg
      have hg0 : (germC a h 0).1 - ((a / 2 : ℝ) : ℂ) = ((-(1 + a) / 2 : ℝ) : ℂ) := by
        rw [germC_value ha0 ha1 hSG]; push_cast; ring
      have h0f : (germC a h 0).1 = ((-1 / 2 : ℝ) : ℂ) := by
        rw [germC_value ha0 ha1 hSG]; norm_num
      have hb1c : ‖(germC a h v).1 - (germC a h 0).1‖ ≤ pg * ‖v‖ := by
        simpa [← h0f] using hb1
      have hbne : (germC a h v).1 - ((a / 2 : ℝ) : ℂ) ≠ 0 := by
        intro hcon
        have hsplit : (germC a h 0).1 - ((a / 2 : ℝ) : ℂ)
            = ((germC a h v).1 - ((a / 2 : ℝ) : ℂ))
              - ((germC a h v).1 - (germC a h 0).1) := by ring
        have h1 : ‖(germC a h 0).1 - ((a / 2 : ℝ) : ℂ)‖
            ≤ ‖(germC a h v).1 - ((a / 2 : ℝ) : ℂ)‖
              + ‖(germC a h v).1 - (germC a h 0).1‖ := by
          rw [hsplit]; exact norm_sub_le _ _
        rw [hcon, norm_zero, zero_add] at h1
        have hnorm : ‖((- (1 + a) / 2 : ℝ) : ℂ)‖ = (1 + a) / 2 := by
          rw [norm_ofReal_abs, abs_of_neg (by linarith)]; ring
        rw [hg0, hnorm] at h1
        have hpv : pg * ‖v‖ ≤ Ke * ‖v‖ := mul_le_mul_of_nonneg_right hKepg (norm_nonneg v)
        have hKev : Ke * ‖v‖ ≤ Ke * Δ := mul_le_mul_of_nonneg_left hv.le hKe0.le
        have hs : ‖(germC a h v).1 - (germC a h 0).1‖ ≤ (1 - a) / 16 := by
          linarith [hb1c, hpv, hKev, hKeΔ]
        have hfin : (1 + a) / 2 ≤ (1 - a) / 16 := le_trans h1 hs
        linarith [hfin, ha0, ha1]
      have hb3 : ‖(germC a h v).2 / ((germC a h v).1 - ((a / 2 : ℝ) : ℂ))‖ ≤ qg * ‖v‖ :=
        norm_div_le_of_le_mul (by positivity) hb2
      have hcl3 : ‖(germC a h v).2 / ((germC a h v).1 - ((a / 2 : ℝ) : ℂ))‖
          ≤ Lam * (fanTh a) ^ (Vis ([] : List Bool)) * ‖v‖ * (1 + Qc * ‖v‖) := by
        rw [hVis_nil, pow_zero, mul_one]
        have h2 : qg * ‖v‖ ≤ Lam * ‖v‖ := mul_le_mul_of_nonneg_right hLamqg (norm_nonneg v)
        have h3 : Lam * ‖v‖ ≤ Lam * ‖v‖ * (1 + Qc * ‖v‖) := by
          have h4 : (1 : ℝ) ≤ 1 + Qc * ‖v‖ := by
            have := mul_nonneg hQc0.le (norm_nonneg v); linarith
          calc Lam * ‖v‖ = Lam * ‖v‖ * 1 := (mul_one _).symm
            _ ≤ Lam * ‖v‖ * (1 + Qc * ‖v‖) := by
                exact mul_le_mul_of_nonneg_left h4 (mul_nonneg hLam0.le (norm_nonneg v))
        linarith [hb3, h2, h3]
      have hcl2 : ‖(germC a h v).1 - (germC a h 0).1‖
          ≤ Ke * (fanTh a) ^ (Vis ([] : List Bool)) * ‖v‖ := by
        rw [hVis_nil, pow_zero, mul_one]
        have h2 : pg * ‖v‖ ≤ Ke * ‖v‖ := mul_le_mul_of_nonneg_right hKepg (norm_nonneg v)
        exact le_trans hb1c h2
      have hb1'' : ‖(germC a h v).1 - ((-1 / 2 : ℝ) : ℂ)‖ ≤ pg * ‖v‖ := hb1
      have hcl5 : 0 < (((germC a h v).1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + (germC a h v).2 ^ 2).re := by
        refine radicand_pos (c := (-1 / 2 : ℝ)) (ρ := pg * ‖v‖) (τ := qg * ‖v‖) ha0 ha1 ⟨0, by norm_num⟩
          (by positivity) (by positivity) ?_ ?_ ?_ ?_ ?_
        · have h1 := mul_le_mul_of_nonneg_right hKepg (norm_nonneg v)
          have h2 := mul_le_mul_of_nonneg_left hv.le hKe0.le
          have hpv : pg * ‖v‖ ≤ Ke * Δ := by linarith [h1, h2]
          linarith [hb1, hpv, hKeΔ, ha1]
        · have hLv : Lam * ‖v‖ ≤ eqLam a / 16 := by
            have h3 : Lam * ‖v‖ ≤ Lam * Δ := mul_le_mul_of_nonneg_left hv.le hLam0.le
            linarith [h3, hLamΔ]
          have h2 : qg * ‖v‖ ≤ Lam * ‖v‖ := mul_le_mul_of_nonneg_right hLamqg (norm_nonneg v)
          linarith [hb3, h2, hLv, hlam1]
        · simpa using hb1''
        · simpa using hbne
        · simpa using hb3
      exact ⟨hgan v hvρg, hcl2, hcl3, hbne, hcl5⟩
    | cons s ε ih =>
      intro v hv
      set w : ℝ := ‖v‖ with hwdef
      have hw0 : 0 ≤ w := by rw [hwdef]; positivity
      have hwlt : w < Δ := by rw [hwdef]; exact hv
      have hwle : w ≤ Δ := hwlt.le
      have hlamv : ‖(eqLam a : ℂ) * v‖ = eqLam a * w := by
        rw [norm_mul, norm_ofReal_abs, abs_of_pos hlam0, hwdef]
      have hlamvΔ : ‖(eqLam a : ℂ) * v‖ < Δ := by
        rw [hlamv]
        calc eqLam a * w ≤ 1 * w := mul_le_mul_of_nonneg_right hlam1.le hw0
          _ = w := one_mul _
          _ < Δ := hwlt
      obtain ⟨ihAn, ihX, ihW, ihb, ihre⟩ := ih ((eqLam a : ℂ) * v) hlamvΔ
      obtain ⟨hzε, k, hk⟩ := (FanSep.axis_walk ha0 ha1 hSG).2 ε
      set x₁ : ℝ := -1 / 2 + 2 * (k : ℝ) with hx₁def
      have hx₁c : (fan a h ε 0).1 = ((x₁ : ℝ) : ℂ) := by
        rw [hx₁def]
        rw [hk]; push_cast; ring
      have hP0 : fan a h ε 0 = (((x₁ : ℝ) : ℂ), (0 : ℂ)) := Prod.ext hx₁c hzε
      set F : ℝ := (fanTh a) ^ (Vis ε) with hFdef
      have hF0 : 0 ≤ F := by rw [hFdef]; positivity
      have hF1 : F ≤ 1 := by rw [hFdef]; exact pow_le_one₀ (le_of_lt hth0) (le_of_lt hth1)
      have hpowV : (fanTh a) ^ (Vis (s :: ε)) = F * tau a ε := by
        rw [hVis_cons s ε, hpow ε, hFdef]
      have hxcn : x₁ + a / 2 ≠ 0 := by
        intro hcon
        have h := (FanSep.centre_numbers ha0 ha1).1 k |>.1
        rw [FanSep.norm_ofReal_add_eq_abs] at h
        have h2 : (1 - a) / 2 ≤ |x₁ + a / 2| := by rw [hx₁def]; exact h
        rw [hcon, abs_zero] at h2
        linarith [ha1, h2]
      have hpar : (fan a h (s :: ε) 0).1 = ((axStep a s x₁ : ℝ) : ℂ) := by
        show (invBranch a s (fan a h ε ((eqLam a : ℂ) * 0))).1 = _
        rw [mul_zero, hP0, FanSep.invBranch_axis a s hxcn]
      set Qp : ℂ × ℂ := fan a h ε ((eqLam a : ℂ) * v) with hQpdef
      have hQpX : ‖Qp.1 - ((x₁ : ℝ) : ℂ)‖ ≤ Ke * F * (eqLam a * w) := by
        rw [hQpdef]
        have h := ihX
        rw [hx₁c, hlamv, hFdef] at h
        exact h
      set τw : ℝ := Lam * F * (eqLam a * w) * (1 + Qc * (eqLam a * w)) with hτwdef
      have hQpW : ‖Qp.2 / (Qp.1 - ((a / 2 : ℝ) : ℂ))‖ ≤ τw := by
        rw [hτwdef, hQpdef]
        have h := ihW
        rw [hlamv, hFdef] at h
        exact h
      have hQb : Qp.1 - ((a / 2 : ℝ) : ℂ) ≠ 0 := by rw [hQpdef]; exact ihb
      have hτw0 : 0 ≤ τw := by rw [hτwdef]; positivity
      have hQp2 : ‖Qp.2‖ ≤ τw * ‖Qp.1 - ((a / 2 : ℝ) : ℂ)‖ := by
        have h := hQpW
        rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr hQb)] at h
        linarith [h]
      have hcx1 : ((x₁ : ℝ) : ℂ) + ((a / 2 : ℝ) : ℂ)
          = (((-1 / 2 + 2 * (k : ℝ)) + a / 2 : ℝ) : ℂ) := by rw [hx₁def]; push_cast; ring
      have hcx2 : ((x₁ : ℝ) : ℂ) - ((a / 2 : ℝ) : ℂ)
          = (((-1 / 2 + 2 * (k : ℝ)) - a / 2 : ℝ) : ℂ) := by rw [hx₁def]; push_cast; ring
      have hc1x : (1 - a) / 2 ≤ ‖((x₁ : ℝ) : ℂ) + ((a / 2 : ℝ) : ℂ)‖ := by
        have h := (FanSep.centre_numbers ha0 ha1).1 k |>.1
        rw [FanSep.norm_ofReal_add_eq_abs] at h
        rw [hcx1, norm_ofReal_abs]
        exact h
      have hc2x : (1 - a) / 2 ≤ ‖((x₁ : ℝ) : ℂ) - ((a / 2 : ℝ) : ℂ)‖ := by
        have h := (FanSep.centre_numbers ha0 ha1).1 k |>.2
        rw [FanSep.norm_ofReal_sub_eq_abs] at h
        rw [hcx2, norm_ofReal_abs]
        exact h
      have hc0x : 0 < ‖((x₁ : ℝ) : ℂ) + ((a / 2 : ℝ) : ℂ)‖ :=
        lt_of_lt_of_le (by linarith) hc1x
      have hrc0 : 0 ≤ ‖((x₁ : ℝ) : ℂ) - ((a / 2 : ℝ) : ℂ)‖
          / ‖((x₁ : ℝ) : ℂ) + ((a / 2 : ℝ) : ℂ)‖ := div_nonneg (norm_nonneg _) hc0x.le
      have hratio_le : (‖((x₁ : ℝ) : ℂ) - ((a / 2 : ℝ) : ℂ)‖
            / ‖((x₁ : ℝ) : ℂ) + ((a / 2 : ℝ) : ℂ)‖) * eqLam a ≤ tau a ε := by
        have h1 : ‖((x₁ : ℝ) : ℂ) - ((a / 2 : ℝ) : ℂ)‖ = |x₁ - a / 2| := by
          rw [hcx2, norm_ofReal_abs]
        have h2 : ‖((x₁ : ℝ) : ℂ) + ((a / 2 : ℝ) : ℂ)‖ = |x₁ + a / 2| := by
          rw [hcx1, norm_ofReal_abs]
        rw [h1, h2]
        have h4 := lam_ratio_le_tau ha0 ha1 hSG hctrV ε
        rw [hx₁c, FanSep.norm_ofReal_sub_eq_abs, FanSep.norm_ofReal_add_eq_abs] at h4
        have h6 : (|x₁ - a / 2| / |x₁ + a / 2|) * eqLam a
            = eqLam a * (|x₁ - a / 2| / |x₁ + a / 2|) := by ring
        linarith [h4, h6.le, h6.ge]
      have hdev : ‖Qp.1 - ((x₁ : ℝ) : ℂ)‖ ≤ (1 - a) / 8 := by
        have h1 : Ke * F * (eqLam a * w) ≤ Ke * (eqLam a * w) := by
          have h2 := mul_le_mul_of_nonneg_left hF1 hKe0.le
          nlinarith [h2, mul_nonneg hlam0.le hw0]
        have h3 : Ke * (eqLam a * w) ≤ Ke * (eqLam a * Δ) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hwle hlam0.le) hKe0.le
        have h4 : Ke * (eqLam a * Δ) ≤ (1 - a) / 16 := by
          have h7 : 0 ≤ Ke * Δ := mul_nonneg hKe0.le hΔ0.le
          have h6 : Ke * eqLam a * Δ ≤ Ke * Δ := by
            calc Ke * eqLam a * Δ = eqLam a * (Ke * Δ) := by ring
              _ ≤ 1 * (Ke * Δ) := mul_le_mul_of_nonneg_right hlam1.le h7
              _ = Ke * Δ := one_mul _
          linarith [h6, hKeΔ, ha1]
        have h5 : ‖Qp.1 - ((x₁ : ℝ) : ℂ)‖ ≤ (1 - a) / 16 := by linarith [hQpX, h1, h3, h4]
        linarith [h5, ha1]
      have hconv : ‖Qp.1 - ((a / 2 : ℝ) : ℂ)‖
          ≤ (‖((x₁ : ℝ) : ℂ) - ((a / 2 : ℝ) : ℂ)‖ / ‖((x₁ : ℝ) : ℂ) + ((a / 2 : ℝ) : ℂ)‖)
            * (1 + Cw * ‖Qp.1 - ((x₁ : ℝ) : ℂ)‖) * ‖Qp.1 + ((a / 2 : ℝ) : ℂ)‖ := by
        have hkey := hCw (c := x₁) (Q := Qp.1) hc1x hc2x hdev
        have h2 : ‖((x₁ : ℝ) : ℂ) - ((a / 2 : ℝ) : ℂ)‖ * ‖Qp.1 + ((a / 2 : ℝ) : ℂ)‖
              * (1 + Cw * ‖Qp.1 - ((x₁ : ℝ) : ℂ)‖)
              = ‖((x₁ : ℝ) : ℂ) - ((a / 2 : ℝ) : ℂ)‖
                * (1 + Cw * ‖Qp.1 - ((x₁ : ℝ) : ℂ)‖) * ‖Qp.1 + ((a / 2 : ℝ) : ℂ)‖ := by ring
        rw [h2] at hkey
        calc ‖Qp.1 - ((a / 2 : ℝ) : ℂ)‖
            = ‖Qp.1 - ((a / 2 : ℝ) : ℂ)‖ * ‖((x₁ : ℝ) : ℂ) + ((a / 2 : ℝ) : ℂ)‖
              / ‖((x₁ : ℝ) : ℂ) + ((a / 2 : ℝ) : ℂ)‖ := by field_simp
          _ ≤ _ := div_le_div_of_nonneg_right hkey hc0x.le
          _ = _ := by field_simp
      set qw : ℝ := τw * (‖((x₁ : ℝ) : ℂ) - ((a / 2 : ℝ) : ℂ)‖
          / ‖((x₁ : ℝ) : ℂ) + ((a / 2 : ℝ) : ℂ)‖)
          * (1 + Cw * ‖Qp.1 - ((x₁ : ℝ) : ℂ)‖) with hqwdef
      have hqw0 : 0 ≤ qw := by rw [hqwdef]; positivity
      have hQ2 : ‖Qp.2‖ ≤ qw * ‖Qp.1 + ((a / 2 : ℝ) : ℂ)‖ := by
        rw [hqwdef]
        calc ‖Qp.2‖ ≤ τw * ‖Qp.1 - ((a / 2 : ℝ) : ℂ)‖ := hQp2
          _ ≤ τw * ((‖((x₁ : ℝ) : ℂ) - ((a / 2 : ℝ) : ℂ)‖
                / ‖((x₁ : ℝ) : ℂ) + ((a / 2 : ℝ) : ℂ)‖)
              * (1 + Cw * ‖Qp.1 - ((x₁ : ℝ) : ℂ)‖) * ‖Qp.1 + ((a / 2 : ℝ) : ℂ)‖) :=
              mul_le_mul_of_nonneg_left hconv hτw0
          _ = τw * (‖((x₁ : ℝ) : ℂ) - ((a / 2 : ℝ) : ℂ)‖
                / ‖((x₁ : ℝ) : ℂ) + ((a / 2 : ℝ) : ℂ)‖)
              * (1 + Cw * ‖Qp.1 - ((x₁ : ℝ) : ℂ)‖) * ‖Qp.1 + ((a / 2 : ℝ) : ℂ)‖ := by ring
      have hd1 : Cw * ‖Qp.1 - ((x₁ : ℝ) : ℂ)‖ ≤ 1 := by
        have h1 : Cw * ‖Qp.1 - ((x₁ : ℝ) : ℂ)‖ ≤ Cw * (Ke * (eqLam a * w)) := by
          have h2 : Ke * F * (eqLam a * w) ≤ Ke * (eqLam a * w) := by
            have h3 := mul_le_mul_of_nonneg_left hF1 hKe0.le
            nlinarith [h3, mul_nonneg hlam0.le hw0]
          exact mul_le_mul_of_nonneg_left (le_trans hQpX h2) hCwpos.le
        have h2 : Cw * Ke * (eqLam a * w) ≤ Cw * Ke * (eqLam a * Δ) := by
          have h := mul_le_mul_of_nonneg_left hwle hlam0.le
          exact mul_le_mul_of_nonneg_left h (by positivity : (0:ℝ) ≤ Cw * Ke)
        have h3 : Cw * Ke * (eqLam a * Δ) ≤ 1 := by
          have h5 : Cw * Ke * (eqLam a * Δ) = Cw * Ke * eqLam a * Δ := by ring
          rw [h5]; exact hCwΔ
        linarith [h1, h2, h3, hCwpos]
      have hQcw : Qc * (eqLam a * w) ≤ 1 := by
        have h1a : eqLam a * w ≤ w := by
          calc eqLam a * w ≤ 1 * w := mul_le_mul_of_nonneg_right hlam1.le hw0
            _ = w := one_mul _
        have h1 : Qc * (eqLam a * w) ≤ Qc * w := mul_le_mul_of_nonneg_left h1a hQc0.le
        have h2 : Qc * w ≤ Qc * Δ := mul_le_mul_of_nonneg_left hwle hQc0.le
        exact le_trans h1 (le_trans h2 hQcΔ)
      have hd : ‖Qp.1 - ((x₁ : ℝ) : ℂ)‖ ≤ Ke * eqLam a * w := by
        have h1 : Ke * F * (eqLam a * w) ≤ Ke * (eqLam a * w) := by
          have h2 := mul_le_mul_of_nonneg_left hF1 hKe0.le
          nlinarith [h2, mul_nonneg hlam0.le hw0]
        linarith [hQpX, h1]
      have hclosw : (1 + Qc * (eqLam a * w)) * (1 + Cw * ‖Qp.1 - ((x₁ : ℝ) : ℂ)‖)
          ≤ 1 + Qc * w :=
        clos_w hQc0 hCwpos hKe0 hlam0 hw0 (norm_nonneg _) hd hQcw hQcbig
      have hrat1 : ‖((x₁ : ℝ) : ℂ) - ((a / 2 : ℝ) : ℂ)‖
          / ‖((x₁ : ℝ) : ℂ) + ((a / 2 : ℝ) : ℂ)‖ * eqLam a ≤ 1 := by
        have h2 : tau a ε ≤ 1 := (htau ε).2.1
        linarith [hratio_le, h2]
      have hqw4 : qw ≤ 4 * Lam * F * w := by
        rw [hqwdef, hτwdef]
        exact qw_bound hLam0.le hF0 hlam0 hw0 hQc0.le hrat1 (by positivity) hd1 hQcw
      have hqw12 : qw ≤ 1 / 2 := by
        have h4 : 4 * Lam * F * w ≤ 1 / 2 := by
          have h5 : 4 * Lam * F * w ≤ 4 * Lam * w := by
            have h6 := mul_le_mul_of_nonneg_left hF1 (by positivity : (0:ℝ) ≤ 4 * Lam)
            nlinarith [h6, hw0]
          have h7 : 4 * Lam * w ≤ 4 * Lam * Δ :=
            mul_le_mul_of_nonneg_left hwle (by positivity : (0:ℝ) ≤ 4 * Lam)
          have h8 : 4 * Lam * Δ ≤ 1 / 2 := by
            have h := mul_le_mul_of_nonneg_left hLamΔ (by positivity : (0:ℝ) ≤ 4)
            linarith [h, hlam1]
          linarith [h5, h7, h8]
        linarith [hqw4, h4]
      have hmle : min (1 - eqLam a) (fanTh a - eqLam a) ≤ tau a ε - eqLam a := by
        rcases eq_or_ne (fLvl ε 0) 0 with h0 | h0
        · have ht : tau a ε = 1 := by unfold tau; rw [if_pos h0]
          rw [ht]; exact min_le_left _ _
        · have ht : tau a ε = fanTh a := by unfold tau; rw [if_neg h0]
          rw [ht]; exact min_le_right _ _
      have hclosx : Ke * F * (eqLam a * w) + Cx * qw ^ 2 ≤ Ke * F * tau a ε * w := by
        have h := clos_x hKe0 hCxpos hLam0 hF0 hF1 hw0 hwle hqw0 hqw4 h16Δ hmle
        have h2 : Ke * F * (eqLam a * w) = Ke * F * eqLam a * w := by ring
        linarith [h, h2.le, h2.ge]
      have hstepw := wFan_cons_le (a := a) (h := h) s ε v hQb
      have hcl3 : ‖wFan a h (s :: ε) v‖
          ≤ Lam * (fanTh a) ^ (Vis (s :: ε)) * ‖v‖ * (1 + Qc * ‖v‖) := by
        have h1 : ‖wFan a h (s :: ε) v‖ ≤ τw
            * (‖((x₁ : ℝ) : ℂ) - ((a / 2 : ℝ) : ℂ)‖
              / ‖((x₁ : ℝ) : ℂ) + ((a / 2 : ℝ) : ℂ)‖)
            * (1 + Cw * ‖Qp.1 - ((x₁ : ℝ) : ℂ)‖) := by
          have h2 : ‖wFan a h (s :: ε) v‖
              ≤ ‖wFan a h ε ((eqLam a : ℂ) * v)‖
                * (‖Qp.1 - ((a / 2 : ℝ) : ℂ)‖ / ‖Qp.1 + ((a / 2 : ℝ) : ℂ)‖) := by
            exact hstepw
          have h3 : ‖wFan a h ε ((eqLam a : ℂ) * v)‖ ≤ τw := hQpW
          have h4 : ‖Qp.1 - ((a / 2 : ℝ) : ℂ)‖ / ‖Qp.1 + ((a / 2 : ℝ) : ℂ)‖
              ≤ (‖((x₁ : ℝ) : ℂ) - ((a / 2 : ℝ) : ℂ)‖
                / ‖((x₁ : ℝ) : ℂ) + ((a / 2 : ℝ) : ℂ)‖)
                * (1 + Cw * ‖Qp.1 - ((x₁ : ℝ) : ℂ)‖) := by
            have hden : 0 < ‖Qp.1 + ((a / 2 : ℝ) : ℂ)‖ := by
              have hsplit : ((x₁ : ℝ) : ℂ) + ((a / 2 : ℝ) : ℂ)
                  = (Qp.1 + ((a / 2 : ℝ) : ℂ)) - (Qp.1 - ((x₁ : ℝ) : ℂ)) := by ring
              have h7 : ‖((x₁ : ℝ) : ℂ) + ((a / 2 : ℝ) : ℂ)‖
                  ≤ ‖Qp.1 + ((a / 2 : ℝ) : ℂ)‖ + ‖Qp.1 - ((x₁ : ℝ) : ℂ)‖ := by
                rw [hsplit]; exact norm_sub_le _ _
              linarith [h7, hc1x, hdev, ha1]
            rw [div_le_iff₀ hden]
            exact hconv
          have h5 : ‖wFan a h ε ((eqLam a : ℂ) * v)‖
              * (‖Qp.1 - ((a / 2 : ℝ) : ℂ)‖ / ‖Qp.1 + ((a / 2 : ℝ) : ℂ)‖)
              ≤ τw * (‖Qp.1 - ((a / 2 : ℝ) : ℂ)‖ / ‖Qp.1 + ((a / 2 : ℝ) : ℂ)‖) :=
            mul_le_mul_of_nonneg_right h3 (by positivity)
          have h6 : τw * (‖Qp.1 - ((a / 2 : ℝ) : ℂ)‖ / ‖Qp.1 + ((a / 2 : ℝ) : ℂ)‖)
              ≤ τw * ((‖((x₁ : ℝ) : ℂ) - ((a / 2 : ℝ) : ℂ)‖
                / ‖((x₁ : ℝ) : ℂ) + ((a / 2 : ℝ) : ℂ)‖)
                * (1 + Cw * ‖Qp.1 - ((x₁ : ℝ) : ℂ)‖)) :=
            mul_le_mul_of_nonneg_left h4 hτw0
          linarith [le_trans h2 h5, h6]
        have h5 : τw * (‖((x₁ : ℝ) : ℂ) - ((a / 2 : ℝ) : ℂ)‖
              / ‖((x₁ : ℝ) : ℂ) + ((a / 2 : ℝ) : ℂ)‖)
              * (1 + Cw * ‖Qp.1 - ((x₁ : ℝ) : ℂ)‖)
            ≤ Lam * F * tau a ε * w * (1 + Qc * w) := by
          rw [hτwdef]
          exact clos_wfan hLam0.le hF0 hw0 hlam0.le hQc0.le hrc0 (by positivity)
            hratio_le (le_of_lt (htau ε).1) hclosw
        have h6 : Lam * F * tau a ε * w * (1 + Qc * w)
            = Lam * (fanTh a) ^ (Vis (s :: ε)) * w * (1 + Qc * w) := by
          rw [hpowV]; ring
        rw [h6] at h5
        exact le_trans h1 h5
      have hstepx := hCx s x₁ Qp qw hc1x hdev hQ2 hqw12
      have hcl2 : ‖(fan a h (s :: ε) v).1 - (fan a h (s :: ε) 0).1‖
          ≤ Ke * (fanTh a) ^ (Vis (s :: ε)) * ‖v‖ := by
        have h1 : (fan a h (s :: ε) v).1 = (invBranch a s Qp).1 := by
          show (invBranch a s (fan a h ε ((eqLam a : ℂ) * v))).1 = _; rw [hQpdef]
        have h2 : (fan a h (s :: ε) 0).1
            = (((-x₁ + sgnB s * sgnR (x₁ + a / 2) : ℝ)) : ℂ) := by
          rw [hpar, axStep]
        rw [h1, h2]
        have h3 : ‖(invBranch a s Qp).1 - ((axStep a s x₁ : ℝ) : ℂ)‖
            ≤ Ke * F * (eqLam a * w) + Cx * qw ^ 2 := by
          show ‖(invBranch a s Qp).1
            - (((-x₁ + sgnB s * sgnR (x₁ + a / 2) : ℝ)) : ℂ)‖
            ≤ Ke * F * (eqLam a * w) + Cx * qw ^ 2
          exact le_trans hstepx (add_le_add hQpX le_rfl)
        have h4 : Ke * F * tau a ε * w = Ke * (fanTh a) ^ (Vis (s :: ε)) * w := by
          rw [hpowV]; ring
        rw [h4] at hclosx
        exact le_trans h3 hclosx
      have hcn2' : ∃ k' : ℤ, axStep a s x₁ = -1 / 2 + 2 * (k' : ℝ) := by
        rw [axStep]
        rcases sgnB_cases s with hs | hs <;> rcases sgnR_cases (x₁ + a / 2) with hr | hr
        · exact ⟨1 - k, by rw [hs, hr, hx₁def]; push_cast; ring⟩
        · exact ⟨-k, by rw [hs, hr, hx₁def]; push_cast; ring⟩
        · exact ⟨-k, by rw [hs, hr, hx₁def]; push_cast; ring⟩
        · exact ⟨1 - k, by rw [hs, hr, hx₁def]; push_cast; ring⟩
      have hnewb : ‖(invBranch a s Qp).1 - ((axStep a s x₁ : ℝ) : ℂ)‖ < (1 - a) / 2 := by
        have h3 : ‖(invBranch a s Qp).1 - ((axStep a s x₁ : ℝ) : ℂ)‖
            ≤ Ke * F * (eqLam a * w) + Cx * qw ^ 2 := by
          show ‖(invBranch a s Qp).1
            - (((-x₁ + sgnB s * sgnR (x₁ + a / 2) : ℝ)) : ℂ)‖
            ≤ Ke * F * (eqLam a * w) + Cx * qw ^ 2
          exact le_trans hstepx (add_le_add hQpX le_rfl)
        have h5 : Ke * F * (eqLam a * w) ≤ (1 - a) / 16 := by
          have h6 : Ke * (eqLam a * w) ≤ Ke * (eqLam a * Δ) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hwle hlam0.le) hKe0.le
          have h7 : Ke * F * (eqLam a * w) ≤ Ke * (eqLam a * w) := by
            have h8 : Ke * F ≤ Ke * 1 := mul_le_mul_of_nonneg_left hF1 hKe0.le
            have h8' : (0:ℝ) ≤ eqLam a * w := mul_nonneg hlam0.le hw0
            calc Ke * F * (eqLam a * w) = (Ke * F) * (eqLam a * w) := by ring
              _ ≤ (Ke * 1) * (eqLam a * w) := mul_le_mul_of_nonneg_right h8 h8'
              _ = Ke * (eqLam a * w) := by ring
          have h9 : Ke * (eqLam a * Δ) ≤ (1 - a) / 16 := by
            have h7' : 0 ≤ Ke * Δ := mul_nonneg hKe0.le hΔ0.le
            have h8 : Ke * (eqLam a * Δ) ≤ Ke * Δ := by
              calc Ke * (eqLam a * Δ) = eqLam a * (Ke * Δ) := by ring
                _ ≤ 1 * (Ke * Δ) := mul_le_mul_of_nonneg_right hlam1.le h7'
                _ = Ke * Δ := one_mul _
            exact le_trans h8 hKeΔ
          exact le_trans h7 (le_trans h6 h9)
        have h10 : Cx * qw ^ 2 ≤ (1 - a) / 16 := by
          have h11 : qw ^ 2 ≤ (4 * Lam * Δ) ^ 2 := by
            have h13 : 4 * Lam * F * w ≤ 4 * Lam * Δ := by
              have h14 : 4 * Lam * F ≤ 4 * Lam * 1 := mul_le_mul_of_nonneg_left hF1 (by positivity)
              calc 4 * Lam * F * w = (4 * Lam * F) * w := by ring
                _ ≤ (4 * Lam * 1) * w := mul_le_mul_of_nonneg_right h14 hw0
                _ ≤ (4 * Lam * 1) * Δ := mul_le_mul_of_nonneg_left hwle (by positivity)
                _ = 4 * Lam * Δ := by ring
            exact pow_le_pow_left₀ hqw0 (le_trans hqw4 h13) 2
          calc Cx * qw ^ 2 ≤ Cx * (4 * Lam * Δ) ^ 2 := mul_le_mul_of_nonneg_left h11 hCxpos.le
            _ ≤ (1 - a) / 16 := h64Δ
        linarith [h3, h5, h10, h1a]
      have hcl4 : (invBranch a s Qp).1 - ((a / 2 : ℝ) : ℂ) ≠ 0 := by
        obtain ⟨k', hk'⟩ := hcn2'
        have h2 : (1 - a) / 2 ≤ ‖((axStep a s x₁ : ℝ) : ℂ) - ((a / 2 : ℝ) : ℂ)‖ := by
          have h := (FanSep.centre_numbers ha0 ha1).1 k' |>.2
          rw [FanSep.norm_ofReal_sub_eq_abs] at h
          rw [FanSep.norm_ofReal_sub_eq_abs]
          rwa [hk']
        intro hcon
        have h3 : ‖((axStep a s x₁ : ℝ) : ℂ) - ((a / 2 : ℝ) : ℂ)‖
            ≤ ‖(invBranch a s Qp).1 - ((a / 2 : ℝ) : ℂ)‖
              + ‖(invBranch a s Qp).1 - ((axStep a s x₁ : ℝ) : ℂ)‖ := by
          have hsplit : ((axStep a s x₁ : ℝ) : ℂ) - ((a / 2 : ℝ) : ℂ)
              = ((invBranch a s Qp).1 - ((a / 2 : ℝ) : ℂ))
                - ((invBranch a s Qp).1 - ((axStep a s x₁ : ℝ) : ℂ)) := by ring
          rw [hsplit]; exact norm_sub_le _ _
        have h4 : (1 - a) / 2 ≤ ‖(invBranch a s Qp).1 - ((axStep a s x₁ : ℝ) : ℂ)‖ := by
          rw [hcon, norm_zero, zero_add] at h3
          exact le_trans h2 h3
        exact absurd (lt_of_lt_of_le hnewb h4) (lt_irrefl _)
      have hcl5 : 0 < (((invBranch a s Qp).1 + ((a / 2 : ℝ) : ℂ)) ^ 2
          + (invBranch a s Qp).2 ^ 2).re := by
        have hρ : Ke * F * w ≤ (1 - a) / 16 := by
          have h6 : Ke * F * w ≤ Ke * w := by
            have h7 := mul_le_mul_of_nonneg_left hF1 hKe0.le
            calc Ke * F * w = (Ke * F) * w := by ring
              _ ≤ (Ke * 1) * w := mul_le_mul_of_nonneg_right h7 hw0
              _ = Ke * w := by ring
          exact le_trans (le_trans h6 (mul_le_mul_of_nonneg_left hwle hKe0.le)) hKeΔ
        have hτ : Lam * F * w * (1 + Qc * w) ≤ eqLam a / 8 := by
          have h1 : Lam * F * w ≤ Lam * w := by
            have h := mul_le_mul_of_nonneg_left hF1 hLam0.le
            calc Lam * F * w = (Lam * F) * w := by ring
              _ ≤ (Lam * 1) * w := mul_le_mul_of_nonneg_right h hw0
              _ = Lam * w := by ring
          have h2 : 1 + Qc * w ≤ 2 := by
            have h := mul_le_mul_of_nonneg_left hwle hQc0.le
            have hQw : Qc * w ≤ 1 := le_trans h hQcΔ
            linarith [hQw]
          have h3 : Lam * w ≤ Lam * Δ := mul_le_mul_of_nonneg_left hwle hLam0.le
          have h4 : Lam * Δ * 2 ≤ eqLam a / 8 := by
            have h := mul_le_mul_of_nonneg_left hLamΔ (by norm_num : (0:ℝ) ≤ 2)
            linarith [h]
          calc Lam * F * w * (1 + Qc * w) ≤ Lam * w * 2 :=
                mul_le_mul h1 h2 (by positivity) (mul_nonneg hLam0.le hw0)
            _ ≤ Lam * Δ * 2 := by linarith [h3]
            _ ≤ eqLam a / 8 := h4
        refine radicand_pos (c := axStep a s x₁) (P := invBranch a s Qp)
          (ρ := Ke * (fanTh a) ^ (Vis (s :: ε)) * ‖v‖)
          (τ := Lam * (fanTh a) ^ (Vis (s :: ε)) * ‖v‖ * (1 + Qc * ‖v‖))
          ha0 ha1 hcn2' (by positivity) (by positivity) ?_ ?_ ?_ ?_ ?_
        · have h1 : Ke * (fanTh a) ^ (Vis (s :: ε)) * ‖v‖ = Ke * F * tau a ε * w := by
            rw [hpowV]; ring
          rw [h1]
          have h2 : Ke * F * tau a ε * w ≤ Ke * F * w := by
            have h4 : 0 ≤ Ke * F * w := by positivity
            calc Ke * F * tau a ε * w = tau a ε * (Ke * F * w) := by ring
              _ ≤ 1 * (Ke * F * w) := mul_le_mul_of_nonneg_right (htau ε).2.1 h4
              _ = Ke * F * w := one_mul _
          exact le_trans h2 hρ
        · have h1 : Lam * (fanTh a) ^ (Vis (s :: ε)) * ‖v‖ * (1 + Qc * ‖v‖)
              = Lam * F * tau a ε * w * (1 + Qc * w) := by
            rw [hpowV]; ring
          rw [h1]
          have h2 : Lam * F * tau a ε * w * (1 + Qc * w) ≤ Lam * F * w * (1 + Qc * w) := by
            have h4 : 0 ≤ Lam * F * w * (1 + Qc * w) := by positivity
            calc Lam * F * tau a ε * w * (1 + Qc * w)
                = tau a ε * (Lam * F * w * (1 + Qc * w)) := by ring
              _ ≤ 1 * (Lam * F * w * (1 + Qc * w)) :=
                  mul_le_mul_of_nonneg_right (htau ε).2.1 h4
              _ = Lam * F * w * (1 + Qc * w) := one_mul _
          exact le_trans h2 hτ
        · have h1 : (fan a h (s :: ε) v).1 = (invBranch a s Qp).1 := by
            show (invBranch a s (fan a h ε ((eqLam a : ℂ) * v))).1 = _
            rw [hQpdef]
          rw [← h1, ← hpar]
          exact hcl2
        · simpa using hcl4
        · have h1 : fan a h (s :: ε) v = invBranch a s Qp := by
            show invBranch a s (fan a h ε ((eqLam a : ℂ) * v)) = invBranch a s Qp
            rw [hQpdef]
          have h2 : wFan a h (s :: ε) v
              = (invBranch a s Qp).2 / ((invBranch a s Qp).1 - (a / 2 : ℂ)) := by
            rw [show (a : ℂ) / 2 = ((a / 2 : ℝ) : ℂ) from (Complex.ofReal_div a 2).symm]
            rw [wFan, h1]
          rw [← h2]
          exact hcl3
      refine ⟨?_, hcl2, hcl3, hcl4, hcl5⟩
      show AnalyticAt ℂ (fan a h (s :: ε)) v
      have hcomp : AnalyticAt ℂ (fun u : ℂ => fan a h ε ((eqLam a : ℂ) * u)) v :=
        AnalyticAt.comp (f := fun u : ℂ => (eqLam a : ℂ) * u) (x := v)
          ihAn (analyticAt_const.mul analyticAt_id)
      refine AnalyticAt.comp (f := fun u : ℂ => fan a h ε ((eqLam a : ℂ) * u)) (x := v)
        (analytic_invBranch (Q := fan a h ε ((eqLam a : ℂ) * v)) ?_) hcomp
      simpa using ihre
  -- assembly
  refine ⟨Δ, max (Lam * (1 + Qc * Δ)) Ke / fanTh a + 1, hΔ0, ?_, ?_⟩
  · have h1 : 0 < max (Lam * (1 + Qc * Δ)) Ke / fanTh a :=
      div_pos (lt_of_lt_of_le hKe0 (le_max_right _ _)) hth0
    linarith
  · intro ε u hu
    rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hu
    obtain ⟨hAn, hXu, hWu, hbu, hreu⟩ := key ε u hu
    set Q0 : ℝ := max (Lam * (1 + Qc * Δ)) Ke / fanTh a + 1 with hQ0def
    have hQ0pos : 0 < Q0 := by
      rw [hQ0def]
      have h1 : 0 < max (Lam * (1 + Qc * Δ)) Ke / fanTh a :=
        div_pos (lt_of_lt_of_le hKe0 (le_max_right _ _)) hth0
      linarith
    have hQ0le : max (Lam * (1 + Qc * Δ)) Ke / fanTh a ≤ Q0 := by
      rw [hQ0def]; linarith
    have hQ0K : Ke ≤ Q0 := by
      have h3 : Ke ≤ max (Lam * (1 + Qc * Δ)) Ke := le_max_right _ _
      have h4 : 0 < max (Lam * (1 + Qc * Δ)) Ke := lt_of_lt_of_le hKe0 h3
      rw [hQ0def]
      have h5 : Ke ≤ max (Lam * (1 + Qc * Δ)) Ke / fanTh a := by
        rw [le_div_iff₀ hth0]
        nlinarith [h4, hth1, h3]
      linarith
    have hstep : (fanTh a) ^ (Vis ε) * fanTh a ≤ (fanTh a) ^ (fVis ε) := by
      rw [hfvis_eq ε, pow_add]
      rcases eq_or_ne (fLvl ε 0) 0 with h | h
      · rw [if_pos h, pow_zero, mul_one]
        have h2 : (0:ℝ) < (fanTh a) ^ (Vis ε) := pow_pos hth0 _
        nlinarith [h2, hth1]
      · rw [if_neg h, pow_one]
    refine ⟨fun z hz => (key ε z (by rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hz; exact hz)).1,
      ?_, ?_⟩
    · have h1 : Lam * (fanTh a) ^ (Vis ε) * ‖u‖ * (1 + Qc * ‖u‖)
          ≤ (Lam * (1 + Qc * Δ)) * (fanTh a) ^ (Vis ε) * ‖u‖ := by
        have h2 : Lam * (1 + Qc * ‖u‖) ≤ Lam * (1 + Qc * Δ) := by
          have h3 := mul_le_mul_of_nonneg_left hu.le hQc0.le
          calc Lam * (1 + Qc * ‖u‖) = Lam * 1 + Lam * (Qc * ‖u‖) := by ring
            _ ≤ Lam * 1 + Lam * (Qc * Δ) := add_le_add le_rfl (mul_le_mul_of_nonneg_left h3 hLam0.le)
            _ = Lam * (1 + Qc * Δ) := by ring
        have h4 : Lam * (fanTh a) ^ (Vis ε) * ‖u‖ * (1 + Qc * ‖u‖)
            = (Lam * (1 + Qc * ‖u‖)) * (fanTh a) ^ (Vis ε) * ‖u‖ := by ring
        rw [h4]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right h2 (by positivity)) (norm_nonneg u)
      have h5 : (Lam * (1 + Qc * Δ)) * (fanTh a) ^ (Vis ε) * ‖u‖
          ≤ Q0 * ‖u‖ * (fanTh a) ^ (fVis ε) := by
        have h6 : (Lam * (1 + Qc * Δ)) * (fanTh a) ^ (Vis ε)
            ≤ Q0 * ((fanTh a) ^ (Vis ε) * fanTh a) := by
          have h7 : (Lam * (1 + Qc * Δ)) ≤ max (Lam * (1 + Qc * Δ)) Ke := le_max_left _ _
          have h8 : (0:ℝ) < (fanTh a) ^ (Vis ε) := pow_pos hth0 _
          have h9 : (max (Lam * (1 + Qc * Δ)) Ke) * (fanTh a) ^ (Vis ε)
              = (max (Lam * (1 + Qc * Δ)) Ke / fanTh a) * ((fanTh a) ^ (Vis ε) * fanTh a) := by
            field_simp
          have h10 : (max (Lam * (1 + Qc * Δ)) Ke / fanTh a) * ((fanTh a) ^ (Vis ε) * fanTh a)
              ≤ Q0 * ((fanTh a) ^ (Vis ε) * fanTh a) := by
            have h11 : 0 ≤ (fanTh a) ^ (Vis ε) * fanTh a := by positivity
            exact mul_le_mul_of_nonneg_right hQ0le h11
          calc (Lam * (1 + Qc * Δ)) * (fanTh a) ^ (Vis ε)
              ≤ (max (Lam * (1 + Qc * Δ)) Ke) * (fanTh a) ^ (Vis ε) :=
                mul_le_mul_of_nonneg_right h7 (le_of_lt h8)
            _ = _ := h9
            _ ≤ _ := h10
        have h12 : 0 ≤ Q0 * ‖u‖ := mul_nonneg hQ0pos.le (norm_nonneg u)
        calc (Lam * (1 + Qc * Δ)) * (fanTh a) ^ (Vis ε) * ‖u‖
            ≤ Q0 * ((fanTh a) ^ (Vis ε) * fanTh a) * ‖u‖ :=
              mul_le_mul_of_nonneg_right h6 (norm_nonneg u)
          _ = (Q0 * ‖u‖) * ((fanTh a) ^ (Vis ε) * fanTh a) := by ring
          _ ≤ (Q0 * ‖u‖) * (fanTh a) ^ (fVis ε) :=
              mul_le_mul_of_nonneg_left hstep h12
          _ = Q0 * ‖u‖ * (fanTh a) ^ (fVis ε) := by ring
      exact le_trans hWu (le_trans h1 h5)
    · have h1 : Ke * (fanTh a) ^ (Vis ε) * ‖u‖ ≤ Q0 * ‖u‖ * (fanTh a) ^ (fVis ε) := by
        have h4 : Ke * (fanTh a) ^ (Vis ε) * ‖u‖
            = (Ke * ((fanTh a) ^ (Vis ε) * fanTh a) / fanTh a) * ‖u‖ := by
          field_simp
        rw [h4]
        have h6 : 0 < (fanTh a) ^ (Vis ε) * fanTh a := by positivity
        have h5 : (Ke * ((fanTh a) ^ (Vis ε) * fanTh a) / fanTh a)
            ≤ Q0 * ((fanTh a) ^ (Vis ε) * fanTh a) := by
          have h5a : Ke * ((fanTh a) ^ (Vis ε) * fanTh a) / fanTh a
              ≤ (max (Lam * (1 + Qc * Δ)) Ke / fanTh a) * ((fanTh a) ^ (Vis ε) * fanTh a) := by
            have hX : 0 ≤ (fanTh a) ^ (Vis ε) * fanTh a := by positivity
            have hM : Ke ≤ max (Lam * (1 + Qc * Δ)) Ke := le_max_right _ _
            calc Ke * ((fanTh a) ^ (Vis ε) * fanTh a) / fanTh a
                = Ke * ((fanTh a) ^ (Vis ε)) := by
                  rw [mul_div_assoc, mul_div_cancel_right₀ _ (ne_of_gt hth0)]
              _ ≤ max (Lam * (1 + Qc * Δ)) Ke * ((fanTh a) ^ (Vis ε)) :=
                  mul_le_mul_of_nonneg_right hM (by positivity)
              _ = (max (Lam * (1 + Qc * Δ)) Ke / fanTh a) * ((fanTh a) ^ (Vis ε) * fanTh a) := by
                  field_simp
          have h5b : (max (Lam * (1 + Qc * Δ)) Ke / fanTh a) * ((fanTh a) ^ (Vis ε) * fanTh a)
              ≤ Q0 * ((fanTh a) ^ (Vis ε) * fanTh a) :=
            mul_le_mul_of_nonneg_right hQ0le h6.le
          linarith [h5a, h5b]
        have h12 : 0 ≤ Q0 * ‖u‖ := mul_nonneg hQ0pos.le (norm_nonneg u)
        calc (Ke * ((fanTh a) ^ (Vis ε) * fanTh a) / fanTh a) * ‖u‖
            ≤ Q0 * ((fanTh a) ^ (Vis ε) * fanTh a) * ‖u‖ :=
              mul_le_mul_of_nonneg_right h5 (norm_nonneg u)
          _ = (Q0 * ‖u‖) * ((fanTh a) ^ (Vis ε) * fanTh a) := by ring
          _ ≤ (Q0 * ‖u‖) * (fanTh a) ^ (fVis ε) :=
              mul_le_mul_of_nonneg_left hstep h12
          _ = Q0 * ‖u‖ * (fanTh a) ^ (fVis ε) := by ring
      exact le_trans hXu h1

end

end Work.EQ.FanTri
