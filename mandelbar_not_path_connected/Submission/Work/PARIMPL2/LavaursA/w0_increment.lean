import Mathlib
import Submission.Work.PARIMPL2.Lavaurs.Defs
import Submission.Work.FlowerGlue2.Defs
import Submission.Work.FlowerGlue2.L0

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `Work.PARIMPL2.LavaursA.w0_increment` — one step of the `c₀`-chart coordinate

In the chart coordinate `w₀ = −P.s c₀/(z − d.z₁)` (i.e. `w₀ = −1/ζ` in the normal form
`z = P.m c₀ + P.s c₀·ζ`), one iterate of the second return map `Ft c₀` moves `w₀` by

  `w₀(Ft c₀ z) − w₀ z = h_{c₀}(ζ)/(1 + ζ·h_{c₀}(ζ))`,  `ζ = −1/w₀ z`,

an exact identity of the normal form (`w0incr_eq` below).  Since the germ constant at the
parabolic parameter is `τ = h_{c₀}(0) = 1` (`Work.FlowerGlue2.tau_c₀`) and
`‖h_{c₀}(ζ) − 1 − h₁ ζ‖ ≤ A‖ζ‖²`, this increment is `1 + O(1/|w₀|)`; hence for `Re w₀ ≥ Rlo`
with `Rlo` large the *real* part of the increment is within `δ` of `1`, uniformly in everything
else.  That is `w0_increment`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open Classical Filter Set Metric
open scoped Topology

noncomputable section

namespace Work.PARIMPL2.LavaursA

open Work.PARIMPL (ParNormal Ft)

/-- At the parabolic parameter the germ's `a` vanishes: it is a root of `a₂ c₀ = 0`. -/
theorem w0incr_a_eq_zero {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (P : ParNormal d) :
    P.a c₀ = 0 := by
  have h := P.a_sq c₀ (Metric.mem_ball_self P.hρ₀)
  rw [P.a2₀] at h
  have h' : P.a c₀ * P.a c₀ = 0 := by simpa [pow_two] using h
  exact mul_self_eq_zero.mp h'

/-- The normal form in the chart at `c₀`:
`Ft c₀ (m c₀ + s c₀·ζ) − z₁ = s c₀·(ζ + ζ²·h c₀ ζ)`. -/
theorem w0incr_ft_chart {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (P : ParNormal d) {ζ : ℂ}
    (hζ : ‖ζ‖ < P.r) :
    Ft c₀ (P.m c₀ + P.s c₀ * ζ) - d.z₁ = P.s c₀ * (ζ + ζ ^ 2 * P.h c₀ ζ) := by
  have hmem : c₀ ∈ Metric.ball c₀ P.ρ₀ := Metric.mem_ball_self P.hρ₀
  have hconj := P.conj c₀ hmem ζ (by simpa [mem_ball_zero_iff] using hζ)
  rw [P.m₀, w0incr_a_eq_zero P] at hconj
  rw [show Work.Implosion.normalForm (0 : ℂ) (P.h c₀) ζ = ζ + ζ ^ 2 * P.h c₀ ζ by
        simp [Work.Implosion.normalForm]] at hconj
  rw [P.m₀, hconj]
  ring

/-- **The exact one-step formula of the chart, in chart coordinates.** -/
theorem w0incr_w0_Ft_chart {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (P : ParNormal d) {ζ : ℂ}
    (hζ : ‖ζ‖ < P.r) (hne : ζ ≠ 0) (hB : 1 + ζ * P.h c₀ ζ ≠ 0) :
    Work.PARIMPL2.w0 P (Ft c₀ (P.m c₀ + P.s c₀ * ζ)) = -1 / ζ / (1 + ζ * P.h c₀ ζ) := by
  have hs : P.s c₀ ≠ 0 := P.s_ne c₀ (Metric.mem_ball_self P.hρ₀)
  have hsub := w0incr_ft_chart P hζ
  have hfac : ζ + ζ ^ 2 * P.h c₀ ζ = ζ * (1 + ζ * P.h c₀ ζ) := by ring
  rw [Work.PARIMPL2.w0, hsub, hfac]
  field_simp

/-- **The exact one-step increment** of the `c₀`-chart coordinate:
`w₀(Ft c₀ z) − w₀ z = h_{c₀}(ζ)/(1 + ζ·h_{c₀}(ζ))` with `ζ = −1/w₀ z`. -/
theorem w0incr_eq {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (P : ParNormal d) {ζ : ℂ}
    (hζ : ‖ζ‖ < P.r) (hne : ζ ≠ 0) (hB : 1 + ζ * P.h c₀ ζ ≠ 0) :
    Work.PARIMPL2.w0 P (Ft c₀ (P.m c₀ + P.s c₀ * ζ)) - (-1 / ζ)
      = P.h c₀ ζ / (1 + ζ * P.h c₀ ζ) := by
  rw [w0incr_w0_Ft_chart P hζ hne hB]
  field_simp
  ring

theorem w0_increment {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (P : Work.PARIMPL.ParNormal d)
    {Pa : Set ℂ} {φa : ℂ → ℂ} (A : Work.FlowerGlue2.AttrCompare P Pa φa) (H : ℝ) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ Rlo : ℝ, 0 < Rlo ∧ ∀ z ∈ Pa, Rlo ≤ (Work.PARIMPL2.w0 P z).re →
      A.N < (Work.PARIMPL2.w0 P z).re → |(φa z).im| ≤ H →
      (1 - δ) ≤ (Work.PARIMPL2.w0 P (Work.PARIMPL.Ft c₀ z)).re - (Work.PARIMPL2.w0 P z).re ∧
      (Work.PARIMPL2.w0 P (Work.PARIMPL.Ft c₀ z)).re - (Work.PARIMPL2.w0 P z).re ≤ (1 + δ) := by
  set Cin : ℝ := 2 * (P.A + ‖P.h1 c₀‖ + 2) with hCin
  have hCin_pos : 0 < Cin := by
    rw [hCin]; linarith [P.hA, norm_nonneg (P.h1 c₀)]
  set t : ℝ := min (1 / 4) (min (P.r / 2) (δ / Cin)) with ht
  have ht_pos : 0 < t := by
    rw [ht]
    exact lt_min (by norm_num) (lt_min (by linarith [P.hr]) (div_pos hδ hCin_pos))
  have ht_le_q : t ≤ 1 / 4 := by rw [ht]; exact min_le_left _ _
  have ht_lt_Pr : t < P.r := by
    have h2 : t ≤ P.r / 2 := by rw [ht]; exact le_trans (min_le_right _ _) (min_le_left _ _)
    linarith [P.hr]
  have ht_le_d : Cin * t ≤ δ := by
    have h : t ≤ δ / Cin := by rw [ht]; exact le_trans (min_le_right _ _) (min_le_right _ _)
    have h2 := mul_le_mul_of_nonneg_left h hCin_pos.le
    rwa [mul_div_cancel₀ δ (ne_of_gt hCin_pos)] at h2
  refine ⟨1 / t, by positivity, fun z _hzPa hRlo _hN _hH => ?_⟩
  have hRlo_pos : (0 : ℝ) < 1 / t := by positivity
  have hz₁ : z ≠ d.z₁ := by
    rintro rfl
    simp only [Work.PARIMPL2.w0, sub_self, div_zero, Complex.zero_re] at hRlo
    linarith
  have hs : P.s c₀ ≠ 0 := P.s_ne c₀ (Metric.mem_ball_self P.hρ₀)
  have hw0ne : Work.PARIMPL2.w0 P z ≠ 0 := by
    rw [Work.PARIMPL2.w0]
    exact div_ne_zero (neg_ne_zero.mpr hs) (sub_ne_zero.mpr hz₁)
  set ζ : ℂ := -1 / Work.PARIMPL2.w0 P z with hζdef
  have hnorm_ge : 1 / t ≤ ‖Work.PARIMPL2.w0 P z‖ := le_trans hRlo (Complex.re_le_norm _)
  have hζ_le : ‖ζ‖ ≤ t := by
    rw [hζdef, norm_div, norm_neg, norm_one]
    have h1 : 1 / ‖Work.PARIMPL2.w0 P z‖ ≤ 1 / (1 / t) :=
      one_div_le_one_div_of_le hRlo_pos hnorm_ge
    rwa [one_div_one_div] at h1
  have hζ_lt_r : ‖ζ‖ < P.r := lt_of_le_of_lt hζ_le ht_lt_Pr
  have hζ_le_q : ‖ζ‖ ≤ 1 / 4 := le_trans hζ_le ht_le_q
  have hζ_ne : ζ ≠ 0 := by
    rw [hζdef]
    exact div_ne_zero (by norm_num) hw0ne
  have hζ_eq_w0 : -1 / ζ = Work.PARIMPL2.w0 P z := by
    rw [hζdef]; field_simp
  have hz_eq : z = P.m c₀ + P.s c₀ * ζ := by
    rw [hζdef, P.m₀, Work.PARIMPL2.w0]
    have hz : z - d.z₁ ≠ 0 := sub_ne_zero.mpr hz₁
    field_simp
    ring
  have hbnd := P.bounds c₀ (Metric.mem_ball_self P.hρ₀)
  have hh2 : ‖P.h c₀ ζ‖ ≤ 2 := hbnd.2.2.2.1 ζ hζ_lt_r
  have hh1 : ‖P.h c₀ ζ - 1‖ ≤ P.A * ‖ζ‖ ^ 2 + ‖P.h1 c₀‖ * ‖ζ‖ := by
    have h1 := hbnd.2.2.1 ζ hζ_lt_r
    have htau : P.h c₀ 0 = 1 := Work.FlowerGlue2.tau_c₀ P
    have h1' : ‖P.h c₀ ζ - 1 - P.h1 c₀ * ζ‖ ≤ P.A * ‖ζ‖ ^ 2 := by
      simpa [htau] using h1
    have hsplit : ‖P.h c₀ ζ - 1‖ = ‖(P.h c₀ ζ - 1 - P.h1 c₀ * ζ) + P.h1 c₀ * ζ‖ := by
      congr 1; ring
    rw [hsplit]
    have h2 := norm_add_le (P.h c₀ ζ - 1 - P.h1 c₀ * ζ) (P.h1 c₀ * ζ)
    have h3 : ‖P.h1 c₀ * ζ‖ = ‖P.h1 c₀‖ * ‖ζ‖ := by rw [norm_mul]
    linarith
  have hζ2 : ‖ζ‖ ^ 2 ≤ t := by
    nlinarith [norm_nonneg ζ, hζ_le, ht_le_q, ht_pos.le]
  have hzhnorm : ‖ζ * P.h c₀ ζ‖ ≤ 1 / 2 := by
    rw [norm_mul]
    nlinarith [norm_nonneg ζ, norm_nonneg (P.h c₀ ζ), hh2, hζ_le_q, ht_pos.le]
  have hB : 1 + ζ * P.h c₀ ζ ≠ 0 := by
    intro hcon
    have h' : ζ * P.h c₀ ζ = -1 := by linear_combination hcon
    have h1 : ‖ζ * P.h c₀ ζ‖ = 1 := by rw [h', norm_neg, norm_one]
    linarith
  have hden_ge : (1 : ℝ) / 2 ≤ ‖1 + ζ * P.h c₀ ζ‖ := by
    have h := norm_sub_le (1 + ζ * P.h c₀ ζ) (ζ * P.h c₀ ζ)
    have h' : ‖(1 : ℂ)‖ ≤ ‖1 + ζ * P.h c₀ ζ‖ + ‖ζ * P.h c₀ ζ‖ := by simpa using h
    rw [norm_one] at h'
    linarith
  have hnum : ‖P.h c₀ ζ - 1 - ζ * P.h c₀ ζ‖ ≤ (P.A + ‖P.h1 c₀‖ + 2) * t := by
    have h1 : ‖P.h c₀ ζ - 1 - ζ * P.h c₀ ζ‖ ≤ ‖P.h c₀ ζ - 1‖ + ‖ζ * P.h c₀ ζ‖ := by
      simpa using norm_sub_le (P.h c₀ ζ - 1) (ζ * P.h c₀ ζ)
    have h2 : ‖ζ * P.h c₀ ζ‖ ≤ 2 * t := by
      rw [norm_mul]
      have h := mul_le_mul hζ_le hh2 (norm_nonneg _) ht_pos.le
      linarith
    have h3 : P.A * ‖ζ‖ ^ 2 ≤ P.A * t := mul_le_mul_of_nonneg_left hζ2 P.hA
    have h4 : ‖P.h1 c₀‖ * ‖ζ‖ ≤ ‖P.h1 c₀‖ * t :=
      mul_le_mul_of_nonneg_left hζ_le (norm_nonneg _)
    linarith
  have hden_pos : 0 < ‖1 + ζ * P.h c₀ ζ‖ := lt_of_lt_of_le (by norm_num) hden_ge
  have hB' : (1 : ℂ) + P.h c₀ ζ * ζ ≠ 0 := by
    intro h; exact hB (by linear_combination h)
  have hquot : ‖P.h c₀ ζ / (1 + ζ * P.h c₀ ζ) - 1‖ ≤ Cin * t := by
    have heq : P.h c₀ ζ / (1 + ζ * P.h c₀ ζ) - 1
        = (P.h c₀ ζ - 1 - ζ * P.h c₀ ζ) / (1 + ζ * P.h c₀ ζ) := by
      field_simp [hB']
      ring
    rw [heq, norm_div, div_le_iff₀ hden_pos, hCin]
    have h6 : 2 * (P.A + ‖P.h1 c₀‖ + 2) * t * (1 / 2)
        ≤ 2 * (P.A + ‖P.h1 c₀‖ + 2) * t * ‖1 + ζ * P.h c₀ ζ‖ :=
      mul_le_mul_of_nonneg_left hden_ge (by positivity)
    have h5 : 2 * (P.A + ‖P.h1 c₀‖ + 2) * t * (1 / 2) = (P.A + ‖P.h1 c₀‖ + 2) * t := by ring
    linarith
  have hstep : Work.PARIMPL2.w0 P (Ft c₀ z) - Work.PARIMPL2.w0 P z
      = P.h c₀ ζ / (1 + ζ * P.h c₀ ζ) := by
    have hmain := w0incr_eq P hζ_lt_r hζ_ne hB
    rw [← hz_eq] at hmain
    rw [hζ_eq_w0] at hmain
    exact hmain
  have hΔeq : (Work.PARIMPL2.w0 P (Ft c₀ z)).re - (Work.PARIMPL2.w0 P z).re
      = (P.h c₀ ζ / (1 + ζ * P.h c₀ ζ)).re := by
    rw [← Complex.sub_re, hstep]
  have hfin : |(P.h c₀ ζ / (1 + ζ * P.h c₀ ζ)).re - 1| ≤ δ := by
    have h1 : |(P.h c₀ ζ / (1 + ζ * P.h c₀ ζ)).re - 1|
        = |(P.h c₀ ζ / (1 + ζ * P.h c₀ ζ) - 1).re| := by
      rw [Complex.sub_re, Complex.one_re]
    rw [h1]
    calc |(P.h c₀ ζ / (1 + ζ * P.h c₀ ζ) - 1).re|
        ≤ ‖P.h c₀ ζ / (1 + ζ * P.h c₀ ζ) - 1‖ := Complex.abs_re_le_norm _
      _ ≤ Cin * t := hquot
      _ ≤ δ := ht_le_d
  rw [hΔeq]
  rw [abs_le] at hfin
  exact ⟨by linarith [hfin.1], by linarith [hfin.2]⟩

end Work.PARIMPL2.LavaursA
