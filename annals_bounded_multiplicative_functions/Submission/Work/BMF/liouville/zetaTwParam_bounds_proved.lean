import Mathlib
import Submission.Work.BMF.liouville.zetaTwVKdefs
import Submission.Work.BMF.VKdenom
import Submission.Work.BMF.liouville.VKd_tendsto_atTop
import Submission.Work.BMF.liouville.ztNumeric_eventually
import Submission.Work.BMF.liouville.VKd_three_exp_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.liouville

open Filter

/-! ## Elementary pointwise facts about the parameter package `ztT`, `ztV`

`ztT L u = |u| + L^2 * exp (L^{1/10}) + 7` and `ztV L u = VKd (2 * ztT L u + 3)`.
These facts are pointwise in `(L, u)`; the uniformity in `u` enters only through the
hypothesis `|u| ≤ exp (L^{5/4})`. -/

private lemma ztE_sq_nonneg (L : ℝ) : 0 ≤ L ^ 2 * ztE L :=
  mul_nonneg (sq_nonneg L) (ztE_pos L).le

private lemma ztT_pos (L u : ℝ) : 0 < ztT L u := by
  have h := ztE_sq_nonneg L
  have h' := abs_nonneg u
  rw [ztT]
  linarith

private lemma abs_lt_ztT (L u : ℝ) : |u| < ztT L u := by
  have h := ztE_sq_nonneg L
  have h' := abs_nonneg u
  rw [ztT]
  linarith

private lemma three_le_two_ztT_add_three (L u : ℝ) : 3 ≤ 2 * ztT L u + 3 := by
  have h := ztT_pos L u
  linarith

private lemma ztV_pos (L u : ℝ) : 0 < ztV L u :=
  Work.BMF.VKd_pos (three_le_two_ztT_add_three L u)

/-- The parameter package is small compared with `exp (L^{5/4})`: if
`2 L^2 exp (L^{1/10}) + 17 ≤ exp (L^{5/4})` and `|u| ≤ exp (L^{5/4})`, then
`ztT L u ≤ 2 exp (L^{5/4})`, `2 * ztT L u + 3 ≤ 3 exp (L^{5/4})` and
`|u| + ztT L u + 3 ≤ 3 exp (L^{5/4})`. -/
private lemma ztT_le_exp (L u : ℝ)
    (hnum : 2 * L ^ 2 * Real.exp (L ^ (1 / 10 : ℝ)) + 17 ≤ Real.exp (L ^ (5 / 4 : ℝ)))
    (hu : |u| ≤ Real.exp (L ^ (5 / 4 : ℝ))) :
    ztT L u ≤ 2 * Real.exp (L ^ (5 / 4 : ℝ)) ∧
    2 * ztT L u + 3 ≤ 3 * Real.exp (L ^ (5 / 4 : ℝ)) ∧
    |u| + ztT L u + 3 ≤ 3 * Real.exp (L ^ (5 / 4 : ℝ)) := by
  have hE0 : (0 : ℝ) ≤ L ^ 2 * Real.exp (L ^ (1 / 10 : ℝ)) :=
    mul_nonneg (sq_nonneg L) (Real.exp_pos _).le
  have hE17 : (17 : ℝ) ≤ Real.exp (L ^ (5 / 4 : ℝ)) := by linarith
  have habs : (0 : ℝ) ≤ |u| := abs_nonneg u
  simp only [ztT, ztE] at *
  refine ⟨by linarith, by linarith, by linarith⟩

private lemma log_three_exp_rpow (L : ℝ) :
    Real.log (3 * Real.exp (L ^ (5 / 4 : ℝ))) = Real.log 3 + L ^ (5 / 4 : ℝ) := by
  rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp]

/-- `log (2 * ztT L u + 3) ≤ 2 L^{5/4}`. -/
private lemma log_two_ztT_add_three_le (L u : ℝ) (h3 : Real.log 3 ≤ L ^ (5 / 4 : ℝ))
    (hnum : 2 * L ^ 2 * Real.exp (L ^ (1 / 10 : ℝ)) + 17 ≤ Real.exp (L ^ (5 / 4 : ℝ)))
    (hu : |u| ≤ Real.exp (L ^ (5 / 4 : ℝ))) :
    Real.log (2 * ztT L u + 3) ≤ 2 * L ^ (5 / 4 : ℝ) := by
  have hle := (ztT_le_exp L u hnum hu).2.1
  have hpos : 0 < 2 * ztT L u + 3 :=
    lt_of_lt_of_le (by norm_num) (three_le_two_ztT_add_three L u)
  calc Real.log (2 * ztT L u + 3) ≤ Real.log (3 * Real.exp (L ^ (5 / 4 : ℝ))) :=
        Real.log_le_log hpos hle
    _ = Real.log 3 + L ^ (5 / 4 : ℝ) := log_three_exp_rpow L
    _ ≤ 2 * L ^ (5 / 4 : ℝ) := by linarith

/-- `log (|u| + ztT L u + 3) ≤ 2 L^{5/4}`. -/
private lemma log_abs_add_ztT_add_three_le (L u : ℝ) (h3 : Real.log 3 ≤ L ^ (5 / 4 : ℝ))
    (hnum : 2 * L ^ 2 * Real.exp (L ^ (1 / 10 : ℝ)) + 17 ≤ Real.exp (L ^ (5 / 4 : ℝ)))
    (hu : |u| ≤ Real.exp (L ^ (5 / 4 : ℝ))) :
    Real.log (|u| + ztT L u + 3) ≤ 2 * L ^ (5 / 4 : ℝ) := by
  have hle := (ztT_le_exp L u hnum hu).2.2
  have hpos : 0 < |u| + ztT L u + 3 := by
    have h := ztT_pos L u
    have h' := abs_nonneg u
    linarith
  calc Real.log (|u| + ztT L u + 3) ≤ Real.log (3 * Real.exp (L ^ (5 / 4 : ℝ))) :=
        Real.log_le_log hpos hle
    _ = Real.log 3 + L ^ (5 / 4 : ℝ) := log_three_exp_rpow L
    _ ≤ 2 * L ^ (5 / 4 : ℝ) := by linarith

/-- Bounds for the parameter package `ztT`, `ztV`, `ztC` of the twisted Vinogradov–Korobov
Perron argument (`Work.BMF.liouville.ztT L u = |u| + L^2*exp(L^{1/10}) + 7` and
`ztV L u = VKd (2*ztT L u + 3)`), uniform in `u` with `|u| ≤ exp (L^{5/4})`:

* `ztC c₁ c₂ / (4 * ztV L u) ≤ η` for any fixed `η > 0`, eventually in `L`;
* `0 < ztT`, `|u| < ztT`, `0 < ztV`, `ztV ≤ L^{9/10}`,
  `log (2 ztT + 3) ≤ 2 L^{5/4}` and `log (|u| + ztT + 3) ≤ 2 L^{5/4}`, eventually in `L`.

(The last two follow from `2*ztT+3 ≤ 3*exp(L^{5/4})`; the `L^{9/10}` bound is
`VKd y ≤ (log y)^{2/3}(log log y)^{1/3} ≤ 2 L^{5/6}(log L)^{1/3} ≤ L^{9/10}`.) -/
theorem zetaTwParam_bounds_proved (c₁ c₂ : ℝ) :
    (∀ η : ℝ, 0 < η → ∀ᶠ L in Filter.atTop, ∀ u : ℝ, |u| ≤ Real.exp (L ^ (5 / 4 : ℝ)) →
        ztC c₁ c₂ / (4 * ztV L u) ≤ η) ∧
    (∀ᶠ L in Filter.atTop, ∀ u : ℝ, |u| ≤ Real.exp (L ^ (5 / 4 : ℝ)) →
        0 < ztT L u ∧ |u| < ztT L u ∧ 0 < ztV L u ∧ ztV L u ≤ L ^ (9 / 10 : ℝ) ∧
        Real.log (2 * ztT L u + 3) ≤ 2 * L ^ (5 / 4 : ℝ) ∧
        Real.log (|u| + ztT L u + 3) ≤ 2 * L ^ (5 / 4 : ℝ)) := by
  -- The quantity `2 L^2 exp (L^{1/10})` tends to `+∞`, so `VKd` of it eventually exceeds
  -- any fixed threshold, uniformly in `u`.
  have hpoly : Filter.Tendsto (fun L : ℝ => 2 * L ^ 2 * ztE L) Filter.atTop Filter.atTop := by
    have hsq : Filter.Tendsto (fun L : ℝ => L ^ 2) Filter.atTop Filter.atTop := by
      have h : Filter.Tendsto (fun L : ℝ => L ^ (((2 : ℕ) : ℝ))) Filter.atTop Filter.atTop :=
        tendsto_rpow_atTop (show (0 : ℝ) < (((2 : ℕ) : ℝ)) by norm_num)
      simpa only [Real.rpow_natCast] using h
    have h2sq : Filter.Tendsto (fun L : ℝ => 2 * L ^ 2) Filter.atTop Filter.atTop :=
      Filter.Tendsto.const_mul_atTop (show (0 : ℝ) < 2 by norm_num) hsq
    have hexp : Filter.Tendsto (fun L : ℝ => ztE L) Filter.atTop Filter.atTop :=
      Real.tendsto_exp_atTop.comp
        (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 10 by norm_num))
    exact Filter.Tendsto.atTop_mul_atTop₀ h2sq hexp
  have hVKdlim : Filter.Tendsto (fun L : ℝ => Work.BMF.VKd (2 * L ^ 2 * ztE L))
      Filter.atTop Filter.atTop := by
    simpa [Function.comp_def] using VKd_tendsto_atTop.comp hpoly
  -- elementary numeric input, proved in `Work.BMF.liouville.ztNumeric_eventually`
  have hM : ∀ᶠ L in Filter.atTop,
      2 * L ^ 2 * Real.exp (L ^ (1 / 10 : ℝ)) + 17 ≤ Real.exp (L ^ (5 / 4 : ℝ)) :=
    ztNumeric_eventually.2.1
  have h2 : ∀ᶠ L in Filter.atTop, Real.log 2 ≤ (3 / 4) * Real.log L :=
    ztNumeric_eventually.2.2.1
  have h3 : ∀ᶠ L in Filter.atTop, Real.log 3 ≤ L ^ (5 / 4 : ℝ) :=
    ztNumeric_eventually.2.2.2.1
  have hlog : ∀ᶠ L in Filter.atTop, 2 * (Real.log L) ^ (1 / 3 : ℝ) ≤ L ^ (1 / 15 : ℝ) :=
    ztNumeric_eventually.2.2.2.2
  constructor
  · intro η hη
    filter_upwards [hVKdlim.eventually_ge_atTop (1 / (4 * η)),
      Filter.eventually_ge_atTop (2 : ℝ)] with L hL hL2 u hu
    have hztE1 : (1 : ℝ) ≤ ztE L := by
      rw [ztE]
      exact Real.one_le_exp (Real.rpow_nonneg (by linarith) _)
    have hx3 : 3 ≤ 2 * L ^ 2 * ztE L := by nlinarith [sq_nonneg L, hL2, hztE1]
    have hstep1 : Work.BMF.VKd (2 * L ^ 2 * ztE L) ≤ Work.BMF.VKd (2 * L ^ 2 * ztE L + 17) :=
      Work.BMF.VKd_mono hx3 (by linarith)
    have hstep2 : Work.BMF.VKd (2 * L ^ 2 * ztE L + 17) ≤ Work.BMF.VKd (2 * ztT L u + 3) := by
      refine Work.BMF.VKd_mono (by linarith) ?_
      rw [ztT]
      have h := abs_nonneg u
      linarith
    have hztV : 1 / (4 * η) ≤ ztV L u := by
      rw [ztV]
      linarith
    have hztVpos : 0 < ztV L u := ztV_pos L u
    have hsmall : ztC c₁ c₂ / (4 * ztV L u) ≤ 1 / (4 * ztV L u) :=
      div_le_div_of_nonneg_right (ztC_le_one c₁ c₂) (by linarith)
    have hone : 1 / (4 * ztV L u) ≤ η := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < 4 * ztV L u)]
      have hm : (1 : ℝ) ≤ ztV L u * (4 * η) :=
        (div_le_iff₀ (by linarith : (0 : ℝ) < 4 * η)).mp hztV
      linarith
    linarith
  · filter_upwards [hM, h2, h3, hlog] with L hM h2 h3 hlog u hu
    refine ⟨ztT_pos L u, abs_lt_ztT L u, ztV_pos L u, ?_, ?_, ?_⟩
    · calc ztV L u = Work.BMF.VKd (2 * ztT L u + 3) := rfl
        _ ≤ Work.BMF.VKd (3 * Real.exp (L ^ (5 / 4 : ℝ))) :=
            Work.BMF.VKd_mono (three_le_two_ztT_add_three L u) ((ztT_le_exp L u hM hu).2.1)
        _ ≤ L ^ (9 / 10 : ℝ) := VKd_three_exp_le L h3 h2 hlog
    · exact log_two_ztT_add_three_le L u h3 hM hu
    · exact log_abs_add_ztT_add_three_le L u h3 hM hu

end Work.BMF.liouville
