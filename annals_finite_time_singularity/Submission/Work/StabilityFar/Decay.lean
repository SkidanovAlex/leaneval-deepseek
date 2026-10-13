/-
# `Work.StabilityFar.Decay` — the far-field decay estimates of `St4`

The far-field decay of `u = BS(ω)` and of `∂ₜu = BS(∂ₜω)` — of the fields *and* of their spatial
derivatives — together with the Lipschitz-in-`x` bound for `∂ₜu` in the far region.  These are
the estimates that make the far-field `α`-Hölder bound of `St4` true: with the vorticity
supported in a fixed ball, the Biot–Savart field is `O(‖x‖^{-2})` with `O(‖x‖^{-3})` derivatives,
so the *joint* derivative of `u.uncurry` is bounded and Hölder in the far region.

The decay estimates are the uniform-in-time forms delivered by `Work.LWP.FarField`; the
Lipschitz-in-`x` bound for `∂ₜu` is the `L²`-Lipschitz bound of the Biot–Savart field on a ball
around a far point (`Work.LWP.BiotSavart.biotSavart_lipschitzOn_far`).
-/
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.StabilityFar.Basic
import Submission.Work.LWP.BiotSavart.farField_decay_fderiv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.StabilityFar

/-- A point of `window T` with `0 ≤ t` is in the half-open interval `Ico 0 (T+1)`, which is the
form in which the uniform far-field estimates of `Work.LWP.FarField` are stated. -/
theorem window_of_Icc {T t : ℝ} (ht : t ∈ Set.Icc 0 T) : t ∈ window T :=
  ⟨by linarith [ht.1], by linarith [ht.2]⟩

theorem Ico_succ_subset_window (T : ℝ) : Set.Ico 0 (T + 1) ⊆ window T :=
  fun t ht => ⟨by linarith [ht.1], le_of_lt ht.2⟩

/-! ## The support of `∂ₜω` on the open window -/

/-- **The support of `∂ₜω`** (open-window form): outside the support ball of `ω`, the function
`s ↦ ω(y,s)` vanishes identically on the window, hence so does its derivative. -/
theorem slicesSupported_timeDeriv_open {ω : R3 → ℝ → R3} {R T : ℝ}
    (h : SlicesSupported ω R T) :
    ∀ t ∈ Set.Ioo (-1) (T + 1), ∀ y : R3, timeDeriv ω y t ≠ 0 → y ∈ Metric.closedBall 0 R := by
  intro t ht y hy
  by_contra hmem
  have hy' : R < ‖y‖ := by
    rw [Metric.mem_closedBall, dist_zero_right] at hmem
    exact lt_of_not_ge hmem
  refine hy (timeDeriv_eq_zero_of_eventuallyEq_zero ?_)
  filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
  by_contra hne
  have := h s hs y hne
  rw [Metric.mem_closedBall, dist_zero_right] at this
  linarith

/-! ## The far-field decay of `u` and `Du` -/

/-- **Far-field decay of the velocity** in the form consumed by `St4`: for `t ∈ [0,T]` and
`‖x‖ ≥ 2R`, `‖u(x,t)‖ ≤ (4/3)·M·R³/‖x‖²`. -/
theorem velocity_decay {ω u : R3 → ℝ → R3} {R M T : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hbs : IsBiotSavartSlice u ω T) (hbdd : SlicesBounded ω M T) (hsupp : SlicesSupported ω R T) :
    ∀ t ∈ Set.Icc 0 T, ∀ x : R3, 2 * R ≤ ‖x‖ →
      ‖u x t‖ ≤ (4 / 3) * M * R ^ 3 / ‖x‖ ^ 2 := by
  intro t ht x hx
  rw [hbs t (window_of_Icc ht) x]
  exact Work.LWP.farField_decay_uniform (T := T + 1) hR hM
    (fun s hs => hbdd s (Ico_succ_subset_window T hs))
    (fun s hs => hsupp s (Ico_succ_subset_window T hs)) t
    (Set.mem_Ico.mpr ⟨ht.1, by linarith [ht.2]⟩) x hx

/-- **Far-field decay of the spatial derivative of the velocity**: for `t ∈ [0,T]` and
`‖x‖ ≥ 2R`, `‖D(u(·,t))(x)‖ ≤ 2^20·M·R³/‖x‖³`. -/
theorem fderiv_decay {ω u : R3 → ℝ → R3} {R M T : ℝ} (hR : 0 < R) (hM : 0 ≤ M)
    (hbs : IsBiotSavartSlice u ω T) (hbdd : SlicesBounded ω M T) (hsupp : SlicesSupported ω R T) :
    ∀ t ∈ Set.Icc 0 T, ∀ x : R3, 2 * R ≤ ‖x‖ →
      ‖fderiv ℝ (u · t) x‖ ≤ 2 ^ 20 * M * R ^ 3 / ‖x‖ ^ 3 := by
  intro t ht x hx
  have hfun : (u · t) = fun y => Work.LWP.biotSavart (fun z => ω z t) y :=
    funext (fun y => hbs t (window_of_Icc ht) y)
  rw [hfun]
  exact Work.LWP.farField_decay_fderiv_uniform (T := T + 1) hR hM
    (fun s hs => hbdd s (Ico_succ_subset_window T hs))
    (fun s hs => hsupp s (Ico_succ_subset_window T hs)) t
    (Set.mem_Ico.mpr ⟨ht.1, by linarith [ht.2]⟩) x hx

/-- **Far-field decay of `∂ₜu`**: `∂ₜω` is supported in the same ball as `ω`
(`slicesSupported_timeDeriv`), so `∂ₜu = BS(∂ₜω)` obeys the same `‖x‖^{-2}` decay. -/
theorem velocity_decay_timeDeriv {ω u : R3 → ℝ → R3} {R M₁ T : ℝ} (hR : 0 ≤ R) (hM₁ : 0 ≤ M₁)
    (hbsDt : IsTimeBiotSavartSlice u ω T) (hbddDt : SlicesBounded (timeDeriv ω) M₁ T)
    (hsupp : SlicesSupported ω R T) :
    ∀ t ∈ Set.Icc 0 T, ∀ x : R3, 2 * R ≤ ‖x‖ →
      ‖timeDeriv u x t‖ ≤ (4 / 3) * M₁ * R ^ 3 / ‖x‖ ^ 2 := by
  intro t ht x hx
  rw [hbsDt t (window_of_Icc ht) x]
  exact Work.LWP.farField_decay_uniform (T := T + 1) hR hM₁
    (fun s hs => hbddDt s (Ico_succ_subset_window T hs))
    (fun s hs => slicesSupported_timeDeriv_open hsupp s ⟨by linarith [hs.1], hs.2⟩) t
    (Set.mem_Ico.mpr ⟨ht.1, by linarith [ht.2]⟩) x hx

/-- **Far-field decay of the spatial derivative of `∂ₜu`**. -/
theorem fderiv_decay_timeDeriv {ω u : R3 → ℝ → R3} {R M₁ T : ℝ} (hR : 0 < R) (hM₁ : 0 ≤ M₁)
    (hbsDt : IsTimeBiotSavartSlice u ω T) (hbddDt : SlicesBounded (timeDeriv ω) M₁ T)
    (hmeasDt : SlicesMeasurable (timeDeriv ω) T) (hsupp : SlicesSupported ω R T) :
    ∀ t ∈ Set.Icc 0 T, ∀ x : R3, 2 * R ≤ ‖x‖ →
      ‖fderiv ℝ (fun z => timeDeriv u z t) x‖ ≤ 2 ^ 20 * M₁ * R ^ 3 / ‖x‖ ^ 3 := by
  intro t ht x hx
  have hfun : (fun z => timeDeriv u z t)
      = fun y => Work.LWP.biotSavart (fun z => timeDeriv ω z t) y :=
    funext (fun y => hbsDt t (window_of_Icc ht) y)
  rw [hfun]
  exact Work.LWP.farField_decay_fderiv_uniform (T := T + 1) hR hM₁
    (fun s hs => hbddDt s (Ico_succ_subset_window T hs))
    (fun s hs => slicesSupported_timeDeriv_open hsupp s ⟨by linarith [hs.1], hs.2⟩) t
    (Set.mem_Ico.mpr ⟨ht.1, by linarith [ht.2]⟩) x hx

/-! ## The Lipschitz-in-`x` bound for `∂ₜu` -/

/-- **`∂ₜu` is Lipschitz in `x` in the far region.**  Since `∂ₜu(·,t) = BS(∂ₜω(·,t))` and
`BS(g)` is `2^20·M₁·R³/‖x‖³`-Lipschitz on the ball of radius `‖x‖/4` around a far point `x`
(`Work.LWP.BiotSavart.biotSavart_lipschitzOn_far`), any two far points at distance `≤ 1` are in
that ball as soon as `4 ≤ ‖x‖`, and the constant is at most `2^17·M₁`. -/
theorem timeDeriv_lipschitz_x {ω u : R3 → ℝ → R3} {R M₁ T : ℝ} (hR : 0 < R) (hM₁ : 0 ≤ M₁)
    (hbsDt : IsTimeBiotSavartSlice u ω T) (hbddDt : SlicesBounded (timeDeriv ω) M₁ T)
    (hmeasDt : SlicesMeasurable (timeDeriv ω) T) (hsupp : SlicesSupported ω R T) :
    ∀ t ∈ Set.Icc 0 T, ∀ x y : R3, 2 * R + 5 < ‖x‖ → ‖x - y‖ ≤ 1 →
      ‖timeDeriv u x t - timeDeriv u y t‖ ≤ 2 ^ 17 * M₁ * ‖x - y‖ := by
  intro t ht x y hx hxy
  have hw : t ∈ window T := window_of_Icc ht
  have hfun : ∀ z : R3, timeDeriv u z t = Work.LWP.biotSavart (fun w => timeDeriv ω w t) z :=
    fun z => hbsDt t hw z
  have hsupp_dt : ∀ z : R3, timeDeriv ω z t ≠ 0 → z ∈ Metric.closedBall 0 R :=
    fun z hz =>
      slicesSupported_timeDeriv_open hsupp t ⟨by linarith [ht.1], by linarith [ht.2]⟩ z hz
  have hxR : 2 * R ≤ ‖x‖ := by linarith
  have hxmem : x ∈ Metric.ball x (‖x‖ / 4) := by
    rw [Metric.mem_ball, dist_self]
    linarith
  have hmem : y ∈ Metric.ball x (‖x‖ / 4) := by
    rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev]
    linarith
  have hlip := Work.LWP.BiotSavart.biotSavart_lipschitzOn_far (le_of_lt hR) hM₁
    (fun z => hbddDt t hw z) hsupp_dt (hmeasDt t hw) hxR
  rw [lipschitzOnWith_iff_norm_sub_le] at hlip
  have hb := hlip hxmem hmem
  rw [hfun x, hfun y]
  have hxpos : 0 < ‖x‖ := by linarith
  have hK : (2 ^ 20 : ℝ) * M₁ * R ^ 3 / ‖x‖ ^ 3 ≤ 2 ^ 17 * M₁ := by
    have hxx : (2 * R) ^ 3 ≤ ‖x‖ ^ 3 := pow_le_pow_left₀ (by linarith) hxR 3
    have h8 : (2 * R) ^ 3 = 8 * R ^ 3 := by ring
    rw [div_le_iff₀ (pow_pos hxpos 3)]
    have hstep : 2 ^ 17 * M₁ * (8 * R ^ 3) ≤ 2 ^ 17 * M₁ * ‖x‖ ^ 3 :=
      mul_le_mul_of_nonneg_left (by rw [← h8]; exact hxx) (by positivity)
    have hpow : (2 : ℝ) ^ 20 = 2 ^ 17 * 8 := by norm_num
    nlinarith [hstep, hpow]
  calc ‖Work.LWP.biotSavart (fun w => timeDeriv ω w t) x
        - Work.LWP.biotSavart (fun w => timeDeriv ω w t) y‖
      ≤ (((2 ^ 20 : ℝ) * M₁ * R ^ 3 / ‖x‖ ^ 3).toNNReal : ℝ) * ‖x - y‖ := hb
    _ = (2 ^ 20 * M₁ * R ^ 3 / ‖x‖ ^ 3) * ‖x - y‖ := by
        rw [Real.coe_toNNReal _ (by positivity)]
    _ ≤ (2 ^ 17 * M₁) * ‖x - y‖ := mul_le_mul_of_nonneg_right hK (norm_nonneg _)

end Work.StabilityFar
