/-
# `Work.FTS.FinalClock.Basic` — the two amplitudes and their elementary calculus

The amplitude `Avort m` solves `A' = -(1+m)A`; under the modulation bound `|m| ≤ 1/2` it is
squeezed between `e^{-3τ/2}` and `e^{-τ/2}`, hence integrable on `[0,∞)` — this is what makes the
blow-up time `T = ∫₀^∞ A` finite and the "blow-up in finite time" of the paper quantitative.
`Bdyn m` is the companion amplitude of the second rescaling (`1 + λ` instead of `1 + μ`); the
exact relation `(1+m)(1+λ) = 1-m` of `Work.Construction.lamfun` is recorded here because it is
what identifies `Bdyn` with the paper's `B(τ)` (design §3).
-/
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.FinalClock.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory Set
open scoped Topology Interval

namespace Work.FTS.FinalClock

/-! ## Squeezing the integrals -/

/-- `∫₀^τ (1 + m) ≤ 3τ/2` under the modulation bound. -/
theorem integral_one_add_le {m : ℝ → ℝ} (hm : MuBound m) (hc : Continuous m) {τ : ℝ}
    (hτ : 0 ≤ τ) : ∫ s in (0 : ℝ)..τ, (1 + m s) ≤ 3 / 2 * τ := by
  have h := intervalIntegral.integral_mono (μ := volume) hτ ((continuous_const.add hc).intervalIntegrable 0 τ)
    (continuous_const.intervalIntegrable 0 τ) (fun x => (one_add_mem_Icc hm x).2)
  have h2 : ∫ s in (0 : ℝ)..τ, (3 / 2 : ℝ) = 3 / 2 * τ := by
    rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    ring
  rwa [h2] at h

/-- `τ/2 ≤ ∫₀^τ (1 + m)` under the modulation bound. -/
theorem integral_half_le_one_add {m : ℝ → ℝ} (hm : MuBound m) (hc : Continuous m) {τ : ℝ}
    (hτ : 0 ≤ τ) : 1 / 2 * τ ≤ ∫ s in (0 : ℝ)..τ, (1 + m s) := by
  have h := intervalIntegral.integral_mono (μ := volume) hτ (continuous_const.intervalIntegrable 0 τ)
    ((continuous_const.add hc).intervalIntegrable 0 τ) (fun x => (one_add_mem_Icc hm x).1)
  have h2 : ∫ s in (0 : ℝ)..τ, (1 / 2 : ℝ) = 1 / 2 * τ := by
    rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    ring
  rwa [h2] at h

/-- `∫₀^τ (1 - m) ≤ 3τ/2` under the modulation bound. -/
theorem integral_one_sub_le {m : ℝ → ℝ} (hm : MuBound m) (hc : Continuous m) {τ : ℝ}
    (hτ : 0 ≤ τ) : ∫ s in (0 : ℝ)..τ, (1 - m s) ≤ 3 / 2 * τ := by
  have h := intervalIntegral.integral_mono (μ := volume) hτ ((continuous_const.sub hc).intervalIntegrable 0 τ)
    (continuous_const.intervalIntegrable 0 τ) (fun x => (one_sub_mem_Icc hm x).2)
  have h2 : ∫ s in (0 : ℝ)..τ, (3 / 2 : ℝ) = 3 / 2 * τ := by
    rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    ring
  rwa [h2] at h

/-- `τ/2 ≤ ∫₀^τ (1 - m)` under the modulation bound. -/
theorem integral_half_le_one_sub {m : ℝ → ℝ} (hm : MuBound m) (hc : Continuous m) {τ : ℝ}
    (hτ : 0 ≤ τ) : 1 / 2 * τ ≤ ∫ s in (0 : ℝ)..τ, (1 - m s) := by
  have h := intervalIntegral.integral_mono (μ := volume) hτ (continuous_const.intervalIntegrable 0 τ)
    ((continuous_const.sub hc).intervalIntegrable 0 τ) (fun x => (one_sub_mem_Icc hm x).1)
  have h2 : ∫ s in (0 : ℝ)..τ, (1 / 2 : ℝ) = 1 / 2 * τ := by
    rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    ring
  rwa [h2] at h

/-! ## Exponential squeezing of the amplitudes -/

/-- `e^{-3τ/2} ≤ Avort m τ` under the modulation bound. -/
theorem exp_le_Avort {m : ℝ → ℝ} (hm : MuBound m) (hc : Continuous m) {τ : ℝ} (hτ : 0 ≤ τ) :
    Real.exp ((-(3 / 2 : ℝ)) * τ) ≤ Avort m τ := by
  rw [Avort, Real.exp_le_exp]
  linarith [integral_one_add_le hm hc hτ]

/-- `Avort m τ ≤ e^{-τ/2}` under the modulation bound. -/
theorem Avort_le_exp {m : ℝ → ℝ} (hm : MuBound m) (hc : Continuous m) {τ : ℝ} (hτ : 0 ≤ τ) :
    Avort m τ ≤ Real.exp ((-(1 / 2 : ℝ)) * τ) := by
  rw [Avort, Real.exp_le_exp]
  linarith [integral_half_le_one_add hm hc hτ]

/-- `e^{-3τ/2} ≤ Bdyn m τ` under the modulation bound. -/
theorem exp_le_Bdyn {m : ℝ → ℝ} (hm : MuBound m) (hc : Continuous m) {τ : ℝ} (hτ : 0 ≤ τ) :
    Real.exp ((-(3 / 2 : ℝ)) * τ) ≤ Bdyn m τ := by
  rw [Bdyn, Real.exp_le_exp]
  linarith [integral_one_sub_le hm hc hτ]

/-- `Bdyn m τ ≤ e^{-τ/2}` under the modulation bound. -/
theorem Bdyn_le_exp {m : ℝ → ℝ} (hm : MuBound m) (hc : Continuous m) {τ : ℝ} (hτ : 0 ≤ τ) :
    Bdyn m τ ≤ Real.exp ((-(1 / 2 : ℝ)) * τ) := by
  rw [Bdyn, Real.exp_le_exp]
  linarith [integral_half_le_one_sub hm hc hτ]

/-- `Avort m τ ≤ 1` for `τ ≥ 0` under the modulation bound. -/
theorem Avort_le_one {m : ℝ → ℝ} (hm : MuBound m) (hc : Continuous m) {τ : ℝ} (hτ : 0 ≤ τ) :
    Avort m τ ≤ 1 := by
  calc Avort m τ ≤ Real.exp ((-(1 / 2 : ℝ)) * τ) := Avort_le_exp hm hc hτ
    _ ≤ 1 := by
        rw [Real.exp_le_one_iff]
        linarith

/-- `Bdyn m τ ≤ 1` for `τ ≥ 0` under the modulation bound. -/
theorem Bdyn_le_one {m : ℝ → ℝ} (hm : MuBound m) (hc : Continuous m) {τ : ℝ} (hτ : 0 ≤ τ) :
    Bdyn m τ ≤ 1 := by
  calc Bdyn m τ ≤ Real.exp ((-(1 / 2 : ℝ)) * τ) := Bdyn_le_exp hm hc hτ
    _ ≤ 1 := by
        rw [Real.exp_le_one_iff]
        linarith

/-! ## Integrability: the blow-up time is finite -/

/-- `Avort m` is integrable on `[0,∞)` when the modulation is bounded: this is the finiteness of
the blow-up time `T = 2∫₀^∞ Avort m ≤ 4` used by `PhysClock`. -/
theorem Avort_integrableOn {m : ℝ → ℝ} (hm : MuBound m) (hc : Continuous m) :
    IntegrableOn (Avort m) (Set.Ioi 0) := by
  have hg : IntegrableOn (fun τ : ℝ => Real.exp ((-(1 / 2 : ℝ)) * τ)) (Set.Ioi 0) :=
    exp_neg_integrableOn_Ioi 0 (b := 1 / 2) (by norm_num)
  refine hg.mono' ((Avort_continuous hc).aestronglyMeasurable) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with τ hτ
  have hτ' : (0 : ℝ) ≤ τ := (Set.mem_Ioi.mp hτ).le
  rw [Real.norm_eq_abs, abs_of_nonneg (Avort_nonneg m τ)]
  exact Avort_le_exp hm hc hτ'

/-- `Bdyn m` is integrable on `[0,∞)` when the modulation is bounded. -/
theorem Bdyn_integrableOn {m : ℝ → ℝ} (hm : MuBound m) (hc : Continuous m) :
    IntegrableOn (Bdyn m) (Set.Ioi 0) := by
  have hg : IntegrableOn (fun τ : ℝ => Real.exp ((-(1 / 2 : ℝ)) * τ)) (Set.Ioi 0) :=
    exp_neg_integrableOn_Ioi 0 (b := 1 / 2) (by norm_num)
  refine hg.mono' ((Bdyn_continuous hc).aestronglyMeasurable) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with τ hτ
  have hτ' : (0 : ℝ) ≤ τ := (Set.mem_Ioi.mp hτ).le
  rw [Real.norm_eq_abs, abs_of_nonneg (Bdyn_nonneg m τ)]
  exact Bdyn_le_exp hm hc hτ'

/-! ## The product identity and the `lamfun` relation -/

/-- The two amplitudes are reciprocal up to the bare exponential of the unmodulated clock:
`Avort m τ · Bdyn m τ = e^{-2τ}`. -/
theorem Avort_mul_Bdyn {m : ℝ → ℝ} (hc : Continuous m) (τ : ℝ) :
    Avort m τ * Bdyn m τ = Real.exp (-(2 * τ)) := by
  have h1 : IntervalIntegrable (fun s : ℝ => 1 + m s) volume 0 τ :=
    (continuous_const.add hc).intervalIntegrable 0 τ
  have h2 : IntervalIntegrable (fun s : ℝ => 1 - m s) volume 0 τ :=
    (continuous_const.sub hc).intervalIntegrable 0 τ
  rw [Avort, Bdyn, ← Real.exp_add]
  have hsum : -(∫ s in (0 : ℝ)..τ, (1 + m s)) + -(∫ s in (0 : ℝ)..τ, (1 - m s))
      = -(2 * τ) := by
    rw [← neg_add, ← intervalIntegral.integral_add h1 h2]
    have hfun : (fun s : ℝ => (1 + m s) + (1 - m s)) = fun _ : ℝ => (2 : ℝ) := by
      funext s
      ring
    rw [hfun, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    ring
  rw [hsum]

/-- The paper's choice `λ = -2μ/(1+μ)` is exactly the constant for which
`(1+μ)(1+λ) = 1-μ` (tex 1355/1357). -/
theorem lamfun_mul {m : ℝ} (hm : m ≠ -1) :
    (1 + m) * (1 + Work.Construction.lamfun m) = 1 - m := by
  have h1 : (1 : ℝ) + m ≠ 0 := by
    intro h
    exact hm (by linarith)
  rw [Work.Construction.lamfun]
  field_simp
  ring

/-- `Bdyn m` is the exponential of the `λ`-modulated rate `(1+m)(1+λ) = 1-m`: this is the form in
which `Bdyn` is the amplitude `B` of the self-similar variable. -/
theorem Bdyn_eq_exp_lamfun {m : ℝ → ℝ} (hm : ∀ t : ℝ, m t ≠ -1) (τ : ℝ) :
    Bdyn m τ
      = Real.exp (-∫ s in (0 : ℝ)..τ,
          (1 + m s) * (1 + Work.Construction.lamfun (m s))) := by
  rw [Bdyn]
  congr 1
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  exact (lamfun_mul (hm s)).symm

end Work.FTS.FinalClock
