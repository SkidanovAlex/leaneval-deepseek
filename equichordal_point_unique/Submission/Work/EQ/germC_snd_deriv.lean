import Mathlib
import Submission.Work.EQ.DefsCore

namespace Work.EQ

open Complex Filter _root_.Topology
open scoped Topology

/-- The `y`-coordinate of the local stable curve has derivative `(1 - a)/2` at the origin: for a
stable germ `h` (`h 0 = 0`, `h' 0 = -1`) and `0 < a < 1`, writing `y(u) = (germC a h u).2` one
has `y'(0) = (1 - a)/2`.  Indeed `y(u)/u = a (h u/u)(h(λu)/u) / ((h(λu) - h u)/u) → a λ/(1 - λ)
= (1 - a)/2` as `u → 0`, `u ≠ 0`, and `y(0) = 0`. -/
theorem germC_snd_deriv {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) :
    deriv (fun u => (germC a h u).2) 0 = (((1 - a) / 2 : ℝ) : ℂ) := by
  obtain ⟨hr, han, h0, hd, hreal, hfe⟩ := hh
  have hmem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) r := by
    simp only [Metric.mem_ball, dist_self]; exact hr
  have hana : AnalyticAt ℂ h 0 := han 0 hmem
  -- the germ is differentiable at `0` with derivative `-1`
  have hder0 : HasDerivAt h (-1) 0 := by
    have hh' := hana.differentiableAt.hasDerivAt
    rwa [hd] at hh'
  have hAcont : ContinuousAt (dslope h 0) 0 :=
    (continuousAt_dslope_same).mpr hder0.differentiableAt
  -- derivative of `v ↦ h (λ v)` at `0`
  have hBder : HasDerivAt (fun v => h ((eqLam a : ℂ) * v)) (-(eqLam a : ℂ)) 0 := by
    have hder0c : HasDerivAt h (-1) ((eqLam a : ℂ) * 0) := by simpa using hder0
    have hh' := hder0c.comp 0 (hasDerivAt_const_mul ((eqLam a : ℂ)))
    simpa [Function.comp_def] using hh'
  have hBcont : ContinuousAt (dslope (fun v => h ((eqLam a : ℂ) * v)) 0) 0 :=
    (continuousAt_dslope_same).mpr hBder.differentiableAt
  have hDder : HasDerivAt (fun v => h ((eqLam a : ℂ) * v) - h v) (-(eqLam a : ℂ) - (-1)) 0 :=
    hBder.sub hder0
  have hDcont : ContinuousAt (dslope (fun v => h ((eqLam a : ℂ) * v) - h v) 0) 0 :=
    (continuousAt_dslope_same).mpr hDder.differentiableAt
  -- values of the three `dslope`s at `0`
  have hA0 : dslope h 0 0 = -1 := by rw [dslope_same, hd]
  have hB0 : dslope (fun v => h ((eqLam a : ℂ) * v)) 0 0 = -(eqLam a : ℂ) := by
    rw [dslope_same, hBder.deriv]
  have hD0 : dslope (fun v => h ((eqLam a : ℂ) * v) - h v) 0 0 = 1 - (eqLam a : ℂ) := by
    rw [dslope_same, hDder.deriv]; ring
  have hD0ne : dslope (fun v => h ((eqLam a : ℂ) * v) - h v) 0 0 ≠ 0 := by
    rw [hD0]
    have hl : eqLam a < 1 := by rw [eqLam, div_lt_one (by linarith)]; linarith
    have : (eqLam a : ℂ) ≠ 1 := by exact_mod_cast (ne_of_lt hl)
    exact sub_ne_zero.mpr (Ne.symm this)
  -- the "slope function" `F`, defined as `y u / u` for `u ≠ 0`
  set F : ℂ → ℂ := fun u => (a : ℂ) * dslope h 0 u
      * dslope (fun v => h ((eqLam a : ℂ) * v)) 0 u
      / dslope (fun v => h ((eqLam a : ℂ) * v) - h v) 0 u with hF
  have hFcont : ContinuousAt F 0 := by
    rw [hF]
    exact ((continuousAt_const.mul hAcont).mul hBcont).div hDcont hD0ne
  -- `y = u * F u`
  have hEq : (fun u => (germC a h u).2) = fun u => u * F u := by
    funext u
    rw [hF]
    simp only [germC]
    ring
  -- the value of `F` at `0` is `(1 - a)/2`
  have hF0 : F 0 = (((1 - a) / 2 : ℝ) : ℂ) := by
    rw [hF]
    simp only [hA0, hB0, hD0]
    have hR : a * ((1 - a) / (1 + a)) / (1 - (1 - a) / (1 + a)) = (1 - a) / 2 := by
      have ha : a ≠ 0 := ne_of_gt ha0
      have hden : (1 - (1 - a) / (1 + a)) = 2 * a / (1 + a) := by field_simp; ring
      rw [hden]
      field_simp
    rw [eqLam, ← hR]
    push_cast
    ring
  -- `y` has derivative `F 0` at `0`, via the slope limit
  have hder : HasDerivAt (fun u => (germC a h u).2) (F 0) 0 := by
    rw [hEq, hasDerivAt_iff_tendsto_slope]
    have hsl : slope (fun u => u * F u) 0 =ᶠ[𝓝[≠] (0 : ℂ)] F := by
      filter_upwards [self_mem_nhdsWithin] with u hu
      rw [slope_def_module]
      simp only [sub_zero, zero_mul, sub_zero, smul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ hu, one_mul]
    have hFt : Tendsto F (𝓝[≠] (0 : ℂ)) (𝓝 (F 0)) :=
      hFcont.tendsto.mono_left nhdsWithin_le_nhds
    exact hFt.congr' hsl.symm
  rw [hder.deriv, hF0]

end Work.EQ
