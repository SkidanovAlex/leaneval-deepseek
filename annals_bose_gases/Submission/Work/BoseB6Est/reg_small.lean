import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.BoseB6Est.beta_close_bounds
import Submission.Work.BoseB6Est.fsInt
import Submission.Work.BoseB6Est.fsTau_eq_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Node B6-est — the small-`r` region of FS's `I₁` estimate (`reg_small`)

FS's `lem:BogIntegral` (`eq:LebesgueError-Total`) estimates the scaled
Bogoliubov zero-point integral `I₁ = ∫ r² (G − G₀)` where

* `G(r) = (τ̃(r)+β(r)) − √((τ̃(r)+β(r))²−β(r)²) − β(r)²/(2r²) = fsGR`,
* `G₀(r) = (r²+8π) − √((r²+8π)²−(8π)²) − (8π)²/(2r²) = fsG0R`

(the model bracket), and the deviation is bounded by FS's error
`ε(μ,ρ_z) = lhyEps a R ε_T K_ℓ s d μ`.  This module proves the **innermost**
region `(0, c₁]`:

  `∫_{0}^{c₁} r² (G − G₀) ≤ 31 · ε(μ,ρ_z)`.

The mathematics is exactly FS's "the part of both integrals where
`|t| ≤ 10(K_ℓs)^{-1}` is bounded by `C(K_ℓs)^{-1}`" (with `c₁ ≤ (K_ℓs)^{-1} ≤ ε`).

* On `(0,c₁]` the kinetic symbol vanishes identically
  (`τ̃(r) = (1−ε_T)[r−c₁]₊² + ε_T[r−c₂]₊² = 0`), so `G` collapses to the `τ = 0`
  bracket `gFun 0 β(r) r`.
* Split at the model value `β ≡ 8π`, `τ = r²`:
  `G − G₀ = [gFun 0 β(r) r − gFun 0 8π r] + [gFun 0 8π r − gFun r² 8π r]`.
  The first bracket is *linear* in `β(r)−8π`, which in `(0,c₁] ⊂ [0,T]` is
  bounded by `η r`; the exact identity `gFun_zero_diff` turns the `r²`-weighted
  bracket into `r²(β−8π) − (β²−(8π)²)/2`, whose integral over `(0,c₁]` is
  `O(η c₁²) ≤ O(ε)`.
  The second bracket is the `τ`-increment at the model coupling: it is
  nonnegative and dominated by `r² + r√(r²+16π)` (via the `D`-form
  `gFun = b²(1/D − 1/(2r²))` of `gFun_eq_phi`), hence `O(r³)`; its integral is
  `O(c₁⁴) ≤ O(ε)`.

The two pieces give the pointwise majorant `27.2·η·r + 8.2·r³`, whose integral
over `(0,c₁]` is `13.6·η·c₁² + 2.05·c₁⁴ ≤ 15.65·ε ≤ 31·ε` using
`η ≤ ε`, `c₁ ≤ 1` and `c₁ ≤ (K_ℓs)^{-1} ≤ ε`.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators

namespace Work.BoseB6Est

/-! ## Elementary radial facts -/

/-- On `(0,c₁]` the kinetic symbol `τ̃` vanishes, so the physical bracket is the
`τ = 0` bracket `gFun 0 β(r) r`. -/
lemma fsGR_eq_gFun_zero (K : FsKernel) {εT c1 c2 : ℝ} (hc1 : 0 ≤ c1) (hc12 : c1 ≤ c2)
    {r : ℝ} (hr0 : 0 ≤ r) (hrc : r ≤ c1) :
    fsGR K εT c1 c2 r = gFun 0 (K.β r) r := by
  rw [fsGR_eq_gFun, fsTau_eq_zero hc1 hc12 hr0 hrc]

/-- `r ↦ r²·(gFun (r²) 8π r)` is continuous, and its `τ`-derivative at the model
coupling is `O(r³)`: `r² (gFun 0 8π r − gFun r² 8π r) ≤ r² (r² + r√(r²+16π))`. -/
lemma gFun_zero_model_diff_le {b r : ℝ} (hb : 0 < b) (hr0 : 0 < r) :
    r ^ 2 * (gFun 0 b r - gFun (r ^ 2) b r) ≤ r ^ 2 * (r ^ 2 + r * Real.sqrt (r ^ 2 + 2 * b)) := by
  have hb0 : 0 ≤ b := hb.le
  set D : ℝ := r ^ 2 + b + Real.sqrt ((r ^ 2) ^ 2 + 2 * (r ^ 2) * b) with hD
  have hDpos : 0 < D := by
    rw [hD]
    have h1 : 0 < r ^ 2 + b := by linarith [pow_pos hr0 2, hb]
    have h2 : 0 ≤ Real.sqrt ((r ^ 2) ^ 2 + 2 * (r ^ 2) * b) := Real.sqrt_nonneg _
    linarith
  have hDb : b ≤ D := by
    rw [hD]
    have h2 : 0 ≤ Real.sqrt ((r ^ 2) ^ 2 + 2 * (r ^ 2) * b) := Real.sqrt_nonneg _
    nlinarith [sq_nonneg r, h2]
  have hphi0 : gFun 0 b r = b ^ 2 * (1 / b - 1 / (2 * r ^ 2)) := by
    rw [gFun_eq_phi (τ := 0) (b := b) (r := r) le_rfl hb0]
    norm_num
  have hphir : gFun (r ^ 2) b r = b ^ 2 * (1 / D - 1 / (2 * r ^ 2)) := by
    rw [gFun_eq_phi (τ := r ^ 2) (b := b) (r := r) (sq_nonneg r) hb0, ← hD]
  have hdiff : gFun 0 b r - gFun (r ^ 2) b r = b * (D - b) / D := by
    rw [hphi0, hphir]
    field_simp
    ring
  have hbD : b / D ≤ 1 := (div_le_one hDpos).mpr hDb
  have hstep1 : b * (D - b) / D ≤ D - b := by
    have h : b / D * (D - b) ≤ 1 * (D - b) := mul_le_mul_of_nonneg_right hbD (by linarith)
    have he : b * (D - b) / D = b / D * (D - b) := by ring
    rw [he]; simpa using h
  have hsqrt : Real.sqrt ((r ^ 2) ^ 2 + 2 * (r ^ 2) * b) = r * Real.sqrt (r ^ 2 + 2 * b) := by
    rw [show (r ^ 2) ^ 2 + 2 * (r ^ 2) * b = r ^ 2 * (r ^ 2 + 2 * b) by ring]
    rw [Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr0.le]
  have hDb' : D - b = r ^ 2 + r * Real.sqrt (r ^ 2 + 2 * b) := by
    rw [hD, hsqrt]; ring
  calc r ^ 2 * (gFun 0 b r - gFun (r ^ 2) b r)
      = r ^ 2 * (b * (D - b) / D) := by rw [hdiff]
    _ ≤ r ^ 2 * (D - b) := mul_le_mul_of_nonneg_left hstep1 (sq_nonneg r)
    _ = r ^ 2 * (r ^ 2 + r * Real.sqrt (r ^ 2 + 2 * b)) := by rw [hDb']

/-! ## The two pointwise pieces -/

/-- **The `β`-deviation piece.**  On `(0,c₁]` one has `r ≤ c₁ < T`, hence the
kernel's closeness bound `|β(r) − 8π| ≤ η r`; the exact `τ = 0` increment
`gFun_zero_diff` gives

  `r² (gFun 0 β(r) r − gFun 0 8π r) = r²(β−8π) − (β² −(8π)²)/2`,

whose absolute value is at most `η r³ + η r (β+8π)/2 ≤ 27.2 η r`. -/
lemma reg_small_pt_beta (K : FsKernel) {a R ρz μ εT c1 c2 Kl s d : ℝ}
    (h : FsI1Regime K a R ρz μ εT c1 c2 Kl s d) {r : ℝ}
    (hr0 : 0 < r) (hrc : r ≤ c1) :
    |r ^ 2 * (gFun 0 (K.β r) r - gFun 0 (8 * Real.pi) r)| ≤ 27.2 * K.η * r := by
  have hb0 : 0 ≤ K.β r := K.nonneg r
  have hb' : 0 ≤ 8 * Real.pi := by positivity
  have hΔ : |K.β r - 8 * Real.pi| ≤ K.η * r :=
    K.close r hr0.le (le_trans hrc (le_of_lt h.hc1T))
  have hbd : K.β r ≤ 26.2 := K.beta_le_B0 h.hηT hr0
  have h8pi : 8 * Real.pi ≤ 26.2 := by nlinarith [Real.pi_lt_d2]
  have h1 := gFun_zero_diff_abs_le hb0 hb' hr0
  have hr2le1 : r ^ 2 ≤ 1 := by
    have hle1 : r ≤ 1 := le_trans hrc (FsI1Regime.c1_le_one h)
    nlinarith
  have hid : r ^ 2 * (1 + (K.β r + 8 * Real.pi) / (2 * r ^ 2))
      = r ^ 2 + (K.β r + 8 * Real.pi) / 2 := by
    field_simp
  calc |r ^ 2 * (gFun 0 (K.β r) r - gFun 0 (8 * Real.pi) r)|
      = r ^ 2 * |gFun 0 (K.β r) r - gFun 0 (8 * Real.pi) r| := by
        rw [abs_mul, abs_of_nonneg (sq_nonneg r)]
    _ ≤ r ^ 2 * (|K.β r - 8 * Real.pi| * (1 + (K.β r + 8 * Real.pi) / (2 * r ^ 2))) :=
        mul_le_mul_of_nonneg_left h1 (sq_nonneg r)
    _ = |K.β r - 8 * Real.pi| * (r ^ 2 * (1 + (K.β r + 8 * Real.pi) / (2 * r ^ 2))) := by ring
    _ = |K.β r - 8 * Real.pi| * (r ^ 2 + (K.β r + 8 * Real.pi) / 2) := by rw [hid]
    _ ≤ (K.η * r) * 27.2 := by
        have h2 : r ^ 2 + (K.β r + 8 * Real.pi) / 2 ≤ 27.2 := by linarith
        exact mul_le_mul hΔ h2 (by positivity) (mul_nonneg K.ηnn hr0.le)
    _ = 27.2 * K.η * r := by ring

/-- **The model `τ`-increment piece.**  `r²(G(0,8π) − G₀)` is at most
`r²(r² + r√(r²+16π))` (`gFun_zero_model_diff_le`), and for `r ≤ 1` this is
`≤ (1 + 7.2) r³ = 8.2 r³`. -/
lemma reg_small_pt_model {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    r ^ 2 * (gFun 0 (8 * Real.pi) r - gFun (r ^ 2) (8 * Real.pi) r) ≤ 8.2 * r ^ 3 := by
  have hb0 : 0 < 8 * Real.pi := by positivity
  have hmain := gFun_zero_model_diff_le (b := 8 * Real.pi) hb0 hr0
  have h72 : r ^ 2 + 2 * (8 * Real.pi) ≤ 7.2 ^ 2 := by
    nlinarith [Real.pi_lt_d2, sq_nonneg r, hr1, hr0]
  have hsqle : Real.sqrt (r ^ 2 + 2 * (8 * Real.pi)) ≤ 7.2 := by
    have h := Real.sqrt_le_sqrt h72
    rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (7.2 : ℝ))] at h
  have h43 : r ^ 4 ≤ r ^ 3 := by
    calc r ^ 4 = r ^ 3 * r := by ring
      _ ≤ r ^ 3 * 1 := mul_le_mul_of_nonneg_left hr1 (by positivity)
      _ = r ^ 3 := by ring
  calc r ^ 2 * (gFun 0 (8 * Real.pi) r - gFun (r ^ 2) (8 * Real.pi) r)
      ≤ r ^ 2 * (r ^ 2 + r * Real.sqrt (r ^ 2 + 2 * (8 * Real.pi))) := hmain
    _ = r ^ 4 + r ^ 3 * Real.sqrt (r ^ 2 + 2 * (8 * Real.pi)) := by ring
    _ ≤ r ^ 4 + r ^ 3 * 7.2 := by
        have h := mul_le_mul_of_nonneg_left hsqle (by positivity : (0 : ℝ) ≤ r ^ 3)
        linarith
    _ ≤ 8.2 * r ^ 3 := by linarith [h43]

/-! ## The region estimate -/

/-- **FS's small-region estimate** `∫_{0}^{c₁} r²(G − G₀) ≤ 31 ε(μ,ρ_z)`. -/
theorem reg_small (K : FsKernel) {a R ρz μ εT c1 c2 Kl s d : ℝ}
    (h : FsI1Regime K a R ρz μ εT c1 c2 Kl s d) :
    (∫ r in Set.Ioc (0 : ℝ) c1, r ^ 2 * (fsGR K εT c1 c2 r - fsG0R r))
      ≤ 31 * Work.BoseB6.lhyEps a R εT Kl s d μ := by
  set eps := Work.BoseB6.lhyEps a R εT Kl s d μ with heps
  have heps0 : 0 ≤ eps := by rw [heps]; exact FsI1Regime.lhyEps_nonneg h
  have hε1 : εT ≤ 1 := by linarith [h.hε1]
  -- integrability of the integrand on `(0,∞)`
  have hg1 : IntegrableOn (fun r : ℝ => r ^ 2 * fsGR K εT c1 c2 r) (Set.Ioi 0) :=
    integrableOn_r2_fsGR K h.hε0 hε1 h.hηT
  have hg' : IntegrableOn (fun r : ℝ => r ^ 2 * fsGR K εT c1 c2 r - r ^ 2 * fsG0R r)
      (Set.Ioi 0) := hg1.sub integrableOn_r2_fsG0R
  have hg : IntegrableOn (fun r : ℝ => r ^ 2 * (fsGR K εT c1 c2 r - fsG0R r))
      (Set.Ioi 0) := by
    refine (MeasureTheory.integrableOn_congr_fun
      (f := fun r : ℝ => r ^ 2 * fsGR K εT c1 c2 r - r ^ 2 * fsG0R r)
      (g := fun r : ℝ => r ^ 2 * (fsGR K εT c1 c2 r - fsG0R r))
      (fun r _ => by ring) measurableSet_Ioi).mp hg'
  have hgIoc : IntegrableOn (fun r : ℝ => r ^ 2 * (fsGR K εT c1 c2 r - fsG0R r))
      (Set.Ioc (0 : ℝ) c1) := hg.mono_set (fun r hr => hr.1)
  -- the majorant is integrable on `(0,c₁]`
  have hmaj_cont : Continuous (fun r : ℝ => 27.2 * K.η * r + 8.2 * r ^ 3) := by fun_prop
  have hmaj : IntegrableOn (fun r : ℝ => 27.2 * K.η * r + 8.2 * r ^ 3)
      (Set.Ioc (0 : ℝ) c1) :=
    hmaj_cont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  -- the pointwise bound
  have hpt : ∀ r ∈ Set.Ioc (0 : ℝ) c1,
      r ^ 2 * (fsGR K εT c1 c2 r - fsG0R r) ≤ 27.2 * K.η * r + 8.2 * r ^ 3 := by
    intro r hr
    have hr0 : 0 < r := hr.1
    have hrc : r ≤ c1 := hr.2
    have hG : fsGR K εT c1 c2 r = gFun 0 (K.β r) r :=
      fsGR_eq_gFun_zero K h.hc1 h.hc12 hr0.le hrc
    have hsplit : r ^ 2 * (gFun 0 (K.β r) r - gFun (r ^ 2) (8 * Real.pi) r)
        = r ^ 2 * (gFun 0 (K.β r) r - gFun 0 (8 * Real.pi) r)
          + r ^ 2 * (gFun 0 (8 * Real.pi) r - gFun (r ^ 2) (8 * Real.pi) r) := by ring
    have hA : r ^ 2 * (gFun 0 (K.β r) r - gFun 0 (8 * Real.pi) r) ≤ 27.2 * K.η * r :=
      le_trans (le_abs_self _) (reg_small_pt_beta K h hr0 hrc)
    have hB : r ^ 2 * (gFun 0 (8 * Real.pi) r - gFun (r ^ 2) (8 * Real.pi) r) ≤ 8.2 * r ^ 3 :=
      reg_small_pt_model hr0 (le_trans hrc (FsI1Regime.c1_le_one h))
    rw [hG, fsG0R_eq_gFun r, hsplit]
    linarith
  have hmono := setIntegral_mono_on hgIoc hmaj measurableSet_Ioc hpt
  -- the value of the majorant integral
  have hval : (∫ r in Set.Ioc (0 : ℝ) c1, (27.2 * K.η * r + 8.2 * r ^ 3))
      = 27.2 * K.η * (c1 ^ 2 / 2) + 8.2 * (c1 ^ 4 / 4) := by
    have h1 : IntervalIntegrable (fun x : ℝ => 27.2 * K.η * x) volume 0 c1 :=
      (continuous_const.mul continuous_id).intervalIntegrable 0 c1
    have h2 : IntervalIntegrable (fun x : ℝ => 8.2 * x ^ 3) volume 0 c1 :=
      (continuous_const.mul (continuous_id.pow 3)).intervalIntegrable 0 c1
    rw [← intervalIntegral.integral_of_le h.hc1]
    rw [intervalIntegral.integral_add h1 h2]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_id,
      integral_pow]
    ring
  -- the numerical bookkeeping
  have hc1inv : c1 ≤ (Kl * s)⁻¹ := by
    rw [h.hc1val]
    have h1 : 0 < (Kl * s)⁻¹ := inv_pos.mpr (mul_pos h.hKl h.hs)
    nlinarith [h.sqrt_mu_div_rhoz_le_two, h1]
  have hc1e : c1 ≤ eps := by
    rw [heps]; exact le_trans hc1inv h.hEpsKl
  have hc1le1 : c1 ≤ 1 := FsI1Regime.c1_le_one h
  have harith : 27.2 * K.η * (c1 ^ 2 / 2) + 8.2 * (c1 ^ 4 / 4) ≤ 31 * eps := by
    have hA : 27.2 * K.η * (c1 ^ 2 / 2) ≤ 13.6 * eps := by
      have h1 : c1 ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ h.hc1 hc1le1 2
      have h2 : K.η ≤ eps := by rw [heps]; exact h.hEpsEta
      nlinarith [K.ηnn, heps0, h.hc1, h1]
    have hB : 8.2 * (c1 ^ 4 / 4) ≤ 2.05 * eps := by
      have h3 : c1 ^ 3 ≤ 1 := by simpa using pow_le_pow_left₀ h.hc1 hc1le1 3
      have h1 : c1 ^ 4 ≤ c1 := by
        calc c1 ^ 4 = c1 ^ 3 * c1 := by ring
          _ ≤ 1 * c1 := mul_le_mul_of_nonneg_right h3 h.hc1
          _ = c1 := by ring
      nlinarith [hc1e, heps0]
    linarith
  calc (∫ r in Set.Ioc (0 : ℝ) c1, r ^ 2 * (fsGR K εT c1 c2 r - fsG0R r))
      ≤ (∫ r in Set.Ioc (0 : ℝ) c1, (27.2 * K.η * r + 8.2 * r ^ 3)) := hmono
    _ = 27.2 * K.η * (c1 ^ 2 / 2) + 8.2 * (c1 ^ 4 / 4) := hval
    _ ≤ 31 * eps := harith

end Work.BoseB6Est
