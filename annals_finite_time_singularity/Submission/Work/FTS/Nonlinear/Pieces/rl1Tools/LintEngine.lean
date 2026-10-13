/-
# `LintEngine` — the pointwise and measure-theoretic kit for the `rl1`-rows of `N`

The `N_i^{gs}`/`N_i^{gg}`/`N_i^{ss}` estimates of the `rl1` family bound the iterated
`∫⁻ r, r⁻¹ (∫⁻ θ, |K θ · N_i(r,θ)|)` of each piece of `N` by `K·α^{1/2}·|g|_{ℋ⁴}`.

This file collects the two kinds of ingredient such an estimate needs, in the exact
shapes the row proofs consume them.

## Pointwise facts

* `abs_K_le_three`: `|K θ| ≤ 3`, `K θ = 3 sin θ cos²θ`;
* `abs_sin_two_mul_deriv_Gam_le`: `|sin(2θ)·Γ'(θ)| ≤ 4α/3` (this is `D_θΓ = α q Γ`
  with `|q| ≤ 4/3`, `Γ ≤ 1`);
* `abs_K_mul_deriv_Gam_le`: `|K θ · Γ'(θ)| ≤ 2α` (because `K θ = (3/2) cos θ · sin 2θ`);
* `FstarPt`: the pointwise size of the profile `F_*` and of `D_zF_*`,
  `|F_*| ≤ 20α·z/(1+z)²` and `|D_zF_*| ≤ 40α·z/(1+z)²`.

## Measure-theoretic engines

Writing `ofReal r⁻¹·(⋯)` for the radial weight `r⁻¹` of the `rl1` norm,

* `inner_le_const`: an angular bound constant in `θ` gives
  `∫⁻ θ in Iθ, ofReal (g θ) ≤ ofReal (2 D)`;
* `outer_le`: the radial integration against `r⁻¹` of a bound `C·r/(1+r)²` gives
  `∫⁻ r in Ioi 0, ofReal r⁻¹ ofReal (C r/(1+r)²) ≤ ofReal (2C)`;
* `outer_le_radial`: the same for a bound `C|ρ r| r/(1+r)²` where `ρ` is only known
  through the weighted `L¹`-bound `∫ |ρ|/(1+r)² ≤ 2X` (the `FK g`-case).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.H2.InvOneAddSq
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.FzFacts
import Submission.Work.FTS.Nonlinear.FstarPkg.DthFstar_W
import Submission.Work.Spaces.c_bounds
import Submission.Work.Spaces.Gam_bounds
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.FM.Core

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.rl1Tools

/-! ## Pointwise facts -/

theorem abs_K_le_three (θ : ℝ) : |Work.Spaces.K θ| ≤ 3 := by
  have hc2 : |Real.cos θ ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [Real.neg_one_le_cos θ, Real.cos_le_one θ]
  have hs : |Real.sin θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩
  rw [Work.Spaces.K, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
  calc 3 * |Real.sin θ| * |Real.cos θ ^ 2| ≤ 3 * 1 * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hs (by norm_num)) hc2 (abs_nonneg _) (by norm_num)
    _ = 3 := by norm_num

theorem abs_sin_two_mul_deriv_Gam_le {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    |Real.sin (2 * θ) * deriv (fun t => Work.Spaces.Gam α t) θ| ≤ 4 * α / 3 := by
  rcases eq_or_lt_of_le hθ.1 with h0 | h0
  · rw [← h0, show 2 * (0 : ℝ) = 0 from by ring, Real.sin_zero, zero_mul, abs_zero]
    positivity
  rcases lt_or_eq_of_le hθ.2 with h1 | h1
  · have h := Work.Spaces.dthU_Gam α θ hα ⟨h0, h1⟩
    rw [Work.Spaces.dthU] at h
    obtain ⟨hG0, hG1⟩ := Work.Spaces.Gam_bounds α θ hα hθ
    have hq : |Work.Spaces.qfun θ| ≤ 4 / 3 := by
      rw [Work.Spaces.qfun, abs_le]
      constructor <;> linarith [Real.neg_one_le_cos (2 * θ), Real.cos_le_one (2 * θ)]
    rw [h, abs_mul, abs_mul, abs_of_pos hα, abs_of_nonneg hG0]
    calc α * |Work.Spaces.qfun θ| * Work.Spaces.Gam α θ ≤ α * (4 / 3) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hq hα.le) hG1 hG0 (by positivity)
      _ = 4 * α / 3 := by ring
  · rw [h1, show 2 * (π / 2) = π from by ring, Real.sin_pi, zero_mul, abs_zero]
    positivity

theorem abs_K_mul_deriv_Gam_le {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.K θ * deriv (fun t => Work.Spaces.Gam α t) θ| ≤ 2 * α := by
  have hK : Work.Spaces.K θ = (3 / 2) * Real.cos θ * Real.sin (2 * θ) := by
    rw [Work.Spaces.K, Real.sin_two_mul]; ring
  have hcos : |Real.cos θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
  have h2 := abs_sin_two_mul_deriv_Gam_le hα hθ
  rw [hK,
    show (3 / 2) * Real.cos θ * Real.sin (2 * θ) * deriv (fun t => Work.Spaces.Gam α t) θ
        = (3 / 2) * Real.cos θ
            * (Real.sin (2 * θ) * deriv (fun t => Work.Spaces.Gam α t) θ) from by ring,
    abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2)]
  calc (3 / 2) * |Real.cos θ|
        * |Real.sin (2 * θ) * deriv (fun t => Work.Spaces.Gam α t) θ|
      ≤ (3 / 2) * 1 * (4 * α / 3) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hcos (by norm_num)) h2 (abs_nonneg _) (by norm_num)
    _ = 2 * α := by ring

/-- **The pointwise size of `F_*` and `D_zF_*`.** -/
theorem FstarPt {α z θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hz : 0 ≤ z)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Construction.Fstar α z θ| ≤ 20 * α * (z / (1 + z) ^ 2) ∧
    |Work.Spaces.Dz (Work.Construction.Fstar α) z θ| ≤ 40 * α * (z / (1 + z) ^ 2) := by
  obtain ⟨hc1, hc2⟩ := Work.Spaces.c_bounds α hα hα1
  have hc0 : 0 < Work.Spaces.c α := by linarith
  obtain ⟨hG0, hG1⟩ := Work.Spaces.Gam_bounds α θ hα hθ
  have hzc : 0 ≤ z / (1 + z) ^ 2 := div_nonneg hz (by positivity)
  have hGc : Work.Spaces.Gam α θ / Work.Spaces.c α ≤ 10 := by
    rw [div_le_iff₀ hc0]; nlinarith
  have hGcnn : 0 ≤ Work.Spaces.Gam α θ / Work.Spaces.c α := div_nonneg hG0 hc0.le
  constructor
  · rw [Work.Construction.Fstar, Work.FM.Fstar,
      abs_of_nonneg (mul_nonneg (mul_nonneg hα.le hGcnn) (by positivity))]
    calc α * (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z / (1 + z) ^ 2)
        ≤ α * 10 * (2 * z / (1 + z) ^ 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hGc hα.le) (by positivity)
      _ = 20 * α * (z / (1 + z) ^ 2) := by ring
  · have heq : (fun z' => Work.Construction.Fstar α z' θ)
        = fun z' => (α * (Work.Spaces.Gam α θ / Work.Spaces.c α)) * Work.FM.Fstar z' := by
      funext z'
      rw [Work.Construction.Fstar]
    have hder : deriv (fun z' => (α * (Work.Spaces.Gam α θ / Work.Spaces.c α))
          * Work.FM.Fstar z') z
        = (α * (Work.Spaces.Gam α θ / Work.Spaces.c α)) * (2 * (1 - z) / (1 + z) ^ 3) :=
      ((Work.FM.hasDerivAt_Fstar z (by linarith)).const_mul
        (α * (Work.Spaces.Gam α θ / Work.Spaces.c α))).deriv
    have hfac : Work.Spaces.Dz (Work.Construction.Fstar α) z θ
        = z * (α * (Work.Spaces.Gam α θ / Work.Spaces.c α)) * deriv Work.FM.Fstar z := by
      rw [Work.Spaces.Dz, Work.Spaces.pz, heq, hder, Work.FM.deriv_Fstar z (by linarith)]
      ring
    have hd : |deriv Work.FM.Fstar z| ≤ 2 / (1 + z) ^ 2 := by
      rw [Work.FM.deriv_Fstar z (by linarith)]
      have h1 : |1 - z| ≤ 1 + z := abs_le.mpr ⟨by linarith, by linarith⟩
      rw [abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 + z) ^ 3), div_le_iff₀ (by positivity)]
      calc 2 * |1 - z| ≤ 2 * (1 + z) := by linarith
        _ = 2 / (1 + z) ^ 2 * (1 + z) ^ 3 := by first | (field_simp; ring) | field_simp | ring
    have h1 : |α * (Work.Spaces.Gam α θ / Work.Spaces.c α)| ≤ 10 * α := by
      rw [abs_mul, abs_of_pos hα, abs_of_nonneg hGcnn]
      calc α * (Work.Spaces.Gam α θ / Work.Spaces.c α) ≤ α * 10 :=
            mul_le_mul_of_nonneg_left hGc hα.le
        _ = 10 * α := by ring
    rw [hfac, abs_mul, abs_mul, abs_of_nonneg hz]
    calc z * |α * (Work.Spaces.Gam α θ / Work.Spaces.c α)| * |deriv Work.FM.Fstar z|
        ≤ z * (10 * α) * (2 / (1 + z) ^ 2) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 hz) hd (abs_nonneg _) (by positivity)
      _ = 20 * α * (z / (1 + z) ^ 2) := by first | (field_simp; ring) | field_simp | ring
      _ ≤ 40 * α * (z / (1 + z) ^ 2) := by
          have h : 0 ≤ α * (z / (1 + z) ^ 2) := mul_nonneg hα.le hzc
          nlinarith [h]

/-! ## The measure-theoretic engines -/

/-- An angular bound which is constant in `θ` integrates to `ofReal (2 D)`. -/
theorem inner_le_const {g : ℝ → ℝ} {D : ℝ} (hD : 0 ≤ D)
    (h : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), g θ ≤ D) :
    (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (g θ)) ≤ ENNReal.ofReal (2 * D) := by
  have h1 : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (g θ))
      ≤ ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal D :=
    MeasureTheory.lintegral_mono_ae (h.mono fun θ hθ => ENNReal.ofReal_le_ofReal hθ)
  refine h1.trans ?_
  rw [MeasureTheory.setLIntegral_const, Work.Spaces.Iθ, Real.volume_Icc,
    show (π / 2 - 0 : ℝ) = π / 2 by ring, ← ENNReal.ofReal_mul hD]
  exact ENNReal.ofReal_le_ofReal (by nlinarith [Real.pi_le_four])

/-- An angular bound of the shape `C·h θ` with `h` nonnegative and integrable
integrates to `ofReal (C · ∫θ h θ)`. -/
theorem inner_le_mul_integral {g k : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hint : MeasureTheory.IntegrableOn k Work.Spaces.Iθ)
    (hnn : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), 0 ≤ k θ)
    (h : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), g θ ≤ C * k θ) :
    (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (g θ))
      ≤ ENNReal.ofReal (C * ∫ θ in Work.Spaces.Iθ, k θ) := by
  have hstep : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (g θ))
      ≤ ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal C * ENNReal.ofReal (k θ) := by
    refine MeasureTheory.lintegral_mono_ae ?_
    filter_upwards [h] with θ hθ
    rw [← ENNReal.ofReal_mul hC]
    exact ENNReal.ofReal_le_ofReal hθ
  refine hstep.trans ?_
  rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hkey : ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, k θ)
      = ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (k θ) :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnn
  rw [← hkey]
  exact le_of_eq (ENNReal.ofReal_mul hC).symm

/-- The radial weight `r⁻¹` against a bound `C·r/(1+r)²`: the product is `C/(1+r)²`,
whose integral over `(0,∞)` is at most `2` (`Work.FTS.H2.InvOneAddSq`). -/
theorem outer_le {C : ℝ} (hC : 0 ≤ C) :
    (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * ENNReal.ofReal (C * r / (1 + r) ^ 2))
      ≤ ENNReal.ofReal (2 * C) := by
  obtain ⟨hint, hle⟩ := Work.FTS.H2.InvOneAddSq
  have hcongr : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      ENNReal.ofReal r⁻¹ * ENNReal.ofReal (C * r / (1 + r) ^ 2)
        = ENNReal.ofReal C * ENNReal.ofReal ((1 / (1 + r)) ^ 2) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : 0 < r := hr
    have hrw : r⁻¹ * (C * r / (1 + r) ^ 2) = C * (1 / (1 + r)) ^ 2 := by
      field_simp
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hr0.le), ← ENNReal.ofReal_mul hC, hrw]
  rw [MeasureTheory.lintegral_congr_ae hcongr]
  rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hkey : ENNReal.ofReal (∫ r in Set.Ioi (0 : ℝ), (1 / (1 + r)) ^ 2)
      = ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal ((1 / (1 + r)) ^ 2) :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun r => by positivity)
  rw [← hkey]
  calc ENNReal.ofReal C * ENNReal.ofReal (∫ r in Set.Ioi (0 : ℝ), (1 / (1 + r)) ^ 2)
      ≤ ENNReal.ofReal C * ENNReal.ofReal 2 :=
        mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hle)
          (show (0 : ENNReal) ≤ ENNReal.ofReal C from bot_le)
    _ = ENNReal.ofReal (2 * C) := by rw [← ENNReal.ofReal_mul hC]; ring_nf

/-- The radial weight `r⁻¹` against a bound `C|ρ r| r/(1+r)²`, where `ρ` is only known
through its weighted `L¹`-bound `∫ |ρ|/(1+r)² ≤ 2X` and the integrability of that
function. -/
theorem outer_le_radial {ρ : ℝ → ℝ} {X C : ℝ} (hC : 0 ≤ C) (hX : 0 ≤ X)
    (hint : MeasureTheory.IntegrableOn (fun z => |ρ z| / (1 + z) ^ 2) (Set.Ioi (0 : ℝ)))
    (hle : (∫ z in Set.Ioi (0 : ℝ), |ρ z| / (1 + z) ^ 2) ≤ 2 * X) :
    (∫⁻ r in Set.Ioi (0 : ℝ),
        ENNReal.ofReal r⁻¹ * ENNReal.ofReal (C * |ρ r| * r / (1 + r) ^ 2))
      ≤ ENNReal.ofReal (4 * C * X) := by
  have hcongr : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      ENNReal.ofReal r⁻¹ * ENNReal.ofReal (C * |ρ r| * r / (1 + r) ^ 2)
        = ENNReal.ofReal C * ENNReal.ofReal (|ρ r| / (1 + r) ^ 2) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : 0 < r := hr
    have hrw : r⁻¹ * (C * |ρ r| * r / (1 + r) ^ 2) = C * (|ρ r| / (1 + r) ^ 2) := by
      field_simp
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hr0.le), ← ENNReal.ofReal_mul hC, hrw]
  rw [MeasureTheory.lintegral_congr_ae hcongr]
  rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hkey : ENNReal.ofReal (∫ z in Set.Ioi (0 : ℝ), |ρ z| / (1 + z) ^ 2)
      = ∫⁻ z in Set.Ioi (0 : ℝ), ENNReal.ofReal (|ρ z| / (1 + z) ^ 2) :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun z => by positivity)
  rw [← hkey]
  calc ENNReal.ofReal C * ENNReal.ofReal (∫ z in Set.Ioi (0 : ℝ), |ρ z| / (1 + z) ^ 2)
      ≤ ENNReal.ofReal C * ENNReal.ofReal (2 * X) :=
        mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hle)
          (show (0 : ENNReal) ≤ ENNReal.ofReal C from bot_le)
    _ = ENNReal.ofReal (C * (2 * X)) := by rw [ENNReal.ofReal_mul hC]
    _ ≤ ENNReal.ofReal (4 * C * X) := ENNReal.ofReal_le_ofReal (by nlinarith)

end Work.FTS.Nonlinear.Pieces.rl1Tools
