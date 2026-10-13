/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `θ`-endpoint growth bound for an angular slice

`Work.FTS.EllipticEst.H2W.lzeroGrowthBound`: for `u : ℝ → ℝ` of class `C^n` on `(0, π/2)` for
every `n`, with `∫_{Iθ} sin θ cos²θ · |Lzero1 u| < ∞`, there is `C ≥ 0` with

  `|u θ| ≤ C · (θ⁻¹ + (π/2 - θ)⁻¹)`   on `(0, π/2)`.

## The argument

`y₁ = sin 2θ` and `y₂ = LzeroSing` (`Work.FTS.EllipticEst.LzeroSing`) are two independent
solutions of `Lzero1 y = 0` on `(0, π/2)` with Wronskian `wron y₁ y₂ = -1/cos θ`.  For
`g = Lzero1 u` and `u` twice differentiable, the Cramer coefficients

  `c₁ = -wron(u, y₂)·cos θ`,  `c₂ = -wron(y₁, u)·cos θ`

satisfy `u = c₁ y₁ + c₂ y₂` and the exact derivative identities

  `c₁' = -g y₂ cos θ`,   `c₂' = g y₁ cos θ = 2 g ψ`,   `ψ = sin θ cos²θ`.

Hence `c₂` is bounded by `|c₂(π/4)| + 2 ∫ ψ|g|` (globally), while `c₁` is bounded through
`|y₂ cos θ| ≤ B₀` and the two pointwise lower bounds for the weight,
`ψ ≥ θ/π` on `[θ, π/4]` and `ψ ≥ (2√2/π²)(π/2-θ)²` on `[π/4, θ]`, which convert the unweighted
`L¹` mass over the interval into the weighted mass `∫ ψ|g|`.  Finally
`|y₂ θ| ≤ B₀/cos θ ≤ B₀π/(2(π/2-θ))` and `|y₁ θ| ≤ min(2θ, 2(π/2-θ))`, and the two cases
`θ ≤ π/4` and `θ ≥ π/4` give the claimed bound.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.H2W.LzeroSolSpan
import Submission.Work.FTS.EllipticEst.LzeroSingContDiffOn
import Submission.Work.FTS.EllipticEst.SliceLocal.integrableOn_sinCos2_Lzero1
import Submission.Work.FTS.EllipticEst.H2W.Lzb.LzeroSingCosBoundClean
import Submission.Work.FTS.EllipticEst.H2W.Lzb.WeightCompare
import Submission.Work.FTS.EllipticEst.H2W.Lzb.WronDerivs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W

set_option autoImplicit false

/-! ## The angular weight and elementary comparisons -/

/-- The angular weight `ψ θ = sin θ * cos θ ^ 2` of the solvability condition. -/
noncomputable def psiW (θ : ℝ) : ℝ := Real.sin θ * Real.cos θ ^ 2

theorem psiW_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ psiW θ := by
  obtain ⟨h0, h1⟩ := hθ
  have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [Real.pi_pos])
  have hc : 0 ≤ Real.cos θ := Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) h1
  rw [psiW]
  positivity

/-- `1 ≤ θ⁻¹ + (π/2-θ)⁻¹` on the open angular interval: each term is at least `1/2`. -/
theorem one_le_inv_add {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    1 ≤ θ⁻¹ + (Real.pi / 2 - θ)⁻¹ := by
  obtain ⟨h0, h1⟩ := hθ
  have hτ : 0 < Real.pi / 2 - θ := by linarith
  have hA : (1 : ℝ) / 2 ≤ θ⁻¹ := by
    have h : θ ≤ 2 := by linarith [Real.pi_le_four]
    have := one_div_le_one_div_of_le h0 h
    simpa [one_div] using this
  have hB : (1 : ℝ) / 2 ≤ (Real.pi / 2 - θ)⁻¹ := by
    have h : Real.pi / 2 - θ ≤ 2 := by linarith [Real.pi_le_four]
    have := one_div_le_one_div_of_le hτ h
    simpa [one_div] using this
  linarith

/-- `sin (2θ) ≤ 2θ` for `θ ≥ 0`. -/
theorem sin_two_mul_le_two_mul {θ : ℝ} (hθ : 0 ≤ θ) : Real.sin (2 * θ) ≤ 2 * θ :=
  Real.sin_le (by linarith)

/-- `sin (2θ) ≤ 2(π/2 - θ)` for `θ ≥ π/4`. -/
theorem sin_two_mul_le_two_sub {θ : ℝ} (hθ : Real.pi / 4 ≤ θ) (hθ2 : θ ≤ Real.pi / 2) :
    Real.sin (2 * θ) ≤ 2 * (Real.pi / 2 - θ) := by
  have h : 2 * θ = Real.pi - 2 * (Real.pi / 2 - θ) := by ring
  rw [h, Real.sin_pi_sub]
  exact Real.sin_le (by linarith)

/-- `1/cos θ ≤ (π/2)/(π/2 - θ)` on `(0, π/2)` (Jordan's inequality for `cos θ = sin(π/2-θ)`). -/
theorem inv_cos_le {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (Real.cos θ)⁻¹ ≤ (Real.pi / 2) * (Real.pi / 2 - θ)⁻¹ := by
  obtain ⟨h0, h1⟩ := hθ
  have hτ : 0 < Real.pi / 2 - θ := by linarith
  have hcos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [h0, Real.pi_pos], h1⟩
  have hle : Real.pi / 2 - θ ≤ Real.pi / 2 := by linarith
  have hj := Real.mul_le_sin (le_of_lt hτ) hle
  rw [Real.sin_pi_div_two_sub] at hj
  have ha : 0 < (2 / Real.pi) * (Real.pi / 2 - θ) := by positivity
  have h1' : (Real.cos θ)⁻¹ ≤ ((2 / Real.pi) * (Real.pi / 2 - θ))⁻¹ :=
    (inv_le_inv₀ hcos ha).mpr hj
  have h2 : ((2 / Real.pi) * (Real.pi / 2 - θ))⁻¹ = (Real.pi / 2) * (Real.pi / 2 - θ)⁻¹ := by
    field_simp
  rwa [h2] at h1'

/-! ## The two Cramer coefficients of a slice, and their derivatives -/

/-- `c₁ = -wron(u, LzeroSing)·cos θ`, the coefficient of the regular solution `sin 2θ` in the
Cramer representation of a solution `u` of `Lzero1 u = g`. -/
noncomputable def cCoef1 (u : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => -(wron u Work.FTS.EllipticEst.LzeroSing θ * Real.cos θ)

/-- `c₂ = -wron(sin 2θ, u)·cos θ`, the coefficient of the singular solution `LzeroSing`. -/
noncomputable def cCoef2 (u : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => -(wron (fun t : ℝ => Real.sin (2 * t)) u θ * Real.cos θ)

/-- The Wronskian of the two solutions of `Lzero1 y = 0` is `-1/cos θ`. -/
theorem wron_sinTwo_LzeroSing {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    wron (fun t : ℝ => Real.sin (2 * t)) Work.FTS.EllipticEst.LzeroSing θ
      = -1 / Real.cos θ := by
  rw [wron]
  change Work.FTS.EllipticEst.LzeroReg θ * deriv Work.FTS.EllipticEst.LzeroSing θ
    - deriv Work.FTS.EllipticEst.LzeroReg θ * Work.FTS.EllipticEst.LzeroSing θ
      = -1 / Real.cos θ
  exact Work.FTS.EllipticEst.LzeroSingWronskian θ hθ

/-- **The Cramer representation**: `u = c₁ sin 2θ + c₂ LzeroSing` on `(0, π/2)`. -/
theorem cramer_id (u : ℝ → ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    u θ = cCoef1 u θ * Real.sin (2 * θ) + cCoef2 u θ * Work.FTS.EllipticEst.LzeroSing θ := by
  have hW := wron_sinTwo_LzeroSing hθ
  have h1 : (0:ℝ) < θ := hθ.1
  have h2 : θ < Real.pi / 2 := hθ.2
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [h1, Real.pi_pos], h2⟩)
  simp only [cCoef1, cCoef2, wron] at hW ⊢
  have hW' : Real.cos θ * (Real.sin (2 * θ) * deriv Work.FTS.EllipticEst.LzeroSing θ
      - deriv (fun t : ℝ => Real.sin (2 * t)) θ * Work.FTS.EllipticEst.LzeroSing θ) = -1 := by
    rw [hW]; field_simp
  linear_combination (u θ) * hW'

/-- `c₁' = -g·y₂·cos θ` where `g = Lzero1 u`. -/
theorem hasDerivAt_cCoef1 {u : ℝ → ℝ}
    (hwr : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (wron u Work.FTS.EllipticEst.LzeroSing)
        (Real.tan θ * wron u Work.FTS.EllipticEst.LzeroSing θ
          + Work.FTS.EllipticEst.Lzero1 u θ * Work.FTS.EllipticEst.LzeroSing θ) θ) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (cCoef1 u)
        (-(Work.FTS.EllipticEst.Lzero1 u θ * Work.FTS.EllipticEst.LzeroSing θ
            * Real.cos θ)) θ := by
  intro θ hθ
  have h1 : (0:ℝ) < θ := hθ.1
  have h2 : θ < Real.pi / 2 := hθ.2
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [h1, Real.pi_pos], h2⟩)
  have h := ((hwr θ hθ).mul (Real.hasDerivAt_cos θ)).neg
  refine h.congr_deriv ?_
  rw [Real.tan_eq_sin_div_cos]
  field_simp
  ring

/-- `c₂' = g·sin 2θ·cos θ = 2 g ψ` where `g = Lzero1 u`. -/
theorem hasDerivAt_cCoef2 {u : ℝ → ℝ}
    (hwr : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (wron (fun t : ℝ => Real.sin (2 * t)) u)
        (Real.tan θ * wron (fun t : ℝ => Real.sin (2 * t)) u θ
          - Work.FTS.EllipticEst.Lzero1 u θ * Real.sin (2 * θ)) θ) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (cCoef2 u)
        (Work.FTS.EllipticEst.Lzero1 u θ * Real.sin (2 * θ) * Real.cos θ) θ := by
  intro θ hθ
  have h1 : (0:ℝ) < θ := hθ.1
  have h2 : θ < Real.pi / 2 := hθ.2
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [h1, Real.pi_pos], h2⟩)
  have h := ((hwr θ hθ).mul (Real.hasDerivAt_cos θ)).neg
  refine h.congr_deriv ?_
  rw [Real.tan_eq_sin_div_cos]
  field_simp
  ring

/-! ## The Newton–Leibniz bound and interval integrability -/

/-- `|f b - f a| ≤ ∫_a^b |f'|` for `a ≤ b` and `f` differentiable on `[a,b]`. -/
theorem abs_sub_le_intervalIntegral_abs {f f' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ x ∈ Set.uIcc a b, HasDerivAt f (f' x) x)
    (hint : IntervalIntegrable f' volume a b) :
    |f b - f a| ≤ ∫ x in a..b, |f' x| := by
  have h1 : ∫ x in a..b, f' x = f b - f a := intervalIntegral.integral_eq_sub_of_hasDerivAt hf hint
  rw [← h1]
  exact intervalIntegral.abs_integral_le_integral_abs hab

/-- Interval integrability on a closed subinterval of `(0, π/2)` from continuity on the
open interval. -/
theorem intervalIntegrable_of_continuousOn_I {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ioo (0 : ℝ) (Real.pi / 2))) {a b : ℝ} (ha : 0 < a)
    (hb : b < Real.pi / 2) (hab : a ≤ b) : IntervalIntegrable f volume a b := by
  refine (hf.mono ?_).intervalIntegrable
  intro x hx
  rw [Set.uIcc_of_le hab] at hx
  exact ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hb⟩

/-- The absolute value of `Lzero1 u` is continuous on the open angular interval when `u` is
of class `C²`. -/
theorem continuousOn_abs_Lzero1 {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 2 u (Set.Ioo (0 : ℝ) (Real.pi / 2))) :
    ContinuousOn (fun s => |Work.FTS.EllipticEst.Lzero1 u s|)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
  (Work.FTS.EllipticEst.SliceLocal.continuousOn_Lzero1_of_contDiffOn_two u hu).abs

/-- Continuity of the weighted mass integrand `ψ·|Lzero1 u|` on the open angular interval. -/
theorem continuousOn_psiW_mul {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 2 u (Set.Ioo (0 : ℝ) (Real.pi / 2))) :
    ContinuousOn (fun s => psiW s * |Work.FTS.EllipticEst.Lzero1 u s|)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have hψ : Continuous (fun s : ℝ => psiW s) := by
    change Continuous (fun s : ℝ => Real.sin s * Real.cos s ^ 2)
    fun_prop
  exact hψ.continuousOn.mul (continuousOn_abs_Lzero1 hu)

/-- The weighted mass of a source over a subinterval of `Iθ` is at most its mass over `Iθ`. -/
theorem intervalIntegral_psiW_le {f : ℝ → ℝ}
    (hint : IntegrableOn (fun s => psiW s * |f s|) Work.Spaces.Iθ) {a b : ℝ} (ha : 0 < a)
    (hb : b ≤ Real.pi / 2) (hab : a ≤ b) :
    ∫ s in a..b, psiW s * |f s| ≤ ∫ s in Work.Spaces.Iθ, psiW s * |f s| := by
  rw [intervalIntegral.integral_of_le hab]
  refine MeasureTheory.setIntegral_mono_set hint ?_ ?_
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with x hx
    exact mul_nonneg (psiW_nonneg hx) (abs_nonneg _)
  · exact Filter.Eventually.of_forall
      (fun x hx => ⟨le_trans ha.le hx.1.le, le_trans hx.2 hb⟩)

/-- On `(0, π/4]` the unweighted `L¹` mass over `[θ, π/4]` is controlled by the weighted mass
over `Iθ`, with constant `π/θ`. -/
theorem integral_abs_le_mass_left {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 2 u (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hint : IntegrableOn (fun s => psiW s * |Work.FTS.EllipticEst.Lzero1 u s|) Work.Spaces.Iθ)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ4 : θ ≤ Real.pi / 4) :
    ∫ s in θ..(Real.pi / 4), |Work.FTS.EllipticEst.Lzero1 u s|
      ≤ (Real.pi / θ) * ∫ s in Work.Spaces.Iθ,
          psiW s * |Work.FTS.EllipticEst.Lzero1 u s| := by
  obtain ⟨hWCl, _⟩ := Lzb.WeightCompare
  have hπ4 : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hcont1 : ContinuousOn (fun s => |Work.FTS.EllipticEst.Lzero1 u s|)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := continuousOn_abs_Lzero1 hu
  have hcont2 : ContinuousOn (fun s => (Real.pi / θ) *
      (psiW s * |Work.FTS.EllipticEst.Lzero1 u s|)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (continuousOn_psiW_mul hu).const_mul _
  have hi1 : IntervalIntegrable (fun s => |Work.FTS.EllipticEst.Lzero1 u s|) volume θ
      (Real.pi / 4) := intervalIntegrable_of_continuousOn_I hcont1 hθ0 hπ4 hθ4
  have hi2 : IntervalIntegrable (fun s => (Real.pi / θ) *
      (psiW s * |Work.FTS.EllipticEst.Lzero1 u s|)) volume θ (Real.pi / 4) :=
    intervalIntegrable_of_continuousOn_I hcont2 hθ0 hπ4 hθ4
  have hθπ : (0 : ℝ) < Real.pi / θ := by positivity
  have hpt : ∀ x ∈ Set.Icc θ (Real.pi / 4),
      |Work.FTS.EllipticEst.Lzero1 u x|
        ≤ (Real.pi / θ) * (psiW x * |Work.FTS.EllipticEst.Lzero1 u x|) := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hθ0 hx.1
    have hw : θ / Real.pi ≤ psiW x := by
      have h := hWCl θ x hθ0 hx.1 hx.2
      change θ / Real.pi ≤ Real.sin x * Real.cos x ^ 2
      exact h
    have hge : 1 ≤ (Real.pi / θ) * psiW x := by
      have h2 : (Real.pi / θ) * (θ / Real.pi) ≤ (Real.pi / θ) * psiW x :=
        mul_le_mul_of_nonneg_left hw (le_of_lt hθπ)
      have h3 : (Real.pi / θ) * (θ / Real.pi) = 1 := by field_simp
      linarith
    calc |Work.FTS.EllipticEst.Lzero1 u x| = 1 * |Work.FTS.EllipticEst.Lzero1 u x| :=
          (one_mul _).symm
      _ ≤ ((Real.pi / θ) * psiW x) * |Work.FTS.EllipticEst.Lzero1 u x| :=
          mul_le_mul_of_nonneg_right hge (abs_nonneg _)
      _ = (Real.pi / θ) * (psiW x * |Work.FTS.EllipticEst.Lzero1 u x|) := by ring
  calc ∫ s in θ..(Real.pi / 4), |Work.FTS.EllipticEst.Lzero1 u s|
      ≤ ∫ s in θ..(Real.pi / 4),
          (Real.pi / θ) * (psiW s * |Work.FTS.EllipticEst.Lzero1 u s|) :=
        intervalIntegral.integral_mono_on hθ4 hi1 hi2 hpt
    _ = (Real.pi / θ) * ∫ s in θ..(Real.pi / 4),
          psiW s * |Work.FTS.EllipticEst.Lzero1 u s| :=
        intervalIntegral.integral_const_mul _ _
    _ ≤ (Real.pi / θ) * ∫ s in Work.Spaces.Iθ,
          psiW s * |Work.FTS.EllipticEst.Lzero1 u s| :=
        mul_le_mul_of_nonneg_left
          (intervalIntegral_psiW_le hint hθ0 (by linarith [Real.pi_pos]) hθ4) (le_of_lt hθπ)

/-- On `[π/4, π/2)` the unweighted `L¹` mass over `[π/4, θ]` is controlled by the weighted mass
over `Iθ`, with constant `π²/(2√2 (π/2-θ)²)`. -/
theorem integral_abs_le_mass_right {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 2 u (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hint : IntegrableOn (fun s => psiW s * |Work.FTS.EllipticEst.Lzero1 u s|) Work.Spaces.Iθ)
    {θ : ℝ} (hθ4 : Real.pi / 4 ≤ θ) (hθ2 : θ < Real.pi / 2) :
    ∫ s in (Real.pi / 4)..θ, |Work.FTS.EllipticEst.Lzero1 u s|
      ≤ (Real.pi ^ 2 / (2 * Real.sqrt 2 * (Real.pi / 2 - θ) ^ 2))
          * ∫ s in Work.Spaces.Iθ, psiW s * |Work.FTS.EllipticEst.Lzero1 u s| := by
  obtain ⟨_, hWCr⟩ := Lzb.WeightCompare
  have hτ : 0 < Real.pi / 2 - θ := by linarith
  have hπ4 : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hπ4lt : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hcont1 : ContinuousOn (fun s => |Work.FTS.EllipticEst.Lzero1 u s|)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := continuousOn_abs_Lzero1 hu
  have hcont2 : ContinuousOn (fun s => (Real.pi ^ 2 / (2 * Real.sqrt 2 *
      (Real.pi / 2 - θ) ^ 2)) * (psiW s * |Work.FTS.EllipticEst.Lzero1 u s|))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := (continuousOn_psiW_mul hu).const_mul _
  have hi1 : IntervalIntegrable (fun s => |Work.FTS.EllipticEst.Lzero1 u s|) volume
      (Real.pi / 4) θ := intervalIntegrable_of_continuousOn_I hcont1 hπ4 hθ2 hθ4
  have hi2 : IntervalIntegrable (fun s => (Real.pi ^ 2 / (2 * Real.sqrt 2 *
      (Real.pi / 2 - θ) ^ 2)) * (psiW s * |Work.FTS.EllipticEst.Lzero1 u s|)) volume
      (Real.pi / 4) θ := intervalIntegrable_of_continuousOn_I hcont2 hπ4 hθ2 hθ4
  have hcpos : (0 : ℝ) < Real.pi ^ 2 / (2 * Real.sqrt 2 * (Real.pi / 2 - θ) ^ 2) := by
    have : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    positivity
  have hpt : ∀ x ∈ Set.Icc (Real.pi / 4) θ,
      |Work.FTS.EllipticEst.Lzero1 u x|
        ≤ (Real.pi ^ 2 / (2 * Real.sqrt 2 * (Real.pi / 2 - θ) ^ 2))
            * (psiW x * |Work.FTS.EllipticEst.Lzero1 u x|) := by
    intro x hx
    have hw : (2 * Real.sqrt 2 / Real.pi ^ 2) * (Real.pi / 2 - θ) ^ 2 ≤ psiW x := by
      have h := hWCr θ x hx.1 hx.2 hθ2
      change (2 * Real.sqrt 2 / Real.pi ^ 2) * (Real.pi / 2 - θ) ^ 2
        ≤ Real.sin x * Real.cos x ^ 2
      exact h
    have hge : 1 ≤ (Real.pi ^ 2 / (2 * Real.sqrt 2 * (Real.pi / 2 - θ) ^ 2)) * psiW x := by
      have h2 := mul_le_mul_of_nonneg_left hw (le_of_lt hcpos)
      have h3 : (Real.pi ^ 2 / (2 * Real.sqrt 2 * (Real.pi / 2 - θ) ^ 2))
          * ((2 * Real.sqrt 2 / Real.pi ^ 2) * (Real.pi / 2 - θ) ^ 2) = 1 := by
        have hs2 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
        have hτne : Real.pi / 2 - θ ≠ 0 := ne_of_gt hτ
        have hne : Real.pi - θ * 2 ≠ 0 := by
          intro hc
          exact hτne (by linarith)
        field_simp
        exact div_self (by linarith)
      linarith
    calc |Work.FTS.EllipticEst.Lzero1 u x| = 1 * |Work.FTS.EllipticEst.Lzero1 u x| :=
          (one_mul _).symm
      _ ≤ ((Real.pi ^ 2 / (2 * Real.sqrt 2 * (Real.pi / 2 - θ) ^ 2)) * psiW x)
            * |Work.FTS.EllipticEst.Lzero1 u x| :=
          mul_le_mul_of_nonneg_right hge (abs_nonneg _)
      _ = (Real.pi ^ 2 / (2 * Real.sqrt 2 * (Real.pi / 2 - θ) ^ 2))
            * (psiW x * |Work.FTS.EllipticEst.Lzero1 u x|) := by ring
  calc ∫ s in (Real.pi / 4)..θ, |Work.FTS.EllipticEst.Lzero1 u s|
      ≤ ∫ s in (Real.pi / 4)..θ, (Real.pi ^ 2 / (2 * Real.sqrt 2 *
          (Real.pi / 2 - θ) ^ 2)) * (psiW s * |Work.FTS.EllipticEst.Lzero1 u s|) :=
        intervalIntegral.integral_mono_on hθ4 hi1 hi2 hpt
    _ = (Real.pi ^ 2 / (2 * Real.sqrt 2 * (Real.pi / 2 - θ) ^ 2))
          * ∫ s in (Real.pi / 4)..θ, psiW s * |Work.FTS.EllipticEst.Lzero1 u s| :=
        intervalIntegral.integral_const_mul _ _
    _ ≤ (Real.pi ^ 2 / (2 * Real.sqrt 2 * (Real.pi / 2 - θ) ^ 2))
          * ∫ s in Work.Spaces.Iθ, psiW s * |Work.FTS.EllipticEst.Lzero1 u s| :=
        mul_le_mul_of_nonneg_left
          (intervalIntegral_psiW_le hint hπ4 (le_of_lt hθ2) hθ4) (le_of_lt hcpos)

/-! ## Bounds for the two Cramer coefficients -/

/-- `|c₁(θ) - c₁(π/4)|` on `θ ≤ π/4`, from `|y₂ cos θ| ≤ B₀` and the weighted-mass bound. -/
theorem abs_cCoef1_sub_le_left {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 2 u (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hder : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (cCoef1 u)
        (-(Work.FTS.EllipticEst.Lzero1 u θ * Work.FTS.EllipticEst.LzeroSing θ
            * Real.cos θ)) θ)
    (hint : IntegrableOn (fun s => psiW s * |Work.FTS.EllipticEst.Lzero1 u s|) Work.Spaces.Iθ)
    {B0 : ℝ} (hB0nn : 0 ≤ B0)
    (hB0 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.FTS.EllipticEst.LzeroSing θ * Real.cos θ| ≤ B0)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ4 : θ ≤ Real.pi / 4) :
    |cCoef1 u θ - cCoef1 u (Real.pi / 4)|
      ≤ B0 * ((Real.pi / θ) * ∫ s in Work.Spaces.Iθ,
          psiW s * |Work.FTS.EllipticEst.Lzero1 u s|) := by
  have hπ4 : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hcont : ContinuousOn
      (fun x => -(Work.FTS.EllipticEst.Lzero1 u x * Work.FTS.EllipticEst.LzeroSing x
        * Real.cos x)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (((Work.FTS.EllipticEst.SliceLocal.continuousOn_Lzero1_of_contDiffOn_two u hu).mul
      (Work.FTS.EllipticEst.LzeroSingContDiffOn 0).continuousOn).mul
      Real.continuous_cos.continuousOn).neg
  have hint' : IntervalIntegrable
      (fun x => -(Work.FTS.EllipticEst.Lzero1 u x * Work.FTS.EllipticEst.LzeroSing x
        * Real.cos x)) volume θ (Real.pi / 4) :=
    intervalIntegrable_of_continuousOn_I hcont hθ0 hπ4 hθ4
  have hderI : ∀ x ∈ Set.uIcc θ (Real.pi / 4),
      HasDerivAt (cCoef1 u)
        (-(Work.FTS.EllipticEst.Lzero1 u x * Work.FTS.EllipticEst.LzeroSing x
            * Real.cos x)) x := by
    intro x hx
    rw [Set.uIcc_of_le hθ4] at hx
    exact hder x ⟨lt_of_lt_of_le hθ0 hx.1, lt_of_le_of_lt hx.2 hπ4⟩
  have hftc := abs_sub_le_intervalIntegral_abs hθ4 hderI hint'
  have hpt : ∀ x ∈ Set.Icc θ (Real.pi / 4),
      |-(Work.FTS.EllipticEst.Lzero1 u x * Work.FTS.EllipticEst.LzeroSing x
          * Real.cos x)| ≤ B0 * |Work.FTS.EllipticEst.Lzero1 u x| := by
    intro x hx
    have hxI : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨lt_of_lt_of_le hθ0 hx.1, lt_of_le_of_lt hx.2 hπ4⟩
    have hcos : 0 < Real.cos x :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hxI.1, Real.pi_pos], hxI.2⟩
    have hb := hB0 x hxI
    rw [abs_mul, abs_of_pos hcos] at hb
    have hcosabs : |Real.cos x| = Real.cos x := abs_of_pos hcos
    calc |-(Work.FTS.EllipticEst.Lzero1 u x * Work.FTS.EllipticEst.LzeroSing x
            * Real.cos x)|
        = |Work.FTS.EllipticEst.Lzero1 u x| * (|Work.FTS.EllipticEst.LzeroSing x|
            * Real.cos x) := by rw [abs_neg, abs_mul, abs_mul, hcosabs]; ring
      _ ≤ |Work.FTS.EllipticEst.Lzero1 u x| * B0 :=
          mul_le_mul_of_nonneg_left hb (abs_nonneg _)
      _ = B0 * |Work.FTS.EllipticEst.Lzero1 u x| := by ring
  have hi1 : IntervalIntegrable
      (fun x => |-(Work.FTS.EllipticEst.Lzero1 u x * Work.FTS.EllipticEst.LzeroSing x
        * Real.cos x)|) volume θ (Real.pi / 4) :=
    intervalIntegrable_of_continuousOn_I hcont.abs hθ0 hπ4 hθ4
  have hi2 : IntervalIntegrable
      (fun x => B0 * |Work.FTS.EllipticEst.Lzero1 u x|) volume θ (Real.pi / 4) :=
    intervalIntegrable_of_continuousOn_I ((continuousOn_abs_Lzero1 hu).const_mul _)
      hθ0 hπ4 hθ4
  calc |cCoef1 u θ - cCoef1 u (Real.pi / 4)|
      = |cCoef1 u (Real.pi / 4) - cCoef1 u θ| := abs_sub_comm _ _
    _ ≤ ∫ x in θ..(Real.pi / 4), |-(Work.FTS.EllipticEst.Lzero1 u x
          * Work.FTS.EllipticEst.LzeroSing x * Real.cos x)| := hftc
    _ ≤ ∫ x in θ..(Real.pi / 4), B0 * |Work.FTS.EllipticEst.Lzero1 u x| :=
        intervalIntegral.integral_mono_on hθ4 hi1 hi2 hpt
    _ = B0 * ∫ x in θ..(Real.pi / 4), |Work.FTS.EllipticEst.Lzero1 u x| :=
        intervalIntegral.integral_const_mul _ _
    _ ≤ B0 * ((Real.pi / θ) * ∫ s in Work.Spaces.Iθ,
          psiW s * |Work.FTS.EllipticEst.Lzero1 u s|) :=
        mul_le_mul_of_nonneg_left (integral_abs_le_mass_left hu hint hθ0 hθ4) hB0nn

/-- `|c₁(θ) - c₁(π/4)|` on `θ ≥ π/4`. -/
theorem abs_cCoef1_sub_le_right {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 2 u (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hder : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (cCoef1 u)
        (-(Work.FTS.EllipticEst.Lzero1 u θ * Work.FTS.EllipticEst.LzeroSing θ
            * Real.cos θ)) θ)
    (hint : IntegrableOn (fun s => psiW s * |Work.FTS.EllipticEst.Lzero1 u s|) Work.Spaces.Iθ)
    {B0 : ℝ} (hB0nn : 0 ≤ B0)
    (hB0 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.FTS.EllipticEst.LzeroSing θ * Real.cos θ| ≤ B0)
    {θ : ℝ} (hθ4 : Real.pi / 4 ≤ θ) (hθ2 : θ < Real.pi / 2) :
    |cCoef1 u θ - cCoef1 u (Real.pi / 4)|
      ≤ B0 * ((Real.pi ^ 2 / (2 * Real.sqrt 2 * (Real.pi / 2 - θ) ^ 2))
          * ∫ s in Work.Spaces.Iθ, psiW s * |Work.FTS.EllipticEst.Lzero1 u s|) := by
  have hπ4pos : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hπ4 : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hcont : ContinuousOn
      (fun x => -(Work.FTS.EllipticEst.Lzero1 u x * Work.FTS.EllipticEst.LzeroSing x
        * Real.cos x)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (((Work.FTS.EllipticEst.SliceLocal.continuousOn_Lzero1_of_contDiffOn_two u hu).mul
      (Work.FTS.EllipticEst.LzeroSingContDiffOn 0).continuousOn).mul
      Real.continuous_cos.continuousOn).neg
  have hint' : IntervalIntegrable
      (fun x => -(Work.FTS.EllipticEst.Lzero1 u x * Work.FTS.EllipticEst.LzeroSing x
        * Real.cos x)) volume (Real.pi / 4) θ :=
    intervalIntegrable_of_continuousOn_I hcont hπ4pos hθ2 hθ4
  have hderI : ∀ x ∈ Set.uIcc (Real.pi / 4) θ,
      HasDerivAt (cCoef1 u)
        (-(Work.FTS.EllipticEst.Lzero1 u x * Work.FTS.EllipticEst.LzeroSing x
            * Real.cos x)) x := by
    intro x hx
    rw [Set.uIcc_of_le hθ4] at hx
    exact hder x ⟨lt_of_lt_of_le hπ4pos hx.1, lt_of_le_of_lt hx.2 hθ2⟩
  have hftc := abs_sub_le_intervalIntegral_abs hθ4 hderI hint'
  have hpt : ∀ x ∈ Set.Icc (Real.pi / 4) θ,
      |-(Work.FTS.EllipticEst.Lzero1 u x * Work.FTS.EllipticEst.LzeroSing x
          * Real.cos x)| ≤ B0 * |Work.FTS.EllipticEst.Lzero1 u x| := by
    intro x hx
    have hxI : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨lt_of_lt_of_le hπ4pos hx.1, lt_of_le_of_lt hx.2 hθ2⟩
    have hcos : 0 < Real.cos x :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hxI.1, Real.pi_pos], hxI.2⟩
    have hb := hB0 x hxI
    rw [abs_mul, abs_of_pos hcos] at hb
    have hcosabs : |Real.cos x| = Real.cos x := abs_of_pos hcos
    calc |-(Work.FTS.EllipticEst.Lzero1 u x * Work.FTS.EllipticEst.LzeroSing x
            * Real.cos x)|
        = |Work.FTS.EllipticEst.Lzero1 u x| * (|Work.FTS.EllipticEst.LzeroSing x|
            * Real.cos x) := by rw [abs_neg, abs_mul, abs_mul, hcosabs]; ring
      _ ≤ |Work.FTS.EllipticEst.Lzero1 u x| * B0 :=
          mul_le_mul_of_nonneg_left hb (abs_nonneg _)
      _ = B0 * |Work.FTS.EllipticEst.Lzero1 u x| := by ring
  have hi1 : IntervalIntegrable
      (fun x => |-(Work.FTS.EllipticEst.Lzero1 u x * Work.FTS.EllipticEst.LzeroSing x
        * Real.cos x)|) volume (Real.pi / 4) θ :=
    intervalIntegrable_of_continuousOn_I hcont.abs hπ4pos hθ2 hθ4
  have hi2 : IntervalIntegrable
      (fun x => B0 * |Work.FTS.EllipticEst.Lzero1 u x|) volume (Real.pi / 4) θ :=
    intervalIntegrable_of_continuousOn_I ((continuousOn_abs_Lzero1 hu).const_mul _)
      hπ4pos hθ2 hθ4
  calc |cCoef1 u θ - cCoef1 u (Real.pi / 4)|
      ≤ ∫ x in (Real.pi / 4)..θ, |-(Work.FTS.EllipticEst.Lzero1 u x
          * Work.FTS.EllipticEst.LzeroSing x * Real.cos x)| := hftc
    _ ≤ ∫ x in (Real.pi / 4)..θ, B0 * |Work.FTS.EllipticEst.Lzero1 u x| :=
        intervalIntegral.integral_mono_on hθ4 hi1 hi2 hpt
    _ = B0 * ∫ x in (Real.pi / 4)..θ, |Work.FTS.EllipticEst.Lzero1 u x| :=
        intervalIntegral.integral_const_mul _ _
    _ ≤ B0 * ((Real.pi ^ 2 / (2 * Real.sqrt 2 * (Real.pi / 2 - θ) ^ 2))
          * ∫ s in Work.Spaces.Iθ, psiW s * |Work.FTS.EllipticEst.Lzero1 u s|) :=
        mul_le_mul_of_nonneg_left (integral_abs_le_mass_right hu hint hθ4 hθ2) hB0nn

/-- Pointwise comparison of the `c₂`-derivative integrand with `2 ψ |g|` on `Iθ`. -/
theorem abs_lzero1_sin_two_cos_le {u : ℝ → ℝ} {x : ℝ} (hx : x ∈ Work.Spaces.Iθ) :
    |Work.FTS.EllipticEst.Lzero1 u x * Real.sin (2 * x) * Real.cos x|
      ≤ 2 * (psiW x * |Work.FTS.EllipticEst.Lzero1 u x|) := by
  have hs2 : Real.sin (2 * x) * Real.cos x = 2 * psiW x := by
    rw [Real.sin_two_mul, psiW]; ring
  have hpsi : 0 ≤ psiW x := psiW_nonneg hx
  rw [show Work.FTS.EllipticEst.Lzero1 u x * Real.sin (2 * x) * Real.cos x
        = Work.FTS.EllipticEst.Lzero1 u x * (Real.sin (2 * x) * Real.cos x) by ring,
      abs_mul, hs2, abs_of_nonneg (mul_nonneg (by norm_num) hpsi)]
  exact le_of_eq (by ring)

/-- `c₂` is controlled globally by its value at `π/4` and twice the weighted mass: its
derivative is `2 g ψ`. -/
theorem abs_cCoef2_sub_le {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 2 u (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hder : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (cCoef2 u)
        (Work.FTS.EllipticEst.Lzero1 u θ * Real.sin (2 * θ) * Real.cos θ) θ)
    (hint : IntegrableOn (fun s => psiW s * |Work.FTS.EllipticEst.Lzero1 u s|) Work.Spaces.Iθ)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    |cCoef2 u θ - cCoef2 u (Real.pi / 4)|
      ≤ 2 * ∫ s in Work.Spaces.Iθ, psiW s * |Work.FTS.EllipticEst.Lzero1 u s| := by
  have hπ4pos : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hπ4 : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hcont : ContinuousOn
      (fun x => Work.FTS.EllipticEst.Lzero1 u x * Real.sin (2 * x) * Real.cos x)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (((Work.FTS.EllipticEst.SliceLocal.continuousOn_Lzero1_of_contDiffOn_two u hu).mul
      (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).mul
      Real.continuous_cos.continuousOn)
  have hcont2 : ContinuousOn
      (fun x => 2 * (psiW x * |Work.FTS.EllipticEst.Lzero1 u x|))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := (continuousOn_psiW_mul hu).const_mul _
  rcases le_total θ (Real.pi / 4) with hle | hge
  · have hderI : ∀ x ∈ Set.uIcc θ (Real.pi / 4),
        HasDerivAt (cCoef2 u)
          (Work.FTS.EllipticEst.Lzero1 u x * Real.sin (2 * x) * Real.cos x) x := by
      intro x hx
      rw [Set.uIcc_of_le hle] at hx
      exact hder x ⟨lt_of_lt_of_le hθ.1 hx.1, lt_of_le_of_lt hx.2 hπ4⟩
    have hi1 : IntervalIntegrable
        (fun x => Work.FTS.EllipticEst.Lzero1 u x * Real.sin (2 * x) * Real.cos x) volume
        θ (Real.pi / 4) := intervalIntegrable_of_continuousOn_I hcont hθ.1 hπ4 hle
    have hftc := abs_sub_le_intervalIntegral_abs hle hderI hi1
    have hi2 : IntervalIntegrable (fun x => 2 * (psiW x * |Work.FTS.EllipticEst.Lzero1 u x|))
        volume θ (Real.pi / 4) := intervalIntegrable_of_continuousOn_I hcont2 hθ.1 hπ4 hle
    have hi3 : IntervalIntegrable
        (fun x => |Work.FTS.EllipticEst.Lzero1 u x * Real.sin (2 * x) * Real.cos x|) volume
        θ (Real.pi / 4) := intervalIntegrable_of_continuousOn_I hcont.abs hθ.1 hπ4 hle
    calc |cCoef2 u θ - cCoef2 u (Real.pi / 4)|
        = |cCoef2 u (Real.pi / 4) - cCoef2 u θ| := abs_sub_comm _ _
      _ ≤ ∫ x in θ..(Real.pi / 4), |Work.FTS.EllipticEst.Lzero1 u x
            * Real.sin (2 * x) * Real.cos x| := hftc
      _ ≤ ∫ x in θ..(Real.pi / 4), 2 * (psiW x * |Work.FTS.EllipticEst.Lzero1 u x|) :=
          intervalIntegral.integral_mono_on hle hi3 hi2 (fun x hx =>
            abs_lzero1_sin_two_cos_le (u := u)
              ⟨le_trans hθ.1.le hx.1, le_trans hx.2 hπ4.le⟩)
      _ = 2 * ∫ x in θ..(Real.pi / 4), psiW x * |Work.FTS.EllipticEst.Lzero1 u x| :=
          intervalIntegral.integral_const_mul _ _
      _ ≤ 2 * ∫ s in Work.Spaces.Iθ, psiW s * |Work.FTS.EllipticEst.Lzero1 u s| :=
          mul_le_mul_of_nonneg_left
            (intervalIntegral_psiW_le hint hθ.1 (by linarith [Real.pi_pos]) hle) (by norm_num)
  · have hderI : ∀ x ∈ Set.uIcc (Real.pi / 4) θ,
        HasDerivAt (cCoef2 u)
          (Work.FTS.EllipticEst.Lzero1 u x * Real.sin (2 * x) * Real.cos x) x := by
      intro x hx
      rw [Set.uIcc_of_le hge] at hx
      exact hder x ⟨lt_of_lt_of_le hπ4pos hx.1, lt_of_le_of_lt hx.2 hθ.2⟩
    have hi1 : IntervalIntegrable
        (fun x => Work.FTS.EllipticEst.Lzero1 u x * Real.sin (2 * x) * Real.cos x) volume
        (Real.pi / 4) θ := intervalIntegrable_of_continuousOn_I hcont hπ4pos hθ.2 hge
    have hftc := abs_sub_le_intervalIntegral_abs hge hderI hi1
    have hi2 : IntervalIntegrable (fun x => 2 * (psiW x * |Work.FTS.EllipticEst.Lzero1 u x|))
        volume (Real.pi / 4) θ :=
      intervalIntegrable_of_continuousOn_I hcont2 hπ4pos hθ.2 hge
    have hi3 : IntervalIntegrable
        (fun x => |Work.FTS.EllipticEst.Lzero1 u x * Real.sin (2 * x) * Real.cos x|) volume
        (Real.pi / 4) θ := intervalIntegrable_of_continuousOn_I hcont.abs hπ4pos hθ.2 hge
    calc |cCoef2 u θ - cCoef2 u (Real.pi / 4)|
        ≤ ∫ x in (Real.pi / 4)..θ, |Work.FTS.EllipticEst.Lzero1 u x
            * Real.sin (2 * x) * Real.cos x| := hftc
      _ ≤ ∫ x in (Real.pi / 4)..θ, 2 * (psiW x * |Work.FTS.EllipticEst.Lzero1 u x|) :=
          intervalIntegral.integral_mono_on hge hi3 hi2 (fun x hx =>
            abs_lzero1_sin_two_cos_le (u := u)
              ⟨le_trans hπ4pos.le hx.1, le_of_lt (lt_of_le_of_lt hx.2 hθ.2)⟩)
      _ = 2 * ∫ x in (Real.pi / 4)..θ, psiW x * |Work.FTS.EllipticEst.Lzero1 u x| :=
          intervalIntegral.integral_const_mul _ _
      _ ≤ 2 * ∫ s in Work.Spaces.Iθ, psiW s * |Work.FTS.EllipticEst.Lzero1 u s| :=
          mul_le_mul_of_nonneg_left
            (intervalIntegral_psiW_le hint hπ4pos (le_of_lt hθ.2) hge) (by norm_num)

/-! ## The arithmetic of the two cases -/

/-- The arithmetic of the case `θ ≤ π/4`. -/
theorem arith_left {C1 C2 B0 K θ τ : ℝ}
    (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hB0 : 0 ≤ B0) (hK : 0 ≤ K) (hθ : 0 < θ) (hτ : 0 < τ)
    (hθ1 : θ ≤ 1) (hinv : 1 ≤ θ⁻¹ + τ⁻¹) :
    2 * C1 * θ + 2 * B0 * Real.pi * K + C2 * (B0 * (Real.pi / 2)) * τ⁻¹
      ≤ (4 * C1 + 16 * B0 * K + 2 * C2 * B0) * (θ⁻¹ + τ⁻¹) := by
  have hpi : Real.pi < 4 := Real.pi_lt_four
  have hτinv : 0 ≤ τ⁻¹ := inv_nonneg.mpr (le_of_lt hτ)
  have hθinv : 0 ≤ θ⁻¹ := inv_nonneg.mpr (le_of_lt hθ)
  have hsum : 0 ≤ θ⁻¹ + τ⁻¹ := by linarith
  have hA : 2 * C1 * θ ≤ 4 * C1 * (θ⁻¹ + τ⁻¹) := by
    have h1 : 2 * θ ≤ 4 * (θ⁻¹ + τ⁻¹) := by nlinarith
    calc 2 * C1 * θ = C1 * (2 * θ) := by ring
      _ ≤ C1 * (4 * (θ⁻¹ + τ⁻¹)) := mul_le_mul_of_nonneg_left h1 hC1
      _ = 4 * C1 * (θ⁻¹ + τ⁻¹) := by ring
  have hB : 2 * B0 * Real.pi * K ≤ 16 * B0 * K * (θ⁻¹ + τ⁻¹) := by
    have h1 : 2 * Real.pi ≤ 16 * (θ⁻¹ + τ⁻¹) := by nlinarith
    calc 2 * B0 * Real.pi * K = (B0 * K) * (2 * Real.pi) := by ring
      _ ≤ (B0 * K) * (16 * (θ⁻¹ + τ⁻¹)) := mul_le_mul_of_nonneg_left h1 (mul_nonneg hB0 hK)
      _ = 16 * B0 * K * (θ⁻¹ + τ⁻¹) := by ring
  have hC : C2 * (B0 * (Real.pi / 2)) * τ⁻¹ ≤ 2 * C2 * B0 * (θ⁻¹ + τ⁻¹) := by
    have h1 : (Real.pi / 2) * τ⁻¹ ≤ 2 * (θ⁻¹ + τ⁻¹) := by nlinarith
    calc C2 * (B0 * (Real.pi / 2)) * τ⁻¹ = (C2 * B0) * ((Real.pi / 2) * τ⁻¹) := by ring
      _ ≤ (C2 * B0) * (2 * (θ⁻¹ + τ⁻¹)) := mul_le_mul_of_nonneg_left h1 (mul_nonneg hC2 hB0)
      _ = 2 * C2 * B0 * (θ⁻¹ + τ⁻¹) := by ring
  have hkey : (4 * C1 + 16 * B0 * K + 2 * C2 * B0) * (θ⁻¹ + τ⁻¹)
      = 4 * C1 * (θ⁻¹ + τ⁻¹) + 16 * B0 * K * (θ⁻¹ + τ⁻¹)
        + 2 * C2 * B0 * (θ⁻¹ + τ⁻¹) := by ring
  linarith [hA, hB, hC, hkey.ge]

/-- The arithmetic of the case `θ ≥ π/4` (so `τ = π/2 - θ ≤ 1`). -/
theorem arith_right {C1 C2 B0 K θ τ : ℝ}
    (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hB0 : 0 ≤ B0) (hK : 0 ≤ K) (hθ : 0 < θ) (hτ : 0 < τ)
    (hτ1 : τ ≤ 1) (hinv : 1 ≤ θ⁻¹ + τ⁻¹) :
    2 * C1 * τ + B0 * (Real.pi ^ 2 / Real.sqrt 2) * K * τ⁻¹ + C2 * (B0 * (Real.pi / 2)) * τ⁻¹
      ≤ (4 * C1 + 16 * B0 * K + 2 * C2 * B0) * (θ⁻¹ + τ⁻¹) := by
  have hpi : Real.pi < 4 := Real.pi_lt_four
  have hpi2 : Real.pi ^ 2 / Real.sqrt 2 ≤ 16 := by
    have h2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    rw [div_le_iff₀ h2]
    have h1 : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_pos, Real.pi_lt_four]
    nlinarith [Real.one_lt_sqrt_two]
  have hτinv : 0 ≤ τ⁻¹ := inv_nonneg.mpr (le_of_lt hτ)
  have hθinv : 0 ≤ θ⁻¹ := inv_nonneg.mpr (le_of_lt hθ)
  have hsum : 0 ≤ θ⁻¹ + τ⁻¹ := by linarith
  have hA : 2 * C1 * τ ≤ 4 * C1 * (θ⁻¹ + τ⁻¹) := by
    have h1 : 2 * τ ≤ 4 * (θ⁻¹ + τ⁻¹) := by nlinarith
    calc 2 * C1 * τ = C1 * (2 * τ) := by ring
      _ ≤ C1 * (4 * (θ⁻¹ + τ⁻¹)) := mul_le_mul_of_nonneg_left h1 hC1
      _ = 4 * C1 * (θ⁻¹ + τ⁻¹) := by ring
  have hB : B0 * (Real.pi ^ 2 / Real.sqrt 2) * K * τ⁻¹
      ≤ 16 * B0 * K * (θ⁻¹ + τ⁻¹) := by
    have h1 : (Real.pi ^ 2 / Real.sqrt 2) * τ⁻¹ ≤ 16 * (θ⁻¹ + τ⁻¹) := by
      nlinarith [hpi2, hτinv, hθinv, hinv, mul_le_mul_of_nonneg_right hpi2 hτinv]
    calc B0 * (Real.pi ^ 2 / Real.sqrt 2) * K * τ⁻¹
        = (B0 * K) * ((Real.pi ^ 2 / Real.sqrt 2) * τ⁻¹) := by ring
      _ ≤ (B0 * K) * (16 * (θ⁻¹ + τ⁻¹)) := mul_le_mul_of_nonneg_left h1 (mul_nonneg hB0 hK)
      _ = 16 * B0 * K * (θ⁻¹ + τ⁻¹) := by ring
  have hC : C2 * (B0 * (Real.pi / 2)) * τ⁻¹ ≤ 2 * C2 * B0 * (θ⁻¹ + τ⁻¹) := by
    have h1 : (Real.pi / 2) * τ⁻¹ ≤ 2 * (θ⁻¹ + τ⁻¹) := by nlinarith
    calc C2 * (B0 * (Real.pi / 2)) * τ⁻¹ = (C2 * B0) * ((Real.pi / 2) * τ⁻¹) := by ring
      _ ≤ (C2 * B0) * (2 * (θ⁻¹ + τ⁻¹)) := mul_le_mul_of_nonneg_left h1 (mul_nonneg hC2 hB0)
      _ = 2 * C2 * B0 * (θ⁻¹ + τ⁻¹) := by ring
  have hkey : (4 * C1 + 16 * B0 * K + 2 * C2 * B0) * (θ⁻¹ + τ⁻¹)
      = 4 * C1 * (θ⁻¹ + τ⁻¹) + 16 * B0 * K * (θ⁻¹ + τ⁻¹)
        + 2 * C2 * B0 * (θ⁻¹ + τ⁻¹) := by ring
  linarith [hA, hB, hC, hkey.ge]

/-! ## The main theorem -/

theorem lzeroGrowthBound (u : ℝ → ℝ)
    (hu : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2)))
    (hint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2 * |Work.FTS.EllipticEst.Lzero1 u θ|)
      Work.Spaces.Iθ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |u θ| ≤ C * (θ⁻¹ + (Real.pi / 2 - θ)⁻¹) := by
  have hu2 : ContDiffOn ℝ 2 u (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hu 2
  obtain ⟨B0, hB0pos, hB0⟩ := Lzb.LzeroSingCosBoundClean
  obtain ⟨hwr1, hwr2⟩ := Lzb.WronDerivs hu2
  have hder1 := hasDerivAt_cCoef1 (u := u) hwr1
  have hder2 := hasDerivAt_cCoef2 (u := u) hwr2
  have hψint : IntegrableOn (fun s => psiW s * |Work.FTS.EllipticEst.Lzero1 u s|)
      Work.Spaces.Iθ := by
    simpa only [psiW] using hint
  let K : ℝ := ∫ s in Work.Spaces.Iθ, psiW s * |Work.FTS.EllipticEst.Lzero1 u s|
  have hKnn : 0 ≤ K := by
    refine MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun s hs => ?_)
    exact mul_nonneg (psiW_nonneg hs) (abs_nonneg _)
  have hB0nn : 0 ≤ B0 := le_of_lt hB0pos
  refine ⟨4 * |cCoef1 u (Real.pi / 4)| + 16 * B0 * K
      + 2 * (|cCoef2 u (Real.pi / 4)| + 2 * K) * B0, by positivity, ?_⟩
  intro θ hθ
  have hθ0 : (0:ℝ) < θ := hθ.1
  have hθπ : θ < Real.pi / 2 := hθ.2
  have hτ : 0 < Real.pi / 2 - θ := by linarith
  have hinv : 1 ≤ θ⁻¹ + (Real.pi / 2 - θ)⁻¹ := one_le_inv_add hθ
  have hC2nn : 0 ≤ |cCoef2 u (Real.pi / 4)| + 2 * K := by positivity
  have hcramer := cramer_id u hθ
  have hy2 : |Work.FTS.EllipticEst.LzeroSing θ|
      ≤ B0 * ((Real.pi / 2) * (Real.pi / 2 - θ)⁻¹) := by
    have hcos : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ0, Real.pi_pos], hθπ⟩
    have hb : |Work.FTS.EllipticEst.LzeroSing θ| * Real.cos θ ≤ B0 := by
      have h := hB0 θ hθ
      rwa [abs_mul, abs_of_pos hcos] at h
    calc |Work.FTS.EllipticEst.LzeroSing θ| ≤ B0 / Real.cos θ := (le_div_iff₀ hcos).mpr hb
      _ = B0 * (Real.cos θ)⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ B0 * ((Real.pi / 2) * (Real.pi / 2 - θ)⁻¹) :=
          mul_le_mul_of_nonneg_left (inv_cos_le hθ) hB0nn
  have hc2 : |cCoef2 u θ| ≤ |cCoef2 u (Real.pi / 4)| + 2 * K := by
    have h := abs_cCoef2_sub_le hu2 hder2 hψint hθ
    calc |cCoef2 u θ| = |cCoef2 u (Real.pi / 4) + (cCoef2 u θ - cCoef2 u (Real.pi / 4))| := by
          ring_nf
      _ ≤ |cCoef2 u (Real.pi / 4)| + |cCoef2 u θ - cCoef2 u (Real.pi / 4)| := abs_add_le _ _
      _ ≤ |cCoef2 u (Real.pi / 4)| + 2 * K := by linarith
  rcases le_total θ (Real.pi / 4) with hle | hge
  · -- Case `θ ≤ π/4`
    have hy1 : |Real.sin (2 * θ)| ≤ 2 * θ := by
      rw [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith)
        (by linarith [Real.pi_pos]))]
      exact sin_two_mul_le_two_mul (by linarith)
    have hc1 : |cCoef1 u θ| ≤ |cCoef1 u (Real.pi / 4)| + B0 * ((Real.pi / θ) * K) := by
      have h := abs_cCoef1_sub_le_left hu2 hder1 hψint hB0nn hB0 hθ0 hle
      calc |cCoef1 u θ| = |cCoef1 u (Real.pi / 4) + (cCoef1 u θ - cCoef1 u (Real.pi / 4))| := by
            ring_nf
        _ ≤ |cCoef1 u (Real.pi / 4)| + |cCoef1 u θ - cCoef1 u (Real.pi / 4)| := abs_add_le _ _
        _ ≤ |cCoef1 u (Real.pi / 4)| + B0 * ((Real.pi / θ) * K) := by linarith
    have hsum : |u θ| ≤ (|cCoef1 u (Real.pi / 4)| + B0 * ((Real.pi / θ) * K)) * (2 * θ)
        + (|cCoef2 u (Real.pi / 4)| + 2 * K)
          * (B0 * ((Real.pi / 2) * (Real.pi / 2 - θ)⁻¹)) := by
      calc |u θ| = |cCoef1 u θ * Real.sin (2 * θ)
            + cCoef2 u θ * Work.FTS.EllipticEst.LzeroSing θ| := by rw [hcramer]
        _ ≤ |cCoef1 u θ * Real.sin (2 * θ)|
              + |cCoef2 u θ * Work.FTS.EllipticEst.LzeroSing θ| := abs_add_le _ _
        _ = |cCoef1 u θ| * |Real.sin (2 * θ)|
              + |cCoef2 u θ| * |Work.FTS.EllipticEst.LzeroSing θ| := by rw [abs_mul, abs_mul]
        _ ≤ (|cCoef1 u (Real.pi / 4)| + B0 * ((Real.pi / θ) * K)) * (2 * θ)
              + (|cCoef2 u (Real.pi / 4)| + 2 * K)
                * (B0 * ((Real.pi / 2) * (Real.pi / 2 - θ)⁻¹)) := by
            have h1 : |cCoef1 u θ| * |Real.sin (2 * θ)|
                ≤ (|cCoef1 u (Real.pi / 4)| + B0 * ((Real.pi / θ) * K)) * (2 * θ) :=
              mul_le_mul hc1 hy1 (abs_nonneg _) (by positivity)
            have h2 : |cCoef2 u θ| * |Work.FTS.EllipticEst.LzeroSing θ|
                ≤ (|cCoef2 u (Real.pi / 4)| + 2 * K)
                  * (B0 * ((Real.pi / 2) * (Real.pi / 2 - θ)⁻¹)) :=
              mul_le_mul hc2 hy2 (abs_nonneg _) (by positivity)
            linarith
    have hEq : (|cCoef1 u (Real.pi / 4)| + B0 * ((Real.pi / θ) * K)) * (2 * θ)
        + (|cCoef2 u (Real.pi / 4)| + 2 * K)
          * (B0 * ((Real.pi / 2) * (Real.pi / 2 - θ)⁻¹))
        = 2 * |cCoef1 u (Real.pi / 4)| * θ + 2 * B0 * Real.pi * K
          + (|cCoef2 u (Real.pi / 4)| + 2 * K) * (B0 * (Real.pi / 2))
            * (Real.pi / 2 - θ)⁻¹ := by
      field_simp
    have harith := arith_left (C1 := |cCoef1 u (Real.pi / 4)|)
      (C2 := |cCoef2 u (Real.pi / 4)| + 2 * K) (B0 := B0) (K := K) (θ := θ)
      (τ := Real.pi / 2 - θ) (abs_nonneg _) hC2nn hB0nn hKnn hθ0 hτ
      (by linarith [hle, Real.pi_lt_four]) hinv
    calc |u θ| ≤ (|cCoef1 u (Real.pi / 4)| + B0 * ((Real.pi / θ) * K)) * (2 * θ)
          + (|cCoef2 u (Real.pi / 4)| + 2 * K)
            * (B0 * ((Real.pi / 2) * (Real.pi / 2 - θ)⁻¹)) := hsum
      _ = 2 * |cCoef1 u (Real.pi / 4)| * θ + 2 * B0 * Real.pi * K
          + (|cCoef2 u (Real.pi / 4)| + 2 * K) * (B0 * (Real.pi / 2))
            * (Real.pi / 2 - θ)⁻¹ := hEq
      _ ≤ (4 * |cCoef1 u (Real.pi / 4)| + 16 * B0 * K
            + 2 * (|cCoef2 u (Real.pi / 4)| + 2 * K) * B0)
          * (θ⁻¹ + (Real.pi / 2 - θ)⁻¹) := harith
  · -- Case `θ ≥ π/4`
    have hy1 : |Real.sin (2 * θ)| ≤ 2 * (Real.pi / 2 - θ) := by
      rw [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith)
        (by linarith [Real.pi_pos]))]
      exact sin_two_mul_le_two_sub hge (le_of_lt hθπ)
    have hc1 : |cCoef1 u θ|
        ≤ |cCoef1 u (Real.pi / 4)|
          + B0 * ((Real.pi ^ 2 / (2 * Real.sqrt 2 * (Real.pi / 2 - θ) ^ 2)) * K) := by
      have h := abs_cCoef1_sub_le_right hu2 hder1 hψint hB0nn hB0 hge hθπ
      calc |cCoef1 u θ| = |cCoef1 u (Real.pi / 4) + (cCoef1 u θ - cCoef1 u (Real.pi / 4))| := by
            ring_nf
        _ ≤ |cCoef1 u (Real.pi / 4)| + |cCoef1 u θ - cCoef1 u (Real.pi / 4)| := abs_add_le _ _
        _ ≤ |cCoef1 u (Real.pi / 4)|
              + B0 * ((Real.pi ^ 2 / (2 * Real.sqrt 2 * (Real.pi / 2 - θ) ^ 2)) * K) := by
            linarith
    have hsum : |u θ|
        ≤ (|cCoef1 u (Real.pi / 4)|
              + B0 * ((Real.pi ^ 2 / (2 * Real.sqrt 2 * (Real.pi / 2 - θ) ^ 2)) * K))
            * (2 * (Real.pi / 2 - θ))
          + (|cCoef2 u (Real.pi / 4)| + 2 * K)
            * (B0 * ((Real.pi / 2) * (Real.pi / 2 - θ)⁻¹)) := by
      calc |u θ| = |cCoef1 u θ * Real.sin (2 * θ)
            + cCoef2 u θ * Work.FTS.EllipticEst.LzeroSing θ| := by rw [hcramer]
        _ ≤ |cCoef1 u θ * Real.sin (2 * θ)|
              + |cCoef2 u θ * Work.FTS.EllipticEst.LzeroSing θ| := abs_add_le _ _
        _ = |cCoef1 u θ| * |Real.sin (2 * θ)|
              + |cCoef2 u θ| * |Work.FTS.EllipticEst.LzeroSing θ| := by rw [abs_mul, abs_mul]
        _ ≤ (|cCoef1 u (Real.pi / 4)|
              + B0 * ((Real.pi ^ 2 / (2 * Real.sqrt 2 * (Real.pi / 2 - θ) ^ 2)) * K))
            * (2 * (Real.pi / 2 - θ))
              + (|cCoef2 u (Real.pi / 4)| + 2 * K)
                * (B0 * ((Real.pi / 2) * (Real.pi / 2 - θ)⁻¹)) := by
            have h1 : |cCoef1 u θ| * |Real.sin (2 * θ)|
                ≤ (|cCoef1 u (Real.pi / 4)|
                    + B0 * ((Real.pi ^ 2 / (2 * Real.sqrt 2 * (Real.pi / 2 - θ) ^ 2)) * K))
                  * (2 * (Real.pi / 2 - θ)) :=
              mul_le_mul hc1 hy1 (abs_nonneg _) (by positivity)
            have h2 : |cCoef2 u θ| * |Work.FTS.EllipticEst.LzeroSing θ|
                ≤ (|cCoef2 u (Real.pi / 4)| + 2 * K)
                  * (B0 * ((Real.pi / 2) * (Real.pi / 2 - θ)⁻¹)) :=
              mul_le_mul hc2 hy2 (abs_nonneg _) (by positivity)
            linarith
    have hEq : (|cCoef1 u (Real.pi / 4)|
          + B0 * ((Real.pi ^ 2 / (2 * Real.sqrt 2 * (Real.pi / 2 - θ) ^ 2)) * K))
        * (2 * (Real.pi / 2 - θ))
        + (|cCoef2 u (Real.pi / 4)| + 2 * K)
          * (B0 * ((Real.pi / 2) * (Real.pi / 2 - θ)⁻¹))
        = 2 * |cCoef1 u (Real.pi / 4)| * (Real.pi / 2 - θ)
          + B0 * (Real.pi ^ 2 / Real.sqrt 2) * K * (Real.pi / 2 - θ)⁻¹
          + (|cCoef2 u (Real.pi / 4)| + 2 * K) * (B0 * (Real.pi / 2))
            * (Real.pi / 2 - θ)⁻¹ := by
      have hc2t : (Real.pi ^ 2 / (2 * Real.sqrt 2 * (Real.pi / 2 - θ) ^ 2))
          * (2 * (Real.pi / 2 - θ)) = (Real.pi ^ 2 / Real.sqrt 2) * (Real.pi / 2 - θ)⁻¹ := by
        have hs2 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
        have hτne : Real.pi / 2 - θ ≠ 0 := ne_of_gt hτ
        field_simp
      have hsplit : (|cCoef1 u (Real.pi / 4)|
            + B0 * ((Real.pi ^ 2 / (2 * Real.sqrt 2 * (Real.pi / 2 - θ) ^ 2)) * K))
          * (2 * (Real.pi / 2 - θ))
          = |cCoef1 u (Real.pi / 4)| * (2 * (Real.pi / 2 - θ))
            + B0 * K * ((Real.pi ^ 2 / Real.sqrt 2) * (Real.pi / 2 - θ)⁻¹) := by
        rw [show (|cCoef1 u (Real.pi / 4)|
              + B0 * ((Real.pi ^ 2 / (2 * Real.sqrt 2 * (Real.pi / 2 - θ) ^ 2)) * K))
            * (2 * (Real.pi / 2 - θ))
            = |cCoef1 u (Real.pi / 4)| * (2 * (Real.pi / 2 - θ))
              + B0 * K * ((Real.pi ^ 2 / (2 * Real.sqrt 2 * (Real.pi / 2 - θ) ^ 2))
                  * (2 * (Real.pi / 2 - θ))) by ring,
          hc2t]
      rw [hsplit]
      ring
    have harith := arith_right (C1 := |cCoef1 u (Real.pi / 4)|)
      (C2 := |cCoef2 u (Real.pi / 4)| + 2 * K) (B0 := B0) (K := K) (θ := θ)
      (τ := Real.pi / 2 - θ) (abs_nonneg _) hC2nn hB0nn hKnn hθ0 hτ
      (by linarith [hge, Real.pi_lt_four]) hinv
    calc |u θ|
        ≤ (|cCoef1 u (Real.pi / 4)|
              + B0 * ((Real.pi ^ 2 / (2 * Real.sqrt 2 * (Real.pi / 2 - θ) ^ 2)) * K))
            * (2 * (Real.pi / 2 - θ))
          + (|cCoef2 u (Real.pi / 4)| + 2 * K)
            * (B0 * ((Real.pi / 2) * (Real.pi / 2 - θ)⁻¹)) := hsum
      _ = 2 * |cCoef1 u (Real.pi / 4)| * (Real.pi / 2 - θ)
          + B0 * (Real.pi ^ 2 / Real.sqrt 2) * K * (Real.pi / 2 - θ)⁻¹
          + (|cCoef2 u (Real.pi / 4)| + 2 * K) * (B0 * (Real.pi / 2))
            * (Real.pi / 2 - θ)⁻¹ := hEq
      _ ≤ (4 * |cCoef1 u (Real.pi / 4)| + 16 * B0 * K
            + 2 * (|cCoef2 u (Real.pi / 4)| + 2 * K) * B0)
          * (θ⁻¹ + (Real.pi / 2 - θ)⁻¹) := harith

end Work.FTS.EllipticEst.H2W
