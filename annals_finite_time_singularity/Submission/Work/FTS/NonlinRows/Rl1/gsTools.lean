/-
# `gsTools` — shared numerical and profile facts of the primed `gs`-rows

The three `gs`-rows `N₁^{gs}, N₂^{gs}, N₃^{gs}` all have the shape

  `|K θ · N_i r θ| ≤ (d_i · r/(1+r)) · M_i r`

with `d_i` an explicit constant times a power of `α`, `M_i r` the `r`-dependent majorant of
the `HQo`-coefficient, and they are all finished by `Work.FTS.NonlinRows.Rl1.Fa_le_of_profile`
with `c_i r = d_i·r/(1+r)`.  This file collects what that closing step needs in general:

* the profile data of `r ↦ r⁻¹·(d·r/(1+r)) = d/(1+r)` (measurability, square-integrability
  and the square-integral bound `≤ 2d²`, inherited from `∫ (1+r)^{-2} ≤ 2`);
* the two square-root identities `√(CA/(γ-1))·α = √(10CA)·α^{1/2}` and
  `√(CA/(γ-1))·α² = √(10CA)·α^{3/2}` (`γ = 1 + α/10`);
* the elementary rate facts `α^{3/2} ≤ α^{1/2}` and `√α·|g|_{ℋ⁴} ≤ Env α g`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.NonlinRows.Rl1.tools
import Submission.Work.FTS.NonlinRows.Rl1.FaStep

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.NonlinRows.Rl1

set_option autoImplicit false

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlin (Xn)

/-- **The profile data of `c r = d·r/(1+r)`.**  On `r > 0` one has
`r⁻¹·c r = d/(1+r)`, so the profile factor of the `L₁₂`-weight is measurable,
square-integrable, and its square-integral is at most `2d²` (using `∫ (1+r)^{-2} ≤ 2`). -/
theorem profile_data {d : ℝ} (hd : 0 ≤ d) :
    AEMeasurable (fun r : ℝ => r⁻¹ * (d * r / (1 + r)))
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) ∧
      MeasureTheory.IntegrableOn (fun r : ℝ => (r⁻¹ * (d * r / (1 + r))) ^ 2)
        (Set.Ioi (0 : ℝ)) ∧
      (∫ r in Set.Ioi (0 : ℝ), (r⁻¹ * (d * r / (1 + r))) ^ 2) ≤ d ^ 2 * 2 ∧
      Real.sqrt (∫ r in Set.Ioi (0 : ℝ), (r⁻¹ * (d * r / (1 + r))) ^ 2)
        ≤ d * Real.sqrt 2 := by
  have hkey : ∀ r : ℝ, 0 < r → r⁻¹ * (d * r / (1 + r)) = d / (1 + r) := by
    intro r hr
    have hr0 : r ≠ 0 := ne_of_gt hr
    have h1r : (1 : ℝ) + r ≠ 0 := ne_of_gt (by linarith)
    field_simp
  have hmeas : AEMeasurable (fun r : ℝ => r⁻¹ * (d * r / (1 + r)))
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    have hbase : AEMeasurable (fun r : ℝ => d * (1 + r)⁻¹)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
      (measurable_const.mul ((measurable_const.add measurable_id).inv)).aemeasurable
    refine hbase.congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    have h := hkey r hr
    rw [h]
    rfl
  have hint : MeasureTheory.IntegrableOn (fun r : ℝ => (r⁻¹ * (d * r / (1 + r))) ^ 2)
      (Set.Ioi (0 : ℝ)) := by
    have hbase : MeasureTheory.IntegrableOn (fun r : ℝ => d ^ 2 * (1 / (1 + r)) ^ 2)
        (Set.Ioi (0 : ℝ)) := (integrableOn_inv_one_add_sq'.1).const_mul _
    refine MeasureTheory.IntegrableOn.congr_fun hbase ?_ measurableSet_Ioi
    intro r hr
    have hr' : (0 : ℝ) < r := hr
    have h1r : (1 : ℝ) + r ≠ 0 := ne_of_gt (by linarith)
    change d ^ 2 * (1 / (1 + r)) ^ 2 = (r⁻¹ * (d * r / (1 + r))) ^ 2
    rw [hkey r hr']
    field_simp
  have hint2 : (∫ r in Set.Ioi (0 : ℝ), (r⁻¹ * (d * r / (1 + r))) ^ 2)
      = d ^ 2 * ∫ r in Set.Ioi (0 : ℝ), (1 / (1 + r)) ^ 2 := by
    have hcong : (∫ r in Set.Ioi (0 : ℝ), (r⁻¹ * (d * r / (1 + r))) ^ 2)
        = ∫ r in Set.Ioi (0 : ℝ), d ^ 2 * (1 / (1 + r)) ^ 2 := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
      intro r hr
      have hr' : (0 : ℝ) < r := hr
      have h1r : (1 : ℝ) + r ≠ 0 := ne_of_gt (by linarith)
      change (r⁻¹ * (d * r / (1 + r))) ^ 2 = d ^ 2 * (1 / (1 + r)) ^ 2
      rw [hkey r hr']
      field_simp
    rw [hcong, MeasureTheory.integral_const_mul]
  have hle : (∫ r in Set.Ioi (0 : ℝ), (r⁻¹ * (d * r / (1 + r))) ^ 2) ≤ d ^ 2 * 2 := by
    rw [hint2]
    exact mul_le_mul_of_nonneg_left integrableOn_inv_one_add_sq'.2 (sq_nonneg _)
  refine ⟨hmeas, hint, hle, ?_⟩
  calc Real.sqrt (∫ r in Set.Ioi (0 : ℝ), (r⁻¹ * (d * r / (1 + r))) ^ 2)
      ≤ Real.sqrt (d ^ 2 * 2) := Real.sqrt_le_sqrt hle
    _ = Real.sqrt (d ^ 2) * Real.sqrt 2 := Real.sqrt_mul (sq_nonneg _) 2
    _ = d * Real.sqrt 2 := by rw [Real.sqrt_sq hd]

/-- `√(CA/(γ-1))·α = √(10CA)·α^{1/2}` (`γ - 1 = α/10`). -/
theorem sqrt_coef_mul_alpha {CA α : ℝ} (hCA : 0 ≤ CA) (hα : 0 < α) :
    Real.sqrt (CA / (Work.Spaces.gam α - 1)) * α = Real.sqrt (10 * CA) * α ^ (1 / 2 : ℝ) := by
  have hγ : Work.Spaces.gam α - 1 = α / 10 := by
    rw [Work.Spaces.gam]; ring
  have hCAα : CA / (Work.Spaces.gam α - 1) = 10 * CA / α := by
    rw [hγ]; field_simp
  have h10α : (0 : ℝ) ≤ 10 * CA / α := div_nonneg (by linarith) hα.le
  rw [hCAα]
  have hα2 : Real.sqrt (α ^ 2) = α := Real.sqrt_sq hα.le
  calc Real.sqrt (10 * CA / α) * α
      = Real.sqrt (10 * CA / α) * Real.sqrt (α ^ 2) := by rw [hα2]
    _ = Real.sqrt (10 * CA / α * α ^ 2) := (Real.sqrt_mul h10α (α ^ 2)).symm
    _ = Real.sqrt (10 * CA * α) := by
        congr 1
        field_simp
    _ = Real.sqrt (10 * CA) * Real.sqrt α := Real.sqrt_mul (by linarith) α
    _ = Real.sqrt (10 * CA) * α ^ (1 / 2 : ℝ) := by rw [Real.sqrt_eq_rpow α]

/-- `√(CA/(γ-1))·α² = √(10CA)·α^{3/2}` (`γ - 1 = α/10`). -/
theorem sqrt_coef_mul_alpha_sq {CA α : ℝ} (hCA : 0 ≤ CA) (hα : 0 < α) :
    Real.sqrt (CA / (Work.Spaces.gam α - 1)) * α ^ 2
      = Real.sqrt (10 * CA) * α ^ (3 / 2 : ℝ) := by
  have h := sqrt_coef_mul_alpha hCA hα
  calc Real.sqrt (CA / (Work.Spaces.gam α - 1)) * α ^ 2
      = (Real.sqrt (CA / (Work.Spaces.gam α - 1)) * α) * α := by ring
    _ = (Real.sqrt (10 * CA) * α ^ (1 / 2 : ℝ)) * α := by rw [h]
    _ = Real.sqrt (10 * CA) * α ^ (3 / 2 : ℝ) := by
        rw [show (3 / 2 : ℝ) = (1 / 2 : ℝ) + 1 by norm_num, Real.rpow_add hα,
          Real.rpow_one]
        ring

/-- `α^{3/2} ≤ α^{1/2}` for `0 < α ≤ 1`. -/
theorem rpow_three_halves_le' {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    α ^ (3 / 2 : ℝ) ≤ α ^ (1 / 2 : ℝ) := by
  rw [show (3 / 2 : ℝ) = (1 / 2 : ℝ) + 1 by norm_num, Real.rpow_add hα, Real.rpow_one]
  have h1 : 0 < α ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hα _
  nlinarith

/-- `(π/2)·√2·120 ≤ 2000`: the numerical factor of the row constants. -/
theorem pi_div_two_mul_sqrt_two_mul : Real.pi / 2 * Real.sqrt 2 * 120 ≤ 2000 := by
  have h2 : Real.sqrt 2 ≤ 2 := by
    have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have h2' := Real.sqrt_nonneg 2
    nlinarith
  have hp : Real.pi / 2 ≤ 2 := by
    have h := Real.pi_lt_four
    have h2' := Real.pi_pos
    linarith
  nlinarith [Real.sqrt_nonneg 2, Real.pi_pos]

/-- `√α·X ≤ Env α g` for `X = |g|_{ℋ⁴}`. -/
theorem sqrt_mul_le_Env {α : ℝ} {g : Fn} (hα : 0 < α) :
    α ^ (1 / 2 : ℝ) * Xn α g ≤ Env α g := by
  have hX0 : 0 ≤ Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hsqrt : α ^ (1 / 2 : ℝ) = Real.sqrt α := (Real.sqrt_eq_rpow α).symm
  rw [hsqrt, Env]
  have h : 0 ≤ α ^ (-(3 / 2 : ℝ)) * (Xn α g) ^ 2 :=
    mul_nonneg (Real.rpow_nonneg hα.le _) (sq_nonneg _)
  have h2 : 0 ≤ α ^ 2 := sq_nonneg α
  linarith

/-- **The row constants fit into `Env`.**  The common conclusion of the three `gs`-rows,
`Fa N ≤ ofReal (2000·√(10CA)·max Ce 0·α^{1/2}·|g|_{ℋ⁴})`, is dominated by
`ofReal (K·Env α g)` with `K = 1 + 2000·(max Ce 0·√(10CA))`, because `√α·|g|_{ℋ⁴} ≤ Env α g`. -/
theorem const_mul_le_K {CA Ce α : ℝ} {g : Fn} (_hCA : 0 ≤ CA) (hα : 0 < α)
    (hEnv : 0 ≤ Env α g) :
    2000 * Real.sqrt (10 * CA) * max Ce 0 * α ^ (1 / 2 : ℝ) * Xn α g
      ≤ (1 + 2000 * (max Ce 0 * Real.sqrt (10 * CA))) * Env α g := by
  have hX0 : 0 ≤ Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hA : 0 ≤ 2000 * (max Ce 0 * Real.sqrt (10 * CA)) :=
    mul_nonneg (by norm_num) (mul_nonneg (le_max_right _ _) (Real.sqrt_nonneg _))
  have h1 : α ^ (1 / 2 : ℝ) * Xn α g ≤ Env α g := sqrt_mul_le_Env hα
  have h2 : 2000 * Real.sqrt (10 * CA) * max Ce 0 * α ^ (1 / 2 : ℝ) * Xn α g
      = (2000 * (max Ce 0 * Real.sqrt (10 * CA))) * (α ^ (1 / 2 : ℝ) * Xn α g) := by ring
  rw [h2]
  have h3 : 2000 * (max Ce 0 * Real.sqrt (10 * CA))
      ≤ 1 + 2000 * (max Ce 0 * Real.sqrt (10 * CA)) := by linarith
  exact le_trans (mul_le_mul_of_nonneg_left h1 hA) (mul_le_mul_of_nonneg_right h3 hEnv)

end Work.FTS.NonlinRows.Rl1
