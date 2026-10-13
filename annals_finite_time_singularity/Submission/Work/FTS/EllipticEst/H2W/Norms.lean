/-
Copyright: work module for the Elgindi finite-time singularity project.

# `H2W.Norms`: the two weighted norms of the level-`0` elliptic estimate

The target of this subproject is the paper's equation `(radialandangularweightL2)`
(Elgindi, Annals **194** (2021), Step 2 of the proof of Proposition `prop:H2`, tex 869--890),

  `α² ‖z²∂_zzΨ · w · sin(2θ)^{-η/2}‖ + ‖∂_θθΨ · w · sin(2θ)^{-η/2}‖ ≤ C ‖F · w · sin(2θ)^{-η/2}‖`,

with `w z = (1+z)²/z²` and `η = 99/100` — i.e. exactly `HkNorm α 0` of the two left hand side
quantities and of the source (the `k = 0` case of `HkIntegrand`, whose mixed-derivative sum is
empty).

This module fixes the *squared* forms of those norms; the target's inequality is recovered from
the squared form by the arithmetic `(a+b)² ≤ 2(a²+b²)` together with the honesty of the
left-hand side, which the hypothesis bundle `EllHyp` provides.

Both norms are **squared** iterated integrals over `[0,∞) × [0,π/2]` with the measure `dz dθ`:

* `nSq g = ∫_z ∫_θ (g z θ · w z)²` — the *radial-weight* (Step 1) norm;
* `NSq g = ∫_z ∫_θ (g z θ · w z / sin(2θ)^{η/2})² = ∫_z ∫_θ (g z θ)² · w z² · sin(2θ)^{-η}`
  — the *radial and angular* (Step 2) norm, which is `HkSq α 0 g` (`NSq_eq_HkSq` below).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Defs

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

/-! ## The angular weight `ρ = sin(2θ)^{-η}` and the full weight `W = w · ρ^{1/2}` -/

/-- `ρ θ = sin(2θ)^{-η}`, the angular weight of the `k = 0` elliptic estimate (`η = 99/100`). -/
def rho (θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))

/-- The full weight `W = w / sin(2θ)^{η/2}`, the weight occurring in `HkIntegrand α 0`. -/
def Wf (z θ : ℝ) : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)

theorem w_nonneg (z : ℝ) : 0 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w]; exact div_nonneg (sq_nonneg _) (sq_nonneg _)

theorem sin_two_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

theorem rho_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ rho θ :=
  Real.rpow_nonneg (sin_two_nonneg hθ) _

/-- The full weight, written as a product: `w / sin(2θ)^{η/2} = w · sin(2θ)^{-η/2}`. -/
theorem Wf_eq_mul {z θ : ℝ} (h : 0 ≤ Real.sin (2 * θ)) :
    Wf z θ = Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2)) := by
  rw [Wf]
  rcases eq_or_lt_of_le h with h0 | h0
  · rw [← h0,
      Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num : Work.Spaces.eta / 2 ≠ 0),
      Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num : -(Work.Spaces.eta / 2) ≠ 0),
      div_zero, mul_zero]
  · rw [Real.rpow_neg h0.le, div_eq_mul_inv]

/-- `(s^{-η/2})² = s^{-η}` for `s > 0`, the algebra behind `Wf_sq_eq`. -/
theorem rpow_half_sq {s : ℝ} (h : 0 < s) :
    (s ^ (-(Work.Spaces.eta / 2))) ^ 2 = s ^ (-(Work.Spaces.eta)) := by
  rw [pow_two, ← Real.rpow_add h,
    show -(Work.Spaces.eta / 2) + -(Work.Spaces.eta / 2) = -(Work.Spaces.eta) by ring]

/-- The square of the full weight is `w² · ρ`, the weight of the iterated integrals below. -/
theorem Wf_sq_eq {z θ : ℝ} (h : 0 ≤ Real.sin (2 * θ)) :
    (Wf z θ) ^ 2 = (Work.Spaces.w z) ^ 2 * rho θ := by
  rw [Wf, rho]
  rcases eq_or_lt_of_le h with h0 | h0
  · rw [← h0,
      Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num : Work.Spaces.eta / 2 ≠ 0),
      Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num : -(Work.Spaces.eta) ≠ 0),
      div_zero, mul_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0)]
  · rw [div_eq_mul_inv, ← Real.rpow_neg h0.le, mul_pow, rpow_half_sq h0]

/-! ## The two squared norms -/

/-- The squared *radial-weight* norm `‖g‖²_w = ∫_z ∫_θ (g · w)²` of the paper's Step 1. -/
def nSq (g : ℝ → ℝ → ℝ) : ℝ := ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
  (g z θ * Work.Spaces.w z) ^ 2

/-- The squared *radial and angular* norm `‖g‖²_W = ∫_z ∫_θ (g · w / sin(2θ)^{η/2})²` of the
paper's Step 2 (the `k = 0` case of `HkSq`). -/
def NSq (g : ℝ → ℝ → ℝ) : ℝ := ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
  (g z θ * Wf z θ) ^ 2

theorem nSq_nonneg (g : ℝ → ℝ → ℝ) : 0 ≤ nSq g := by
  refine integral_nonneg fun z => integral_nonneg fun θ => ?_
  positivity

theorem NSq_nonneg (g : ℝ → ℝ → ℝ) : 0 ≤ NSq g := by
  refine integral_nonneg fun z => integral_nonneg fun θ => ?_
  positivity

theorem nSq_congr {f g : ℝ → ℝ → ℝ} (h : ∀ z θ, f z θ = g z θ) : nSq f = nSq g := by
  refine setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
  refine setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
  rw [h]

theorem NSq_congr {f g : ℝ → ℝ → ℝ} (h : ∀ z θ, f z θ = g z θ) : NSq f = NSq g := by
  refine setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
  refine setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
  rw [h]

/-- `nSq` is the `L2Sq` of `g · w`. -/
theorem nSq_eq_L2Sq (g : ℝ → ℝ → ℝ) : nSq g = Work.Spaces.L2Sq (fun z θ => g z θ * Work.Spaces.w z) :=
  rfl

/-- `NSq` is the `L2Sq` of `g · Wf`. -/
theorem NSq_eq_L2Sq (g : ℝ → ℝ → ℝ) : NSq g = Work.Spaces.L2Sq (fun z θ => g z θ * Wf z θ) :=
  rfl

/-- `Wf ≥ w` on the open quadrant: `w / sin(2θ)^{η/2} ≥ w` because `sin(2θ) ∈ (0,1]` there. -/
theorem w_le_Wf {z θ : ℝ} (h : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.w z ≤ Wf z θ := by
  have hpos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [h.1]) (by linarith [h.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hpow_pos : 0 < (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) :=
    Real.rpow_pos_of_pos hpos _
  have hpow_le : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≤ 1 := by
    calc (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
        ≤ (1 : ℝ) ^ (Work.Spaces.eta / 2) :=
          Real.rpow_le_rpow hpos.le hs1 (by rw [Work.Spaces.eta]; norm_num)
      _ = 1 := by simp
  rw [Wf, le_div_iff₀ hpow_pos]
  calc Work.Spaces.w z * (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
      ≤ Work.Spaces.w z * 1 := mul_le_mul_of_nonneg_left hpow_le (w_nonneg z)
    _ = Work.Spaces.w z := mul_one _

/-- `NSq` is the `k = 0` `HkSq`, i.e. the squared `HkNorm` of the chapter. -/
theorem NSq_eq_HkSq (α : ℝ) (g : ℝ → ℝ → ℝ) : Work.Spaces.HkSq α 0 g = NSq g := by
  rw [Work.Spaces.HkSq, NSq]
  refine setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
  refine setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
  simp only [Work.Spaces.HkIntegrand, Finset.range_one, Finset.sum_singleton]
  norm_num
  rw [Wf]

end Work.FTS.EllipticEst.H2W
