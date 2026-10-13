/-
  WilE10 — foundations: the compactification `psi` and its inverse, and the restricted
  exponential `rexp`.

  Self-contained apart from the frozen vocabulary (`Submission.Work.Wilkies.E.Spec`).
-/
import Submission.Work.Wilkies.E.Spec
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilE10

open WilkiesDesign WilkiesDesign.E

/-! ## The compactification `psi` -/

theorem psi_abs_lt_one (x : ℝ) : |psi x| < 1 := by
  have h1 : 0 < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have h2 : |x| < Real.sqrt (1 + x ^ 2) := by
    rw [Real.lt_sqrt (abs_nonneg x)]
    nlinarith [sq_abs x]
  rw [psi, abs_div, abs_of_pos h1, div_lt_one h1]
  exact h2

theorem psi_abs_le_one (x : ℝ) : |psi x| ≤ 1 := le_of_lt (psi_abs_lt_one x)

/-- The inverse compactification `(-1,1) → ℝ`. -/
def psiR (u : ℝ) : ℝ := u / Real.sqrt (1 - u ^ 2)

theorem psi_sq (x : ℝ) : psi x ^ 2 = x ^ 2 / (1 + x ^ 2) := by
  rw [psi, div_pow, Real.sq_sqrt (by positivity)]

theorem one_sub_psi_sq (x : ℝ) : 1 - psi x ^ 2 = 1 / (1 + x ^ 2) := by
  rw [psi, div_pow, Real.sq_sqrt (by positivity)]
  field_simp
  ring

theorem sqrt_one_sub_psi_sq (x : ℝ) :
    Real.sqrt (1 - psi x ^ 2) = 1 / Real.sqrt (1 + x ^ 2) := by
  rw [one_sub_psi_sq x, Real.sqrt_div (by norm_num) (1 + x ^ 2), Real.sqrt_one, one_div]

theorem psiR_psi (x : ℝ) : psiR (psi x) = x := by
  rw [psiR, sqrt_one_sub_psi_sq x, psi]
  field_simp

theorem one_add_psiR_sq {u : ℝ} (hu : |u| < 1) : 1 + psiR u ^ 2 = 1 / (1 - u ^ 2) := by
  have h1 : 0 < 1 - u ^ 2 := by nlinarith [abs_nonneg u, sq_abs u, hu]
  rw [psiR, div_pow, Real.sq_sqrt (le_of_lt h1)]
  field_simp
  ring

theorem psi_psiR {u : ℝ} (hu : |u| < 1) : psi (psiR u) = u := by
  have h1 : 0 < 1 - u ^ 2 := by nlinarith [abs_nonneg u, sq_abs u, hu]
  have h2 : Real.sqrt (1 + psiR u ^ 2) = 1 / Real.sqrt (1 - u ^ 2) := by
    rw [one_add_psiR_sq hu, Real.sqrt_div (by norm_num) (1 - u ^ 2), Real.sqrt_one, one_div]
  rw [psi, h2, psiR]
  field_simp

theorem psi_injective : Function.Injective psi := by
  intro x y hxy
  rw [← psiR_psi x, ← psiR_psi y, hxy]

/-- The graph of `psi` is the graph of an *algebraic* function: `u = psi t` is characterised
by `u²(1+t²) = t²` together with the sign condition `ut ≥ 0`. -/
theorem psi_eq_of_sq {u t : ℝ} (h : u ^ 2 * (1 + t ^ 2) = t ^ 2) (hsgn : 0 ≤ u * t) :
    u = psi t := by
  have hsq : u ^ 2 = (psi t) ^ 2 := by
    have hpt2 : psi t ^ 2 = t ^ 2 / (1 + t ^ 2) := by
      rw [psi, div_pow, Real.sq_sqrt (by positivity)]
    rw [hpt2, eq_div_iff (by positivity : (1:ℝ) + t ^ 2 ≠ 0)]
    exact h
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h' | h'
  · exact h'
  · have hle : psi t * t ≤ 0 := by
      have : u * t = -(psi t * t) := by rw [h']; ring
      linarith [hsgn, this]
    have hpt : psi t * t = t ^ 2 / Real.sqrt (1 + t ^ 2) := by
      rw [psi]; field_simp
    have hge : 0 ≤ psi t * t := by rw [hpt]; positivity
    have hzero : psi t * t = 0 := le_antisymm hle hge
    have ht : t = 0 := by
      have h1 : t ^ 2 / Real.sqrt (1 + t ^ 2) = 0 := by rw [← hpt]; exact hzero
      have hpos : 0 < Real.sqrt (1 + t ^ 2) := Real.sqrt_pos.mpr (by positivity)
      have h2 : t ^ 2 = 0 := by
        by_contra hc
        exact absurd h1
          (ne_of_gt (div_pos (lt_of_le_of_ne (sq_nonneg t) (Ne.symm hc)) hpos))
      exact sq_eq_zero_iff.mp h2
    have : psi t = 0 := by rw [ht]; norm_num [psi]
    linarith [h', this]

/-- The `ψ`-image of a large real number: if `u²(1+s²) = 1`, `u s > 0` and `|s| < 1` then
`u = psi (1/s)` and `|1/s| > 1`. -/
theorem psi_recip_eq {u s : ℝ} (h : u ^ 2 * (1 + s ^ 2) = 1) (hs : 0 < u * s)
    (hsl : |s| < 1) :
    u = psi s⁻¹ ∧ 1 < |s⁻¹| := by
  have hs0 : s ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hs; exact lt_irrefl 0 hs
  have ha : 0 < |s| := abs_pos.mpr hs0
  have hsq : u ^ 2 * (1 + (s⁻¹) ^ 2) = (s⁻¹) ^ 2 := by
    rw [inv_pow]
    field_simp
    linear_combination h
  have hsign : 0 ≤ u * s⁻¹ := by
    have : u * s⁻¹ = (u * s) * (s ^ 2)⁻¹ := by field_simp
    rw [this]
    exact mul_nonneg (le_of_lt hs) (by positivity)
  exact ⟨psi_eq_of_sq hsq hsign, by
    rw [abs_inv, inv_eq_one_div]
    exact (one_lt_div ha).mpr hsl⟩

/-! ## The restricted exponential `rexp` -/

theorem rexp_eq_exp {x : ℝ} (h : |x| ≤ 1) : rexp x = Real.exp x := by
  rw [rexp, if_pos h]

theorem rexp_eq_zero {x : ℝ} (h : 1 < |x|) : rexp x = 0 := by
  rw [rexp, if_neg (not_le.mpr h)]

theorem rexp_eq_exp_of_sq {x q : ℝ} (h : x ^ 2 + q ^ 2 = 1) : rexp x = Real.exp x :=
  rexp_eq_exp (by nlinarith [sq_nonneg x, sq_abs x, sq_nonneg q])

theorem rexp_eq_zero_inv {s : ℝ} (hs0 : s ≠ 0) (hsl : |s| < 1) : rexp s⁻¹ = 0 := by
  refine rexp_eq_zero ?_
  rw [abs_inv, inv_eq_one_div]
  exact (one_lt_div (abs_pos.mpr hs0)).mpr hsl

end Work.WilE10
