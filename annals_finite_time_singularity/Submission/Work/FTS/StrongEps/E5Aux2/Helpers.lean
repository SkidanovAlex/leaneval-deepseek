/-
# `Submission/Work/FTS/StrongEps/E5Aux2/Helpers.lean`

Self-contained helpers for `Work.FTS.StrongEps.E5Aux2.N0_N_Transport_dens_le`.

The target lemma bounds the three `L₁₂`-densities of the profiles
`N₀ α (F_* + f) f`, `N α (F_* + f) Φ` and `Transport f` (with `f` the projected slice of the
scheme) by `C(1+C₀)(1+B)(Maj s/s + 1/(1+s)²)`.  The proof reduces to a pointwise bound of the
form `K θ * |profile s θ| ≤ A * cos θ` on `Iθ` (then `Work.FTS.StrongEps.E5Aux2.AbsL12densLe`
integrates), where `K θ = 3 sin θ cos²θ`.

This module contains the pieces of that reduction which are independent of the interface data:

* `abs_deriv_add_sub_le` — the *unconditional* additivity defect of `deriv`: for `v`
  differentiable at `x`, `|deriv (u+v) x - deriv u x| ≤ |deriv v x|`.  This is what lets the
  `Rop`/`Uop`/`Vop`-values of `PhiTil α (F_*+f) Φ` be compared with those of
  `PhiTil α f Φ` (the only profile the interface `EpsDecay` bounds) *without* assuming anything
  about the differentiability of `PhiTil α f Φ`;
* the difference profile `dProf z θ = -sin(2θ)/(2(1+z))` — the difference of the two `Theta`
  parts (proved in `Work.FTS.StrongEps.E5Aux2.ThetaDiff`) — together with its two partial
  derivatives and the differentiability of its slices;
* the two elementary two-factor scalar inequalities which turn the pairs
  `(Maj s + c/(1+s)) * (c' s/(1+s)² + Maj s)` and `(Maj s + c/(1+s)) * (c' s/(1+s)²)` into
  multiples of `Maj s + s/(1+s)²`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.Spaces.Defs
import Submission.Work.FM.Defs
import Submission.Work.Construction.Defs
import Submission.Work.Construction.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5Aux2

set_option autoImplicit false

/-! ## Splitting `|·|` of a product -/

/-- `|a * b * c * d| ≤ |a| * |b| * |c| * |d|`. -/
lemma abs_mul4_le (a b c d : ℝ) : |a * b * c * d| ≤ |a| * |b| * |c| * |d| :=
  le_of_eq (by rw [abs_mul, abs_mul, abs_mul])

/-- `|a * b * c| ≤ |a| * |b| * |c|`. -/
lemma abs_mul3_le (a b c : ℝ) : |a * b * c| ≤ |a| * |b| * |c| :=
  le_of_eq (by rw [abs_mul, abs_mul])

/-- `|a + b + c + d + e + f| ≤ |a| + |b| + |c| + |d| + |e| + |f|`. -/
lemma abs_six_le (a b c d e f : ℝ) :
    |a + b + c + d + e + f| ≤ |a| + |b| + |c| + |d| + |e| + |f| := by
  have h1 : |a + b + c + d + e + f| ≤ |a + b + c + d + e| + |f| := abs_add_le _ _
  have h2 : |a + b + c + d + e| ≤ |a + b + c + d| + |e| := abs_add_le _ _
  have h3 : |a + b + c + d| ≤ |a + b + c| + |d| := abs_add_le _ _
  have h4 : |a + b + c| ≤ |a + b| + |c| := abs_add_le _ _
  have h5 : |a + b| ≤ |a| + |b| := abs_add_le _ _
  linarith

/-- `|a + b + c + d + e| ≤ |a| + |b| + |c| + |d| + |e|`. -/
lemma abs_five_le (a b c d e : ℝ) :
    |a + b + c + d + e| ≤ |a| + |b| + |c| + |d| + |e| := by
  have h1 : |a + b + c + d + e| ≤ |a + b + c + d| + |e| := abs_add_le _ _
  have h2 : |a + b + c + d| ≤ |a + b + c| + |d| := abs_add_le _ _
  have h3 : |a + b + c| ≤ |a + b| + |c| := abs_add_le _ _
  have h4 : |a + b| ≤ |a| + |b| := abs_add_le _ _
  linarith

/-! ## The additivity defect of `deriv` -/

/-- **The additivity defect of `deriv` is bounded by `|deriv v|`.**  For functions
`u v : ℝ → ℝ` with `v` differentiable at `x`,
`|deriv (u+v) x - deriv u x| ≤ |deriv v x|`.

Both cases are uniform: if `u` is differentiable at `x` this is `deriv_add` (and the left side
is `deriv v x`); if not, neither `u` nor `u + v` is differentiable at `x` (`v` is), so both
`deriv`s are `0` and the left side vanishes. -/
lemma abs_deriv_add_sub_le (u v : ℝ → ℝ) {x : ℝ} (hv : DifferentiableAt ℝ v x) :
    |deriv (fun t => u t + v t) x - deriv u x| ≤ |deriv v x| := by
  by_cases hu : DifferentiableAt ℝ u x
  · have hfun : (fun t => u t + v t) = u + v := rfl
    rw [hfun, deriv_add hu hv, add_sub_cancel_left]
  · have hsum : ¬ DifferentiableAt ℝ (fun t => u t + v t) x := by
      intro h
      apply hu
      have h2 : DifferentiableAt ℝ (fun t => (u t + v t) + (-v t)) x := h.add hv.neg
      refine h2.congr_of_eventuallyEq ?_
      filter_upwards with t
      ring
    rw [deriv_zero_of_not_differentiableAt hsum, deriv_zero_of_not_differentiableAt hu,
      sub_zero, abs_zero]
    exact abs_nonneg _

/-! ## The difference profile `-sin(2θ)/(2(1+z))` -/

/-- The difference of the `Theta`-parts of `f` and `F_* + f`,
`dProf z θ = -sin(2θ)/(2(1+z))` (`Work.FTS.StrongEps.E5Aux2.ThetaDiff`). -/
def dProf (z θ : ℝ) : ℝ := -Real.sin (2 * θ) / (2 * (1 + z))

@[simp] lemma dProf_apply (z θ : ℝ) : dProf z θ = -Real.sin (2 * θ) / (2 * (1 + z)) := rfl

/-- `∂_z` of the difference profile: `sin(2θ)/(2(1+z)²)`. -/
lemma dProf_pz (z θ : ℝ) (hz : 0 < z) :
    Work.Spaces.pz dProf z θ = Real.sin (2 * θ) / (2 * (1 + z) ^ 2) := by
  have hz0 : (1 : ℝ) + z ≠ 0 := by positivity
  have hd : DifferentiableAt ℝ (fun z' : ℝ => 1 + z') z := by fun_prop
  have hder : deriv (fun z' : ℝ => (-(Real.sin (2 * θ) / 2)) / (1 + z')) z
      = -(Real.sin (2 * θ) / 2) * (-1) / (1 + z) ^ 2 := by
    rw [deriv_const_div (𝕜 := ℝ) (c := (-(Real.sin (2 * θ) / 2)))
      (d := fun z' : ℝ => 1 + z') hd hz0]
    simp
  have hfun : (fun z' : ℝ => -Real.sin (2 * θ) / (2 * (1 + z')))
      = fun z' : ℝ => (-(Real.sin (2 * θ) / 2)) / (1 + z') := by
    funext z'
    field_simp
    try ring
  simp only [dProf, Work.Spaces.pz]
  rw [hfun, hder]
  field_simp
  try ring

/-- `∂_θ` of the difference profile: `-cos(2θ)/(1+z)`. -/
lemma dProf_pth (z θ : ℝ) (hz : 0 < z) :
    Work.Spaces.pth dProf z θ = -Real.cos (2 * θ) / (1 + z) := by
  have hfun : (fun θ' : ℝ => -Real.sin (2 * θ') / (2 * (1 + z)))
      = fun θ' : ℝ => (-(1 / (2 * (1 + z)))) * Real.sin (2 * θ') := by
    funext θ'
    field_simp
    try ring
  simp only [dProf, Work.Spaces.pth]
  rw [hfun, deriv_const_mul_field, Work.Construction.deriv_sin_two]
  field_simp
  try ring

/-- The `z`-slice of the difference profile is differentiable. -/
lemma dProf_diff_z (z θ : ℝ) (hz : 0 < z) :
    DifferentiableAt ℝ (fun z' : ℝ => dProf z' θ) z := by
  have hz0 : (1 : ℝ) + z ≠ 0 := by positivity
  have hfun : (fun z' : ℝ => dProf z' θ)
      = fun z' : ℝ => (-(Real.sin (2 * θ) / 2)) / (1 + z') := by
    funext z'
    simp only [dProf_apply]
    field_simp
    try ring
  rw [hfun]
  have hd : DifferentiableAt ℝ (fun z' : ℝ => 1 + z') z := by fun_prop
  exact hd.inv hz0 |>.const_mul _

/-- The `θ`-slice of the difference profile is differentiable. -/
lemma dProf_diff_th (z θ : ℝ) :
    DifferentiableAt ℝ (fun θ' : ℝ => dProf z θ') θ := by
  have hfun : (fun θ' : ℝ => dProf z θ')
      = fun θ' : ℝ => (-(1 / (2 * (1 + z)))) * Real.sin (2 * θ') := by
    funext θ'
    simp only [dProf_apply]
    field_simp
    try ring
  rw [hfun]
  exact (Real.differentiableAt_sin.comp θ
    (differentiableAt_id.const_mul 2)).const_mul _

/-! ## Two elementary two-factor bounds -/

/-- `(Maj s + c/(1+s)) * (c' s/(1+s)² + Maj s) ≤ (c + c' + c c' + 1) * (Maj s + s/(1+s)²)`
for `0 ≤ Maj s ≤ 1`, `s > 0` and `c, c' ≥ 0`. -/
lemma typeAB_le {M s c₁ c₂ : ℝ} (hM0 : 0 ≤ M) (hM1 : M ≤ 1) (hs : 0 < s)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) :
    (M + c₁ / (1 + s)) * (c₂ * (s / (1 + s) ^ 2) + M)
      ≤ (c₁ + c₂ + c₁ * c₂ + 1) * (M + s / (1 + s) ^ 2) := by
  have h1s : (0 : ℝ) < 1 + s := by linarith
  have hs2nn : 0 ≤ s / (1 + s) ^ 2 := div_nonneg hs.le (sq_nonneg _)
  have hQ0 : 0 ≤ M + s / (1 + s) ^ 2 := add_nonneg hM0 hs2nn
  have hQge : M ≤ M + s / (1 + s) ^ 2 := le_add_of_nonneg_right hs2nn
  have hQge2 : s / (1 + s) ^ 2 ≤ M + s / (1 + s) ^ 2 := le_add_of_nonneg_left hM0
  have hsm1 : s / (1 + s) ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  have hs3 : s / (1 + s) ^ 3 ≤ s / (1 + s) ^ 2 := by
    have hle : (1 + s) ^ 2 ≤ (1 + s) ^ 3 := by nlinarith [sq_nonneg (1 + s)]
    exact div_le_div_of_nonneg_left hs.le (by positivity) hle
  have hMs : M * (s / (1 + s) ^ 2) ≤ M := by
    simpa using mul_le_mul_of_nonneg_left hsm1 hM0
  have hmul : M * M ≤ M := by nlinarith
  have hexp : (M + c₁ / (1 + s)) * (c₂ * (s / (1 + s) ^ 2) + M)
      = M * M + c₂ * (M * (s / (1 + s) ^ 2)) + c₁ * (M / (1 + s))
        + c₁ * c₂ * (s / (1 + s) ^ 3) := by
    field_simp
    try ring
  rw [hexp]
  have k1 : c₁ * (M / (1 + s)) ≤ c₁ * M := by
    have h : M / (1 + s) ≤ M := by
      rw [div_le_iff₀ h1s]; nlinarith
    exact mul_le_mul_of_nonneg_left h hc₁
  have k2 : c₁ * c₂ * (s / (1 + s) ^ 3) ≤ c₁ * c₂ * (s / (1 + s) ^ 2) :=
    mul_le_mul_of_nonneg_left hs3 (mul_nonneg hc₁ hc₂)
  have k3 : c₂ * (M * (s / (1 + s) ^ 2)) ≤ c₂ * M :=
    mul_le_mul_of_nonneg_left hMs hc₂
  have hD : M * M ≤ M + s / (1 + s) ^ 2 := le_trans hmul hQge
  have hA : c₂ * M ≤ c₂ * (M + s / (1 + s) ^ 2) := mul_le_mul_of_nonneg_left hQge hc₂
  have hB : c₁ * M ≤ c₁ * (M + s / (1 + s) ^ 2) := mul_le_mul_of_nonneg_left hQge hc₁
  have hC : c₁ * c₂ * (s / (1 + s) ^ 2) ≤ c₁ * c₂ * (M + s / (1 + s) ^ 2) :=
    mul_le_mul_of_nonneg_left hQge2 (mul_nonneg hc₁ hc₂)
  nlinarith [k1, k2, k3, hD, hA, hB, hC]

/-- `(Maj s + c/(1+s)) * (c' s/(1+s)²) ≤ (c' + c c') * (Maj s + s/(1+s)²)`. -/
lemma typeAC_le {M s c₁ c₂ : ℝ} (hM0 : 0 ≤ M) (hM1 : M ≤ 1) (hs : 0 < s)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) :
    (M + c₁ / (1 + s)) * (c₂ * (s / (1 + s) ^ 2))
      ≤ (c₂ + c₁ * c₂) * (M + s / (1 + s) ^ 2) := by
  have hs2nn : 0 ≤ s / (1 + s) ^ 2 := div_nonneg hs.le (sq_nonneg _)
  have hQge : M ≤ M + s / (1 + s) ^ 2 := le_add_of_nonneg_right hs2nn
  have hQge2 : s / (1 + s) ^ 2 ≤ M + s / (1 + s) ^ 2 := le_add_of_nonneg_left hM0
  have hsm1 : s / (1 + s) ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  have hs3 : s / (1 + s) ^ 3 ≤ s / (1 + s) ^ 2 := by
    have hle : (1 + s) ^ 2 ≤ (1 + s) ^ 3 := by nlinarith [sq_nonneg (1 + s)]
    exact div_le_div_of_nonneg_left hs.le (by positivity) hle
  have hMs : M * (s / (1 + s) ^ 2) ≤ M := by
    simpa using mul_le_mul_of_nonneg_left hsm1 hM0
  have hexp : (M + c₁ / (1 + s)) * (c₂ * (s / (1 + s) ^ 2))
      = c₂ * (M * (s / (1 + s) ^ 2)) + c₁ * c₂ * (s / (1 + s) ^ 3) := by
    field_simp
    try ring
  rw [hexp]
  have h1 : c₂ * (M * (s / (1 + s) ^ 2)) ≤ c₂ * M :=
    mul_le_mul_of_nonneg_left hMs hc₂
  have h2 : c₁ * c₂ * (s / (1 + s) ^ 3) ≤ c₁ * c₂ * (s / (1 + s) ^ 2) :=
    mul_le_mul_of_nonneg_left hs3 (mul_nonneg hc₁ hc₂)
  have hA : c₂ * M ≤ c₂ * (M + s / (1 + s) ^ 2) := mul_le_mul_of_nonneg_left hQge hc₂
  have hB : c₁ * c₂ * (s / (1 + s) ^ 2) ≤ c₁ * c₂ * (M + s / (1 + s) ^ 2) :=
    mul_le_mul_of_nonneg_left hQge2 (mul_nonneg hc₁ hc₂)
  nlinarith [h1, h2, hA, hB]

end Work.FTS.StrongEps.E5Aux2
