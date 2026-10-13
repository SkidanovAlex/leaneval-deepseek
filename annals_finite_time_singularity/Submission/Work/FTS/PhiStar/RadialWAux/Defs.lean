/-
# `RadialWAux.Defs` — the rescaled pieces of the radial Green's function

`Work.FTS.PhiStar.Radial.radGreen α m c` is the explicit decaying solution of the mode-`m` Euler
equation

  `-α²z² a'' - α(5+α) z a' + λ_m a = c`,   `λ_m = 2m(2m+5)`,

written as

  `radGreen α m c z = K·( z^{-q}·∫₀^z c(t) t^{q-1} dt + z^{p}·∫_{Ioi z} c(t) t^{-p-1} dt )`

with the indicial exponents

  `p = 2m/α`  (growing at `∞`),   `q = (2m+5)/α`  (decaying at `∞`),   `K = 1/(α(4m+5))`.

**The two rescaled pieces.**  Substituting `t = z u` in either integral turns `radGreen` into
`smooth (in z)` integrals over the *fixed* domains `(0,1)` and `(1,∞)`:

  `radGreen α m c z = K·( Φ z + Ψ z )`,   `Φ z = ∫₀¹ c(zu)·u^{q-1} du`,
                                          `Ψ z = ∫_{u>1} c(zu)·u^{-p-1} du`.

In this form *every* `z`-derivative is a differentiation under an integral sign over a fixed
domain — which is exactly what makes the weighted derivative bound `RadialW` provable.

This file only fixes the vocabulary and the elementary side facts (`p ≥ 10`, `q ≥ 35`, `K > 0`);
the analytic estimates live in the sibling modules.
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.PhiStar.StarDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.RadialWAux

set_option autoImplicit false

/-- The growing indicial exponent `p = 2m/α`. -/
def radP (α : ℝ) (m : ℕ) : ℝ := 2 * (m : ℝ) / α

/-- The (positive) decaying indicial exponent `q = (2m+5)/α`, i.e. `s⁻ = -q`. -/
def radQ (α : ℝ) (m : ℕ) : ℝ := (2 * (m : ℝ) + 5) / α

/-- The normalising constant `K = 1/(α(4m+5))` of the Green function. -/
def radK (α : ℝ) (m : ℕ) : ℝ := 1 / (α * (4 * (m : ℝ) + 5))

/-- The "inner" part of the Green function, in rescaled form:
`Φ z = ∫₀¹ c(zu)·u^{q-1} du`. -/
def radPhi (α : ℝ) (m : ℕ) (c : ℝ → ℝ) : ℝ → ℝ :=
  fun z => ∫ u in (0 : ℝ)..1, c (z * u) * u ^ (radQ α m - 1)

/-- The "outer" part of the Green function, in rescaled form:
`Ψ z = ∫_{u>1} c(zu)·u^{-p-1} du`. -/
def radPsi (α : ℝ) (m : ℕ) (c : ℝ → ℝ) : ℝ → ℝ :=
  fun z => ∫ u in Set.Ioi 1, c (z * u) * u ^ (-(radP α m) - 1)

/-- The index of `RadialW` up to which the weighted family is asserted. -/
abbrev radWOrder : ℕ := 22

/-! ### Elementary side facts -/

theorem radP_pos {α : ℝ} (hα : 0 < α) {m : ℕ} (hm : 1 ≤ m) : 0 < radP α m := by
  have h : (0 : ℝ) < 2 * (m : ℝ) := by
    have : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    linarith
  simp only [radP]; exact div_pos h hα

theorem radQ_pos {α : ℝ} (hα : 0 < α) (m : ℕ) : 0 < radQ α m := by
  have h : (0 : ℝ) < 2 * (m : ℝ) + 5 := by positivity
  simp only [radQ]; exact div_pos h hα

/-- `p = 2m/α ≥ 10` for `α ≤ 1/5`, `m ≥ 1`. -/
theorem ten_le_radP {α : ℝ} (hα : 0 < α) (hα5 : α ≤ 1 / 5) {m : ℕ} (hm : 1 ≤ m) :
    10 ≤ radP α m := by
  have hmr : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  simp only [radP]
  rw [le_div_iff₀ hα]
  nlinarith [hα5, hmr]

/-- `q = (2m+5)/α ≥ 35` for `α ≤ 1/5`, `m ≥ 1`. -/
theorem thirtyfive_le_radQ {α : ℝ} (hα : 0 < α) (hα5 : α ≤ 1 / 5) {m : ℕ} (hm : 1 ≤ m) :
    35 ≤ radQ α m := by
  have hmr : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  simp only [radQ]
  rw [le_div_iff₀ hα]
  nlinarith [hα5, hmr]

/-- `(4m+5)/α = p + q`, the total indicial gap. -/
theorem radP_add_radQ {α : ℝ} (hα : 0 < α) (m : ℕ) :
    radP α m + radQ α m = (4 * (m : ℝ) + 5) / α := by
  simp only [radP, radQ]; field_simp; ring

/-- `K = 1/(α(4m+5)) = 1/(α²(p+q))`. -/
theorem radK_eq {α : ℝ} (hα : 0 < α) (m : ℕ) :
    radK α m = 1 / (α ^ 2 * (radP α m + radQ α m)) := by
  rw [radP_add_radQ hα m, radK]
  congr 1
  field_simp

theorem radK_pos {α : ℝ} (hα : 0 < α) (m : ℕ) : 0 < radK α m := by
  simp only [radK]; positivity

/-- The factor `α(4m+5) = 1/K`, kept as a named quantity: it is the constant that the weight
`z^{k-8}` combines with in the assembly. -/
theorem radK_mul_alpha {α : ℝ} (hα : 0 < α) (m : ℕ) :
    radK α m * (α * (4 * (m : ℝ) + 5)) = 1 := by
  simp only [radK]
  field_simp

end Work.FTS.PhiStar.RadialWAux
