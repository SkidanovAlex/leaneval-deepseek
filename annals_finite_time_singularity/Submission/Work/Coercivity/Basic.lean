/-
# The coercivity chapter: basic API of the operators, weights and energies

Elementary consequences of the definitions in `Submission/Work/Coercivity/Defs.lean`:
the identification of the angular data with the `Work.Spaces` and `Work.FM` versions,
the algebra of the weight `w` (including the identity `L(g)·w = g·w + z∂_z(g·w)` that
drives all the coercivity estimates), and the energy functionals in the weighted
inner-product form used by the coercivity computations.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Coercivity.Defs
import Submission.Work.Spaces.Gam_bounds
import Submission.Work.Spaces.CAux.integrableOn_GamK
import Submission.Work.Spaces.c_bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-! ## Agreement of the angular data with `Work.Spaces` and `Work.FM` -/

theorem K_eq_Kpaper : Spaces.K = FM.Kpaper := by
  funext θ; rw [Spaces.K, FM.Kpaper]

theorem Gam_eq_Gamma (α : ℝ) : Spaces.Gam α = FM.Gamma α := by
  funext θ; rw [Spaces.Gam, FM.Gamma]

theorem c_eq_cK (α : ℝ) : Spaces.c α = FM.cK Spaces.K (Spaces.Gam α) := by
  rw [Spaces.c, FM.cK]
  refine integral_congr_ae ?_
  filter_upwards with θ
  rw [K_eq_Kpaper, Gam_eq_Gamma, mul_comm]

theorem L12f_eq (f : ℝ → ℝ → ℝ) (z : ℝ) : L12f f z = FM.L12 Spaces.K f z := rfl

/-- `c` is positive throughout the range of parameters used in the paper. -/
theorem c_pos {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) : 0 < Spaces.c α :=
  lt_of_lt_of_le (by norm_num) (Spaces.c_bounds α hα hα1).1

theorem c_ne_zero {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) : Spaces.c α ≠ 0 :=
  ne_of_gt (c_pos hα hα1)

/-- `Γ(θ)/c` is bounded by `10` on the angular interval. -/
theorem Gam_div_c_bound {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {θ : ℝ} (hθ : θ ∈ Spaces.Iθ) :
    |Spaces.Gam α θ / Spaces.c α| ≤ 10 := by
  have hc := (Spaces.c_bounds α hα hα1).1
  have hG := (Spaces.Gam_bounds α θ hα hθ).2
  have hG0 := (Spaces.Gam_bounds α θ hα hθ).1
  have hcp := c_pos hα hα1
  rw [abs_of_nonneg (div_nonneg hG0 (le_of_lt hcp))]
  rw [div_le_iff₀ hcp]
  nlinarith

/-! ## The weight `w` -/

theorem w_eq (z : ℝ) : Spaces.w z = (1 + z) ^ 2 / z ^ 2 := rfl

theorem w_pos {z : ℝ} (hz : 0 < z) : 0 < Spaces.w z := by
  rw [w_eq]; positivity

theorem w_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ Spaces.w z := by
  rw [w_eq]; positivity

theorem w_eq_decomp {z : ℝ} (hz : z ≠ 0) :
    Spaces.w z = 1 / z ^ 2 + 2 / z + 1 := by
  rw [w_eq]; field_simp; ring

theorem inv_sq_le_w {z : ℝ} (hz : 0 < z) : 1 / z ^ 2 ≤ Spaces.w z := by
  have h := w_eq_decomp (ne_of_gt hz)
  rw [h]
  have : 0 ≤ 2 / z + 1 := by positivity
  linarith

theorem inv_le_w {z : ℝ} (hz : 0 < z) : 1 / z ≤ Spaces.w z := by
  have h := w_eq_decomp (ne_of_gt hz)
  rw [h, ← sub_nonneg]
  have h1 : 1 / z ^ 2 + 2 / z + 1 - 1 / z = 1 / z ^ 2 + 1 / z + 1 := by ring
  rw [h1]
  positivity

theorem one_le_w {z : ℝ} (hz : 0 < z) : 1 ≤ Spaces.w z := by
  have h := w_eq_decomp (ne_of_gt hz)
  rw [h]
  have h1 : 0 ≤ 1 / z ^ 2 + 2 / z := by positivity
  linarith

theorem w_sq_eq {z : ℝ} (hz : z ≠ 0) :
    Spaces.w z ^ 2 = 1 / z ^ 4 + 4 / z ^ 3 + 6 / z ^ 2 + 4 / z + 1 := by
  have h := w_eq_decomp hz
  rw [h]; field_simp; ring

/-! ## The identity `𝓛(g)·w = g·w + z∂_z(g·w)` -/

/-- **The identity `LW` of the paper**, in algebraic form (no differentiability needed):
`𝓛(g)·w = g·w + z ∂_z(g·w)`, with the derivative written out.  This is the pointwise
identity behind every coercivity computation of §6 of the paper. -/
theorem L_mul_w (f : ℝ → ℝ → ℝ) (z θ : ℝ) (hz : 0 < z) :
    L f z θ * Spaces.w z
      = f z θ * Spaces.w z
        + z * (Spaces.pz f z θ * Spaces.w z - f z θ * (2 * (1 + z) / z ^ 3)) := by
  have h : ((1 : ℝ) + z) ≠ 0 := by positivity
  rw [L, Spaces.Dz, Spaces.pz]
  simp only [Spaces.w]
  field_simp
  ring

/-! ## The energies in weighted-inner-product form -/

theorem Ef_eq_wip (f : ℝ → ℝ → ℝ) :
    Ef f = wip (fun z _ => Spaces.w z ^ 2) f f := by
  simp only [Ef, Spaces.L2Sq, wip]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
  ring

end Work.Coercivity
