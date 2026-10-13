/-
Work module for the Elgindi finite-time singularity project.

# An explicit `C^∞` angular cutoff

`chiCut` is the smooth step `θ ↦ 1 - smoothTransition (8/π * (θ - π/4))`: it equals `1` for
`θ ≤ π/4`, equals `0` for `3π/8 ≤ θ`, and takes values in `[0,1]` everywhere.  Its first two
derivatives vanish outside the transition interval `(π/4, 3π/8)` (and at the two endpoints, by
Fermat: `π/4` and `3π/8` are global extrema).

Nothing here is specific to the Euler project; the file only states the elementary facts needed
to assemble `Work.FTS.EllipticEst.Prop.TraceLeftPieces.exists_cutoff`.
-/
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS.EllipticEst.Prop.TraceLeftPieces

/-- The explicit smooth cutoff: `θ ↦ 1 - smoothTransition (8/π * (θ - π/4))`. -/
noncomputable def chiCut (θ : ℝ) : ℝ :=
  1 - Real.smoothTransition (8 / Real.pi * (θ - Real.pi / 4))

lemma chiCut_eq_one {θ : ℝ} (h : θ ≤ Real.pi / 4) : chiCut θ = 1 := by
  have hpos : (0 : ℝ) < 8 / Real.pi := div_pos (by norm_num) Real.pi_pos
  have hle : 8 / Real.pi * (θ - Real.pi / 4) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hpos.le (by linarith)
  simp [chiCut, Real.smoothTransition.zero_of_nonpos hle]

lemma chiCut_eq_zero {θ : ℝ} (h : 3 * Real.pi / 8 ≤ θ) : chiCut θ = 0 := by
  have hge : (1 : ℝ) ≤ 8 / Real.pi * (θ - Real.pi / 4) := by
    rw [div_mul_eq_mul_div, one_le_div Real.pi_pos]
    linarith
  simp [chiCut, Real.smoothTransition.one_of_one_le hge]

lemma chiCut_nonneg (θ : ℝ) : 0 ≤ chiCut θ := by
  have := Real.smoothTransition.le_one (8 / Real.pi * (θ - Real.pi / 4))
  simp only [chiCut]; linarith

lemma chiCut_le_one (θ : ℝ) : chiCut θ ≤ 1 := by
  have := Real.smoothTransition.nonneg (8 / Real.pi * (θ - Real.pi / 4))
  simp only [chiCut]; linarith

lemma chiCut_contDiff : ContDiff ℝ 2 chiCut := by
  unfold chiCut
  fun_prop

/-- `chiCut` is `C^∞`, hence so are its derivatives (recorded here for reuse). -/
lemma chiCut_contDiff_top : ContDiff ℝ (⊤ : ℕ∞) chiCut := by
  unfold chiCut
  fun_prop

/-! ### Where the derivatives vanish -/

lemma chiCut_deriv_eq_zero_of_lt {θ : ℝ} (h : θ < Real.pi / 4) : deriv chiCut θ = 0 := by
  have hloc : chiCut =ᶠ[𝓝 θ] fun _ => (1 : ℝ) := by
    filter_upwards [isOpen_Iio.mem_nhds h] with y hy
    exact chiCut_eq_one (le_of_lt hy)
  rw [hloc.deriv_eq, deriv_const]

lemma chiCut_deriv_eq_zero_of_gt {θ : ℝ} (h : 3 * Real.pi / 8 < θ) : deriv chiCut θ = 0 := by
  have hloc : chiCut =ᶠ[𝓝 θ] fun _ => (0 : ℝ) := by
    filter_upwards [isOpen_Ioi.mem_nhds h] with y hy
    exact chiCut_eq_zero (le_of_lt hy)
  rw [hloc.deriv_eq, deriv_const]

/-- At `π/4` the function `chiCut` has a global maximum, so its derivative vanishes there. -/
lemma chiCut_deriv_at_quarter : deriv chiCut (Real.pi / 4) = 0 := by
  have hmax : IsLocalMax chiCut (Real.pi / 4) :=
    Filter.Eventually.of_forall fun θ => by
      rw [chiCut_eq_one le_rfl]
      exact chiCut_le_one θ
  exact hmax.deriv_eq_zero

/-- At `3π/8` the function `chiCut` has a global minimum, so its derivative vanishes there. -/
lemma chiCut_deriv_at_three_eighths : deriv chiCut (3 * Real.pi / 8) = 0 := by
  have hmin : IsLocalMin chiCut (3 * Real.pi / 8) :=
    Filter.Eventually.of_forall fun θ => by
      rw [chiCut_eq_zero le_rfl]
      exact chiCut_nonneg θ
  exact hmin.deriv_eq_zero

lemma chiCut_deriv_eq_zero_left {θ : ℝ} (h : θ ≤ Real.pi / 4) : deriv chiCut θ = 0 := by
  rcases lt_or_eq_of_le h with hlt | heq
  · exact chiCut_deriv_eq_zero_of_lt hlt
  · rw [heq]; exact chiCut_deriv_at_quarter

lemma chiCut_deriv_eq_zero_right {θ : ℝ} (h : 3 * Real.pi / 8 ≤ θ) : deriv chiCut θ = 0 := by
  rcases lt_or_eq_of_le h with hlt | heq
  · exact chiCut_deriv_eq_zero_of_gt hlt
  · rw [← heq]; exact chiCut_deriv_at_three_eighths

lemma chiCut_deriv2_eq_zero_of_lt {θ : ℝ} (h : θ < Real.pi / 4) : deriv (deriv chiCut) θ = 0 := by
  have hloc : deriv chiCut =ᶠ[𝓝 θ] fun _ => (0 : ℝ) := by
    filter_upwards [isOpen_Iio.mem_nhds h] with y hy
    exact chiCut_deriv_eq_zero_left (le_of_lt hy)
  rw [hloc.deriv_eq, deriv_const]

lemma chiCut_deriv2_eq_zero_of_gt {θ : ℝ} (h : 3 * Real.pi / 8 < θ) :
    deriv (deriv chiCut) θ = 0 := by
  have hloc : deriv chiCut =ᶠ[𝓝 θ] fun _ => (0 : ℝ) := by
    filter_upwards [isOpen_Ioi.mem_nhds h] with y hy
    exact chiCut_deriv_eq_zero_right (le_of_lt hy)
  rw [hloc.deriv_eq, deriv_const]

end Work.FTS.EllipticEst.Prop.TraceLeftPieces
