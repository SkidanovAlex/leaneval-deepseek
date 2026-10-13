import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.BSIdent.Defs
import Submission.Work.FTS.BSIdent.Cyl.DecayAux.Basic
import Submission.Work.FTS.BSIdent.Weyl.Levels._stub
import Submission.Work.FTS.BSIdent.Weyl.Levels._dev5
import Submission.Work.FTS.BSIdent.Weyl.Levels._dev6
import Submission.Work.FTS.BSIdent.Weyl.Levels._dev7
import Submission.Work.FTS.BSIdent.Weyl.Levels._dev8
import Submission.Work.FTS.BSIdent.Weyl.Levels._dev9

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FTS.BSIdent.Weyl.Dev10

open Filter Set MeasureTheory
open scoped Topology
open Work.FTS.BSIdent.Weyl.Dev5 (GG)
open Work.FTS.BSIdent.Weyl.Dev8 (rhoP_zero_pos rhoP_zero_eq_abs)

variable {Φ : Work.FTS.BSIdent.Fam} {τ : ℝ}

/-- `GG` vanishes at `(w₀, π/2)`. -/
theorem GG_pi_div_two_eq_zero {w₀ : ℝ} (hw₀ : 0 < w₀)
    (hπ : ∀ w : ℝ, 0 < w → Φ w (Real.pi / 2) τ = 0) :
    GG Φ τ w₀ (Real.pi / 2) = 0 := by
  rw [Dev5.GG_of_nonneg (Φ := Φ) (τ := τ) (le_of_lt (by linarith [Real.pi_pos]))]
  exact hπ w₀ hw₀

theorem GG_neg_pi_div_two_eq_zero {w₀ : ℝ} (hw₀ : 0 < w₀)
    (hπ : ∀ w : ℝ, 0 < w → Φ w (Real.pi / 2) τ = 0) :
    GG Φ τ w₀ (-(Real.pi / 2)) = 0 := by
  rw [Dev5.GG_of_neg (Φ := Φ) (τ := τ) (by linarith [Real.pi_pos])]
  rw [show -( -(Real.pi / 2)) = Real.pi / 2 from by ring, hπ w₀ hw₀, neg_zero]

/-- The `w`-derivative of `GG` vanishes at `(w₀, π/2)`. -/
theorem pdR_GG_pi_div_two_eq_zero {w₀ : ℝ} (hw₀ : 0 < w₀)
    (hπ : ∀ w : ℝ, 0 < w → Φ w (Real.pi / 2) τ = 0) :
    Work.Cyl.pdR (GG Φ τ) w₀ (Real.pi / 2) = 0 := by
  have hev : (fun w' : ℝ => GG Φ τ w' (Real.pi / 2)) =ᶠ[𝓝 w₀]
      (fun _ => (0:ℝ)) := by
    filter_upwards [Ioi_mem_nhds hw₀] with w' hw'
    exact GG_pi_div_two_eq_zero (τ := τ) hw' hπ
  show deriv (fun w' : ℝ => GG Φ τ w' (Real.pi / 2)) w₀ = 0
  rw [Filter.EventuallyEq.deriv_eq hev, deriv_const]

theorem pdR_GG_neg_pi_div_two_eq_zero {w₀ : ℝ} (hw₀ : 0 < w₀)
    (hπ : ∀ w : ℝ, 0 < w → Φ w (Real.pi / 2) τ = 0) :
    Work.Cyl.pdR (GG Φ τ) w₀ (-(Real.pi / 2)) = 0 := by
  have hev : (fun w' : ℝ => GG Φ τ w' (-(Real.pi / 2))) =ᶠ[𝓝 w₀]
      (fun _ => (0:ℝ)) := by
    filter_upwards [Ioi_mem_nhds hw₀] with w' hw'
    exact GG_neg_pi_div_two_eq_zero (τ := τ) hw' hπ
  show deriv (fun w' : ℝ => GG Φ τ w' (-(Real.pi / 2))) w₀ = 0
  rw [Filter.EventuallyEq.deriv_eq hev, deriv_const]

/-- The `θ`-derivative of `GG` at `(w₀, π/2)` is the axis level. -/
theorem pdZ_GG_pi_div_two_eq {w₀ : ℝ} :
    Work.Cyl.pdZ (GG Φ τ) w₀ (Real.pi / 2)
      = deriv (fun θ => Φ w₀ θ τ) (Real.pi / 2) := by
  have hev : (fun θ' : ℝ => GG Φ τ w₀ θ') =ᶠ[𝓝 (Real.pi / 2)]
      (fun θ' : ℝ => Φ w₀ θ' τ) := by
    filter_upwards [Ioi_mem_nhds (by linarith [Real.pi_pos] : (0:ℝ) < Real.pi / 2)] with θ' hθ'
    exact Dev5.GG_of_nonneg (Φ := Φ) (τ := τ) hθ'.le
  show deriv (fun θ' : ℝ => GG Φ τ w₀ θ') (Real.pi / 2) = _
  exact Filter.EventuallyEq.deriv_eq hev

/-- `GG` is odd in `θ`. -/
theorem GG_neg_theta {w : ℝ} (hw : 0 < w) (h0 : ∀ w : ℝ, 0 < w → Φ w 0 τ = 0) (θ : ℝ) :
    GG Φ τ w (-θ) = -GG Φ τ w θ := by
  rcases lt_trichotomy θ 0 with h | h | h
  · rw [Dev5.GG_of_nonneg (Φ := Φ) (τ := τ) (by linarith), Dev5.GG_of_neg (Φ := Φ) (τ := τ) h,
      neg_neg]
  · subst h
    rw [neg_zero, Dev5.GG_of_nonneg (Φ := Φ) (τ := τ) le_rfl, h0 w hw, neg_zero]
  · rw [Dev5.GG_of_neg (Φ := Φ) (τ := τ) (by linarith),
      Dev5.GG_of_nonneg (Φ := Φ) (τ := τ) h.le, neg_neg]

theorem pdZ_GG_neg_pi_div_two_eq {w₀ : ℝ} (hw₀ : 0 < w₀)
    (h0 : ∀ w : ℝ, 0 < w → Φ w 0 τ = 0) :
    Work.Cyl.pdZ (GG Φ τ) w₀ (-(Real.pi / 2))
      = deriv (fun θ => Φ w₀ θ τ) (Real.pi / 2) := by
  have hodd : ∀ y : ℝ, (fun θ' : ℝ => GG Φ τ w₀ θ') (-y) = -(fun θ' : ℝ => GG Φ τ w₀ θ') y :=
    fun y => GG_neg_theta (Φ := Φ) (τ := τ) hw₀ h0 y
  have h := Work.FTS.BSIdent.Cyl.deriv_odd_eq (f := fun θ' : ℝ => GG Φ τ w₀ θ') hodd (-(Real.pi / 2))
  rw [show -( -(Real.pi / 2)) = Real.pi / 2 from by ring] at h
  show deriv (fun θ' : ℝ => GG Φ τ w₀ θ') (-(Real.pi / 2)) = _
  rw [h]
  exact pdZ_GG_pi_div_two_eq (Φ := Φ) (τ := τ) (w₀ := w₀)

end Work.FTS.BSIdent.Weyl.Dev10
