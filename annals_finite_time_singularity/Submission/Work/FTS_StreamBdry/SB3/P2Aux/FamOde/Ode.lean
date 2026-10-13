import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_StreamBdry.SB3.P2Aux.FamOde.Weight

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `FamOde.Ode` — the differentiated integrating factor and the Lipschitz comparison

For `F : ℝ → ℝ` a `θ`-slice satisfying `(F')' + c·F' = H` on `(0, π/2)` with
`c = coco` (`FamOde.coco`), the product `W := m·F'` with `m = wfn` satisfies
`W' = m·H` (`hasDerivAt_W`), and `|m·H| ≤ Φ = phfn A C` whenever `|H| ≤ A/sin 2θ + C`
(`abs_wfn_mul_le`).  We also record the Lipschitz comparison
`|W b - W a| ≤ C(b-a)` from a pointwise bound `|W'| ≤ C` on `(a,b)`.
-/

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS_StreamBdry.SB3.P2Aux.FamOde

lemma hasDerivAt_wfn {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    HasDerivAt wfn (wfn θ * coco θ) θ := by
  have h : HasDerivAt (fun x : ℝ => Real.sin x ^ 2 * Real.cos x ^ 3)
      (2 * Real.sin θ ^ (2 - 1) * Real.cos θ * Real.cos θ ^ 3
        + Real.sin θ ^ 2 * (3 * Real.cos θ ^ (3 - 1) * -Real.sin θ)) θ :=
    (Real.hasDerivAt_sin θ).pow 2 |>.mul ((Real.hasDerivAt_cos θ).pow 3)
  have hs : Real.sin θ ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [Real.pi_pos, hθ.2]))
  have hc : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩)
  have key : (2 * Real.sin θ ^ (2 - 1) * Real.cos θ * Real.cos θ ^ 3
        + Real.sin θ ^ 2 * (3 * Real.cos θ ^ (3 - 1) * -Real.sin θ))
      = wfn θ * coco θ := by
    simp only [wfn, coco, Real.tan_eq_sin_div_cos, Real.sin_two_mul, Real.cos_two_mul']
    field_simp
    try ring
  convert h using 1
  · rfl
  · exact key.symm

lemma hasDerivAt_W {F Hz : ℝ → ℝ} {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) (Real.pi / 2))
    (hodeθ : HasDerivAt (deriv F) (Hz θ - coco θ * deriv F θ) θ) :
    HasDerivAt (fun θ' => wfn θ' * deriv F θ') (wfn θ * Hz θ) θ := by
  have h := (hasDerivAt_wfn hθ).mul hodeθ
  convert h using 1
  ring

lemma abs_wfn_mul_le {A C : ℝ} {Hz : ℝ → ℝ} {θ : ℝ}
    (hθ : θ ∈ Ioo (0 : ℝ) (Real.pi / 2))
    (hHθ : |Hz θ| ≤ A / Real.sin (2 * θ) + C) :
    |wfn θ * Hz θ| ≤ phfn A C θ := by
  have hs : Real.sin θ ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [Real.pi_pos, hθ.2]))
  have hc : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩)
  have hw : 0 ≤ wfn θ := wfn_nonneg_of_mem hθ
  calc |wfn θ * Hz θ| = wfn θ * |Hz θ| := by rw [abs_mul, abs_of_nonneg hw]
    _ ≤ wfn θ * (A / Real.sin (2 * θ) + C) := mul_le_mul_of_nonneg_left hHθ hw
    _ = phfn A C θ := by
        simp only [wfn, phfn, Real.sin_two_mul]
        field_simp
        try ring

/-- If `W` is continuous on `[a,b]`, differentiable on `(a,b)` with `|W'| ≤ C` there, then
`|W b - W a| ≤ C(b-a)`. -/
lemma abs_sub_le_mul_of_deriv_le {W : ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn W (Icc a b)) (hdiff : DifferentiableOn ℝ W (Ioo a b))
    (hb : ∀ x ∈ Ioo a b, |deriv W x| ≤ C) : |W b - W a| ≤ C * (b - a) := by
  have h1 : W b - W a ≤ C * (b - a) :=
    Convex.image_sub_le_mul_sub_of_deriv_le (convex_Icc a b) hcont
      (by simpa only [interior_Icc] using hdiff)
      (fun x hx => (abs_le.mp (hb x (by rwa [interior_Icc] at hx))).2)
      a (left_mem_Icc.mpr hab) b (right_mem_Icc.mpr hab) hab
  have h2 : W a - W b ≤ C * (b - a) := by
    have hneg := Convex.image_sub_le_mul_sub_of_deriv_le (convex_Icc a b) hcont.neg
      (by simpa only [interior_Icc] using hdiff.neg)
      (fun x hx => by
        have hx' : x ∈ Ioo a b := by rwa [interior_Icc] at hx
        have := (abs_le.mp (hb x hx')).1
        change deriv (fun y => -W y) x ≤ C
        rw [deriv.fun_neg]
        linarith)
      a (left_mem_Icc.mpr hab) b (right_mem_Icc.mpr hab) hab
    have h2' : W a ≤ W b + C * (b - a) := by simpa using hneg
    linarith
  rw [abs_le]
  constructor <;> linarith

end Work.FTS_StreamBdry.SB3.P2Aux.FamOde
