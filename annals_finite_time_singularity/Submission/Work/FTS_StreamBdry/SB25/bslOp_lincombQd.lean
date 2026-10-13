import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB25.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.SB25

/-! ## Linearity of `bslOp` on the open quadrant

`Work.Elliptic.bslOp α = -α²z²∂_zz - α(5+α)z∂_z + L₀` with
`L₀ = -∂_θθ + ∂_θ(tan θ · ·) - 6` is a linear differential operator.  Its additivity is
`Work.Elliptic.bslOp_add` (hypotheses: `Real.cos θ ≠ 0` and `C²` at the point for both summands)
and its homogeneity is `Work.FTS.BSIdent.OddExt.bslOp_const_mul` (no differentiability needed:
`deriv` commutes with a constant unconditionally).  The two combine into
`BslOpLincomb α a b P Q`, the statement needed by the SB2/SB5 chain.

The `Qd`-restriction and the `C²` hypotheses are not decoration: `Real.tan` is not
differentiable at `θ = π/2`, and `deriv` is totalised, so both additivity and (in the
non-constant-coefficient slots) homogeneity genuinely fail without them — see
`Submission/Work/FTS_StreamBdry/SB25/bslOp_lincomb.lean` and `_counter.lean`. -/

/-- `Function.uncurry` of a constant multiple. -/
private lemma uncurry_const_mul (c : ℝ) (P : ℝ → ℝ → ℝ) :
    Function.uncurry (fun z' θ' => c * P z' θ')
      = fun y : ℝ × ℝ => c * Function.uncurry P y := by
  funext y
  rcases y with ⟨z, θ⟩
  rfl

/-- Multiplication by a constant preserves `C^n` at a point, in the `Function.uncurry` shape in
which the hypotheses of `BslOpLincomb` are phrased. -/
private lemma contDiffAt_uncurry_const_mul {P : ℝ → ℝ → ℝ} {z θ c : ℝ} {n : WithTop ℕ∞}
    (hP : ContDiffAt ℝ n (Function.uncurry P) (z, θ)) :
    ContDiffAt ℝ n (Function.uncurry (fun z' θ' => c * P z' θ')) (z, θ) := by
  have h : ContDiffAt ℝ n (fun y : ℝ × ℝ => c * Function.uncurry P y) (z, θ) := by
    simpa only [smul_eq_mul] using hP.const_smul c
  simpa only [uncurry_const_mul] using h

theorem bslOp_lincombQd (α a b : ℝ) (P Q : ℝ → ℝ → ℝ) :
    Work.FTS_StreamBdry.SB25.BslOpLincomb α a b P Q := by
  intro z θ hmem hP hQ
  have hcos : Real.cos θ ≠ 0 := ne_of_gt (Work.FTS_StreamBdry.cos_pos_of_Qd hmem)
  rw [Work.Elliptic.bslOp_add α (fun z' θ' => a * P z' θ') (fun z' θ' => b * Q z' θ') z θ hcos
      (contDiffAt_uncurry_const_mul (c := a) hP) (contDiffAt_uncurry_const_mul (c := b) hQ),
    Work.FTS.BSIdent.OddExt.bslOp_const_mul α a P z θ,
    Work.FTS.BSIdent.OddExt.bslOp_const_mul α b Q z θ]

end Work.FTS_StreamBdry.SB25
