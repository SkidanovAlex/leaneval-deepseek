import Mathlib.Tactic.Have
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxA0.Assembly
import Submission.Work.SmallBoxD1Assembly
import Submission.Work.SmallBoxD1Scalar
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxA0

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal
open Submission BoseGases
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## `boxOp` is (real-)homogeneous in the state

`boxOp s f h Ψ x = Σ_i f (x i) · ∫_z h z · Ψ(update x i z)` is linear in `Ψ`; here we
record only the scalar-homogeneity in the state slot, which is what `modeP` and hence
`kinPWord` scale by. -/

private lemma boxOp_smul_const (s : ℝ) {N : ℕ} (f h : ℝ³ → ℝ) (cs : ℝ)
    (Ψ : X N → ℝ) (x : X N) :
    boxOp s f h (cs • Ψ) x = cs * boxOp s f h Ψ x := by
  simp only [boxOp, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hrew : (∫ z in acube s, h z * (cs * Ψ (Function.update x i z)))
      = cs * ∫ z in acube s, h z * Ψ (Function.update x i z) := by
    rw [show (fun z => h z * (cs * Ψ (Function.update x i z)))
          = fun z => cs * (h z * Ψ (Function.update x i z)) by funext z; ring]
    rw [MeasureTheory.integral_const_mul]
  rw [hrew]
  ring

/-! ## `modeP` is quadratic in the state

`modeP s g Ψ = (s³)⁻¹ ∫_x (boxOp s 1 g Ψ x)²`, so homogeneity gives the `cs²`. -/

private lemma modeP_smul (s : ℝ) {n : ℕ} (g : ℝ³ → ℝ) (cs : ℝ) (Φ : X (n + 1) → ℝ) :
    modeP s g (cs • Φ) = cs ^ 2 * modeP s g Φ := by
  unfold modeP
  have hpt : (fun x : X (n + 1) => (boxOp s (fun _ => (1 : ℝ)) g (cs • Φ) x) ^ 2)
      = fun x => cs ^ 2 * (boxOp s (fun _ => (1 : ℝ)) g Φ x) ^ 2 := by
    funext x
    rw [boxOp_smul_const]
    ring
  rw [hpt, MeasureTheory.integral_const_mul]
  ring

/-- **`kinPWord` is homogeneous of degree `2` in the state.**  The whole word is
`(2π)⁻³ ∫_p F(‖p‖)·(P_{u_p} + P_{v_p})(Φ)`; each `modeP` is quadratic in `Φ` and the
`p`-integral/coefficient are `Φ`-independent, so the scalar pulls out of the Bochner
integral by `integral_const_mul`. -/
theorem kinPWord_smul {n : ℕ} {s c : ℝ} (cs : ℝ) {Φ : X (n + 1) → ℝ} :
    kinPWord s c (cs • Φ) = cs ^ 2 * kinPWord s c Φ := by
  unfold kinPWord
  have hpt : (fun p : ℝ³ => fsKinCoeff c ‖p‖ *
        (modeP s (qModeRe s p) (cs • Φ) + modeP s (qModeIm s p) (cs • Φ)))
      = fun p : ℝ³ => cs ^ 2 * (fsKinCoeff c ‖p‖ *
        (modeP s (qModeRe s p) Φ + modeP s (qModeIm s p) Φ)) := by
    funext p
    rw [modeP_smul, modeP_smul]
    ring
  rw [hpt, MeasureTheory.integral_const_mul]
  ring

end Work.SmallBoxA0
