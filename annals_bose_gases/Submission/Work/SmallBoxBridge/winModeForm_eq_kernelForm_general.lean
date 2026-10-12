import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxBridge.Resolve.winModeForm_eq_kernelForm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The (c1) kernel identity without hypotheses on the window

`Work.SmallBoxBridge.Resolve.winModeForm_eq_kernelForm` establishes the (c1)
resolution-of-identity identity

  `winModeForm χ F u = ∫_x (χ·u)(x) · ∫_y K_F(x−y)·(χ·u)(y) dy`

under the extra assumptions that the window `χ` be measurable and bounded by `1`.
Both sides of that identity, however, only see the *product* `g = χ·u`: the left-hand side is

  `(2π)⁻³ ∫_p F‖p‖ · ‖kinFT g p‖²`   with   `kinFT g p = ∫_y e^{−i⟪p,y⟫} g(y) dy`,

and the right-hand side is the position-space quadratic form of `g` against the kernel
`K_F = 𝓕⁻¹F`.  Hence, applying the corpus lemma to the *constant* window `χ ≡ 1` and the
function `g = χ·u` — which is integrable by hypothesis — removes both hypotheses.

This is the general form needed downstream, where the window is an arbitrary (e.g. only
locally summable / non-measurable in the formal statement) cut-off.
-/

namespace Work.SmallBoxBridge

open MeasureTheory

/-- **The (c1) kernel identity for an arbitrary window.**  For any `χ u : ℝ³ → ℝ` with
`χ·u` integrable and any symbol `F` with `p ↦ F‖p‖` integrable, the windowed mode form of
`χ·F(√−Δ)·χ` equals the position-space quadratic form of `χ·u` against the kernel
`K_F = 𝓕⁻¹F`. -/
theorem winModeForm_eq_kernelForm_general (χ u : EuclideanSpace ℝ (Fin 3) → ℝ) (F : ℝ → ℝ)
    (hF : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => F ‖p‖))
    (hu : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin 3) => χ x * u x)) :
    Submission.BoseGases.winModeForm χ F u = ∫ x : EuclideanSpace ℝ (Fin 3),
      (χ x * u x) * (∫ y : EuclideanSpace ℝ (Fin 3),
        Submission.BoseGases.kinKernel F (x - y) * (χ y * u y)) := by
  -- Both sides only depend on the pointwise product `χ·u`; the two windowed Fourier
  -- transforms coincide as functions of `y`.
  have hfg : (fun y : EuclideanSpace ℝ (Fin 3) => (χ y : ℂ) * (u y : ℂ))
      = (fun y => (((1 : ℝ) : ℂ)) * ((χ y * u y : ℝ) : ℂ)) := by
    funext y
    rw [Complex.ofReal_mul, Complex.ofReal_one]
    ring
  -- Reduce the left-hand side to the case of the constant window `χ ≡ 1`.
  have h1 : Submission.BoseGases.winModeForm χ F u
      = Submission.BoseGases.winModeForm (fun _ : EuclideanSpace ℝ (Fin 3) => 1) F
          (fun x => χ x * u x) := by
    unfold Submission.BoseGases.winModeForm
    congr 1
    apply MeasureTheory.integral_congr_ae
    filter_upwards with p
    congr 2
    congr 1
    rw [hfg]
  -- Apply the corpus identity for the constant window and identify the two sides.
  rw [h1, Work.SmallBoxBridge.Resolve.winModeForm_eq_kernelForm (fun _ => 1) (fun x => χ x * u x)
    F hF (by simpa using hu) measurable_const (fun x => by simp)]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  have hinner : (∫ y : EuclideanSpace ℝ (Fin 3),
        Submission.BoseGases.kinKernel F (x - y) * (1 * (χ y * u y)))
      = ∫ y : EuclideanSpace ℝ (Fin 3),
        Submission.BoseGases.kinKernel F (x - y) * (χ y * u y) :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun y => by ring))
  rw [hinner]
  ring

end Work.SmallBoxBridge
