import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Submission.Work.BoseB6.BogIntegral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB6Est.lhyR3Integral`

The full-space integral of the Bogoliubov model bracket `lhyR3` on `Fin 3 → ℝ`
at the model coupling `c = 8π` is the negative of the model value:

    ∫_{ℝ³} lhyR3 (8π) = −lhyValue (8π).

This is the value of FS `lem:BogIntegral`'s `I₁` (layer 1, the "value" part),
in the form in which the mode-lattice sums of node B6 are taken
(`Fin 3 → ℝ` with the Euclidean norm `eucNorm3` rather than
`EuclideanSpace ℝ (Fin 3)`).

The proof transports the already-proved Euclidean-space identity
`Work.BoseB6.integral_lhyFun` (equivalently `Work.BoseBox.bog_model_integral`)
along the measure-preserving identification
`WithLp.toLp 2 : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)`, using
`Work.BoseBox.eucNorm3_eq_norm` to match the norms.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Work.BoseB6Est

/-- `lhyR3` and `lhyFun` agree after transporting along `WithLp.toLp 2`. -/
theorem lhyR3_eq_lhyFun_toLp (c : ℝ) (x : Fin 3 → ℝ) :
    Work.BoseB6.lhyR3 c x = Work.BoseB6.lhyFun c (WithLp.toLp 2 x) := by
  simp only [Work.BoseB6.lhyR3, Work.BoseB6.lhyFun, Work.BoseBox.eucNorm3_eq_norm x]

/-- The integral of `lhyR3 c` over `Fin 3 → ℝ` is the integral of `lhyFun c` over
`EuclideanSpace ℝ (Fin 3)`. -/
theorem integral_lhyR3_eq_integral_lhyFun (c : ℝ) :
    (∫ x : Fin 3 → ℝ, Work.BoseB6.lhyR3 c x)
      = ∫ k : EuclideanSpace ℝ (Fin 3), Work.BoseB6.lhyFun c k := by
  have hmp : MeasurePreserving
      (WithLp.toLp 2 : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)) volume volume :=
    PiLp.volume_preserving_toLp (Fin 3)
  have hcomp := hmp.integral_comp (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding
    (fun k : EuclideanSpace ℝ (Fin 3) => Work.BoseB6.lhyFun c k)
  rw [← hcomp]
  exact integral_congr_ae (Filter.Eventually.of_forall (lhyR3_eq_lhyFun_toLp c))

theorem lhyR3Integral :
    (∫ x : Fin 3 → ℝ, Work.BoseB6.lhyR3 (8 * Real.pi) x) = -Work.BoseB6.lhyValue (8 * Real.pi) := by
  rw [integral_lhyR3_eq_integral_lhyFun]
  exact Work.BoseB6.integral_lhyFun (by positivity : (0 : ℝ) < 8 * Real.pi)

end Work.BoseB6Est
