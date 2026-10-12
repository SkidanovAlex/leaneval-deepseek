import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.ChiSmallC2
import Submission.Work.DLSmallKernels
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A3 — `conv3Small M = χ_M ⋆ χ_M` is `C²` (`3 ≤ M`)

Third stage of `conv3Small_quadratic_dev`: the cosine-M self-convolution
`conv3Small M x = ∫ y, χ_M(y)·χ_M(x − y)` (`DLSmallKernels`) is `C²` on
`ℝ³`.

Ingredients: the function equality `conv3Small M = convolution χ_M χ_M`
(`MeasureTheory.convolution` with `ContinuousLinearMap.mul ℝ ℝ` — the
`convolution_def` unfolding; reusable version of the local equality inside
`conv3Small_continuous`); the A2 factor `chiSmall M` is `C²` with compact
support (`chiSmall_contDiff_two_hasCompactSupport`); its local integrability
(from continuity); and Mathlib's
`HasCompactSupport.contDiff_convolution_left`.
-/

noncomputable section
open MeasureTheory Metric Filter
open scoped Real Topology ContDiff
namespace Submission
set_option autoImplicit false
set_option linter.unusedVariables false
namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- `conv3Small M` is the Mathlib convolution `χ_M ⋆ χ_M` (pointwise, as
functions) — reusable form of the equality used inside
`conv3Small_continuous`. -/
lemma conv3Small_eq_convolution (M : ℕ) :
    (fun x : ℝ³ => conv3Small M x)
      = MeasureTheory.convolution (chiSmall M) (chiSmall M) (ContinuousLinearMap.mul ℝ ℝ)
          (volume : Measure ℝ³) := by
  funext x
  unfold conv3Small
  rw [MeasureTheory.convolution_def]
  simp

/-- `chiSmall M` is locally integrable (`1 ≤ M`), from continuity. -/
lemma chiSmall_locallyIntegrable {M : ℕ} (hM : 1 ≤ M) :
    MeasureTheory.LocallyIntegrable (chiSmall M) (volume : Measure ℝ³) :=
  (chiSmall_continuous hM).locallyIntegrable

/-- **A3: the cosine-M self-convolution `conv3Small M` is `C²`** (`3 ≤ M`):
convolution smoothness `HasCompactSupport.contDiff_convolution_left` with the
`C²_c` factor `chiSmall M` (A2) and its local integrability. -/
lemma conv3Small_contDiff_two {M : ℕ} (hM : 3 ≤ M) :
    ContDiff ℝ 2 (fun x : ℝ³ => conv3Small M x) := by
  have heq := conv3Small_eq_convolution M
  rw [heq]
  exact HasCompactSupport.contDiff_convolution_left (L := ContinuousLinearMap.mul ℝ ℝ)
    (chiSmall_hasCompactSupport (by omega : 1 ≤ M)) (chiSmall_contDiff_two hM)
    (chiSmall_locallyIntegrable (by omega : 1 ≤ M))

end BoseGases
end Submission
