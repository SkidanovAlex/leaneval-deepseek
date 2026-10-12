import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1B.sectorCountBoxAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.PBW_nonneg`

FS's per-box mass `∬ w_{1,B(u)} = PBW h μ u` is nonnegative — at **every** `μ` and every `u`, with
no admissibility hypothesis: the kernel `wSmall1Pair` is pointwise nonnegative, so the statement is
two applications of `integral_nonneg_of_ae` (`Work.BoseFixB1.w1MassB_nonneg` without its unused
positivity hypotheses on `ℓ`, `d`).
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixB1B

open _root_.BoseGases Submission.BoseGases Work.SmallBoxSliding Work.BoseFixB1

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **`PBW h μ u = ∬ w_{1,B(u)} ≥ 0`**, for every `μ` and `u`. -/
theorem PBW_nonneg {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (μ : ℝ) (u : E3) :
    0 ≤ PBW h μ u := by
  rw [PBW, Work.BoseFixB1.w1MassB]
  have hinner : ∀ x : E3,
      0 ≤ ∫ y : E3, Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u x y := by
    intro x
    apply integral_nonneg_of_ae
    filter_upwards
      [Work.SmallBoxSliding.ae_g0_comp_sub hv hvrad hv_supp hR h x] with y hy
    simp only [Submission.BoseGases.wSmall1Pair, Submission.BoseGases.wSmallPair,
      Submission.BoseGases.wSmallScaled]
    exact mul_nonneg
      (mul_nonneg (Work.SmallBoxSliding.chiSmallB_nonneg (PBM v μ) (PBℓ v μ) (PBd v μ) u x)
        (div_nonneg
          (div_nonneg hy
            (Work.SmallBoxSliding.convScaleSmall_nonneg (PBM v μ) (PBℓ v μ * PBd v μ) (x - y)))
          (Submission.BoseGases.convScale_nonneg (PBℓ v μ) (x - y))))
      (Work.SmallBoxSliding.chiSmallB_nonneg (PBM v μ) (PBℓ v μ) (PBd v μ) u y)
  exact integral_nonneg_of_ae (Filter.Eventually.of_forall hinner)

end Work.BoseFixB1B
