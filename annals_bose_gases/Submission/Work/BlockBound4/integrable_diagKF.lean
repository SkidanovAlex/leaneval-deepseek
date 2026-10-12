import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BlockBound4.diag_main_term_le_sharp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BlockBound4

open MeasureTheory

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

theorem integrable_diagKF {s c0 av M : ℝ} (hs : 0 < s) (hc0 : 0 < c0) (hav : 0 < av)
    (hM : 2 ≤ M) {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hWmeas : Measurable (Submission.BoseGases.d1Bcoef W))
    (hWb : ∀ q : EuclideanSpace ℝ (Fin 3),
      |Submission.BoseGases.d1Bcoef W q| ≤ 16 * Real.pi * av)
    (hInt : MeasureTheory.Integrable (fun q : EuclideanSpace ℝ (Fin 3) =>
      (Submission.BoseGases.d1Bcoef W q) ^ 2 / ‖q‖ ^ 2)) :
    MeasureTheory.Integrable (fun q : EuclideanSpace ℝ (Fin 3) =>
      Work.BlockBound4.diagKF s c0 av M W q * M) := by
  have hM0 : (0 : ℝ) ≤ M := by linarith
  have hExt : MeasureTheory.IntegrableOn
      (fun q : ℝ³ => Work.BlockBound4.diagKF s c0 av M W q * M)
      (Submission.BoseGases.d1Ext c0) volume :=
    integrableOn_diagKF_ext hs hc0 hav hM0 hWmeas hWb hInt
  have hInt' : MeasureTheory.IntegrableOn
      (fun q : ℝ³ => Work.BlockBound4.diagKF s c0 av M W q * M)
      (Submission.BoseGases.d1Int c0) volume :=
    integrableOn_diagKF_int hs hc0 hav hM0 hWmeas hWb
  rw [← MeasureTheory.integrableOn_univ, ← Submission.BoseGases.d1Int_union_d1Ext c0,
    MeasureTheory.integrableOn_union]
  exact ⟨hInt', hExt⟩

end Work.BlockBound4
