import ChallengeDeps
import Submission.Work.BoseFixB3.Eps.convI_abs_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1

theorem chooseAboxBounds {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 ℓ : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {N : ℕ} (hℓ : 0 < ℓ) {i j : Fin N} (hij : i ≠ j) :
    (∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)),
        |Classical.choose h (x i - x j)| ≤ 1)
    ∧ MeasureTheory.AEStronglyMeasurable (fun x : Submission.BoseGases.X N =>
        Classical.choose h (x i - x j))
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)) := by
  refine ⟨?_, ?_⟩
  · exact Submission.BoseGases.w0_abs_le_one_box_ae hℓ hR0 hv hvrad hv_supp h hij
  · exact Submission.BoseGases.w0_diff_aem hℓ hij (Classical.choose_spec h).2.lhs_integrable

end Work.BoseFixB1
