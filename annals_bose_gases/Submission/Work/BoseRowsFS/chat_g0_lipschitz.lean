import ChallengeDeps
import Submission.Work.BoseGateFS.chat_W1fun_lipschitz
import Submission.Work.BoseRowsFS.chat_g0_abs_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseRowsFS

theorem chat_g0_lipschitz {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ}
    (hR : 0 < R) (hv_nonneg : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R) (p q : EuclideanSpace ℝ (Fin 3)) :
    |Work.BoseFixR.chat (Submission.BoseGases.g0 v h) p
      - Work.BoseFixR.chat (Submission.BoseGases.g0 v h) q|
      ≤ 8 * Real.pi * R * _root_.BoseGases.a v * ‖p - q‖ := by
  have hint : MeasureTheory.Integrable (Submission.BoseGases.g0 v h) :=
    Submission.BoseGases.g0_integrable hR hv_supp h
  have hsupp : ∀ x : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.g0 v h x ≠ 0 → ‖x‖ < R := by
    intro x hx
    by_contra hge
    exact hx (Submission.BoseGases.g0_zero_of_norm_ge hv_supp (not_lt.mp hge) h)
  calc |Work.BoseFixR.chat (Submission.BoseGases.g0 v h) p
        - Work.BoseFixR.chat (Submission.BoseGases.g0 v h) q|
      ≤ R * (∫ x : EuclideanSpace ℝ (Fin 3), |Submission.BoseGases.g0 v h x|) * ‖p - q‖ :=
        Work.BoseGateFS.chat_lipschitz_of_support hint hsupp p q
    _ = R * (8 * Real.pi * _root_.BoseGases.a v) * ‖p - q‖ := by
        rw [integral_abs_g0_eq hR hv_nonneg hvrad hv_supp h]
    _ = 8 * Real.pi * R * _root_.BoseGases.a v * ‖p - q‖ := by ring

end Work.BoseRowsFS
