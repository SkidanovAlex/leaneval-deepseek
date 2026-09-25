import Mathlib
import Submission.Work.BourgainPlan.Oscillation.lacunary_defs
import Submission.Work.BourgainPlan.Oscillation.lacunary_truncated_maximal_l2
import Submission.Work.BourgainPlan.Oscillation.oscZ_lacunary_defs
import Submission.Work.BourgainPlan.Oscillation.polyBlockCoreN_eq_weighted
import Submission.Work.BourgainPlan.Oscillation.poly_cutoff_N
import Submission.Work.BourgainPlan.Oscillation.nbrhd_maximal_lacunary
import Submission.Work.BourgainPlan.Oscillation.oscZ_core_lacunary
import Submission.Work.BourgainPlan.Oscillation.polyActIdxN_card_le_one_pow
import Submission.Work.BourgainPlan.Oscillation.oscZ_err_lacunary
import Submission.Work.BourgainPlan.Oscillation.lacScale_radii_window_count
import Submission.Work.BourgainPlan.Oscillation.lacScale_cutoff_exists
import Submission.Work.BourgainPlan.Oscillation.oscZ_block_lacunary_v2_core
import Submission.Work.BourgainPlan.Maximal.model_maximal_pre

namespace Work.BourgainPlan.Oscillation

/-- **The per-block oscillation inequality at the lacunary scales.** -/
theorem oscZ_block_lacunary_v2 (P : Polynomial ℤ) (hc : 0 < P.leadingCoeff)
    (hd : 2 ≤ P.natDegree) (ρ : ℝ) (hρ : 1 < ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (g : ℤ → ℂ) (s : Finset ℤ),
      (∀ n, n ∉ s → g n = 0) →
      ∀ (J : ℕ) (k : ℕ → ℕ), StrictMono k →
        Work.BourgainPlan.Oscillation.oscZ
            (fun i x => Work.BourgainPlan.Oscillation.polyModelBlockOp P g s m
              (Work.BourgainPlan.Oscillation.lacScale ρ i) x) J k
          ≤ ENNReal.ofReal (C * (2:ℝ)^(-(m:ℝ) * Work.BourgainPlan.Maximal.polySig P)
                * ((m:ℝ)+2)^2) ^ 2 *
              ∫⁻ x : ℤ, ‖g x‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count := by
  obtain ⟨K₁, _hK₁, hcut⟩ := poly_cutoff_N P hc hd
  refine oscZ_block_lacunary_v2_core P hc hd ρ hρ K₁ ?_ ?_ ?_ ?_ ?_
  · intro m N hN h4m
    exact ⟨(hcut m N hN h4m).1, (hcut m N hN h4m).2.1, (hcut m N hN h4m).2.2⟩
  · exact lacScale_cutoff_exists ρ hρ K₁
  · exact oscZ_core_lacunary (nbrhd_maximal_lacunary Work.BourgainPlan.Maximal.circleNeighborhoodMaximal_univ)
  · exact oscZ_err_lacunary P hc hd ρ hρ (polyActIdxN_card_le_one_pow P hd)
  · exact lacScale_radii_window_count P hd ρ hρ

end Work.BourgainPlan.Oscillation
