import Mathlib
import Submission.Work.BourgainPlan.Oscillation.Lacunary.defs
import Submission.Work.BourgainPlan.Oscillation.Lacunary.bb_estimates
import Submission.Work.Analysis.Geometric.tsum_min_geometric_le

namespace Work.BourgainPlan.Oscillation.Lacunary

theorem boundary_tsum_sq_le (ρ : ℝ) (hρ : 1 < ρ) :
    ∃ B : ℝ, 0 < B ∧ ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      ∑' i : ℕ, ‖Work.BourgainPlan.Oscillation.Lacunary.bb ρ i θ‖ ^ 2 ≤ B := by
  have hρ0 : 0 < ρ := by linarith
  have hr4 : (1:ℝ) < ρ^4 := one_lt_pow₀ hρ (by norm_num)
  have hden : 0 < ρ^4 - 1 := by linarith
  refine ⟨Cpt * (2*ρ^4/(ρ^4-1)) + 1, ?_, ?_⟩
  · have h1 : 0 < Cpt * (2*ρ^4/(ρ^4-1)) := by
      apply mul_pos Cpt_pos
      exact div_pos (by positivity) hden
    linarith
  · intro θ hθ0 hθ1
    have hgeom := Work.Analysis.Geometric.tsum_min_geometric_le (ρ^4) (θ^4) hr4 (by positivity)
    have hmaj : Summable (fun i : ℕ => Cpt * min (θ^4*(ρ^4)^i) ((θ^4)⁻¹*((ρ^4)⁻¹)^i)) :=
      hgeom.1.mul_left Cpt
    have hpt : ∀ i : ℕ, ‖bb ρ i θ‖^2 ≤ Cpt * min (θ^4*(ρ^4)^i) ((θ^4)⁻¹*((ρ^4)⁻¹)^i) := by
      intro i
      have h := bb_sq_le_cc ρ hρ i θ hθ0 hθ1
      rwa [min_cc_eq ρ i θ] at h
    have hf : Summable (fun i : ℕ => ‖bb ρ i θ‖^2) :=
      Summable.of_nonneg_of_le (fun i => sq_nonneg _) hpt hmaj
    calc ∑' i : ℕ, ‖bb ρ i θ‖^2
        ≤ ∑' i : ℕ, Cpt * min (θ^4*(ρ^4)^i) ((θ^4)⁻¹*((ρ^4)⁻¹)^i) :=
          Summable.tsum_le_tsum hpt hf hmaj
      _ = Cpt * ∑' i : ℕ, min (θ^4*(ρ^4)^i) ((θ^4)⁻¹*((ρ^4)⁻¹)^i) := tsum_mul_left
      _ ≤ Cpt * (2*ρ^4/(ρ^4-1)) :=
          mul_le_mul_of_nonneg_left hgeom.2 Cpt_pos.le
      _ ≤ Cpt * (2*ρ^4/(ρ^4-1)) + 1 := le_add_of_nonneg_right zero_le_one

end Work.BourgainPlan.Oscillation.Lacunary
