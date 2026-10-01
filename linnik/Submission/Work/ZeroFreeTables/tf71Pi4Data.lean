import Mathlib
import Submission.Work.ZeroFreeTables.testFn7_1
import Submission.Work.ZeroFreeTables.Engine

namespace Work.ZeroFreeTables

/-- The two facts about `π/4` used throughout: it lies in `(0, π/2)`. -/
theorem tf71Pi4_mem : (0:ℝ) < Real.pi / 4 ∧ Real.pi / 4 < Real.pi / 2 :=
  ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩

theorem tf71Pi4Data (lam : ℝ) (hlam : 0 < lam) :
    (∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Set.Ioo (0:ℝ) (2 * Work.ZeroFreeTables.tf71γ (Real.pi / 4) lam),
        ‖iteratedDeriv 2 (Work.ZeroFreeTables.tf71f (Real.pi / 4) lam) t‖ ≤ B) ∧
      ContinuousOn (Work.ZeroFreeTables.tf71f (Real.pi / 4) lam) (Set.Ici 0) ∧
      (∀ t : ℝ, 2 * Work.ZeroFreeTables.tf71γ (Real.pi / 4) lam ≤ t →
        Work.ZeroFreeTables.tf71f (Real.pi / 4) lam t = 0) ∧
      ContDiffOn ℝ 2 (Work.ZeroFreeTables.tf71f (Real.pi / 4) lam)
        (Set.Ioo 0 (2 * Work.ZeroFreeTables.tf71γ (Real.pi / 4) lam)) ∧
      0 < Work.ZeroFreeTables.tf71f (Real.pi / 4) lam 0 ∧
      (∀ t : ℝ, 0 ≤ Work.ZeroFreeTables.tf71f (Real.pi / 4) lam t) ∧
      (∀ z : ℂ, 0 ≤ z.re → 0 ≤ (∫ t in (0:ℝ)..(2 * Work.ZeroFreeTables.tf71γ (Real.pi / 4) lam),
          Complex.exp (-(z * (t : ℂ))) *
            ((Work.ZeroFreeTables.tf71f (Real.pi / 4) lam t : ℝ) : ℂ)).re) := by
  obtain ⟨hθ0, hθ1⟩ := tf71Pi4_mem
  have hγpos : 0 < tf71γ (Real.pi / 4) lam := tf71γ_pos hθ0 hθ1 hlam
  refine ⟨tf71f_bound (Real.pi / 4) lam hγpos,
    tf71f_cont (Real.pi / 4) lam,
    fun t ht => tf71f_supp hθ0 hθ1 hlam t ht,
    tf71f_diff (Real.pi / 4) lam hγpos,
    tf71f_zero_pos (Real.pi / 4) lam hθ0 hθ1 hlam,
    tf71f_nonneg (Real.pi / 4) lam hθ0 hθ1 hlam,
    fun z hz => ?_⟩
  simpa only [tf71Fc] using tf71Fc_re_nonneg (Real.pi / 4) lam hθ0 hθ1 hlam z hz

end Work.ZeroFreeTables
