import Mathlib
import Submission.Work.PL.Defs

namespace Work.Geo.DualStretch

/-- A finite affinely independent set of points of `ℝⁿ` becomes a linearly independent family in
`ℝⁿ × ℝ` after appending the coordinate `1`. -/
theorem linearIndependent_prod_one {n : ℕ} {σ : Finset (PL.E n)}
    (hσ : AffineIndependent ℝ ((↑) : σ → PL.E n)) :
    LinearIndependent ℝ (fun w : σ => (((w : PL.E n), (1 : ℝ)) : PL.E n × ℝ)) := by
  rw [linearIndependent_iff']
  intro s g hg i hi
  -- second coordinate: `∑ g j = 0`
  have hg1 : ∑ j ∈ s, g j = 0 := by
    have h := congrArg Prod.snd hg
    rw [Prod.snd_sum] at h
    simpa [Prod.smul_snd] using h
  -- first coordinate: `∑ g j • j = 0`
  have hg2 : ∑ j ∈ s, g j • (j : PL.E n) = 0 := by
    have h := congrArg Prod.fst hg
    rw [Prod.fst_sum] at h
    simpa [Prod.smul_fst] using h
  refine hσ s g hg1 ?_ i hi
  rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero s g _ hg1 (0 : PL.E n),
    Finset.weightedVSubOfPoint_apply s g _ (0 : PL.E n)]
  simpa using hg2

end Work.Geo.DualStretch
