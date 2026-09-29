import Mathlib
import Submission.Work.TMContract.Defs

namespace Work.TMContract.Gluing

open Filter

/-- **Contract lemma 3.**  `LiouvilleAbove α b` (`b > 0`) says that for arbitrarily large
`q` the distance `fracDist (qα) = |qα - round (qα)|` from `qα` to the nearest integer is
below `e^{-bq}`.  Divided by `q` this is exactly the distance from `α` to the rational
`round (qα)/q`, so the approximants `round (qα)/q` are good for every prescribed accuracy
`δ` and follow the Liouville rate `e^{-bq}`. -/
theorem liouville_nearest_int {α b δ : ℝ} (hb : 0 < b) (hLiou : Work.TMContract.LiouvilleAbove α b)
    (hδ : 0 < δ) (Q : ℕ) :
    ∃ᶠ q : ℕ in Filter.atTop, max Q 1 ≤ q ∧
      |α - (round ((q : ℝ) * α) : ℝ) / (q : ℝ)| < δ / (q : ℝ) ∧
      |α - (round ((q : ℝ) * α) : ℝ) / (q : ℝ)| < Real.exp (-(b * q)) / (q : ℝ) := by
  -- the threshold `max Q 1` is eventually exceeded,
  have h1 : ∀ᶠ q : ℕ in Filter.atTop, max Q 1 ≤ q :=
    Filter.eventually_atTop.2 ⟨max Q 1, fun q hq => hq⟩
  -- and `e^{-bq} < δ` eventually because `b > 0` and `δ > 0`,
  have h2 : ∀ᶠ q : ℕ in Filter.atTop, Real.exp (-(b * (q:ℝ))) < δ := by
    have hg : Filter.Tendsto (fun q : ℕ => b * (q:ℝ)) Filter.atTop Filter.atTop :=
      Filter.Tendsto.const_mul_atTop hb tendsto_natCast_atTop_atTop
    have ht : Filter.Tendsto (fun q : ℕ => Real.exp (-(b * (q:ℝ)))) Filter.atTop (nhds 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp hg
    exact ht.eventually (isOpen_Iio.mem_nhds hδ)
  -- while `fracDist (qα) < e^{-bq}` frequently by hypothesis.
  refine ((hLiou.and_eventually h2).and_eventually h1).mono ?_
  rintro q ⟨⟨hq3, hq2⟩, hq1⟩
  have hq1' : (1:ℕ) ≤ q := le_trans (le_max_right Q 1) hq1
  have hqle : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq1'
  have hqpos : (0:ℝ) < (q:ℝ) := lt_of_lt_of_le one_pos hqle
  -- `α - round(qα)/q = (qα - round(qα))/q`,
  have hkey : α - (round ((q:ℝ)*α) : ℝ)/(q:ℝ)
      = ((q:ℝ)*α - (round ((q:ℝ)*α) : ℝ))/(q:ℝ) := by
    field_simp
  -- hence its absolute value is exactly `fracDist (qα)/q`
  have hnorm : |α - (round ((q:ℝ)*α) : ℝ)/(q:ℝ)|
      = Work.TMContract.fracDist ((q:ℝ)*α) / (q:ℝ) := by
    rw [hkey, abs_div, abs_of_pos hqpos]
    rfl
  refine ⟨hq1, ?_, ?_⟩
  · rw [hnorm]
    exact div_lt_div_of_pos_right (lt_trans hq3 hq2) hqpos
  · rw [hnorm]
    exact div_lt_div_of_pos_right hq3 hqpos

end Work.TMContract.Gluing
