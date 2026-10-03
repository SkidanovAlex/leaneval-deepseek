import Mathlib
import Submission.Work.HornSC.CellBoundaryJordan.BlockDefs

namespace Work.HornSC.CellBoundaryJordan

/-- If `R` contains the closed lattice rectangle `[a,c] × [b,d]` (as a subset of `ℂ`) and
`z` is strictly inside it, then a small open ball around `z` is contained in `R`. -/
lemma exists_ball_subset_of_rect {R : Set ℂ} {z : ℂ} {a c b d : ℤ}
    (haz : (a : ℝ) < z.re) (hzc : z.re < (c : ℝ))
    (hbz : (b : ℝ) < z.im) (hzd : z.im < (d : ℝ))
    (hR : ∀ w : ℂ, (a : ℝ) ≤ w.re → w.re ≤ (c : ℝ) → (b : ℝ) ≤ w.im → w.im ≤ (d : ℝ) → w ∈ R) :
    ∃ r : ℝ, 0 < r ∧ ∀ w : ℂ, ‖w - z‖ < r → w ∈ R := by
  refine ⟨min (min (z.re - (a:ℝ)) ((c:ℝ) - z.re)) (min (z.im - (b:ℝ)) ((d:ℝ) - z.im)), ?_, ?_⟩
  · refine lt_min (lt_min ?_ ?_) (lt_min ?_ ?_) <;> linarith
  · intro w hw
    have hre : |w.re - z.re| ≤ ‖w - z‖ := by
      have h := Complex.abs_re_le_norm (w - z); simpa using h
    have him : |w.im - z.im| ≤ ‖w - z‖ := by
      have h := Complex.abs_im_le_norm (w - z); simpa using h
    have habsr : |w.re - z.re| <
        min (min (z.re - (a:ℝ)) ((c:ℝ) - z.re)) (min (z.im - (b:ℝ)) ((d:ℝ) - z.im)) :=
      lt_of_le_of_lt hre hw
    have habsi : |w.im - z.im| <
        min (min (z.re - (a:ℝ)) ((c:ℝ) - z.re)) (min (z.im - (b:ℝ)) ((d:ℝ) - z.im)) :=
      lt_of_le_of_lt him hw
    have hr1 : min (min (z.re - (a:ℝ)) ((c:ℝ) - z.re)) (min (z.im - (b:ℝ)) ((d:ℝ) - z.im)) ≤
        z.re - (a:ℝ) := le_trans (min_le_left _ _) (min_le_left _ _)
    have hr2 : min (min (z.re - (a:ℝ)) ((c:ℝ) - z.re)) (min (z.im - (b:ℝ)) ((d:ℝ) - z.im)) ≤
        (c:ℝ) - z.re := le_trans (min_le_left _ _) (min_le_right _ _)
    have hr3 : min (min (z.re - (a:ℝ)) ((c:ℝ) - z.re)) (min (z.im - (b:ℝ)) ((d:ℝ) - z.im)) ≤
        z.im - (b:ℝ) := le_trans (min_le_right _ _) (min_le_left _ _)
    have hr4 : min (min (z.re - (a:ℝ)) ((c:ℝ) - z.re)) (min (z.im - (b:ℝ)) ((d:ℝ) - z.im)) ≤
        (d:ℝ) - z.im := le_trans (min_le_right _ _) (min_le_right _ _)
    refine hR w ?_ ?_ ?_ ?_ <;> linarith [le_abs_self (w.re - z.re), neg_le_abs (w.re - z.re),
      le_abs_self (w.im - z.im), neg_le_abs (w.im - z.im)]

end Work.HornSC.CellBoundaryJordan
