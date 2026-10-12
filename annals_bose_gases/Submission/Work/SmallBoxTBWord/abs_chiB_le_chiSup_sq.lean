import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.SmallBoxTBWord.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxTBWord

/-- The sliding window `χ_{B(u)} = χ(x/ℓ)·χ(x/(ℓd) − u)` is bounded by
`chiSup ^ 2`: both factors are dilates of the corpus cutoff `χ`, whose
sup-bound is `chiSup` (`Submission.BoseGases.abs_chiScale_le_chiSup`), and
`chiSup ≥ 0`. -/
theorem abs_chiB_le_chiSup_sq {ℓ d : ℝ} (u x : EuclideanSpace ℝ (Fin 3)) :
    |Submission.BoseGases.chiB ℓ d u x| ≤ Submission.BoseGases.chiSup ^ 2 := by
  have h1 : |Submission.BoseGases.chiScale ℓ x| ≤ Submission.BoseGases.chiSup :=
    Submission.BoseGases.abs_chiScale_le_chiSup ℓ x
  have h2 : |Submission.BoseGases.chiScale (ℓ * d) (x - (ℓ * d) • u)| ≤
      Submission.BoseGases.chiSup :=
    Submission.BoseGases.abs_chiScale_le_chiSup (ℓ * d) _
  have h := mul_le_mul h1 h2 (abs_nonneg _)
    (le_of_lt Submission.BoseGases.chiSup_pos)
  rw [Submission.BoseGases.chiB, abs_mul, pow_two]
  exact h

end Work.SmallBoxTBWord
