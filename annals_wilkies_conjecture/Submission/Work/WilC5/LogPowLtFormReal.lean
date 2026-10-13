import Mathlib
import Submission.Work.WilC5.LogPwDefs
import Submission.Work.WilC5.LogFunReal

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

namespace Work.WilC5

theorem LogPowLtFormReal (N k : ℕ)
    (hN : ∀ x : ℝ, (N : ℝ) < x → (Real.log x) ^ k < x) (xs : Fin 2 → ℝ) :
    (Work.WilC5.logPowLtForm N k).Realize (Work.WilC5.emptyVar : Empty → ℝ) xs := by
  rw [Work.WilC5.logPowLtForm_realize]
  rintro ⟨h1, h2⟩
  rw [Work.WilC5.leE_real, Work.WilC5.numTerm_realize_real, not_le] at h1
  rw [Work.WilC5.leE_real, not_le, Work.WilC5.powTerm_realize_real]
  have h21 : Term.realize (Sum.elim (Work.WilC5.emptyVar : Empty → ℝ) xs)
      (Work.WilC5.v2 1) = xs 1 := by
    simp [Work.WilC5.v2]
  rw [h21]
  rcases (Work.WilC5.logDefSet_real (xs 0) (xs 1)).mp h2 with ⟨hpos, hlog⟩ | ⟨hle, hzero⟩
  · rw [hlog]; exact hN (xs 0) h1
  · exact absurd h1 (not_lt.mpr (le_trans hle (by positivity)))

end Work.WilC5
