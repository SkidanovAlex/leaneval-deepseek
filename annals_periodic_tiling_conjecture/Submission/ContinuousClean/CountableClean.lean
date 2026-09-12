import Mathlib
import ChallengeDeps

open PeriodicTilingConjecture
open Filter Bornology MeasureTheory
open scoped Pointwise

namespace Submission.ContinuousClean

theorem countable_clean
    {d : ℕ} {Λ : Set (Fin d → ℝ)} (hΛ : IsPeriodicContinuousTilingSet Λ) :
    Λ.Countable := by
  classical
  rcases hΛ with ⟨L, hdisc, hlatt, s, rfl⟩
  letI : DiscreteTopology L := hdisc
  letI : IsZLattice ℝ L := hlatt
  have hLcount : (L : Set (Fin d → ℝ)).Countable := by
    have hcount : Countable L := by
      letI : Module.Finite ℤ L := ZLattice.module_finite ℝ L
      exact Finsupp.Countable.of_moduleFinite (R := ℤ) (M := L)
    exact Set.to_countable (L : Set (Fin d → ℝ))
  have hscount : (s : Set (Fin d → ℝ)).Countable := s.countable_toSet
  rw [show (s + L : Set (Fin d → ℝ)) =
      Set.image2 (fun a b : Fin d → ℝ => a + b) (s : Set (Fin d → ℝ)) (L : Set (Fin d → ℝ)) by
    rfl]
  exact Set.Countable.image2 hscount hLcount _

end Submission.ContinuousClean
