import Mathlib
import Submission.Work.WilC4aCS.Defs
import Submission.Work.WilC4aCS.rotSq_eq_zero_iff

namespace Work.WilC4aCS

/-- The pointwise criterion `rotSq_eq_zero_iff` upgrades to a neighbourhood statement: `rotSq ψ`
vanishes near the origin if and only if every `rotTerm ψ · a b` vanishes near the origin.

This is the "sum of squares vanishes eventually" bookkeeping used when the radial-orthogonality
defect is produced by a critical-point argument: locally `rotSq = 0` is exactly the conjunction of
the finitely many local conditions `rotTerm a b = 0`. -/
theorem rotSq_eq_zero_of_eventually {m : ℕ} (ψ : (Fin m → ℝ) → ℝ) :
    (∀ᶠ x in nhds (0 : Fin m → ℝ), Work.WilC4aCS.rotSq ψ x = 0) ↔
      ∀ a b : Fin m, ∀ᶠ x in nhds (0 : Fin m → ℝ), Work.WilC4aCS.rotTerm ψ x a b = 0 := by
  constructor
  · intro h a b
    filter_upwards [h] with x hx
    exact (rotSq_eq_zero_iff ψ x).mp hx a b
  · intro h
    have h' : ∀ᶠ x in nhds (0 : Fin m → ℝ),
        ∀ a b : Fin m, Work.WilC4aCS.rotTerm ψ x a b = 0 := by
      rw [Filter.eventually_all]
      exact fun a => by rw [Filter.eventually_all]; exact h a
    filter_upwards [h'] with x hx
    exact (rotSq_eq_zero_iff ψ x).mpr hx

end Work.WilC4aCS
