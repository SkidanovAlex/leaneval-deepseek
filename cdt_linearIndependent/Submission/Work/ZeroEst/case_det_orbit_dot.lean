import Mathlib
import Submission.Work.ZeroEst.one_var_defs

namespace Work.ZeroEst

/-- Iterated form of the fundamental identity `⟨ΛQ, f⟩ = θ⟨Q, f⟩` (`Lam_dot`):
the `k`-th `Λ`-orbit of a polynomial coefficient vector `P` tested against the
`D`-closed system `f` equals the `k`-fold application of `θ = q·d/dx` to the
starting combination `∑ i, Pᵢ fᵢ`. -/
theorem case_det_orbit_dot (m : ℕ) (q : Polynomial ℚ) (A : Fin m → Fin m → Polynomial ℚ)
    (f : Fin m → PowerSeries ℚ)
    (hrel : ∀ i, (q : PowerSeries ℚ) * PowerSeries.derivative (R := ℚ) (f i)
      = ∑ j, (A i j : PowerSeries ℚ) * f j)
    (P : Fin m → Polynomial ℚ) (k : ℕ) :
    (∑ i, ((Work.ZeroEst.orbit q A P k) i : PowerSeries ℚ) * f i)
      = ((fun S => (q : PowerSeries ℚ) * PowerSeries.derivative (R := ℚ) S)^[k])
          (∑ i, (P i : PowerSeries ℚ) * f i) := by
  induction k with
  | zero => simp [orbit_zero]
  | succ k ih =>
      rw [orbit_succ, Lam_dot q A f hrel (orbit q A P k), ih,
        Function.iterate_succ_apply']

end Work.ZeroEst
