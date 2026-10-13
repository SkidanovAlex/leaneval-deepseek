import Mathlib
import Submission.Work.WilC4aRW.Defs

namespace Work.WilC4aRW.LinEquiv

theorem shear_complexIncl {n : ℕ} (v : Fin (n + 1) → ℝ) (j : Fin (n + 1))
    (T : (Fin (n + 1) → ℝ) ≃ₗ[ℝ] (Fin (n + 1) → ℝ))
    (hT : ∀ x, T x = x + (x j) • (v - Pi.single j 1))
    (Tc : (Fin (n + 1) → ℂ) ≃ₗ[ℂ] (Fin (n + 1) → ℂ))
    (hTc : ∀ z, Tc z = z + (z j) • (Work.WilC4aRW.cplxIncl v - Pi.single j 1)) :
    ∀ y, Tc (Work.WilC4aRW.cplxIncl y) = Work.WilC4aRW.cplxIncl (T y) := by
  intro y
  rw [hTc, hT]
  ext i
  by_cases h : i = j <;>
    simp [Work.WilC4aRW.cplxIncl, Pi.single_eq_same, Pi.single_eq_of_ne, h]

end Work.WilC4aRW.LinEquiv
