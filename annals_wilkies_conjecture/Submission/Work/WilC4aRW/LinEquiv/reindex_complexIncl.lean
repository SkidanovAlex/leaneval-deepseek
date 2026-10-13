import Mathlib
import Submission.Work.WilC4aRW.Defs

namespace Work.WilC4aRW.LinEquiv

theorem reindex_complexIncl {n : ℕ} (σ : Fin (n + 1) ≃ Fin (n + 1))
    (P : (Fin (n + 1) → ℝ) ≃ₗ[ℝ] (Fin (n + 1) → ℝ)) (hP : ∀ x i, P x i = x (σ i))
    (Pc : (Fin (n + 1) → ℂ) ≃ₗ[ℂ] (Fin (n + 1) → ℂ)) (hPc : ∀ x i, Pc x i = x (σ i)) :
    ∀ y, Pc (Work.WilC4aRW.cplxIncl y) = Work.WilC4aRW.cplxIncl (P y) := by
  intro y
  ext i
  simp only [Work.WilC4aRW.cplxIncl_apply]
  rw [hPc (Work.WilC4aRW.cplxIncl y) i, Work.WilC4aRW.cplxIncl_apply, hP y i]

end Work.WilC4aRW.LinEquiv
