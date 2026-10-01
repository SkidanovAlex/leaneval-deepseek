import Mathlib
import Submission.Work.LinnikBurgess.ddDefs
import Submission.Work.LinnikBurgess.cubic_phase_main

namespace Work.LinnikBurgess

theorem cubic_phase_prime_pow (p K : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p)
    (H : Polynomial ℤ) (hH : Work.LinnikBurgess.IsCubic p H) :
    ‖Commons.NumberTheory.GaussSum.Tsum (p ^ K) H‖ ≤ 8 * (p : ℝ) ^ ((2 * (K : ℝ)) / 3) := by
  obtain ⟨β, γ, δ, R, hδ, hH'⟩ := hH
  rw [hH']
  exact cubic_phase_general p hp5 K β γ δ R hδ

end Work.LinnikBurgess
