import Mathlib
import Submission.Work.Holonomy3.model_deps

namespace Work.Holonomy3

/-- When the window `[N-D, N]` contains all of `[0, N]` (i.e. `N ≤ D`), the product
`L^{≥l}_{N,D}` of the primes `l < p ≤ N` having a multiple in the window is simply the product of
all primes in `(l, N]`, so its logarithm is `θ(N) - θ(l)`. -/
theorem log_Lge_eq_theta_sub_of_le {l N D : ℕ} (hl : l ≤ N) (hND : N ≤ D) :
    Real.log ((Submission.CDT.LcmGe.Lge l N D : ℕ) : ℝ)
      = Chebyshev.theta (N : ℝ) - Chebyshev.theta (l : ℝ) := by
  -- `N ≤ D` forces the window `[N-D, N]` to be the full interval `[0, N]`.
  have hsub : N - D = 0 := Nat.sub_eq_zero_of_le hND
  -- Hence the "has a multiple in the window" condition is automatic: `p ∣ p`.
  have hfilter : (Finset.Icc 1 N).filter
      (fun p => p.Prime ∧ l < p ∧ (∃ m ∈ (Finset.Icc (N - D) N).erase 0, p ∣ m))
      = (Finset.Icc 1 N).filter (fun p => p.Prime ∧ l < p) := by
    apply Finset.filter_congr
    intro p hp
    rw [Finset.mem_Icc] at hp
    constructor
    · intro h; exact ⟨h.1, h.2.1⟩
    · rintro ⟨hpp, hlp⟩
      refine ⟨hpp, hlp, ⟨p, ?_, dvd_rfl⟩⟩
      rw [Finset.mem_erase, Finset.mem_Icc, hsub]
      exact ⟨hpp.ne_zero, Nat.zero_le p, hp.2⟩
  rw [Submission.CDT.LcmGe.Lge_cast, hfilter]
  rw [Real.log_prod]
  · exact (Commons.NumberTheory.Chebyshev.theta_sub_theta_eq l N hl).symm
  · intro p hp
    rw [Finset.mem_filter, Finset.mem_Icc] at hp
    exact_mod_cast hp.2.1.pos.ne'

end Work.Holonomy3
