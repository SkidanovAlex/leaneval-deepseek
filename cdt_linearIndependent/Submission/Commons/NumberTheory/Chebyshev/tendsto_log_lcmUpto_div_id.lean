import Mathlib
import Submission.Commons.NumberTheory.PrimeNumberTheorem.psi_isEquivalent

namespace Commons.NumberTheory.Chebyshev

open Filter Asymptotics
open scoped Topology

theorem tendsto_log_lcmUpto_div_id :
    Filter.Tendsto (fun n : ℕ => Real.log ((Nat.lcmUpto n : ℕ) : ℝ) / (n : ℝ)) Filter.atTop
      (nhds 1) := by
  -- For natural `x`, `ψ x = log (lcmUpto x)`, so it suffices to show `ψ x / x → 1`.
  have hne : ∀ᶠ x : ℝ in atTop, x ≠ 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact ne_of_gt hx
  have hpsi : Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (nhds 1) :=
    (isEquivalent_iff_tendsto_one (l := atTop) (u := fun x : ℝ => Chebyshev.psi x)
      (v := fun x : ℝ => x) hne).mp
      Commons.NumberTheory.PrimeNumberTheorem.psi_isEquivalent
  have hcomp : Tendsto (fun n : ℕ => Chebyshev.psi ((n : ℕ) : ℝ) / (n : ℝ)) atTop (nhds 1) :=
    hpsi.comp tendsto_natCast_atTop_atTop
  simpa only [Chebyshev.psi_eq_log_lcmUpto] using hcomp

end Commons.NumberTheory.Chebyshev
