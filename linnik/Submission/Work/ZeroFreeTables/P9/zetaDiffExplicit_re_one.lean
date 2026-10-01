import Mathlib
import Submission.Work.ZeroFreeTables.P9.zetaDiffExplicit_gen
import Submission.Work.ZeroFreeTables.P9.tsum_inv_add_two_shift

namespace Work.ZeroFreeTables.P9

open scoped Classical BigOperators

theorem zetaDiffExplicit_re_one {s : ℂ} (hs : 1 < s.re) :
    (iteratedDeriv 1 (logDeriv riemannZeta) s).re
      = ((1 / (s - 1)) ^ 2).re
        - (∑' u : ℂ, (analyticOrderNatAt completedRiemannZeta u : ℝ) * ((1 / (s - u)) ^ 2).re)
        - (∑' n : ℕ, ((1 / (s + ((2 * (n + 1) : ℕ) : ℂ))) ^ 2).re) := by
  obtain ⟨hsumA, heq⟩ := zetaDiffExplicit_gen 1 le_rfl hs
  obtain ⟨hsumB0, -⟩ := tsum_inv_add_two_shift 1 le_rfl hs
  have hsumB : Summable (fun n : ℕ => (1 / (s + ((2 * (n + 1) : ℕ) : ℂ))) ^ 2) :=
    (summable_nat_add_iff (f := fun n : ℕ => (1 / (s + ((2 * n : ℕ) : ℂ))) ^ 2) 1).mpr hsumB0
  -- clean form of the complex identity
  have hkey : (∑' u : ℂ, (analyticOrderNatAt completedRiemannZeta u : ℂ) * (1 / (s - u)) ^ 2)
      + (∑' n : ℕ, (1 / (s + ((2 * (n + 1) : ℕ) : ℂ))) ^ 2)
      = - iteratedDeriv 1 (logDeriv riemannZeta) s + 1 / (s - 1) ^ 2 := by
    simpa using heq
  -- take real parts
  have h2 : (∑' u : ℂ, ((analyticOrderNatAt completedRiemannZeta u : ℂ) * (1 / (s - u)) ^ 2).re)
      + (∑' n : ℕ, ((1 / (s + ((2 * (n + 1) : ℕ) : ℂ))) ^ 2).re)
      = - (iteratedDeriv 1 (logDeriv riemannZeta) s).re + (1 / (s - 1) ^ 2).re := by
    have h := congrArg Complex.re hkey
    rw [Complex.add_re, Complex.re_tsum hsumA, Complex.re_tsum hsumB, Complex.add_re,
      Complex.neg_re] at h
    exact h
  -- identify the first series with the real-multiplicity series
  have hAeq : (∑' u : ℂ, ((analyticOrderNatAt completedRiemannZeta u : ℂ) * (1 / (s - u)) ^ 2).re)
      = ∑' u : ℂ, (analyticOrderNatAt completedRiemannZeta u : ℝ) * ((1 / (s - u)) ^ 2).re :=
    tsum_congr fun u => by simp [Complex.mul_re]
  rw [hAeq] at h2
  rw [one_div_pow]
  linarith [h2]

end Work.ZeroFreeTables.P9
