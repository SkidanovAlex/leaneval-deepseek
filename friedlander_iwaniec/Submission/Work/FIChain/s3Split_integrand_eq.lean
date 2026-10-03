import Mathlib
import Submission.Work.FIChain.s3SplitDefs

namespace Work.FIChain

set_option autoImplicit false
set_option maxHeartbeats 800000

open Finset
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The `(1.7)`-split of the `λ⁺` level integrand, as a pointwise algebraic identity:
the MAIN integrand `μ d · g̃(ℓd)·(Ã(m₂) − Ã(m₁))` plus the REM integrand
`μ d ·(r̃(ℓd,m₂) − r̃(ℓd,m₁))` sum to `μ d ·(g̃(ℓd)·Ã(m₂) + r̃(ℓd,m₂) − (g̃(ℓd)·Ã(m₁) + r̃(ℓd,m₁)))`,
and dividing by `u` distributes over the two sums. -/
theorem s3Split_integrand_eq (x : ℕ) (z sz : ℝ) (Cm : ℕ) (ℓ : ℕ) (u : ℝ) :
    (∑ d ∈ Finset.Icc 1 ⌊u⌋₊, (ArithmeticFunction.moebius d : ℝ) *
      (Submission.ASP.FIgtil (ℓ * d) * Work.FIChain.AcountAtilC ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊
        + Submission.ASP.rtildeFull Submission.ASP.FIr Submission.ASP.FIg Submission.ASP.FIgtil Submission.ASP.FIa (ℓ * d) ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊
        - (Submission.ASP.FIgtil (ℓ * d) * Work.FIChain.AcountAtilC ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊
          + Submission.ASP.rtildeFull Submission.ASP.FIr Submission.ASP.FIg Submission.ASP.FIgtil Submission.ASP.FIa (ℓ * d) ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊))) / u
      = Work.FIChain.s3MainI x z sz Cm ℓ u / u + Work.FIChain.s3RemI x z sz Cm ℓ u / u := by
  simp only [s3MainI, s3RemI]
  have hsum :
      (∑ d ∈ Finset.Icc 1 ⌊u⌋₊, (ArithmeticFunction.moebius d : ℝ) *
        (Submission.ASP.FIgtil (ℓ * d) * Work.FIChain.AcountAtilC ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊
          + Submission.ASP.rtildeFull Submission.ASP.FIr Submission.ASP.FIg Submission.ASP.FIgtil Submission.ASP.FIa (ℓ * d) ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊
          - (Submission.ASP.FIgtil (ℓ * d) * Work.FIChain.AcountAtilC ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊
            + Submission.ASP.rtildeFull Submission.ASP.FIr Submission.ASP.FIg Submission.ASP.FIgtil Submission.ASP.FIa (ℓ * d) ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊)))
      = (∑ d ∈ Finset.Icc 1 ⌊u⌋₊, (ArithmeticFunction.moebius d : ℝ) *
          Submission.ASP.FIgtil (ℓ * d) *
            (Work.FIChain.AcountAtilC ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊
              - Work.FIChain.AcountAtilC ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊))
        + (∑ d ∈ Finset.Icc 1 ⌊u⌋₊, (ArithmeticFunction.moebius d : ℝ) *
            (Submission.ASP.rtildeFull Submission.ASP.FIr Submission.ASP.FIg Submission.ASP.FIgtil Submission.ASP.FIa (ℓ * d) ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊
              - Submission.ASP.rtildeFull Submission.ASP.FIr Submission.ASP.FIg Submission.ASP.FIgtil Submission.ASP.FIa (ℓ * d) ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun d _ => by ring)
  rw [hsum, add_div]

end

end Work.FIChain
