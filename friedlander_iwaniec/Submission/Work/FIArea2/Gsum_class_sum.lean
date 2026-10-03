import Mathlib
import Submission.Work.FIArea2.CCountPoissonDefs
import Submission.Work.FIArea2.G8Defs

namespace Work.FIArea2

open Finset
open scoped BigOperators

/-- The product sum over the residue square `[0,|Δ|)²` written as an iterated sum, with the
summand normalised: `Xof z₁ z₂ (γ₁,γ₂)` unfolded (`Xof_re`, `Xof_im`) and the exponential factor
written out (`eGam`). -/
private lemma Gsum_class_sum_iterated (z1 z2 : GaussianInt) (h1 h2 : ℤ) :
    (∑ γ ∈ Finset.range (Work.FIPlan.absDelta z1 z2)
            ×ˢ Finset.range (Work.FIPlan.absDelta z1 z2),
        (if (Work.FIArea2.Xof z1 z2 ((γ.1 : ℤ), (γ.2 : ℤ))).re
                % ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℤ) = 0
              ∧ (Work.FIArea2.Xof z1 z2 ((γ.1 : ℤ), (γ.2 : ℤ))).im
                % ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℤ) = 0
          then Work.FIArea2.eGam (Work.FIPlan.absDelta z1 z2) γ h1 h2 else 0))
      = (∑ γ1 ∈ Finset.range (Work.FIPlan.absDelta z1 z2),
          ∑ γ2 ∈ Finset.range (Work.FIPlan.absDelta z1 z2),
            (if ((γ1 : ℤ) ^ 2 * z2.re - (γ2 : ℤ) ^ 2 * z1.re)
                    % ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℤ) = 0
                  ∧ ((γ1 : ℤ) ^ 2 * z2.im - (γ2 : ℤ) ^ 2 * z1.im)
                    % ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℤ) = 0
              then Complex.exp (2 * Real.pi * Complex.I
                * ((((γ1 : ℤ) * h1 + (γ2 : ℤ) * h2 : ℤ)) : ℝ)
                  / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)) else 0)) := by
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
  simp only [Work.FIArea2.Xof_re, Work.FIArea2.Xof_im, Work.FIArea2.eGam]

/-- **The class sum identity (6.10)**: summing the exponential factor over the admissible classes
modulo `m = |Δ|` and multiplying by `m` recovers `m·G(h₁,h₂)`, i.e. the arithmetic sum `Gsum`
of (6.10) is exactly the class sum normalised by `m⁻¹`. -/
theorem Gsum_class_sum (z1 z2 : GaussianInt) (hm : Work.FIPlan.absDelta z1 z2 ≠ 0) (h1 h2 : ℤ) :
    (∑ γ ∈ Finset.range (Work.FIPlan.absDelta z1 z2)
            ×ˢ Finset.range (Work.FIPlan.absDelta z1 z2),
        (if (Work.FIArea2.Xof z1 z2 ((γ.1 : ℤ), (γ.2 : ℤ))).re
                % ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℤ) = 0
              ∧ (Work.FIArea2.Xof z1 z2 ((γ.1 : ℤ), (γ.2 : ℤ))).im
                % ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℤ) = 0
          then Work.FIArea2.eGam (Work.FIPlan.absDelta z1 z2) γ h1 h2 else 0))
      = ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℂ) * Work.FIArea2.Gsum z1 z2 h1 h2 := by
  classical
  have hm0 : ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hm
  rw [Gsum_class_sum_iterated z1 z2 h1 h2, Work.FIArea2.Gsum]
  rw [← mul_assoc, Complex.ofReal_inv, Complex.ofReal_natCast, mul_inv_cancel₀ hm0, one_mul]

end Work.FIArea2
