/-
# The `h = 0` term of (6.9) is the *repaired* main term (6.13)

`Ccount_smooth_eq_poisson` (delegated) identifies `C(z₁,z₂)` with

  `|z₁z₂|^{−1/2} Σ_{h ∈ ℤ²} Fint F γ(−h₁|Δz₂|^{−1/2}, −h₂|Δz₁|^{−1/2})·Gsum z₁ z₂ h₁ h₂`.

This file computes its `h = 0` term:

* `Gsum_zero_zero`: the arithmetic sum (6.10) at `h = 0` is the **count** `(6.12)` normalised by
  `|Δ|`, i.e. exactly `Work.FIArea2.G0fix` — *not* the frozen `Work.FIPlan.G0` (which uses the
  Jacobi symbol of `Re(z̄₁z₂)` rather than the residue `z₂/z₁`, see `G0_defect.lean`);
* `Fint_zero_zero`: the Fourier integral (6.8) at `(0,0)` is the integral `F₀(z₁,z₂)` of (6.11).

Consequently the `h = 0` term is `|z₁z₂|^{−1/2}·F₀·G0fix`, which together with the (7.10) expansion
`F₀ = f̂(0)E(γ)` (`lemma_7_2_core`) *is* (6.13) with the correct kernel: the repaired main term
`Work.FIArea2.C0true` of `MainTermFix.lean`.  This pins down, in Lean, that the frozen `Area2`'s
`C0mod` cannot be obtained as the zero frequency of (6.9), independently of the log-prefactor
normalisation recorded in `NOTES.md` §11.
-/
import Mathlib
import Submission.Work.FIArea2.SmoothSec6Defs
import Submission.Work.FIArea2.G8Defs
import Submission.Work.FIArea2.G0_fix
import Submission.Work.FIArea2.FintDefs

namespace Work.FIArea2

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **(6.10) at `h = 0`.**  `G(0,0) = |Δ|^{−1}·#{(γ₁,γ₂) mod |Δ| : γ₁²z₂ ≡ γ₂²z₁ (mod |Δ|)}`,
i.e. the count (6.12) normalised by `|Δ|` — which is `Work.FIArea2.G0fix`, the corrected kernel.
(`e(0) = 1`, so the exponential sum degenerates to the count.) -/
theorem Gsum_zero_zero (z1 z2 : GaussianInt) :
    Gsum z1 z2 0 0 = ((G0fix z1 z2 : ℝ) : ℂ) := by
  have hexp : ∀ γ1 γ2 : ℤ, Complex.exp (2 * Real.pi * Complex.I
      * (((γ1 * 0 + γ2 * 0 : ℤ)) : ℝ) / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)) = 1 := by
    intro γ1 γ2
    norm_num
  have hsum : (∑ γ1 ∈ Finset.range (Work.FIPlan.absDelta z1 z2),
        ∑ γ2 ∈ Finset.range (Work.FIPlan.absDelta z1 z2),
          (if (γ1 ^ 2 * z2.re - γ2 ^ 2 * z1.re) % (Work.FIPlan.absDelta z1 z2 : ℤ) = 0 ∧
              (γ1 ^ 2 * z2.im - γ2 ^ 2 * z1.im) % (Work.FIPlan.absDelta z1 z2 : ℤ) = 0
            then Complex.exp (2 * Real.pi * Complex.I
              * (((γ1 * 0 + γ2 * 0 : ℤ)) : ℝ)
                / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)) else 0))
      = ∑ p ∈ (Finset.range (Work.FIPlan.absDelta z1 z2)
            ×ˢ Finset.range (Work.FIPlan.absDelta z1 z2)),
          (if (p.1 ^ 2 * z2.re - p.2 ^ 2 * z1.re) % (Work.FIPlan.absDelta z1 z2 : ℤ) = 0 ∧
              (p.1 ^ 2 * z2.im - p.2 ^ 2 * z1.im) % (Work.FIPlan.absDelta z1 z2 : ℤ) = 0
            then (1 : ℂ) else 0) := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun γ1 _ => Finset.sum_congr rfl fun γ2 _ => ?_
    by_cases h : (γ1 ^ 2 * z2.re - γ2 ^ 2 * z1.re) % (Work.FIPlan.absDelta z1 z2 : ℤ) = 0 ∧
        (γ1 ^ 2 * z2.im - γ2 ^ 2 * z1.im) % (Work.FIPlan.absDelta z1 z2 : ℤ) = 0
    · rw [if_pos h, if_pos h, hexp]
    · rw [if_neg h, if_neg h]
  unfold Gsum G0fix Cnt
  rw [hsum, Finset.sum_boole]
  push_cast
  rw [div_eq_mul_inv, mul_comm]

/-- **(6.8) at `u = 0`**, the integral `F₀(z₁,z₂)` of (6.11): `Fint F γ 0 0 = ∫_{ℝ²} F(g(t))dt`
with `g` the quartic (7.1). -/
theorem Fint_zero_zero (F : ℝ → ℝ) (γ : ℝ) :
    Fint F γ 0 0 = ∫ t : ℝ × ℝ, ((F (gQuartic γ t) : ℝ) : ℂ) := by
  unfold Fint gQuartic
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp

end

end Work.FIArea2
