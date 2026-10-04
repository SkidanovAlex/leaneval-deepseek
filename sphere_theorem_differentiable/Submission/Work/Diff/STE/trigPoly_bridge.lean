import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.integral_fourierExp
import Submission.Work.Diff.STE.integral_seriesFun_mul_conj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Trigonometric polynomials: the finite-sum bridge to the `L²` pairing

`trigFun p` (defined in `Torus.lean`) is the trigonometric polynomial
`x ↦ Σ_k p k · exp (2πi k·x)` of a finitely supported coefficient family — the range of the
Friedrichs mollifier.  We record

* `seriesFun_finsupp` : a finitely supported family is `trigFun`;
* `integral_trigFun_mul_star_seriesFun` : for a series-representable `L¹` function `u` with
  coefficients `c`, the `L²` pairing of a trigonometric polynomial against `u` is the *finite*
  coefficient sum `Σ_k p k · star (c k)`.

The second identity is what computes `d/dt` of the energy in the Friedrichs-mollifier proof of
short-time existence (design `D2`): the right-hand side of the mollified ODE is a trigonometric
polynomial, so the pairing against the solution reduces to a finite coefficient sum with no
convergence issues.
-/

noncomputable section

namespace Work.Diff.STE

open MeasureTheory BigOperators
open scoped ComplexConjugate

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A finitely supported coefficient family is the trigonometric polynomial with those
coefficients. -/
theorem seriesFun_finsupp (p : (ι → ℤ) →₀ ℂ) :
    seriesFun (fun k => p k) = trigFun p := by
  funext x
  rw [seriesFun, trigFun]
  refine tsum_eq_sum (s := p.support) (fun b hb => ?_)
  have h0 : p b = 0 := by simpa [Finsupp.mem_support_iff] using hb
  rw [h0, zero_mul]

/-- The `L²` pairing of a trigonometric polynomial against a series-representable `L¹` function is
the finite coefficient sum. -/
theorem integral_trigFun_mul_star_seriesFun (p : (ι → ℤ) →₀ ℂ) (c : (ι → ℤ) → ℂ)
    (hc : Summable (fun k : ι → ℤ => ‖c k‖)) :
    ∫ x in unitCube (ι := ι), trigFun p x * star (seriesFun c x)
      = ∑ k ∈ p.support, p k * star (c k) := by
  rw [← seriesFun_finsupp p]
  have hp : Summable (fun k : ι → ℤ => ‖p k‖) := by
    apply summable_of_ne_finset_zero (s := p.support)
    intro b hb
    have h0 : p b = 0 := by simpa [Finsupp.mem_support_iff] using hb
    rw [h0, norm_zero]
  rw [integral_seriesFun_mul_conj (fun k => p k) c hp hc]
  refine tsum_eq_sum (s := p.support) (fun b hb => ?_)
  have h0 : p b = 0 := by simpa [Finsupp.mem_support_iff] using hb
  rw [h0, zero_mul]

end Work.Diff.STE
