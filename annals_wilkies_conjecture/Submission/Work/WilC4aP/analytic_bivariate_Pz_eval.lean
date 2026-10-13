import Mathlib
import Submission.Work.WilC4aP.Basic

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
open scoped BigOperators

namespace Work.WilC4aP

open Polynomial

/-- `(z, Y) ↦ (Pz P z).eval Y` is a finite sum of the analytic functions
`(z, Y) ↦ P.coeff i z * Y ^ i` (one summand per monomial of `P`), hence analytic
whenever all the coefficients of `P` are analytic at `z₀`. -/
theorem analytic_bivariate_Pz_eval (P : Polynomial (ℂ → ℂ)) (z₀ α : ℂ) (han : Work.WilC4aP.HolCoeffs P z₀) :
    AnalyticAt ℂ (fun p : ℂ × ℂ => (Work.WilC4aP.Pz P p.1).eval p.2) (z₀, α) := by
  -- `(Pz P z).eval Y` is the finite sum `∑ i ∈ P.support, P.coeff i z * Y ^ i`.
  have hfun : (fun p : ℂ × ℂ => (Pz P p.1).eval p.2)
      = (Finset.sum P.support (fun i => fun p : ℂ × ℂ => P.coeff i p.1 * p.2 ^ i)) := by
    funext p
    rw [Pz, Polynomial.eval_map, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
    simp [evAt_apply, Finset.sum_apply]
  rw [hfun]
  -- Each summand is analytic at `(z₀, α)`: the coefficient is analytic in the first
  -- variable, and `p ↦ p.2 ^ i` is a power of the analytic second projection.
  refine Finset.analyticAt_sum P.support (fun i _ => ?_)
  exact ((han i).comp (analyticAt_fst (p := (z₀, α)))).mul
    ((analyticAt_snd (p := (z₀, α))).pow i)

end Work.WilC4aP
