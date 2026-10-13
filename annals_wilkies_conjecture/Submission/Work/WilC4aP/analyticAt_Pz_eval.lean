import Mathlib
import Submission.Work.WilC4aP.Basic

namespace Work.WilC4aP

open Polynomial

/-- The map `(z, Y) ↦ (Pz P z).eval Y` is analytic at `(0, α)` whenever all coefficients of `P`
are analytic at `0`.

Route: `(Pz P z).eval Y = ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i z * Y ^ i` (combine
`Polynomial.eval_eq_sum_range'` with `Polynomial.coeff_map` and `Polynomial.natDegree_map_le`).
Each summand is analytic at `(0, α)`: the factor `p ↦ P.coeff i p.1` is `P.coeff i` composed with
the continuous linear projection `fst` (`han i` gives analyticity at `0`, use `AnalyticAt.comp`,
`ContinuousLinearMap.analyticAt`), the factor `p ↦ p.2 ^ i` is `snd` raised to the `i`-th power
(`AnalyticAt.pow`), and analyticity is closed under finite sums (`Finset.analyticAt_sum`, or
induct with `AnalyticAt.add`) and products (`AnalyticAt.mul`). -/
theorem analyticAt_Pz_eval (P : Polynomial (ℂ → ℂ)) (han : Work.WilC4aP.HolCoeffs P 0) (α : ℂ) :
    AnalyticAt ℂ (fun p : ℂ × ℂ => (Work.WilC4aP.Pz P p.1).eval p.2) (0, α) := by
  -- Rewrite the polynomial evaluation as a finite sum with coefficients evaluated at `z`.
  have hsum : ∀ (z Y : ℂ), (Pz P z).eval Y =
      ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i z * Y ^ i := by
    intro z Y
    have hnd : (Pz P z).natDegree < P.natDegree + 1 :=
      Nat.lt_succ_of_le (Polynomial.natDegree_map_le (f := evAt z) (p := P))
    rw [Polynomial.eval_eq_sum_range' hnd Y]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp [Pz, Polynomial.coeff_map]
  have hfun : (fun p : ℂ × ℂ => (Pz P p.1).eval p.2) =
      (∑ i ∈ Finset.range (P.natDegree + 1),
        fun p : ℂ × ℂ => P.coeff i p.1 * p.2 ^ i) := by
    funext p
    rw [Finset.sum_apply]
    exact hsum p.1 p.2
  rw [hfun]
  refine Finset.analyticAt_sum (Finset.range (P.natDegree + 1)) (fun i _ => ?_)
  have hF : AnalyticAt ℂ (fun p : ℂ × ℂ => p.1) (0, α) :=
    ContinuousLinearMap.analyticAt (ContinuousLinearMap.fst ℂ ℂ ℂ) (0, α)
  have hS : AnalyticAt ℂ (fun p : ℂ × ℂ => p.2) (0, α) :=
    ContinuousLinearMap.analyticAt (ContinuousLinearMap.snd ℂ ℂ ℂ) (0, α)
  exact (AnalyticAt.comp (x := (0, α)) (f := fun p : ℂ × ℂ => p.1) (han i) hF).mul (hS.pow i)

end Work.WilC4aP
