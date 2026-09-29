import Mathlib
import Submission.Work.CLift.analytic

/-!
# Area CLift — the ODE satisfied by the analytic function of `P`

The unlikely `G`-function `P = logP a b r_a r_b r_ab r₀` of Theorem C satisfies the inhomogeneous
order-2 ODE with polynomial coefficients and polynomial right-hand side (`logP_ode` in
`Submission.CDT.LogMIdentities`):

`P₂ · P'' + P₁ · P' + P₀ · P = r_a·Ra + r_b·Rb + r_ab·Rab`.

This module evaluates that power-series identity at a complex point `x` with `‖x‖ ≤ 1/2`, where
every series involved converges absolutely (coefficient bounds `(3/2)^k` from `hR : PRadius`), and
obtains the corresponding identity for the analytic functions `U0, U1, U2`
(the coefficient series of `P` and of its first two formal derivatives).

## Method

`Work.CLift.evA A x = ∑_k (coeff k A) x^k` is the analytic evaluation of a rational power series.
The two ingredients are

* `evA_mul_hasSum`: for two absolutely convergent evaluations, the coefficient series of the product
  is summable with `HasSum` value `evA A x * evA B x` — the Cauchy product
  (`hasSum_sum_range_mul_of_summable_norm` plus `PowerSeries.coeff_mul`);
* `summable_norm_poly`: the coefficient series of a polynomial is finitely supported, hence
  summable.

Absolute convergence of `U0`, `U1`, `U2` is `summable_norm_U0/1/2` (`CLift.analytic`).
Evaluating `logP_ode` on both sides (`evA_P2/P1/P0`, `evA_Rh`) gives the claim.
-/

namespace Work.CLift

open PowerSeries Submission.CDTPlan Submission.CDT
open scoped BigOperators

noncomputable section

/-! ## Evaluating a product of two absolutely convergent series -/

/-- **Cauchy product for `evA`.** If the coefficient series of `A` and `B` are absolutely
convergent at `x`, then the coefficient series of the product `A * B` is summable with sum
`evA A x * evA B x`.  (In particular it is summable, which `evA_mul` alone does not record.) -/
lemma evA_mul_hasSum (A B : PowerSeries ℚ) (x : ℂ)
    (hA : Summable fun k => ‖((PowerSeries.coeff k A : ℚ) : ℂ) * x ^ k‖)
    (hB : Summable fun k => ‖((PowerSeries.coeff k B : ℚ) : ℂ) * x ^ k‖) :
    HasSum (fun n => ((PowerSeries.coeff n (A * B) : ℚ) : ℂ) * x ^ n)
      (evA A x * evA B x) := by
  have h := hasSum_sum_range_mul_of_summable_norm hA hB
  refine h.congr_fun (fun n => ?_)
  rw [PowerSeries.coeff_mul,
    ← Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun k l => ((PowerSeries.coeff k A : ℚ) : ℂ) * x ^ k
        * (((PowerSeries.coeff l B : ℚ) : ℂ) * x ^ l))]
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [show x ^ n = x ^ p.1 * x ^ p.2 by rw [← pow_add, hp]]
  ring

/-- The coefficient series of a polynomial is finitely supported, hence absolutely summable. -/
lemma summable_norm_poly (p : Polynomial ℚ) (x : ℂ) :
    Summable fun k => ‖((PowerSeries.coeff k (p : PowerSeries ℚ) : ℚ) : ℂ) * x ^ k‖ := by
  refine summable_of_ne_finset_zero (s := Finset.range (p.natDegree + 1)) (fun k hk => ?_)
  rw [Finset.mem_range, not_lt] at hk
  rw [Polynomial.coeff_coe, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
  simp

/-! ## The ODE for `U0, U1, U2` -/

theorem ode_holds (m n : ℕ) (ra rb rab r0 : ℤ) (hR : PRadius) (hAdm : CAdm m n)
    (hRel : CRel m n ra rb rab r0) (x : ℂ) (hx : ‖x‖ ≤ 1 / 2) :
    P2p m n x * U2 m n ra rb rab r0 x + P1p m n x * U1 m n ra rb rab r0 x
      + P0p m n x * U0 m n ra rb rab r0 x = Rhp m n ra rb rab x := by
  -- the bridge between `PC` and `logP (aa m) (bb n)`
  have hPt : Pt m n ra rb rab r0 = logP (aa m) (bb n) ra rb rab r0 := by
    simp only [Pt, PC]
    congr 1
    · simp only [aa]; push_cast; ring
    · simp only [bb]; push_cast; ring
  -- `U0, U1, U2` are the evaluations of `P` and of its formal derivatives
  have hU0 : U0 m n ra rb rab r0 x = evA (Pt m n ra rb rab r0) x := by
    unfold U0 evA coef
    apply tsum_congr
    intro k
    rfl
  have hU1 : U1 m n ra rb rab r0 x
      = evA (PowerSeries.derivative (R := ℚ) (Pt m n ra rb rab r0)) x := by
    unfold U1 evA coef
    apply tsum_congr
    intro k
    rw [PowerSeries.coeff_derivative]
    push_cast
    ring
  have hU2 : U2 m n ra rb rab r0 x
      = evA (PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) (Pt m n ra rb rab r0))) x := by
    unfold U2 evA coef
    apply tsum_congr
    intro k
    rw [Commons.RingTheory.PowerSeries.coeff_der2]
    push_cast
    ring
  -- absolute convergence of the polynomial coefficients
  have sP2 : Summable fun k => ‖((PowerSeries.coeff k
      (logPAP2 (aa m) (bb n)) : ℚ) : ℂ) * x ^ k‖ := by
    rw [← P2poly_coe m n]; exact summable_norm_poly (P2poly m n) x
  have sP1 : Summable fun k => ‖((PowerSeries.coeff k
      (logPAP1 (aa m) (bb n)) : ℚ) : ℂ) * x ^ k‖ := by
    rw [← P1poly_coe m n]; exact summable_norm_poly (P1poly m n) x
  have sP0 : Summable fun k => ‖((PowerSeries.coeff k
      (logPAP0 (aa m) (bb n)) : ℚ) : ℂ) * x ^ k‖ := by
    rw [← P0poly_coe m n]; exact summable_norm_poly (P0poly m n) x
  -- absolute convergence of the derivative series (from `summable_norm_U*`)
  have sd2 : Summable fun k => ‖((PowerSeries.coeff k
      (PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) (Pt m n ra rb rab r0))) : ℚ) : ℂ)
        * x ^ k‖ := by
    refine (summable_norm_U2 m n ra rb rab r0 hR hAdm hRel x hx).congr (fun k => ?_)
    have h : ((PowerSeries.coeff k (PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ)
        (Pt m n ra rb rab r0))) : ℚ) : ℂ)
        = ((k : ℂ) + 1) * ((k : ℂ) + 2) * coef m n ra rb rab r0 (k + 2) := by
      rw [Commons.RingTheory.PowerSeries.coeff_der2]
      unfold coef
      push_cast
      ring
    rw [h]
  have sd1 : Summable fun k => ‖((PowerSeries.coeff k
      (PowerSeries.derivative (R := ℚ) (Pt m n ra rb rab r0)) : ℚ) : ℂ) * x ^ k‖ := by
    refine (summable_norm_U1 m n ra rb rab r0 hR hAdm hRel x hx).congr (fun k => ?_)
    have h : ((PowerSeries.coeff k (PowerSeries.derivative (R := ℚ) (Pt m n ra rb rab r0)) : ℚ) : ℂ)
        = ((k : ℂ) + 1) * coef m n ra rb rab r0 (k + 1) := by
      rw [PowerSeries.coeff_derivative]
      unfold coef
      push_cast
      ring
    rw [h]
  have sd0 : Summable fun k => ‖((PowerSeries.coeff k (Pt m n ra rb rab r0) : ℚ) : ℂ)
      * x ^ k‖ := by
    refine (summable_norm_U0 m n ra rb rab r0 hR hAdm hRel x hx).congr (fun k => ?_)
    unfold coef
    rfl
  -- the three products, evaluated by the Cauchy product
  have hs2 : HasSum (fun k => ((PowerSeries.coeff k (logPAP2 (aa m) (bb n)
      * PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) (Pt m n ra rb rab r0))) : ℚ) : ℂ)
        * x ^ k)
      (P2p m n x * U2 m n ra rb rab r0 x) := by
    rw [← evA_P2 m n x, hU2]
    exact evA_mul_hasSum _ _ x sP2 sd2
  have hs1 : HasSum (fun k => ((PowerSeries.coeff k (logPAP1 (aa m) (bb n)
      * PowerSeries.derivative (R := ℚ) (Pt m n ra rb rab r0)) : ℚ) : ℂ) * x ^ k)
      (P1p m n x * U1 m n ra rb rab r0 x) := by
    rw [← evA_P1 m n x, hU1]
    exact evA_mul_hasSum _ _ x sP1 sd1
  have hs0 : HasSum (fun k => ((PowerSeries.coeff k (logPAP0 (aa m) (bb n)
      * Pt m n ra rb rab r0) : ℚ) : ℂ) * x ^ k)
      (P0p m n x * U0 m n ra rb rab r0 x) := by
    rw [← evA_P0 m n x, hU0]
    exact evA_mul_hasSum _ _ x sP0 sd0
  -- add them up, coefficient-wise
  have hcomb : HasSum (fun k => ((PowerSeries.coeff k (logPAP2 (aa m) (bb n)
        * PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) (Pt m n ra rb rab r0))) : ℚ) : ℂ)
          * x ^ k
      + ((PowerSeries.coeff k (logPAP1 (aa m) (bb n)
        * PowerSeries.derivative (R := ℚ) (Pt m n ra rb rab r0)) : ℚ) : ℂ) * x ^ k
      + ((PowerSeries.coeff k (logPAP0 (aa m) (bb n)
        * Pt m n ra rb rab r0) : ℚ) : ℂ) * x ^ k)
      ((P2p m n x * U2 m n ra rb rab r0 x + P1p m n x * U1 m n ra rb rab r0 x)
        + P0p m n x * U0 m n ra rb rab r0 x) :=
    (hs2.add hs1).add hs0
  -- identify the summand with the coefficients of the operator applied to `P`
  have hevW : evA (logPAODE (aa m) (bb n) (Pt m n ra rb rab r0)) x
      = (P2p m n x * U2 m n ra rb rab r0 x + P1p m n x * U1 m n ra rb rab r0 x)
        + P0p m n x * U0 m n ra rb rab r0 x := by
    rw [evA]
    refine (hcomb.congr_fun (fun k => ?_)).tsum_eq
    unfold logPAODE
    rw [Commons.RingTheory.PowerSeries.coeff_add_s,
      Commons.RingTheory.PowerSeries.coeff_add_s]
    push_cast
    ring
  -- the right-hand side is the evaluation of the polynomial `Rhpoly`
  have hWR : evA (logPAODE (aa m) (bb n) (Pt m n ra rb rab r0)) x = Rhp m n ra rb rab x := by
    have hode := Submission.CDT.logP_ode (aa m) (bb n) ra rb rab r0
    have hW : logPAODE (aa m) (bb n) (Pt m n ra rb rab r0)
        = PowerSeries.C (ra : ℚ) * RaFam (aa m) (bb n)
          + PowerSeries.C (rb : ℚ) * RbFam (aa m) (bb n)
          + PowerSeries.C (rab : ℚ) * RabFam (aa m) (bb n) := by
      rw [hPt]; exact hode
    rw [hW, evA_Rh]
  rw [← hevW, hWR]

end

end Work.CLift
