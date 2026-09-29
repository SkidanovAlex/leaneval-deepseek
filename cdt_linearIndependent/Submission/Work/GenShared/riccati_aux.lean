import Mathlib
import Submission.Work.GenShared.periods_defs
import Submission.Work.GenShared.rreg_Dv

/-!
# Elementary helpers for `Work.GenShared.riccati_core`

* `ball_infinite` — a metric ball of positive radius in `ℂ` is infinite;
* `rreg_algMap` — a polynomial coefficient is regular everywhere;
* `rval_algMap` — its value is the polynomial evaluation;
* `rval_add`, `rval_mul`, `rval_neg` — `Rval` behaves additively/multiplicatively at points where
  the arguments are regular (`RatFunc.eval_add`/`eval_mul` transported along `Rval f z =
  RatFunc.eval (RingHom.id ℂ) z f`).
-/

namespace Work.GenShared

open Complex Metric Work.GenShared
open Submission.CDT (dRat)

/-- A metric ball with positive radius in `ℂ` is infinite. -/
lemma ball_infinite (z0 : ℂ) {ε : ℝ} (hε : 0 < ε) : (Metric.ball z0 ε).Infinite := by
  have h : (Set.Ioo (0:ℝ) ε).Infinite := Set.Ioo_infinite hε
  have hinj : Set.InjOn (fun t : ℝ => z0 + (t:ℂ)) (Set.Ioo 0 ε) := by
    intro a _ b _ hab
    have h2 : (a:ℂ) = (b:ℂ) := add_left_cancel hab
    exact Complex.ofReal_injective h2
  refine (h.image hinj).mono ?_
  rintro x ⟨t, ht, rfl⟩
  rw [Metric.mem_ball, Complex.dist_eq]
  rw [show z0 + (t:ℂ) - z0 = (t:ℂ) by ring, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1]
  exact ht.2

/-- `Rval` is `RatFunc.eval` at the identity. -/
lemma rval_eq_eval (f : RatFunc ℂ) (z : ℂ) :
    Rval f z = RatFunc.eval (RingHom.id ℂ) z f := by
  simp [Rval, RatFunc.eval, Polynomial.eval₂_id]

/-- A polynomial coefficient is regular everywhere. -/
lemma rreg_algMap (p : Polynomial ℂ) (z : ℂ) :
    Rreg (algebraMap (Polynomial ℂ) (RatFunc ℂ) p) z := by
  simp [Rreg, RatFunc.denom_algebraMap]

/-- The value of a polynomial coefficient. -/
lemma rval_algMap (p : Polynomial ℂ) (z : ℂ) :
    Rval (algebraMap (Polynomial ℂ) (RatFunc ℂ) p) z = p.eval z := by
  simp [Rval, RatFunc.num_algebraMap, RatFunc.denom_algebraMap]

/-- `Rval` is additive at a point at which both arguments are regular. -/
lemma rval_add {x y : RatFunc ℂ} {z : ℂ} (hx : Rreg x z) (hy : Rreg y z) :
    Rval (x + y) z = Rval x z + Rval y z := by
  have hx' : Polynomial.eval₂ (RingHom.id ℂ) z x.denom ≠ 0 := by
    simpa [Rreg, Polynomial.eval₂_id] using hx
  have hy' : Polynomial.eval₂ (RingHom.id ℂ) z y.denom ≠ 0 := by
    simpa [Rreg, Polynomial.eval₂_id] using hy
  have h := RatFunc.eval_add (f := RingHom.id ℂ) (a := z) (x := x) (y := y) hx' hy'
  simpa [Rval, RatFunc.eval, Polynomial.eval₂_id] using h

/-- `Rval` is multiplicative at a point at which both arguments are regular. -/
lemma rval_mul {x y : RatFunc ℂ} {z : ℂ} (hx : Rreg x z) (hy : Rreg y z) :
    Rval (x * y) z = Rval x z * Rval y z := by
  have hx' : Polynomial.eval₂ (RingHom.id ℂ) z x.denom ≠ 0 := by
    simpa [Rreg, Polynomial.eval₂_id] using hx
  have hy' : Polynomial.eval₂ (RingHom.id ℂ) z y.denom ≠ 0 := by
    simpa [Rreg, Polynomial.eval₂_id] using hy
  have h := RatFunc.eval_mul (f := RingHom.id ℂ) (a := z) (x := x) (y := y) hx' hy'
  simpa [Rval, RatFunc.eval, Polynomial.eval₂_id] using h

end Work.GenShared
