import Mathlib
import Submission.Work.MotK.TGen.SdualTBrick
import Submission.Work.MotK.TwCensus.TwistFieldTGTrdeg

set_option linter.unusedVariables false -- v435-speed

/-!
# `trdeg_K K(t)(C_h) = 2` for the generic T-twist field

`Work.MotK.twistFieldTG K D h = K(C_h) ⊆ K̄(E)` is the T-twist curve of the Kummer class of `h`
(`Submission/Work/MotK/LinkCertGen.lean`), whose transcendence degree over `K` is one
(`Work.MotK.TwCensus.TwistFieldTGTrdeg`).  This file computes the transcendence degree of its
*function field in one more variable*, `RatFunc ↥(Work.MotK.twistFieldTG K D h)`: it is `2`.

This is the input that makes the residue field `RatFunc ↥(twistFieldTG K D h)` (the class of the
ruling divisor `sdualT`, see `Submission/Work/MotK/TwCensus/STClass.lean`) a *surface*, so that
the dimension count of the census route applies to it.

## Route

The tower law `trdeg_add_eq` reads

  `trdeg_K K(C_h) + trdeg_{K(C_h)} K(t)(C_h) = trdeg_K K(t)(C_h)`,

so the goal is the sum of two lemmas:

* `Algebra.trdeg K ↥(Work.MotK.twistFieldTG K D h) = 1`
  (`Work.MotK.TwCensus.TwistFieldTGTrdeg`, a `K`-form of `K̄(E)`);
* `Algebra.trdeg F (RatFunc F) = 1` for any field `F`: `RatFunc F = Frac F[t]` is algebraic over
  `F[t]` (`IsFractionRing.comap_isAlgebraic_iff`) and `trdeg_F F[t] = 1`
  (`Polynomial.trdeg_of_isDomain`).
-/

namespace Work.MotK.TwCensus

/-- **Tower law for `RatFunc`.**  If a `K`-field `F` has transcendence degree `1` over `K`, then
its rational function field `F(t)` has transcendence degree `2` over `K`.

This is the tower law `trdeg_add_eq` (giving `trdeg_K F + trdeg_F F(t) = trdeg_K F(t)`) together
with `trdeg_F F(t) = 1`: `F(t)` is the fraction field of `F[t]`, hence algebraic over `F[t]`, and
`trdeg_F F[t] = 1` (`Polynomial.trdeg_of_isDomain`). -/
lemma trdeg_ratFunc_eq_two_of_trdeg_eq_one (K F : Type) [Field K] [Field F] [Algebra K F]
    (h1 : Algebra.trdeg K F = 1) : Algebra.trdeg K (RatFunc F) = 2 := by
  -- `F(t) = Frac F[t]` is algebraic over `F[t]`, so the polynomial ring contributes everything.
  have h2 : Algebra.trdeg F (RatFunc F) = 1 := by
    haveI : Algebra.IsAlgebraic (Polynomial F) (RatFunc F) :=
      (IsFractionRing.comap_isAlgebraic_iff (A := Polynomial F) (K := RatFunc F)
        (C := RatFunc F)).mpr inferInstance
    have hz : Algebra.trdeg (Polynomial F) (RatFunc F) = 0 := trdeg_eq_zero
    have h := trdeg_add_eq F (Polynomial F) (A := RatFunc F)
    rw [hz, add_zero] at h
    rw [Polynomial.trdeg_of_isDomain] at h
    exact h.symm
  -- Tower law: `trdeg_K F + trdeg_F F(t) = trdeg_K F(t)`.
  have h := trdeg_add_eq K F (A := RatFunc F)
  rw [h1, h2] at h
  rw [← h]
  norm_num

/-- **`trdeg_K K(t)(C_h) = 2`.**  The rational function field in one variable over the T-twist
field `K(C_h)` of good Klein data `D` at `h ≠ 0` has transcendence degree `2` over `K`: the
T-twist curve contributes `1` (`TwistFieldTGTrdeg`) and the extra variable another `1`. -/
theorem TwistFieldTGRatFuncTrdeg (K : Type) [Field K] (D : Work.MotV.KleinData K) (hD : D.Good)
    (h : K) (hh : h ≠ 0) :
    Algebra.trdeg K (RatFunc ↥(Work.MotK.twistFieldTG K D h)) = 2 :=
  -- The T-twist curve contributes one transcendental; `trdeg_ratFunc_eq_two_of_trdeg_eq_one`
  -- adds the extra variable.
  trdeg_ratFunc_eq_two_of_trdeg_eq_one K ↥(Work.MotK.twistFieldTG K D h)
    (TwistFieldTGTrdeg K D hD h hh)

end Work.MotK.TwCensus
