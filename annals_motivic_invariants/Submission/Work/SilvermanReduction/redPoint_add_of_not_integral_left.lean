import Mathlib
import Submission.Work.SilvermanReduction.Basic
import Submission.Work.SilvermanReduction.val_y_lt_sq_of_equation
import Submission.Work.SilvermanReduction.isIntegralK_addX_of_not_integral_left
import Submission.Work.SilvermanReduction.redPoint_add_of_not_integral_sum
import Submission.Work.SilvermanReduction.redPoint_add_self_of_not_integral_double
import Submission.Work.SilvermanReduction.redPoint_neg_of_integral

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Silverman, *AEC*, VII.2.1: the negative-valuation half of the additivity of the reduction

The additivity of the reduction map `redPoint R W : E(K) → Ẽ(k)` on the points of a Weierstrass
curve with good reduction (Silverman, *AEC*, VII.2.1) is proved in two halves:

* `redPoint_add_of_integral` (**integral × integral**) and
* `redPoint_add_of_not_integral_left` (this file): the first point has **negative valuation**,
  i.e. `E₁(K) + E(K) ⊆ E(K)` with the sum reducing correctly.

Everything is phrased over a discrete valuation ring `R` with fraction field `K` and a Weierstrass
curve `W/K` with good reduction at `R`; the two case lemmas are assembled into `redPoint_add` in
`Submission/Work/SilvermanReduction/Add.lean`.

The mathematics of the negative-valuation case.  Write `P = (x,y)` and `Q = (u,v)`, so that
`redPoint R W P = 0`.  The proof rests on two estimates, delegated to their own modules and only
needed here in the shape in which they are stated:

* `val_y_lt_sq_of_equation` — for a point of an integral Weierstrass equation with `val x > 1` one
  has `val y < (val x)²` (the `y²`-term of the equation is dominated by `x³`);
* `isIntegralK_addX_of_not_integral_left` — the chord identity
  `(x-u)² · addX x u (slope x u y v) = N` with
  `N = x²u + xu² + 2a₂xu + a₄(x+u) + 2a₆ - a₁(xv+uy) - a₃(y+v) - 2yv`
  bounds every term of `N - u(x-u)²` by `val x`, so that `val(addX - u) < 1`: the sum `P + Q`
  is again integral.

Then, with `Q` integral and `T = -Q`:

* if the sum's `x`-coordinate differs from `u`, the additivity `redPoint_add_of_not_integral_sum`
  for a pair of integral points whose sum has negative valuation gives
  `redPoint (P+Q) + redPoint (-Q) = redPoint P = 0`, whence `redPoint (P+Q) = redPoint Q`;
* if the sum's `x`-coordinate equals `u`, then `P + Q = ±(-Q) = ∓Q`; the sign `P + Q = Q` forces
  `P = 0`, and the sign `P + Q = -Q` makes `P` the *double* of the integral point `P + Q`, so the
  doubling case `redPoint_add_self_of_not_integral_double` (whose proof uses that the doubling
  denominator `2y + a₁x + a₃` vanishes modulo the maximal ideal) applies.

When `Q` itself has negative valuation, the sum `P + Q` cannot be integral (`Q = -P + (P+Q)` with
`-P` of negative valuation and `P + Q` integral would, by the same estimate, force `-P` integral);
hence `P + Q = 0` or `P + Q` has negative valuation, and both sides evaluate to `0`.

The negation compatibility `redPoint_neg_of_integral` for integral points is used throughout.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open WeierstrassCurve WeierstrassCurve.Affine
open IsLocalRing (ResidueField residue)
open scoped WithZero

namespace Work.SilvermanReduction

noncomputable section

/-- **Silverman, AEC, VII.2.1 (the negative-valuation case).**  If the first point `(x, y)` has
*negative valuation* at the place (its `x`-coordinate does not lift to `R`, so `redPoint` sends it
to `0`), then the reduction of the sum is the reduction of the second point:
`redPoint (P + Q) = redPoint P + redPoint Q`, both sides reading `redPoint Q`.

Mathematically this is the statement `E₁(K) + E₀(K) ⊆ E₀(K)` for the subgroup `E₁(K)` of points of
negative valuation, which is the beginning of the filtration `E(K) ⊇ E₀ ⊇ E₁ ⊇ …` of Silverman
VII.2.2.  Proof route: write `x(P+Q) = W.addX x u λ` with `λ = (y-v)/(x-u)` (here `v(λ) < 0`) and
use the identity
`(x-u)^2 * W.addX x u (W.slope x u y v) = N(x,y,u,v)`
where `N = x²u + xu² + 2a₂xu + a₄(x+u) + 2a₆ - a₁(xv+uy) - a₃(y+v) - 2yv`, together with the
curve equations for `(x,y)` and `(u,v)`.  Comparing valuations shows `v(x(P+Q) - u) > 0` (the
leading term of `N` is `x²u`, which dominates `-2yv` and all other terms — the special cases
`v(x) = v(u) < 0` and `u` integral have to be handled separately, since then `λ²` and `-x` cancel
at leading order), and symmetrically for the `y`-coordinate, so `P + Q` is integral and reduces to
`red Q`.  When `Q` is itself of negative valuation, both sides are `0`. -/
theorem redPoint_add_of_not_integral_left {K : Type*} [Field K] [DecidableEq K]
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R K] [IsFractionRing R K] [DecidableEq (IsLocalRing.ResidueField R)]
    {W : WeierstrassCurve.Affine K} [W.HasGoodReduction R]
    {x y u v : K} (h : WeierstrassCurve.Affine.Nonsingular W x y)
    (h' : WeierstrassCurve.Affine.Nonsingular W u v)
    (hx : ¬ ∃ r : R, algebraMap R K r = x) :
    Work.SilvermanReduction.redPoint R W (WeierstrassCurve.Affine.Point.some x y h +
        WeierstrassCurve.Affine.Point.some u v h')
      = Work.SilvermanReduction.redPoint R W (WeierstrassCurve.Affine.Point.some x y h)
        + Work.SilvermanReduction.redPoint R W (WeierstrassCurve.Affine.Point.some u v h') := by
  classical
  have hvalx : 1 < val R K x := by
    by_contra hc
    exact hx ((IsIntegralK.iff_exists (R := R) x).mp (not_lt.mp hc))
  have hredP : redPoint R W (Point.some x y h) = 0 := redPoint_some_eq_zero R h hx
  have hPneg : HasNegativeValuation R (Point.some x y h) :=
    (hasNegativeValuation_some_iff R h).mpr hvalx
  by_cases hu : ∃ r : R, algebraMap R K r = u
  · -- Case 1: the second point is integral
    have hxne : x ≠ u := by rintro rfl; exact hx hu
    have huI : IsIntegralK R K u := (IsIntegralK.iff_exists u).mpr hu
    have hvI : IsIntegralK R K v := isIntegralK_of_equation h'.1 huI
    have hybound : val R K y < val R K x * val R K x := val_y_lt_sq_of_equation h.1 hvalx
    have haddX : IsIntegralK R K (W.addX x u (W.slope x u y v)) :=
      isIntegralK_addX_of_not_integral_left h.1 h'.1 hvalx huI hvI hybound hxne
    have heq : W.Equation (W.addX x u (W.slope x u y v)) (W.addY x u y (W.slope x u y v)) :=
      equation_add h.1 h'.1 (fun hxy => hxne hxy.1)
    have hns : W.Nonsingular (W.addX x u (W.slope x u y v)) (W.addY x u y (W.slope x u y v)) :=
      nonsingular_add h h' (fun hxy => hxne hxy.1)
    have haddY : IsIntegralK R K (W.addY x u y (W.slope x u y v)) :=
      isIntegralK_of_equation heq haddX
    have haddXi : ∃ r : R, algebraMap R K r = W.addX x u (W.slope x u y v) :=
      (IsIntegralK.iff_exists _).mp haddX
    have hsum : Point.some x y h + Point.some u v h' =
        Point.some (W.addX x u (W.slope x u y v)) (W.addY x u y (W.slope x u y v)) hns :=
      Point.add_of_X_ne hxne
    have hneguv : W.Nonsingular u (W.negY u v) := (nonsingular_neg u v).mpr h'
    have hT : Point.some u (W.negY u v) hneguv = -(Point.some u v h') :=
      (Point.some_congr hneguv _).trans (Point.neg_some h').symm
    have hSpoint : Point.some (W.addX x u (W.slope x u y v)) (W.addY x u y (W.slope x u y v)) hns
        + Point.some u (W.negY u v) hneguv = Point.some x y h := by
      rw [← hsum, hT, add_assoc, add_neg_cancel, add_zero]
    by_cases hxS : W.addX x u (W.slope x u y v) = u
    · -- Sub-case B: the sum has the same x-coordinate as -Q
      have hcases := (Point.X_eq_iff (W := W) (h₁ := hns) (h₂ := hneguv)).mp hxS
      rcases hcases with hSB | hSB
      · -- S = T = -Q: the doubling lemma
        have hSS : Point.some (W.addX x u (W.slope x u y v)) (W.addY x u y (W.slope x u y v)) hns
            + Point.some (W.addX x u (W.slope x u y v)) (W.addY x u y (W.slope x u y v)) hns
            = Point.some x y h := by
          rw [hSB]; rw [hSB] at hSpoint; exact hSpoint
        have h2S : HasNegativeValuation R
            (Point.some (W.addX x u (W.slope x u y v)) (W.addY x u y (W.slope x u y v)) hns
              + Point.some (W.addX x u (W.slope x u y v)) (W.addY x u y (W.slope x u y v)) hns) := by
          rw [hSS]; exact hPneg
        have key2 := redPoint_add_self_of_not_integral_double (W := W) hns haddXi h2S
        have hkey2' : redPoint R W (Point.some x y h) =
            redPoint R W (Point.some (W.addX x u (W.slope x u y v)) (W.addY x u y (W.slope x u y v)) hns)
            + redPoint R W (Point.some (W.addX x u (W.slope x u y v))
                (W.addY x u y (W.slope x u y v)) hns) := by
          rw [← hSS]; exact key2
        have hzero : redPoint R W (Point.some (W.addX x u (W.slope x u y v))
              (W.addY x u y (W.slope x u y v)) hns)
            = - redPoint R W (Point.some (W.addX x u (W.slope x u y v))
                (W.addY x u y (W.slope x u y v)) hns) := by
          have h0 : (0 : Point (W.reduction R)) =
              redPoint R W (Point.some (W.addX x u (W.slope x u y v))
                  (W.addY x u y (W.slope x u y v)) hns)
              + redPoint R W (Point.some (W.addX x u (W.slope x u y v))
                  (W.addY x u y (W.slope x u y v)) hns) := by
            rw [← hredP]; exact hkey2'
          exact eq_neg_of_add_eq_zero_left h0.symm
        have hSQ : redPoint R W (Point.some (W.addX x u (W.slope x u y v))
              (W.addY x u y (W.slope x u y v)) hns) = - redPoint R W (Point.some u v h') := by
          rw [hSB, hT, redPoint_neg_of_integral (W := W) h' hu]
        have hfinal : redPoint R W (Point.some u v h') =
            redPoint R W (Point.some (W.addX x u (W.slope x u y v))
                (W.addY x u y (W.slope x u y v)) hns) :=
          neg_injective (hSQ.symm.trans hzero)
        rw [hredP, zero_add, hsum]
        exact hfinal.symm
      · -- S = -T = Q implies P = 0
        exfalso
        have hSQ : Point.some (W.addX x u (W.slope x u y v)) (W.addY x u y (W.slope x u y v)) hns
            = Point.some u v h' := by
          rw [hSB, hT, neg_neg]
        have hP0 : Point.some x y h = 0 := by
          have hcancel : Point.some x y h + Point.some u v h'
              = (0 : Point W) + Point.some u v h' := by
            rw [zero_add, hsum, hSQ]
          exact add_right_cancel hcancel
        exact Point.some_ne_zero h hP0
    · -- Sub-case A: the sum is a genuine integral point
      have hSp : HasNegativeValuation R
          (Point.some (W.addX x u (W.slope x u y v)) (W.addY x u y (W.slope x u y v)) hns
            + Point.some u (W.negY u v) hneguv) := by
        rw [hSpoint]; exact hPneg
      have key := redPoint_add_of_not_integral_sum (W := W) hns hneguv haddXi hu hxS hSp
      have h1 : redPoint R W (Point.some x y h) =
          redPoint R W (Point.some (W.addX x u (W.slope x u y v))
              (W.addY x u y (W.slope x u y v)) hns)
          + redPoint R W (-(Point.some u v h')) := by
        rw [← hSpoint, ← hT]
        exact key
      rw [redPoint_neg_of_integral (W := W) h' hu] at h1
      have h3 : redPoint R W (Point.some (W.addX x u (W.slope x u y v))
            (W.addY x u y (W.slope x u y v)) hns) - redPoint R W (Point.some u v h') = 0 := by
        rw [sub_eq_add_neg, ← h1, hredP]
      have hfinal : redPoint R W (Point.some (W.addX x u (W.slope x u y v))
            (W.addY x u y (W.slope x u y v)) hns) = redPoint R W (Point.some u v h') :=
        sub_eq_zero.mp h3
      rw [hredP, zero_add, hsum]
      exact hfinal
  · -- Case 2: the second point has negative valuation
    have hredQ : redPoint R W (Point.some u v h') = 0 := redPoint_some_eq_zero R h' hu
    have hvalu : 1 < val R K u := by
      by_contra hc
      exact hu ((IsIntegralK.iff_exists u).mp (not_lt.mp hc))
    rw [hredP, hredQ, add_zero]
    rw [redPoint_eq_zero_iff R (Point.some x y h + Point.some u v h')]
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨hne0, hnotneg⟩ := hcon
    obtain ⟨x_S, y_S, h_S, hSeq⟩ : ∃ (x_S y_S : K) (h_S : W.Nonsingular x_S y_S),
        Point.some x y h + Point.some u v h' = Point.some x_S y_S h_S := by
      generalize hpt : Point.some x y h + Point.some u v h' = Pt
      cases Pt with
      | zero => exact (hne0 hpt).elim
      | some x_S y_S h_S => exact ⟨x_S, y_S, h_S, rfl⟩
    have hnotneg' : ¬ HasNegativeValuation R (Point.some x_S y_S h_S) := hSeq ▸ hnotneg
    have hxSint : ∃ r : R, algebraMap R K r = x_S :=
      (not_hasNegativeValuation_some_iff R h_S).mp hnotneg'
    have hxSI : IsIntegralK R K x_S := (IsIntegralK.iff_exists x_S).mpr hxSint
    have hySI : IsIntegralK R K y_S := isIntegralK_of_equation h_S.1 hxSI
    have hneguv : W.Nonsingular u (W.negY u v) := (nonsingular_neg u v).mpr h'
    have hT : Point.some u (W.negY u v) hneguv = -(Point.some u v h') :=
      (Point.some_congr hneguv _).trans (Point.neg_some h').symm
    have hTS : Point.some u (W.negY u v) hneguv + Point.some x_S y_S h_S = Point.some x y h := by
      rw [hT, ← hSeq]; abel
    by_cases hux : u = x_S
    · have hcases := (Point.X_eq_iff (W := W) (h₁ := hneguv) (h₂ := h_S)).mp hux
      rcases hcases with hST | hST
      · exact absurd (by rw [← hST]; exact (hasNegativeValuation_some_iff R hneguv).mpr hvalu) hnotneg'
      · have hSQ : Point.some x_S y_S h_S = Point.some u v h' := by
          have hneg : -(Point.some x_S y_S h_S) = -(Point.some u v h') := hST.symm.trans hT
          exact neg_injective hneg
        have hP0 : Point.some x y h = 0 := by
          have hcancel : Point.some x y h + Point.some u v h'
              = (0 : Point W) + Point.some u v h' := by
            rw [zero_add, hSeq, hSQ]
          exact add_right_cancel hcancel
        exact Point.some_ne_zero h hP0
    · have hyneg : val R K (W.negY u v) < val R K u * val R K u :=
        val_y_lt_sq_of_equation hneguv.1 hvalu
      have hIx : IsIntegralK R K (W.addX u x_S (W.slope u x_S (W.negY u v) y_S)) :=
        isIntegralK_addX_of_not_integral_left hneguv.1 h_S.1 hvalu hxSI hySI hyneg hux
      have hPsum : Point.some u (W.negY u v) hneguv + Point.some x_S y_S h_S
          = Point.some (W.addX u x_S (W.slope u x_S (W.negY u v) y_S))
              (W.addY u x_S (W.negY u v) (W.slope u x_S (W.negY u v) y_S))
              (nonsingular_add hneguv h_S (fun hxy => hux hxy.1)) :=
        Point.add_of_X_ne hux
      have hPS : Point.some (W.addX u x_S (W.slope u x_S (W.negY u v) y_S))
            (W.addY u x_S (W.negY u v) (W.slope u x_S (W.negY u v) y_S))
            (nonsingular_add hneguv h_S (fun hxy => hux hxy.1))
            = Point.some x y h := by
        rw [← hPsum, hTS]
      have hxeq : x = W.addX u x_S (W.slope u x_S (W.negY u v) y_S) := by
        rw [Point.some.injEq] at hPS
        exact hPS.1.symm
      exact absurd (by rw [hxeq]; exact hIx) (not_le.mpr hvalx)

end

end Work.SilvermanReduction
