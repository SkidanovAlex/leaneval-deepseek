import Mathlib
import Submission.Work.C17y.gen_van
import Submission.Work.GenShared.periods_defs
import Submission.Work.GenShared.hasDerivAt_rval

namespace Work.C17y

open Complex Metric
open Submission.CDT (dRat)
open Work.GenShared (Rval Rreg W Dv Wev rreg_mul rreg_sum rreg_div_poly rreg_dRat hasDerivAt_rval Rval_div)

set_option linter.unusedVariables false

/-- **The derivative identity when the `y1'`-coefficient vanishes.**

This is the case `n.2.1 = 0` of `Work.C17y.hasDerivAt_wev`, where the differentiability of `deriv y1`
at `z` is *not* needed (the term `Rval b * deriv y1` is identically zero), so a `C¹` solution of the
ODE suffices.

Explicitly, for `a : K` and `c : Fin k → K` (`K = ℂ(x)`), the function
`w ↦ Rval a w * y1 w + ∑ i, Rval (c i) w * J i w` has, at a point `z` where `a`, the `c i`, `p2` and
the `rd i` do not vanish, derivative `Wev y1 J (Dv p2 p1 p0 rn rd (a, 0, c)) z`, i.e. the value
`[Rval (dRat a) z + ∑ i Rval (c i * (rn i / rd i)) z] * y1 z + Rval a z * deriv y1 z
   + ∑ i Rval (dRat (c i)) z * J i z`. -/
theorem hasDerivAt_wev_bzero {k : ℕ} (p2 p1 p0 : Polynomial ℂ) (rn rd : Fin k → Polynomial ℂ)
    {x0 : ℂ} {δ : ℝ} {y1 : ℂ → ℂ} {J : Fin k → ℂ → ℂ} {a : RatFunc ℂ} {c : Fin k → RatFunc ℂ}
    {z : ℂ}
    (hz : z ∈ Metric.ball x0 δ)
    (hy1d : DifferentiableOn ℂ y1 (Metric.ball x0 δ))
    (hJderiv : ∀ i, ∀ w ∈ Metric.ball x0 δ,
      HasDerivAt (J i) ((rn i).eval w / (rd i).eval w * y1 w) w)
    (hp2 : p2.eval z ≠ 0) (hrd : ∀ i, (rd i).eval z ≠ 0)
    (ha : a.denom.eval z ≠ 0) (hc : ∀ i, (c i).denom.eval z ≠ 0) :
    HasDerivAt (fun w => Work.GenShared.Rval a w * y1 w + ∑ i, Work.GenShared.Rval (c i) w * J i w)
      (Work.GenShared.Wev y1 J (Work.GenShared.Dv p2 p1 p0 rn rd (a, 0, c)) z) z := by
  -- The value of `Wev y1 J (Dv … (a,0,c)) z`, expanded using that the connection on `(a,0,c)`
  -- has components `dRat a + ∑ᵢ cᵢ·(rnᵢ/rdᵢ)`, `a`, `(dRat (cᵢ))ᵢ`.
  have hval : Wev y1 J (Dv p2 p1 p0 rn rd (a, 0, c)) z
      = (Rval (dRat a) z * y1 z + Rval a z * deriv y1 z)
        + ∑ i, (Rval (dRat (c i)) z * J i z
            + Rval (c i) z * ((rn i).eval z / (rd i).eval z * y1 z)) := by
    have hd1 : (Dv p2 p1 p0 rn rd (a, 0, c)).1
        = dRat a + ∑ i, c i * (algebraMap (Polynomial ℂ) (RatFunc ℂ) (rn i)
            / algebraMap (Polynomial ℂ) (RatFunc ℂ) (rd i)) := by
      simp [Dv]
    have hd21 : (Dv p2 p1 p0 rn rd (a, 0, c)).2.1 = a := by simp [Dv]
    have hd22 : (Dv p2 p1 p0 rn rd (a, 0, c)).2.2 = fun i => dRat (c i) := by
      funext i; simp [Dv]
    have hgre : ∀ i, Rreg (c i * (algebraMap (Polynomial ℂ) (RatFunc ℂ) (rn i)
        / algebraMap (Polynomial ℂ) (RatFunc ℂ) (rd i))) z :=
      fun i => rreg_mul (hc i) (rreg_div_poly (hrd i))
    have hsumre : Rreg (∑ i, c i * (algebraMap (Polynomial ℂ) (RatFunc ℂ) (rn i)
        / algebraMap (Polynomial ℂ) (RatFunc ℂ) (rd i))) z :=
      rreg_sum _ hgre
    have hRadd : Rval (dRat a + ∑ i, c i * (algebraMap (Polynomial ℂ) (RatFunc ℂ) (rn i)
          / algebraMap (Polynomial ℂ) (RatFunc ℂ) (rd i))) z
        = Rval (dRat a) z + ∑ i, Rval (c i) z * ((rn i).eval z / (rd i).eval z) := by
      rw [Rval_add _ _ _ (rreg_dRat ha) hsumre]
      congr 1
      rw [Rval_sum _ _ hgre]
      apply Finset.sum_congr rfl
      intro i _
      rw [Rval_mul _ _ _ (hc i) (rreg_div_poly (hrd i)), Rval_div _ _ _ (hrd i)]
    have hsRHS : (∑ i, (Rval (dRat (c i)) z * J i z
          + Rval (c i) z * ((rn i).eval z / (rd i).eval z * y1 z)))
        = ∑ i, (Rval (dRat (c i)) z * J i z
          + (Rval (c i) z * ((rn i).eval z / (rd i).eval z)) * y1 z) :=
      Finset.sum_congr rfl (fun i _ => by ring)
    simp only [Wev, hd1, hd21, hd22]
    rw [hRadd, add_mul]
    rw [hsRHS, Finset.sum_add_distrib, ← Finset.sum_mul]
    ring
  have hy1_at : DifferentiableAt ℂ y1 z :=
    hy1d.differentiableAt (Metric.isOpen_ball.mem_nhds hz)
  have hmul : HasDerivAt (fun w => Rval a w * y1 w)
      (Rval (dRat a) z * y1 z + Rval a z * deriv y1 z) z :=
    (hasDerivAt_rval a z ha).mul hy1_at.hasDerivAt
  have hsum : HasDerivAt (fun w => ∑ i, Rval (c i) w * J i w)
      (∑ i, (Rval (dRat (c i)) z * J i z
        + Rval (c i) z * ((rn i).eval z / (rd i).eval z * y1 z))) z := by
    have h := HasDerivAt.sum (u := Finset.univ)
      (A := fun i w => Rval (c i) w * J i w)
      (A' := fun i => Rval (dRat (c i)) z * J i z
        + Rval (c i) z * ((rn i).eval z / (rd i).eval z * y1 z))
      (fun i _ => (hasDerivAt_rval (c i) z (hc i)).mul (hJderiv i z hz))
    have hfun : (∑ i, fun w => Rval (c i) w * J i w)
        = (fun w => ∑ i, Rval (c i) w * J i w) := by
      funext w; simp
    rw [hfun] at h
    exact h
  rw [hval]
  exact hmul.add hsum

end Work.C17y
