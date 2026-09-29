import Mathlib
import Submission.Work.C17RC.defs

namespace Work.C17RC

/-- **Clearing denominators in a Riccati equation.**  If the Riccati equation
`p2*(u' + u^2) + p1*u + p0 = 0` holds in `K(X)` (with `'` = `Submission.CDT.dRat`), then the
denominator-cleared identity
`p2*(u.num'*u.denom - u.num*u.denom') + p2*u.num^2 + p1*u.num*u.denom + p0*u.denom^2 = 0`
holds in `K[X]`.  (`u.num`, `u.denom` are the canonical numerator/denominator of `u : RatFunc K`;
`u.denom` is monic and `IsCoprime u.num u.denom`.) -/
theorem riccati_clear {K : Type*} [Field K] (p2 p1 p0 : Polynomial K) (u : RatFunc K)
    (h : algebraMap (Polynomial K) (RatFunc K) p2 * (Submission.CDT.dRat u + u ^ 2)
      + algebraMap (Polynomial K) (RatFunc K) p1 * u
      + algebraMap (Polynomial K) (RatFunc K) p0 = 0) :
    p2 * (u.num.derivative * u.denom - u.num * u.denom.derivative) + p2 * u.num ^ 2
      + p1 * u.num * u.denom + p0 * u.denom ^ 2 = 0 := by
  have hden : u.denom ≠ 0 := RatFunc.denom_ne_zero u
  have hAmap : algebraMap (Polynomial K) (RatFunc K) u.denom ≠ 0 := by simpa using hden
  have hnum : u = algebraMap (Polynomial K) (RatFunc K) u.num
      / algebraMap (Polynomial K) (RatFunc K) u.denom := (RatFunc.num_div_denom u).symm
  have key : (algebraMap (Polynomial K) (RatFunc K))
      (p2 * (u.num.derivative * u.denom - u.num * u.denom.derivative) + p2 * u.num ^ 2
        + p1 * u.num * u.denom + p0 * u.denom ^ 2) = 0 := by
    rw [hnum, Submission.CDT.dRat_div] at h
    simp only [map_add, map_mul, map_sub, map_pow] at h ⊢
    field_simp at h ⊢
    ring_nf at h ⊢
    linear_combination h
  exact RatFunc.algebraMap_injective K (by simpa using key)

end Work.C17RC
