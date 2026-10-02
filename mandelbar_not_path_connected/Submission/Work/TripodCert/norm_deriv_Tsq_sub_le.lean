import Mathlib
import Submission.Work.Landing.Core
import Submission.Work.SeedDyn.deriv_Tsq_ne_zero

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.TripodCert

/-- Lipschitz-type estimate for the derivative of the holomorphic second iterate
`Tsq c z = (z² + c̄)² + c` of the tricorn map `T_c z = z̄² + c`.

Since `deriv (Tsq c) w = 4 w (w² + c̄)` is a polynomial, the difference of the derivatives
factors as
`deriv (Tsq c) u - deriv (Tsq c) v = 4 (u - v) (u² + u v + v² + c̄)`,
and the triangle inequality bounds the remaining factor by
`‖u‖² + ‖u‖‖v‖ + ‖v‖² + ‖c‖`.  This is the quantitative continuity of `deriv (Tsq c)`
used to certify that the tripod of `Tsq c` is a locally finite tree. -/
theorem norm_deriv_Tsq_sub_le (c u v : ℂ) :
    ‖deriv (Work.Landing.Tsq c) u - deriv (Work.Landing.Tsq c) v‖
      ≤ 4 * ‖u - v‖ * (‖u‖ ^ 2 + ‖u‖ * ‖v‖ + ‖v‖ ^ 2 + ‖c‖) := by
  -- Bound on the quadratic factor appearing in the factorisation.
  have h2 : ‖u ^ 2 + u * v + v ^ 2 + star c‖ ≤ ‖u‖ ^ 2 + ‖u‖ * ‖v‖ + ‖v‖ ^ 2 + ‖c‖ := by
    calc ‖u ^ 2 + u * v + v ^ 2 + star c‖
        ≤ ‖u ^ 2 + u * v + v ^ 2‖ + ‖star c‖ := norm_add_le _ _
      _ ≤ ‖u ^ 2 + u * v‖ + ‖v ^ 2‖ + ‖star c‖ := by gcongr; exact norm_add_le _ _
      _ ≤ ‖u ^ 2‖ + ‖u * v‖ + ‖v ^ 2‖ + ‖star c‖ := by gcongr; exact norm_add_le _ _
      _ = ‖u‖ ^ 2 + ‖u‖ * ‖v‖ + ‖v‖ ^ 2 + ‖c‖ := by
          rw [norm_pow, norm_pow, norm_mul, norm_star]
  -- The explicit difference of the derivatives.
  have hkey : deriv (Work.Landing.Tsq c) u - deriv (Work.Landing.Tsq c) v
      = 4 * (u - v) * (u ^ 2 + u * v + v ^ 2 + star c) := by
    rw [Work.SeedDyn.deriv_Tsq_eq c u, Work.SeedDyn.deriv_Tsq_eq c v]; ring
  rw [hkey, norm_mul, norm_mul]
  have h4 : ‖(4 : ℂ)‖ = 4 := by norm_num
  rw [h4]
  calc 4 * ‖u - v‖ * ‖u ^ 2 + u * v + v ^ 2 + star c‖
      ≤ 4 * ‖u - v‖ * (‖u‖ ^ 2 + ‖u‖ * ‖v‖ + ‖v‖ ^ 2 + ‖c‖) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)

end Work.TripodCert
