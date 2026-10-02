import Mathlib
import Submission.Work.FatouParabolic.Defs
import Submission.Work.LANDCL.Critical.not_isRepelling_criticalValue
import Submission.Work.LANDCL.Deriv.preimage_zero

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The critical points of the iterates of `Tsq c`

The holomorphic second iterate `Tsq c z = (z² + c̄)² + c` of the antiholomorphic quadratic
`T_c(z) = z̄² + c` has derivative

  `deriv (Tsq c) w = 4·w·(w² + c̄) = 4·w·conj (T_c w)`

(`Work.LANDCL.Critical.Tsq_deriv`), so its critical points are exactly the critical point `0` and
the `0`-preimages of `T_c`:

  `deriv (Tsq c) w = 0 ↔ w = 0 ∨ T_c w = 0`.

By the chain rule, the derivative of an iterate is the product of the derivatives along the orbit
(`Work.LANDCL.Critical.deriv_iterate_eq_prod`), so `deriv ((Tsq c)^[m]) w` vanishes exactly when
some point `(Tsq c)^[j] w`, `j < m`, is a critical point of `Tsq c`.  This is the statement proved
here; it is the criterion used to locate the critical points of the second return map.
-/

namespace Work.FatouParabolic.Critical

open LeanEval.ComplexAnalysis (Tantibar)

/-- **The critical points of `Tsq c`.**  Since `deriv (Tsq c) z = 4·z·(z² + c̄)`, the derivative
vanishes exactly at the critical point `0` and at the preimages of the critical point `0` under
`T_c`. -/
lemma deriv_tsq_eq_zero_iff (c z : ℂ) :
    deriv (Work.Landing.Tsq c) z = 0 ↔ z = 0 ∨ Tantibar c z = 0 := by
  rw [Work.LANDCL.Critical.Tsq_deriv]
  have h4 : (4 : ℂ) * z * (z ^ 2 + star c) = (4 * z) * (z ^ 2 + star c) := by ring
  rw [h4, mul_eq_zero]
  have h4z : (4 : ℂ) * z = 0 ↔ z = 0 := by
    constructor
    · intro h; exact (mul_eq_zero.mp h).resolve_left (by norm_num)
    · intro h; rw [h, mul_zero]
  have hc : z ^ 2 + star c = 0 ↔ Tantibar c z = 0 := by
    rw [← Work.LANDCL.Critical.star_Tantibar, star_eq_zero]
  rw [h4z, hc]

/-- **The critical points of the iterates of `Tsq c`.**  The derivative of the `m`-th iterate of
`Tsq c` at `w` vanishes exactly when some point of the finite orbit
`w, (Tsq c) w, …, (Tsq c)^[m-1] w` is a critical point of `Tsq c`, i.e. is either `0` or a
preimage of `0` under `T_c`. -/
theorem deriv_iterate_tsq_eq_zero_iff (c : ℂ) {w : ℂ} {m : ℕ} :
    deriv ((Work.Landing.Tsq c)^[m]) w = 0 ↔
      ∃ j ∈ Finset.range m, (Work.Landing.Tsq c)^[j] w = 0 ∨
        LeanEval.ComplexAnalysis.Tantibar c ((Work.Landing.Tsq c)^[j] w) = 0 := by
  rw [Work.LANDCL.Critical.deriv_iterate_eq_prod (Work.LANDCL.Critical.differentiable_Tsq c) m w,
    Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨j, hj, hz⟩
    exact ⟨j, hj, (deriv_tsq_eq_zero_iff c _).mp hz⟩
  · rintro ⟨j, hj, hz⟩
    exact ⟨j, hj, (deriv_tsq_eq_zero_iff c _).mpr hz⟩

end Work.FatouParabolic.Critical
