/-
# **D5**: the holomorphic second return map `Tsq c = (T_c)^2` is conformal on the escaping set

Area `Submission/Work/SeedDyn/` of the mandelbar project.  For a parameter `c` of the mandelbar
(`LeanEval.ComplexAnalysis.Mandelbar`) the *escaping set* `esc c = Work.ParamRays.escapingSet c` is
the complement of the filled Julia set of the antiholomorphic quadratic `T_c(z) = z̄² + c`, and
`Work.Landing.Tsq c z = (z² + c̄)² + c` is its holomorphic second iterate.

The result proved here is item **D5** of the design note `NOTES_LEAD_mandelbar_seed.md`: `Tsq c`
has no critical point in the escaping set, i.e. it is (locally) conformal there.

## The mathematics

Since `Tsq c z = (z² + c̄)² + c` is a quartic polynomial,

  `deriv (Tsq c) w = 4 · w · (w² + c̄)`  (`deriv_Tsq_eq`),

so `deriv (Tsq c) w = 0` iff `w = 0` or `w² + c̄ = 0`.  Both alternatives are impossible for a
point `w` of the escaping set:

* `T_c w = conj (w² + c̄)`, so `w² + c̄ = 0` means `T_c w = 0` — but the escaping set is forward
  invariant under `T_c` (`Work.SeedDyn.Tantibar_mem_esc`), and `0 ∉ esc c` because `c` lies in the
  mandelbar, i.e. the critical orbit of `T_c` is bounded;
* `w = 0` is excluded for the same reason, `0 ∉ esc c`.

Hence the factorisation `4 · w · (w² + c̄)` never vanishes on `esc c`.

## Main results

* `Work.SeedDyn.deriv_Tsq_eq` — the explicit derivative `4 · w · (w² + c̄)`;
* `Work.SeedDyn.Tantibar_eq_star` — `T_c w = conj (w² + c̄)`;
* `Work.SeedDyn.zero_notMem_esc` — for `c ∈ M*` the critical point `0` does not escape;
* `Work.SeedDyn.deriv_Tsq_ne_zero` (**D5**) — the target.
-/
import Mathlib
import Submission.Work.SeedDyn.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Topology ComplexConjugate

namespace Work.SeedDyn

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

noncomputable section

/-! ## The explicit derivative of `Tsq c` and the conjugate form of `Tantibar c` -/

/-- The derivative of the quartic polynomial `Tsq c z = (z² + c̄)² + c`:
`deriv (Tsq c) w = 4 · w · (w² + c̄)`. -/
theorem deriv_Tsq_eq (c w : ℂ) : deriv (Work.Landing.Tsq c) w = 4 * w * (w ^ 2 + star c) := by
  show deriv (fun z : ℂ => (z ^ 2 + star c) ^ 2 + c) w = 4 * w * (w ^ 2 + star c)
  have h1 : HasDerivAt (fun z : ℂ => z ^ 2 + star c) (2 * w) w := by
    simpa using ((hasDerivAt_id w).pow 2).add_const (star c)
  have h2 : HasDerivAt (fun z : ℂ => (z ^ 2 + star c) ^ 2 + c)
      (2 * (w ^ 2 + star c) * (2 * w)) w := by
    simpa using ((h1.pow 2).add_const c)
  rw [h2.deriv]
  ring

/-- The conjugate of `Tantibar c w` is the factor `w² + c̄` occurring in `deriv (Tsq c)`.
Equivalently `Tantibar c w = conj (w² + c̄)`. -/
theorem Tantibar_eq_star (c w : ℂ) : Tantibar c w = star (w ^ 2 + star c) := by
  simp [Tantibar]

/-! ## The critical point does not escape -/

/-- For a parameter `c` of the mandelbar the critical point `0` does not belong to the escaping
set: by definition of the mandelbar the critical orbit is bounded, so `T_c` does not escape from
`0`. -/
theorem zero_notMem_esc {c : ℂ} (hc : c ∈ Mandelbar) : (0 : ℂ) ∉ esc c := by
  rw [mem_esc]
  exact fun h => (Work.ParamRays.mem_mandelbar_iff_not_escaping c).mp hc h

/-! ## D5 -/

/-- **D5.**  For `c` in the mandelbar the holomorphic second iterate `Tsq c = (T_c)^[2]` has no
critical point in the escaping set: its derivative is nonzero at every escaping point. -/
theorem deriv_Tsq_ne_zero {c : ℂ} (hc : c ∈ LeanEval.ComplexAnalysis.Mandelbar) {z : ℂ}
    (hz : z ∈ Work.SeedDyn.esc c) : deriv (Work.Landing.Tsq c) z ≠ 0 := by
  have hz0 : z ≠ 0 := fun h0 => zero_notMem_esc hc (h0 ▸ hz)
  have hzc : z ^ 2 + star c ≠ 0 := by
    intro h0
    have hT : Tantibar c z = 0 := by rw [Tantibar_eq_star, h0, star_zero]
    exact zero_notMem_esc hc (hT ▸ Tantibar_mem_esc hz)
  intro hzero
  rw [deriv_Tsq_eq] at hzero
  exact (mul_ne_zero (mul_ne_zero (by norm_num) hz0) hzc) hzero

end

end Work.SeedDyn
