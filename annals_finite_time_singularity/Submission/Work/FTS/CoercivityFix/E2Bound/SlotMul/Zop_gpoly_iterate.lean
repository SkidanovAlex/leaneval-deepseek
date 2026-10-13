/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `Zop`-iterates of `gpoly`

Under the Möbius chart `zchart z = (z - 1)/(z + 1)` the one-dimensional operator
`Zop u = z ↦ z·u'(z)` becomes the polynomial map `Tmul P = ½(1 - X²)P'`:
for `z > 0`,

    `Zop (gpoly P) z = gpoly (Tmul P) z`          (`Zop_gpoly_step`)

where `gpoly P z = P.eval (zchart z)`.  Iterating this (`Zop_gpoly_iterate`)
identifies every `Zop`-iterate of a polynomial in the chart with the polynomial
in the chart obtained by iterating `Tmul` on the coefficients.  Consequently
every `Zop^[b] (gpoly P)` is bounded on `(0,∞)` (the chart variable lies in
`(-1,1)` there), which is what `zop_phi_bound` consumes.

The key point in the induction is that although `Zop` involves `deriv` (and so
does not commute with pointwise equality), each iterate *is* a polynomial in the
chart, hence the two sides of the induction hypothesis agree on a whole
neighbourhood of `z`, and their derivatives agree there too
(`Filter.EventuallyEq.deriv_eq`).
-/
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.CoercivityFix.E2Bound.ZopPhiDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter Polynomial

namespace Work.FTS.CoercivityFix.E2Bound

/-- The Möbius chart `z ↦ (z - 1)/(z + 1)` has derivative `2/(z+1)²`. -/
lemma hasDerivAt_zchart (z : ℝ) (hz : z ≠ -1) :
    HasDerivAt (fun w => zchart w) (2 / (z + 1) ^ 2) z := by
  have hz1 : z + 1 ≠ 0 := by intro h; exact hz (by linarith)
  have h : HasDerivAt (fun w : ℝ => (w - 1) / (w + 1)) (2 / (z + 1) ^ 2) z := by
    have hd := ((hasDerivAt_id z).sub_const 1).div ((hasDerivAt_id z).add_const 1) hz1
    convert hd using 1
    · funext w
      simp only [id_eq, Pi.div_apply]
    · simp only [id_eq]
      ring
  simpa only [zchart_apply] using h

/-- One step of the intertwining: on `(0,∞)`, `Zop` acting on `gpoly P` is
`gpoly (Tmul P)`. -/
lemma Zop_gpoly_step (P : Polynomial ℝ) {z : ℝ} (hz : 0 < z) :
    Work.Spaces.Zop (gpoly P) z = gpoly (Tmul P) z := by
  have hz1 : z + 1 ≠ 0 := by intro h; linarith
  have hchain : deriv (fun w => P.eval (zchart w)) z
      = (Polynomial.derivative P).eval (zchart z) * (2 / (z + 1) ^ 2) := by
    have h : HasDerivAt (fun w => P.eval (zchart w))
        ((Polynomial.derivative P).eval (zchart z) * (2 / (z + 1) ^ 2)) z :=
      (Polynomial.hasDerivAt P (zchart z)).comp z (hasDerivAt_zchart z (by intro h; linarith))
    exact h.deriv
  have hc : z * (2 / (z + 1) ^ 2) = (1 : ℝ) / 2 * (1 - (zchart z) ^ 2) := by
    rw [zchart]
    field_simp
    ring
  show z * deriv (fun w => P.eval (zchart w)) z = (Tmul P).eval (zchart z)
  rw [hchain]
  simp only [Tmul_apply, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_one, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
  rw [mul_comm ((Polynomial.derivative P).eval (zchart z)) (2 / (z + 1) ^ 2), ← mul_assoc, hc]

end Work.FTS.CoercivityFix.E2Bound

namespace Work.FTS.CoercivityFix.E2Bound.SlotMul

theorem Zop_gpoly_iterate (P : Polynomial ℝ) (b : ℕ) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      (Work.Spaces.Zop^[b] (Work.FTS.CoercivityFix.E2Bound.gpoly P)) z
        = Work.FTS.CoercivityFix.E2Bound.gpoly
            (Work.FTS.CoercivityFix.E2Bound.Tmul^[b] P) z := by
  induction b with
  | zero => intro z hz; simp
  | succ b ih =>
    intro z hz
    have hmem : Set.Ioi (0 : ℝ) ∈ 𝓝 z := isOpen_Ioi.mem_nhds hz
    have heq : (Work.Spaces.Zop^[b] (Work.FTS.CoercivityFix.E2Bound.gpoly P))
        =ᶠ[𝓝 z] Work.FTS.CoercivityFix.E2Bound.gpoly
            (Work.FTS.CoercivityFix.E2Bound.Tmul^[b] P) :=
      Filter.eventually_of_mem hmem (fun w hw => ih w hw)
    have hderiv : deriv (Work.Spaces.Zop^[b] (Work.FTS.CoercivityFix.E2Bound.gpoly P)) z
        = deriv (Work.FTS.CoercivityFix.E2Bound.gpoly
            (Work.FTS.CoercivityFix.E2Bound.Tmul^[b] P)) z := heq.deriv_eq
    rw [Function.iterate_succ_apply']
    rw [show Work.Spaces.Zop (Work.Spaces.Zop^[b] (Work.FTS.CoercivityFix.E2Bound.gpoly P)) z
        = Work.Spaces.Zop (Work.FTS.CoercivityFix.E2Bound.gpoly
            (Work.FTS.CoercivityFix.E2Bound.Tmul^[b] P)) z by
      simp only [Work.Spaces.Zop, hderiv]]
    rw [Work.FTS.CoercivityFix.E2Bound.Zop_gpoly_step
        (Work.FTS.CoercivityFix.E2Bound.Tmul^[b] P) hz]
    rw [Function.iterate_succ_apply']

end Work.FTS.CoercivityFix.E2Bound.SlotMul
