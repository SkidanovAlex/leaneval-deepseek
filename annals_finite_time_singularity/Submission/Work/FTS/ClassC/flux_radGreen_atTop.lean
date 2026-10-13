import Mathlib.Analysis.Calculus.Deriv.Basic
import Submission.Work.FTS.ClassC.ModeEnergyDefs
import Submission.Work.FTS.PhiStar.Radial.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

set_option autoImplicit false

/-!
# `Work.FTS.ClassC.flux_radGreen_atTop`

The boundary term `flux α a` of the per-mode weighted energy identity
(`FTS/ClassC/ModeEnergyDefs.lean`) is

  `flux α a z = α²·(rw z · a' a) - (α²/2)·(rwb z · a²) + ((α(5+α))/2)·(rw z / z)·a²`,

with `rw z = (1+z)^4/z^2` and `rwb z = (1+z)^3(2z-2)/z^3`.  The two hypotheses of the target
say that, for `a = radGreen α m c`,

  `z·a(z)² → 0`  and  `z·a(z)·(z·a'(z)) → 0`  as `z → ∞`.

Both decay statements are *exactly* what is needed: each of the three coefficients of `flux`
equals an explicit bounded function times one of the two small quantities.  Since
`(1+z)/z → 1` and `(2z-2)/z → 2`, we have (for `z ≠ 0`)

  `rw z ·(a'a)   = ((1+z)/z)^4 · (z·a·(z a'))`,
  `rwb z·a²      = (((1+z)/z)^3·((2z-2)/z)) · (z·a²)`,
  `(rw z/z)·a²   = ((1+z)/z)^4 · (z·a²)`,

and each right-hand side is the product of a convergent coefficient with a function tending to
`0`, hence tends to `0`.  The conclusion follows by linearity.

Note that neither `hα` nor `m` nor `c` is used: the statement holds for any `α` and any
function satisfying the two decay hypotheses.
-/

/-- `(1+z)/z → 1` at `atTop`. -/
private lemma tendsto_one_add_div_self : Tendsto (fun z : ℝ => (1 + z) / z) atTop (nhds 1) := by
  have hdiv : Tendsto (fun z : ℝ => (1 : ℝ) / z) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (Filter.tendsto_id (α := ℝ) (x := Filter.atTop))
  have h : Tendsto (fun z : ℝ => 1 + 1 / z) atTop (nhds 1) := by
    simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1))).add hdiv
  refine Tendsto.congr' ?_ h
  filter_upwards [Filter.eventually_ne_atTop (α := ℝ) (0 : ℝ)] with z hz
  field_simp
  ring

/-- `((1+z)/z)^n → 1` at `atTop`. -/
private lemma tendsto_one_add_div_self_pow (n : ℕ) :
    Tendsto (fun z : ℝ => ((1 + z) / z) ^ n) atTop (nhds 1) := by
  simpa using tendsto_one_add_div_self.pow n

/-- `(2z-2)/z → 2` at `atTop`. -/
private lemma tendsto_two_mul_sub_div_self :
    Tendsto (fun z : ℝ => (2 * z - 2) / z) atTop (nhds 2) := by
  have hdiv : Tendsto (fun z : ℝ => (2 : ℝ) / z) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (Filter.tendsto_id (α := ℝ) (x := Filter.atTop))
  have h : Tendsto (fun z : ℝ => 2 - 2 / z) atTop (nhds 2) := by
    simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (2 : ℝ)) atTop (nhds 2))).sub hdiv
  refine Tendsto.congr' ?_ h
  filter_upwards [Filter.eventually_ne_atTop (α := ℝ) (0 : ℝ)] with z hz
  field_simp
  try ring

theorem flux_radGreen_atTop {α : ℝ} (hα : 0 < α) (m : ℕ) {c : ℝ → ℝ}
    (h1 : Filter.Tendsto (fun z => z * (Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2)
      Filter.atTop (nhds 0))
    (h2 : Filter.Tendsto
      (fun z => z * (Work.FTS.PhiStar.Radial.radGreen α m c z)
        * (z * deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z)) Filter.atTop (nhds 0)) :
    Filter.Tendsto (Work.FTS.ClassC.flux α (Work.FTS.PhiStar.Radial.radGreen α m c))
      Filter.atTop (nhds 0) := by
  let a : ℝ → ℝ := Work.FTS.PhiStar.Radial.radGreen α m c
  have h1' : Tendsto (fun z : ℝ => z * (a z) ^ 2) atTop (nhds 0) := h1
  have h2' : Tendsto (fun z : ℝ => z * a z * (z * deriv a z)) atTop (nhds 0) := h2
  have he1 : Tendsto (fun z : ℝ => ((1 + z) / z) ^ 4) atTop (nhds 1) :=
    tendsto_one_add_div_self_pow 4
  have he2 : Tendsto (fun z : ℝ => ((1 + z) / z) ^ 3 * ((2 * z - 2) / z)) atTop (nhds 2) := by
    simpa using (tendsto_one_add_div_self_pow 3).mul tendsto_two_mul_sub_div_self
  have hA : Tendsto (fun z : ℝ => α ^ 2 * (((1 + z) / z) ^ 4 * (z * a z * (z * deriv a z))))
      atTop (nhds 0) := by
    simpa using ((he1.mul h2').const_mul (α ^ 2))
  have hB : Tendsto (fun z : ℝ =>
      (α ^ 2 / 2) * (((1 + z) / z) ^ 3 * ((2 * z - 2) / z) * (z * (a z) ^ 2))) atTop (nhds 0) := by
    simpa using ((he2.mul h1').const_mul (α ^ 2 / 2))
  have hC : Tendsto (fun z : ℝ => ((α * (5 + α)) / 2) * (((1 + z) / z) ^ 4 * (z * (a z) ^ 2)))
      atTop (nhds 0) := by
    simpa using ((he1.mul h1').const_mul ((α * (5 + α)) / 2))
  have hF : Tendsto (fun z : ℝ =>
        α ^ 2 * (((1 + z) / z) ^ 4 * (z * a z * (z * deriv a z)))
        - (α ^ 2 / 2) * (((1 + z) / z) ^ 3 * ((2 * z - 2) / z) * (z * (a z) ^ 2))
        + ((α * (5 + α)) / 2) * (((1 + z) / z) ^ 4 * (z * (a z) ^ 2))) atTop (nhds 0) := by
    simpa using ((hA.sub hB).add hC)
  refine Tendsto.congr' ?_ hF
  filter_upwards [Filter.eventually_ne_atTop (α := ℝ) (0 : ℝ)] with z hz
  simp only [flux, Work.FTS.ClassC.rw, Work.FTS.ClassC.rwb, a]
  field_simp
  try ring

end Work.FTS.ClassC
