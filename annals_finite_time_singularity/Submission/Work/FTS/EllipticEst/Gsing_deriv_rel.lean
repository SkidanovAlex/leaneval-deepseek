import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Elliptic.Defs
import Submission.Work.Elliptic.GsingFuncs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

open scoped Real Topology
open MeasureTheory Set Filter

set_option linter.unusedVariables false

/-! ## The first-order relation satisfied by the singular term `Gsing`

`Gsing α F = Gstar α F + Gbar α F` is the singular term `G` of §'The singular term'
(tex 1027) of Elgindi's paper, with the two summands

* `Gstar α F = -(1/(4α)) L₁₂(F)`, and
* `Gbar α F z = -(3/(4α)) z^{-5/α} ∫_0^z s^{(5-α)/α} F_*(s) ds`

(the *pre*-integration-by-parts form of `\bar G`; see `Work.Elliptic.Defs`).

The paper's first integral of the ODE for `G` (tex 1026) is
`R^{(5+α)/α} ∂_R G = -(15/(4α²)) ∫_0^R s^{(5-α)/α} F_*(s) ds`.  Dividing by
`R^{(5+α)/α}` and using `-(15/(4α²)) = (5/(α R)) · (-(3/(4α))) · R^{5/α}` gives exactly

  `α z ∂_z(Gsing α F) z = -5 (Gbar α F) z`   (`z > 0`),

which is the relation proved below.  Written out, `deriv (Gsing α F) z` is the explicit
first-derivative value `DGstar α F z + DGbar α F z` of `Work.Elliptic.GsingFuncs`, and the
identity is purely algebraic: `α z DGstar = (3/4) F_*` while
`α z DGbar = -5 Gbar - (3/4) F_*`, the two `F_*`-terms cancelling.

The corresponding `HasDerivAt` facts live in `Work.Elliptic.Gsing_ode`, but they are
`private` there (and that module additionally proves the second-order ODE, which needs the
extra hypothesis `hFc`); they are re-derived here so that this module is self-contained. -/

/-- `Abar` has derivative `DAbar` at every `z > 0`. -/
private lemma hasDerivAt_Abar_ft (α : ℝ) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (Work.Elliptic.Abar α) (Work.Elliptic.DAbar α z) z := by
  have hzne : z ≠ 0 := ne_of_gt hz
  have hp : HasDerivAt (fun y : ℝ => y ^ (-(5 / α))) ((-(5 / α)) * z ^ (-(5 / α) - 1)) z :=
    Real.hasDerivAt_rpow_const (Or.inl hzne)
  have h := hp.const_mul (-(3 / (4 * α)))
  convert h using 1
  · ext y; rfl
  · show (-(3 / (4 * α)) * (-(5 / α))) * z ^ (-(5 / α) - 1)
        = -(3 / (4 * α)) * (-(5 / α) * z ^ (-(5 / α) - 1))
    ring

/-- `Gstar` has derivative `DGstar`. -/
private lemma hasDerivAt_Gstar_ft (α : ℝ) (F : ℝ → ℝ → ℝ) {z : ℝ}
    (hL12 : HasDerivAt (Work.Elliptic.L12 F) (-(3 * Work.Elliptic.Fstar F z / z)) z) :
    HasDerivAt (Work.Elliptic.Gstar α F) (Work.Elliptic.DGstar α F z) z := by
  have h := hL12.const_mul (-(1 / (4 * α)))
  have hfun : (fun y : ℝ => -(1 / (4 * α)) * Work.Elliptic.L12 F y)
      = Work.Elliptic.Gstar α F := rfl
  rw [hfun] at h
  simpa only [Work.Elliptic.DGstar] using h

/-- `Gbar` has derivative `DGbar` at every `z > 0`. -/
private lemma hasDerivAt_Gbar_ft (α : ℝ) (F : ℝ → ℝ → ℝ) {z : ℝ} (hz : 0 < z)
    (hJ : HasDerivAt (Work.Elliptic.Jfun α F)
      (z ^ ((5 - α) / α) * Work.Elliptic.Fstar F z) z) :
    HasDerivAt (Work.Elliptic.Gbar α F) (Work.Elliptic.DGbar α F z) z := by
  have hA : HasDerivAt (Work.Elliptic.Abar α) (Work.Elliptic.DAbar α z) z :=
    hasDerivAt_Abar_ft α hz
  have h := hA.mul hJ
  have hfun : (Work.Elliptic.Abar α * Work.Elliptic.Jfun α F) = Work.Elliptic.Gbar α F := rfl
  rw [hfun] at h
  simpa only [Work.Elliptic.DGbar] using h

/-- The algebraic content of `α z ∂_z Gsing = -5 Gbar`: `α = 0` and `z = 0` are the only
degeneracies, and they are excluded by the two hypotheses. -/
private lemma gsing_rel_algebra_ft (α : ℝ) (F : ℝ → ℝ → ℝ) {z : ℝ} (hα : 0 < α) (hz : 0 < z) :
    α * z * (Work.Elliptic.DGstar α F z + Work.Elliptic.DGbar α F z)
      = -5 * Work.Elliptic.Gbar α F z := by
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hα0 : α ≠ 0 := ne_of_gt hα
  -- `A := z ^ (-(5/α))` and `z⁻¹` are the only two `z`-powers occurring; all the others
  -- are rewritten in terms of them, exactly as in `Work.Elliptic.Gsing_algebra`.
  have hApos : 0 < z ^ (-(5 / α)) := Real.rpow_pos_of_pos hz _
  have hAne : z ^ (-(5 / α)) ≠ 0 := ne_of_gt hApos
  have hp1 : z ^ (-(5 / α) - 1) = z ^ (-(5 / α)) * z⁻¹ := by
    rw [show -(5 / α) - 1 = -(5 / α) + (-1) by ring, Real.rpow_add hz, Real.rpow_neg_one]
  have hpt : z ^ ((5 - α) / α) = z⁻¹ / z ^ (-(5 / α)) := by
    rw [eq_div_iff hAne, ← Real.rpow_add hz,
      show (5 - α) / α + -(5 / α) = -1 by field_simp; ring, Real.rpow_neg_one]
  unfold Work.Elliptic.DGstar Work.Elliptic.DGbar Work.Elliptic.Abar Work.Elliptic.DAbar
    Work.Elliptic.Gbar Work.Elliptic.Jfun
  rw [hp1, hpt]
  field_simp
  ring

theorem Gsing_deriv_rel (α : ℝ) (F : ℝ → ℝ → ℝ) (hα : 0 < α)
    (hL12 : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun z' => Work.Elliptic.L12 F z') (-(3 * Work.Elliptic.Fstar F z / z)) z)
    (hFc : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.Fstar F) (deriv (Work.Elliptic.Fstar F) z) z)
    (hJ : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun z' => ∫ s in (0 : ℝ)..z', s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s)
        (z ^ ((5 - α) / α) * Work.Elliptic.Fstar F z) z) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      α * z * deriv (Work.Elliptic.Gsing α F) z = -5 * Work.Elliptic.Gbar α F z := by
  intro z hz
  have hzpos : 0 < z := hz
  have hJz : HasDerivAt (Work.Elliptic.Jfun α F)
      (z ^ ((5 - α) / α) * Work.Elliptic.Fstar F z) z := by
    have h := hJ z hz
    have hfun : (fun z' => ∫ s in (0 : ℝ)..z', s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s)
        = Work.Elliptic.Jfun α F := rfl
    rw [hfun] at h
    exact h
  -- `Gsing` is differentiable at `z` with the explicit derivative `DGstar + DGbar`
  have hGsing : HasDerivAt (Work.Elliptic.Gsing α F)
      (Work.Elliptic.DGstar α F z + Work.Elliptic.DGbar α F z) z := by
    have h1 : HasDerivAt (Work.Elliptic.Gstar α F) (Work.Elliptic.DGstar α F z) z :=
      hasDerivAt_Gstar_ft α F (hL12 z hz)
    have h2 : HasDerivAt (Work.Elliptic.Gbar α F) (Work.Elliptic.DGbar α F z) z :=
      hasDerivAt_Gbar_ft α F hzpos hJz
    have h := h1.add h2
    have hfun : (Work.Elliptic.Gstar α F + Work.Elliptic.Gbar α F)
        = Work.Elliptic.Gsing α F := rfl
    rw [hfun] at h
    exact h
  rw [hGsing.deriv]
  exact gsing_rel_algebra_ft α F hα hzpos

end Work.FTS.EllipticEst
