/-
Copyright: work module for the Elgindi finite-time singularity project.

# `abs_mixed_le_HkNorm_RegQ`: the pointwise `L^∞`–`ℋ⁴` trade-off in the interior class

Elgindi's Corollary `SecondDerivativesBounded` bounds every mixed derivative
`D_z^b D_θ^a f` of order `a + b ≤ 2` pointwise inside the quadrant by

  `10 / √(γ-1) · |f|_{ℋ⁴}`.

The available form of the estimate with the *interior supremum* is
`Work.FTS.H2.mixed_supAbsO_le` (for `SmoothQuad f ∧ HkMem α 4 f ∧ BdryTraces α 4 f`).
Passing from the interior *supremum* to the *pointwise* statement is delicate because
`supAbsO` is Lean's junk value `0` on an unbounded set: to conclude
`|g z θ| ≤ supAbsO g` from a bound on `supAbsO g` one has to know that `g` is bounded on the
open quadrant.  Such a (numerical constant unknown, positivity irrelevant) bound is the
pointwise form `Work.FTS.H2.HQ.LinfQpt` of the same trade-off, whose two one-dimensional
Hardy ingredients are `Work.FTS.H2.HardyThetaO` (angular) and `Work.FTS.H2.hardyZ_open`
(radial).  This is the same route as the `(b,a) = (0,0)` instance
`Work.FTS.Nonlinear.Pieces.rl1Tools.abs_le_ten_sqrt_gam`, here for all `a + b ≤ 2`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.H2.LinfQ
import Submission.Work.FTS.H2.HQ.LinfQpt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.RegPkgGal.Der

set_option autoImplicit false

/-- **The interior `L^∞`–`ℋ⁴` trade-off in the class `RegQ`, pointwise.**

For `f` of class `Work.FTS.Nonlin.RegQ β 4` (that is `SmoothQuad f`, `HkMem β 4 f` and
`BdryTraces β 4 f`) with `0 < β ≤ 1`, every mixed derivative `D_z^b D_θ^a f` with `a + b ≤ 2`
is bounded at each point `(z,θ)` of the *open* quadrant by
`10 / √(γ-1) · |f|_{ℋ⁴}`.  (No bound is claimed at `z = 0` or at the angular boundaries
`θ = 0, π/2`: `RegQ` leaves the values there free.) -/
theorem abs_mixed_le_HkNorm_RegQ {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) {f : ℝ → ℝ → ℝ}
    (hreg : Work.FTS.Nonlin.RegQ β 4 f) (b a : ℕ) (hab : a + b ≤ 2) {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ' : θ < Real.pi / 2) :
    |Work.Spaces.mixed b a f z θ| ≤ 10 / Real.sqrt (Work.Spaces.gam β - 1) *
      Work.Spaces.HkNorm β 4 f := by
  -- the pointwise form of the same trade-off, with a finite (but numerically unknown) constant
  obtain ⟨C, _hCpos, hL⟩ := Work.FTS.H2.HQ.LinfQpt
  -- the two one-dimensional Hardy inequalities, in the shapes `LinfQpt` asks them for
  have hAng : ∀ (u : ℝ → ℝ → ℝ) (z : ℝ), Work.FTS.LocData.SmoothQuad u →
      z ∈ Set.Ioi (-1) → Tendsto (fun θ => u z θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) →
      IntegrableOn (fun σ => (Work.Spaces.pth u z σ) ^ 2
        * Real.sin (2 * σ) ^ (2 - Work.Spaces.gam β)) Work.Spaces.Iθ →
      ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), u z θ ^ 2
        ≤ 100 / (Work.Spaces.gam β - 1) * ∫ σ in Work.Spaces.Iθ,
            Work.Spaces.pth u z σ ^ 2 * Real.sin (2 * σ) ^ (2 - Work.Spaces.gam β) :=
    fun u z hu hz h0 hint => Work.FTS.H2.HardyThetaO β hβ hβ1 u z hu hz h0 hint
  have hRad : ∀ (v : ℝ → ℝ), ContDiffOn ℝ 1 v (Set.Ioi 0) → Tendsto v atTop (nhds 0) →
      IntegrableOn (fun s => (s * deriv v s) ^ 2 * Work.Spaces.w s ^ 2) Work.Spaces.Iz →
      ∀ z ∈ Set.Ioi 0, v z ^ 2
        ≤ ∫ s in Work.Spaces.Iz, (s * deriv v s) ^ 2 * Work.Spaces.w s ^ 2 :=
    fun v hcd hdec hint => Work.FTS.H2.hardyZ_open hcd hdec hint
  -- a uniform (but numerically unknown) bound on the open quadrant
  have hglobal : ∀ z' θ', 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
      |Work.Spaces.mixed b a f z' θ'| ≤ C / Real.sqrt (Work.Spaces.gam β - 1)
        * Work.FTS.Nonlin.Xn β f :=
    fun z' θ' hz' hθ0 hθ1 => hL β f b a hβ hβ1 hab hreg hAng hRad z' hz' θ' hθ0 hθ1
  -- so `supAbsO` is the honest supremum, and the pointwise value is bounded by it
  have hsup : |Work.Spaces.mixed b a f z θ| ≤ Work.FTS.H2.supAbsO (Work.Spaces.mixed b a f) :=
    Work.FTS.H2.le_supAbsO hz hθ hθ' hglobal
  have hsupb : Work.FTS.H2.supAbsO (Work.Spaces.mixed b a f)
      ≤ 10 / Real.sqrt (Work.Spaces.gam β - 1) * Work.Spaces.HkNorm β 4 f :=
    Work.FTS.H2.mixed_supAbsO_le β f hβ hβ1 hreg.1 hreg.2.1 hreg.2.2 b a hab
  exact le_trans hsup hsupb

end Work.FTS.RegPkgGal.Der
