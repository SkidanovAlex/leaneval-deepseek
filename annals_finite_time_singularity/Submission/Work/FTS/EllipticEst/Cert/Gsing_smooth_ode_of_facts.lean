import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Have
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.Elliptic.Defs
import Submission.Work.Elliptic.GsingFuncs
import Submission.Work.Elliptic.Gsing_ode
import Submission.Work.FTS.EllipticEst.HasDerivAt_L12_of_Fstar_facts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cert

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

/-! ## Two analytic ingredients

The self-similar singular term `Gsing α F = Gstar α F + Gbar α F` is built from the two radial
functions

* `L12 F z = 3 ∫_z^∞ F_*(r)/r dr` (the tail integral), and
* `Jfun α F z = ∫_0^z s^{(5-α)/α} F_*(s) ds` (the primitive appearing in `Gbar`),

and the hypotheses of the theorem prescribe the derivatives of both on `(0,∞)`: `hL12` gives
`(L12 F)' = -3F_*(z)/z` and `hasDerivAt_integral_rpow_mul_Fstar` below gives
`(Jfun α F)' = z^{(5-α)/α}F_*(z)`.  Both prescribed derivatives are smooth on `(0,∞)` as soon
as `F_*` is (`hFsm`), so smoothness of `L12 F` and of `Jfun α F` — hence of `Gsing α F` —
follows from the elementary "smooth primitive" lemma below.  The second order ODE is then
`Work.Elliptic.Gsing_ode`. -/

/-- A function which is differentiable on `(0,∞)` with derivative prescribed by a `C^∞`
function `g` on `(0,∞)` is itself `C^∞` on `(0,∞)`.

This is `contDiffOn_infty_iff_deriv_of_isOpen` applied on the open set `(0,∞)`: the derivative
`deriv f` agrees there with `g` (by `HasDerivAt.deriv`), and `ContDiffOn` is a local property. -/
private theorem contDiffOn_infty_of_hasDerivAt {f g : ℝ → ℝ}
    (hderiv : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt f (g z) z)
    (hg : ∀ m : ℕ, ContDiffOn ℝ m g (Set.Ioi 0)) :
    ∀ m : ℕ, ContDiffOn ℝ m f (Set.Ioi 0) := by
  have hgTop : ContDiffOn ℝ ∞ g (Set.Ioi 0) := contDiffOn_infty.mpr hg
  have hfTop : ContDiffOn ℝ ∞ f (Set.Ioi 0) := by
    rw [contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨fun z hz => (hderiv z hz).differentiableAt.differentiableWithinAt, ?_⟩
    exact hgTop.congr (fun z hz => (hderiv z hz).deriv)
  exact contDiffOn_infty.mp hfTop

/-- **FTC for the inner integral of `Gbar`.**  If `F_*` is continuous on `(0,∞)` and
`r ↦ F_*(r)/r` is integrable on `(0,∞)`, then `z ↦ ∫_0^z s^{(5-α)/α} F_*(s) ds` has derivative
`z^{(5-α)/α} F_*(z)` at every `z > 0`.

The point is the interval integrability of the integrand on `(0,z]`: for `0 < s ≤ z` the
identity `s^{(5-α)/α+1} = s^{(5-α)/α}·s` (and `(5-α)/α + 1 = 5/α > 0` independently of `α`)
writes the integrand as the integrable function `F_*(s)/s` times the factor `s^{5/α}`, which is
continuous on the compact `[0,z]`. -/
private theorem hasDerivAt_integral_rpow_mul_Fstar (α : ℝ) (F : ℝ → ℝ → ℝ) (hα : 0 < α)
    (hFsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar F) (Set.Ioi 0))
    (hFint : MeasureTheory.IntegrableOn (fun r : ℝ => Work.Elliptic.Fstar F r / r) (Set.Ioi 0)) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun z' : ℝ => ∫ s in (0 : ℝ)..z', s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s)
        (z ^ ((5 - α) / α) * Work.Elliptic.Fstar F z) z := by
  intro z hz
  have hzpos : (0 : ℝ) < z := hz
  -- `F_*` is continuous on `(0,∞)`, hence so is the integrand
  have hFcont : ContinuousOn (Work.Elliptic.Fstar F) (Set.Ioi (0 : ℝ)) := (hFsm 0).continuousOn
  have hfcontOn : ContinuousOn
      (fun s : ℝ => s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s) (Set.Ioi (0 : ℝ)) := by
    intro x hx
    exact ((Real.continuousAt_rpow_const x ((5 - α) / α)
      (Or.inl (ne_of_gt hx))).continuousWithinAt).mul (hFcont x hx)
  have hcont : ContinuousAt (fun s : ℝ => s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s) z :=
    (Real.continuousAt_rpow_const z ((5 - α) / α) (Or.inl (ne_of_gt hzpos))).mul
      (hFcont.continuousAt (isOpen_Ioi.mem_nhds hz))
  have hmeas : StronglyMeasurableAtFilter
      (fun s : ℝ => s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s) (𝓝 z) MeasureTheory.volume :=
    hfcontOn.stronglyMeasurableAtFilter isOpen_Ioi z hz
  -- integrability of the integrand on the interval `(0,z]`
  have hint : IntegrableOn (fun s : ℝ => s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s)
      (Set.Ioc (0 : ℝ) z) := by
    have hgIoc : IntegrableOn (fun x : ℝ => Work.Elliptic.Fstar F x / x) (Set.Ioc (0 : ℝ) z) :=
      hFint.mono_set (fun x hx => hx.1)
    have hIcc : IntegrableOn (fun x : ℝ => Work.Elliptic.Fstar F x / x) (Set.Icc (0 : ℝ) z) :=
      (integrableOn_Icc_iff_integrableOn_Ioc).mpr hgIoc
    -- the factor `x^((5-α)/α+1) = x^(5/α)` is continuous on the compact `[0,z]`
    have hp5 : (0 : ℝ) ≤ (5 - α) / α + 1 := by
      have h : (5 - α) / α + 1 = 5 / α := by field_simp; ring
      rw [h]; positivity
    have hcont' : ContinuousOn (fun x : ℝ => x ^ ((5 - α) / α + 1)) (Set.Icc (0 : ℝ) z) :=
      (Real.continuous_rpow_const hp5).continuousOn
    have hmul : IntegrableOn
        (fun x : ℝ => (Work.Elliptic.Fstar F x / x) * x ^ ((5 - α) / α + 1))
        (Set.Icc (0 : ℝ) z) := hIcc.mul_continuousOn hcont' isCompact_Icc
    have hmul' : IntegrableOn
        (fun x : ℝ => (Work.Elliptic.Fstar F x / x) * x ^ ((5 - α) / α + 1))
        (Set.Ioc (0 : ℝ) z) := hmul.mono_set Set.Ioc_subset_Icc_self
    refine hmul'.congr_fun ?_ measurableSet_Ioc
    intro x hx
    have hxpos : 0 < x := hx.1
    have hrw : x ^ ((5 - α) / α + 1) = x ^ ((5 - α) / α) * x := by
      rw [Real.rpow_add hxpos, Real.rpow_one]
    show Work.Elliptic.Fstar F x / x * x ^ ((5 - α) / α + 1)
      = x ^ ((5 - α) / α) * Work.Elliptic.Fstar F x
    rw [hrw]
    field_simp
  have hInt : IntervalIntegrable
      (fun s : ℝ => s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s) MeasureTheory.volume 0 z :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hzpos.le).mpr hint
  exact intervalIntegral.integral_hasDerivAt_right hInt hmeas hcont

theorem Gsing_smooth_ode_of_facts (α : ℝ) (F : ℝ → ℝ → ℝ) (hα : 0 < α)
    (hFsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar F) (Set.Ioi 0))
    (hFint : MeasureTheory.IntegrableOn (fun r : ℝ => Work.Elliptic.Fstar F r / r) (Set.Ioi 0))
    (hL12 : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.L12 F) (-(3 * Work.Elliptic.Fstar F z / z)) z) :
    (∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Gsing α F) (Set.Ioi 0)) ∧
      ∀ z ∈ Set.Ioi (0 : ℝ),
        α ^ 2 * z ^ 2 * deriv (fun z' => deriv (Work.Elliptic.Gsing α F) z') z
          + α * (5 + α) * z * deriv (Work.Elliptic.Gsing α F) z
        = (15 / 4) * Work.Elliptic.Fstar F z := by
  -- the derivative of `F_*` itself
  have hFc : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.Fstar F) (deriv (Work.Elliptic.Fstar F) z) z := by
    intro z hz
    exact (((hFsm 1).differentiableOn (by decide)).differentiableAt
      (isOpen_Ioi.mem_nhds hz)).hasDerivAt
  -- the two prescribed derivatives are smooth on `(0,∞)`
  have hdivsm : ∀ m : ℕ, ContDiffOn ℝ m (fun z : ℝ => -(3 * Work.Elliptic.Fstar F z / z))
      (Set.Ioi 0) := by
    intro m
    have h2 : ContDiffOn ℝ m (fun z : ℝ => 3 * Work.Elliptic.Fstar F z / z) (Set.Ioi 0) :=
      (contDiffOn_const.mul (hFsm m)).div contDiffOn_id (fun z hz => ne_of_gt hz)
    exact h2.neg
  have hrpwsm : ∀ m : ℕ,
      ContDiffOn ℝ m (fun z : ℝ => z ^ ((5 - α) / α) * Work.Elliptic.Fstar F z) (Set.Ioi 0) := by
    intro m
    exact (contDiffOn_id.rpow_const_of_ne (fun z hz => ne_of_gt hz)).mul (hFsm m)
  -- hence `L12 F` and `Jfun α F` are smooth, and so are `Gstar`, `Gbar` and `Gsing`
  have hL12sm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.L12 F) (Set.Ioi 0) :=
    contDiffOn_infty_of_hasDerivAt hL12 hdivsm
  have hJ := hasDerivAt_integral_rpow_mul_Fstar α F hα hFsm hFint
  have hJsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Jfun α F) (Set.Ioi 0) :=
    contDiffOn_infty_of_hasDerivAt hJ hrpwsm
  have hGstar : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Gstar α F) (Set.Ioi 0) := by
    intro m
    exact (contDiffOn_const (c := -(1 / (4 * α)))).mul (hL12sm m)
  have hGbar : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Gbar α F) (Set.Ioi 0) := by
    intro m
    have h1 : ContDiffOn ℝ m (fun z : ℝ => z ^ (-(5 / α))) (Set.Ioi 0) :=
      contDiffOn_id.rpow_const_of_ne (fun z hz => ne_of_gt hz)
    exact (contDiffOn_const.mul h1).mul (hJsm m)
  constructor
  · intro m
    exact (hGstar m).add (hGbar m)
  · intro z hz
    exact Work.Elliptic.Gsing_ode α F hα hL12 hFc hJ z hz

end Work.FTS.EllipticEst.Cert
