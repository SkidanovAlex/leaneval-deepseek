import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.Stability.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Stability

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-! ## The bump, and the cut-off by an explicit formula -/

/-- The bump function of the cut-off, **kept for the workspace's `ContDiffBump` bookkeeping only**:
it is the `ContDiffBump (0:ℝ)` with `rIn = 1`, `rOut = 2`.  Its coercion to a function is no
longer used to define `chi` (see there): that coercion is `(someContDiffBumpBase ℝ).toFun 2`, a
`Classical.choice` which does not reduce. -/
noncomputable def bump : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩

/-- **THE CUT-OFF**, by an explicit formula: `chi x = smoothTransition (2 - ‖x‖)`, the value at
scale `2` of Mathlib's bump base `ContDiffBumpBase.ofInnerProductSpace ℝ`, written down directly
so that it *reduces* (see the module header).  Every fact below is the old abstract `ContDiffBump`
interface, reproved from Mathlib's `Real.smoothTransition` API in
`Submission.Work.ChiExplicit.Defs`. -/
noncomputable def chi : ℝ → ℝ := fun x => Real.smoothTransition (2 - ‖x‖)

/-- The definition as a rewrite rule — this is `rfl`, and that is the *point* of the explicit
formula: unlike the former coercion of `bump`, `chi` reduces. -/
theorem chi_apply (x : ℝ) : chi x = Real.smoothTransition (2 - ‖x‖) := rfl


theorem bump_rOut : bump.rOut = 2 := rfl

theorem chi_contDiff : ContDiff ℝ (⊤ : ℕ∞) chi :=
  Work.ChiExplicit.chi_contDiff (⊤ : ℕ∞)

theorem chi_continuous : Continuous chi := chi_contDiff.continuous

theorem chi_nonneg (x : ℝ) : 0 ≤ chi x := Work.ChiExplicit.chi_nonneg x

theorem chi_le_one (x : ℝ) : chi x ≤ 1 := Work.ChiExplicit.chi_le_one x

/-- `chi = 1` on `[-1,1]`. -/
theorem chi_eq_one {x : ℝ} (h : |x| ≤ 1) : chi x = 1 := Work.ChiExplicit.chi_eq_one h

/-- `chi = 0` off `(-2,2)`. -/
theorem chi_eq_zero {x : ℝ} (h : 2 ≤ |x|) : chi x = 0 := Work.ChiExplicit.chi_eq_zero h

/-- `chi` is even. -/
theorem chi_neg (x : ℝ) : chi (-x) = chi x := Work.ChiExplicit.chi_neg x

/-- `chi(0) = 1`. -/
theorem chi_zero : chi 0 = 1 := Work.ChiExplicit.chi_zero




/-! ## A genuine smoothness class on the box

**Warning (workspace convention).**  `Work.Spaces.SmoothNbhd f` is *by definition*
`ContDiffOn ℝ ⊤ (uncurry f) (Ioi(-1) ×ˢ Ioo(-1)(π/2+1))`, and in this Mathlib the order
`⊤ : ℕ∞ω` is the *analytic* order `ω`, not smoothness (`∞`), as recorded by
`ContDiffWithinAt.analyticWithinAt` and by the team's `Work.Coercivity.pthIter_analyticOn`,
`Work.Coercivity.E2jet_analyticOn`.  Consequently `SmoothNbhd` is **not** preserved by the
cut-off: an analytic function equal to `1` near `z = 0` and to `0` far away cannot exist
(`chi(z/Z)·f` with `f ≡ 1` is the counterexample).  We therefore introduce the class actually
meant by "smooth on a neighbourhood of the closed quadrant". -/

/-- The *smooth* order `∞ = ((⊤ : ℕ∞) : ℕ∞ω)` of `ContDiff`, as an explicit term (so that the
notation `ω` of `open scoped ContDiff` — which would clash with the variable name `ω` used for
vector fields below — is not needed).  Note `∞ ≤ ⊤ = ω`, i.e. analyticity implies smoothness. -/
abbrev smoothOrder : WithTop ℕ∞ := ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- **Genuine smoothness** (`C^∞`, not analyticity) on the open box
`Ioi(-1) × Ioo(-1)(π/2+1)` containing the closed quadrant.  This is the class in which the
cut-off lives; `Work.Spaces.SmoothNbhd f → SmoothFar f`. -/
def SmoothFar (f : F2) : Prop :=
  ContDiffOn ℝ smoothOrder (Function.uncurry f) (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π / 2 + 1))

/-- Every `SmoothNbhd` function is `SmoothFar` (analyticity implies smoothness). -/
theorem SmoothFar.of_smoothNbhd {f : F2} (h : Work.Spaces.SmoothNbhd f) : SmoothFar f :=
  h.of_le le_top

/-! ## The cut-off of a profile -/



/-- The **far part** `(1 - chi(z/Z))·f`: it vanishes for `z ≤ Z` and agrees with `f` for `z ≥ 2Z`. -/
def zfar (Z : ℝ) (f : F2) : F2 := fun z θ => (1 - chi (z / Z)) * f z θ


theorem zfar_apply (Z : ℝ) (f : F2) (z θ : ℝ) :
    zfar Z f z θ = (1 - chi (z / Z)) * f z θ := rfl


/-- For `Z > 0` and `z ≤ Z` the far part vanishes. -/
theorem zfar_eq_zero {Z : ℝ} (hZ : 0 < Z) {z : ℝ} (hz0 : 0 ≤ z) (hz : z ≤ Z) (f : F2)
    (θ : ℝ) : zfar Z f z θ = 0 := by
  have h : z / Z ≤ 1 := by rw [div_le_one hZ]; exact hz
  have h2 : -(1 : ℝ) ≤ z / Z := by
    have : 0 ≤ z / Z := div_nonneg hz0 hZ.le
    linarith
  rw [zfar_apply, chi_eq_one (abs_le.mpr ⟨h2, h⟩)]
  ring



/-! ## The far-field tail hypotheses -/


/-- **The `ℋ^k` far-tail decay hypothesis**: the `θ`-integrated `ℋ^k`-integrand of the far part
is dominated by `M²/z²` on `z ≥ Z`.  (The `θ`-integral is needed because the angular weight
`sin(2θ)^{-γ}` is unbounded; it is integrable, so this is the natural pointwise-in-`z` form.) -/
def FarTailDom (α : ℝ) (k : ℕ) (M Z : ℝ) (f : F2) : Prop :=
  ∀ z ∈ Work.Spaces.Iz, Z ≤ z →
    (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (zfar Z f) z θ) ≤ M ^ 2 / z ^ 2

/-- **The physical cut-off** of a vector field on `ℝ³`: `ω ↦ chi(ρ(x)/L) • ω(x)`, where
`ρ(x) = ‖x‖` (`Work.Cyl.rho`).  The corresponding threshold in the self-similar variable is
`Z = L^α` (`Work.Cyl.Rc`): `chi(ρ/L) = chi((z/Z)^{1/α})` for `z = ρ^α`. -/
def omegaCut (L : ℝ) (ω : Work.Cyl.R3 → Work.Cyl.R3) : Work.Cyl.R3 → Work.Cyl.R3 :=
  fun x => chi (Work.Cyl.rho x / L) • ω x

end Work.Stability
