/-
# The STABILITY layer — **St1: the cut-off data and the far-field tails**

This module (`Submission.Work.Stability.Cutoff`) is St1 of the design
(`NOTES_LEAD_Stability.md`): the compactly supported cut-off of the data and the two tail
bounds that make the far-field part harmless.

## The cut-off (repointed, round `ChiExplicit`)

**`chi` is now given by an explicit formula**,

  `chi x = Real.smoothTransition (2 - ‖x‖)`,

the value at scale `2` of Mathlib's bump base `ContDiffBumpBase.ofInnerProductSpace ℝ`
(`toFun R x = smoothTransition ((R - ‖x‖)/(R-1))`, see
`Mathlib/Analysis/Calculus/BumpFunction/InnerProduct.lean`), written down directly.  Until this
repointing, `chi` was *defined* as the coercion to a function of the bundled bump
`bump : ContDiffBump (0:ℝ)` with `rIn = 1`, `rOut = 2`, namely `(someContDiffBumpBase ℝ).toFun 2`
— a `Classical.choice` over Mathlib's bump base, which does **not** reduce and whose value Lean
cannot see.  That made true facts about the function Mathlib builds — the monotonicity of the
cut-off on the annulus `(1,2)` (`Work.R1G11.CutoffTail`) and the quantitative decay of `χ'/χ`
(`Work.R1G12.ChiQuant`) — *unprovable* from the abstract interface, since the axioms of
`ContDiffBumpBase` are satisfied by non-monotone bumps.  Writing the formula down is the honest
fix (it is the *same function*, not a weakening): the whole abstract interface below is reproved
from Mathlib's `Real.smoothTransition` API, so every downstream file re-elaborates unchanged, and
the *new* properties of the formula — monotonicity, the `log chi` tail, the `χ'/χ` decay — live
in `Submission/Work/ChiExplicit/`.

`bump` itself is kept, together with `bump_rIn`/`bump_rOut`, for the workspace's `ContDiffBump`
bookkeeping, but `chi` is no longer its coercion: `chi_apply` now unfolds to the explicit formula.

`chi` is `C^∞`, `0 ≤ chi ≤ 1`, `chi = 1` on `[-1,1]` and `chi = 0` off `(-2,2)`.  It is *even*
(`chi_neg`), hence `chi'(0) = 0` (`chi_deriv_zero`).

The cut-off of a profile (a function of the self-similar variables) at scale `Z > 0` is

  `zcut Z f = chi(z/Z) · f`,   `zfar Z f = (1 - chi(z/Z)) · f`,

so that `zfar Z f = 0` for `z ≤ Z` and `zfar Z f = f` for `z ≥ 2Z`.  On `ℝ³` the cut-off of the
*physical* data is `omegaCut L ω = chi(ρ(x)/L) • ω(x)` with `ρ(x) = ‖x‖` (`Work.Cyl.rho`); the
corresponding threshold in the self-similar variable is `Z = L^α` (`Work.Cyl.Rc`), and the
results of this module are stated in the `z`-variable (which is where the `ℋ^k`/`𝒲^{l,∞}` norms
live).

## The two tail bounds

* **`ℋ^k`** (`HkSq_zfar_le`, `HkSq_tail_le`): if the `θ`-integrated `ℋ^k`-integrand of the far
  part decays like `M²/z²` beyond `Z` (`FarTailDom`), then
  `|zfar Z f|_{ℋ^k}² ≤ M²/Z`, i.e. `|zfar Z f|_{ℋ^k} ≤ M·Z^{-1/2}`.  In the application the
  decay `M²/z²` is the profile's own `z^{-1}` decay (`F_*`'s weighted `D`-derivatives are
  `O(α/z)`), so the bound reads `O((α + |g₀|_{ℋ⁴})·Z^{-1/2}) = O(α·L^{-α/2})`.
* **`𝒲^{l,∞}`** (`WlInf_zfar_le`): the same with the supremum instead of the `L²`-square: if each
  weighted sup-term of the far part is `≤ M/z` beyond `Z` (`FarTailSup`), then
  `|zfar Z f|_{𝒲^{l,∞}} ≤ M/Z`, i.e. `O(α·L^{-α})`.

The *closure* of the bootstrap consumes these with `Z = L^α`: `α·L^{-α} ≤ α^{7/4}` is the paper's
`ε₀ ≤ α^{7/4}` (tex 1546), i.e. `L ≥ α^{-5/(2α)}`, a *fixed* constant, and `L` is chosen once and
for all.

## Class membership

`zcut` preserves everything the class `C^{1,α} ∩ {odd} ∩ {compact support}` needs
(`SmoothNbhd`, `VanishTheta`, the quadratic vanishing at `z = 0` of `SmoothCompact_HkInf`, compact
support) and on `ℝ³` the radial factor `chi(ρ/L)` is even in every coordinate, so it preserves
`IsOdd` (`Work.Cyl.IsOdd`/`FiniteTimeSingularity.IsOdd`), `div`-freeness, and `C^{1,α}`.
-/
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Stability.Defs
import Submission.Work.ChiExplicit.Defs
import Submission.Work.ChiExplicit.chi_contDiff

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

theorem bump_rIn : bump.rIn = 1 := rfl

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

/-- `chi` is positive near `0`. -/
theorem chi_pos_of_abs_lt_one {x : ℝ} (h : |x| < 1) : 0 < chi x :=
  Work.ChiExplicit.chi_pos_of_abs_lt_one h

/-- `chi` is **strictly positive on the open ball of radius `2`**, i.e. on `(-2,2)`. -/
theorem chi_pos_of_abs_lt_two {x : ℝ} (h : |x| < 2) : 0 < chi x :=
  Work.ChiExplicit.chi_pos_of_abs_lt_two h

/-- **THE SUPPORT OF THE CUT-OFF**: `chi` vanishes exactly off the open ball of radius `2`. -/
theorem chi_support : Function.support chi = Metric.ball (0 : ℝ) 2 :=
  Work.ChiExplicit.chi_support

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

/-- The cut-off factor at scale `Z`: `z ↦ chi(z/Z)`. -/
noncomputable def cutFun (Z : ℝ) (z : ℝ) : ℝ := chi (z / Z)

/-- The **cut-off profile** `chi(z/Z)·f`: it agrees with `f` for `z ≤ Z`. -/
def zcut (Z : ℝ) (f : F2) : F2 := fun z θ => chi (z / Z) * f z θ

/-- The **far part** `(1 - chi(z/Z))·f`: it vanishes for `z ≤ Z` and agrees with `f` for `z ≥ 2Z`. -/
def zfar (Z : ℝ) (f : F2) : F2 := fun z θ => (1 - chi (z / Z)) * f z θ

theorem zcut_apply (Z : ℝ) (f : F2) (z θ : ℝ) : zcut Z f z θ = chi (z / Z) * f z θ := rfl

theorem zfar_apply (Z : ℝ) (f : F2) (z θ : ℝ) :
    zfar Z f z θ = (1 - chi (z / Z)) * f z θ := rfl

/-- The cut-off and the far part add up to the original profile. -/
theorem zcut_add_zfar (Z : ℝ) (f : F2) :
    zcut Z f + zfar Z f = f := by
  funext z θ
  simp only [Pi.add_apply, zcut_apply, zfar_apply]
  ring

/-- For `Z > 0` and `z ≤ Z` the far part vanishes. -/
theorem zfar_eq_zero {Z : ℝ} (hZ : 0 < Z) {z : ℝ} (hz0 : 0 ≤ z) (hz : z ≤ Z) (f : F2)
    (θ : ℝ) : zfar Z f z θ = 0 := by
  have h : z / Z ≤ 1 := by rw [div_le_one hZ]; exact hz
  have h2 : -(1 : ℝ) ≤ z / Z := by
    have : 0 ≤ z / Z := div_nonneg hz0 hZ.le
    linarith
  rw [zfar_apply, chi_eq_one (abs_le.mpr ⟨h2, h⟩)]
  ring

/-- For `Z > 0` and `z ≤ Z` the cut-off agrees with the profile. -/
theorem zcut_eq_self {Z : ℝ} (hZ : 0 < Z) {z : ℝ} (hz0 : 0 ≤ z) (hz : z ≤ Z) (f : F2)
    (θ : ℝ) : zcut Z f z θ = f z θ := by
  have h : z / Z ≤ 1 := by rw [div_le_one hZ]; exact hz
  have h2 : -(1 : ℝ) ≤ z / Z := by
    have : 0 ≤ z / Z := div_nonneg hz0 hZ.le
    linarith
  rw [zcut_apply, chi_eq_one (abs_le.mpr ⟨h2, h⟩)]
  ring

/-- For `z ≥ 2Z` the far part agrees with the profile. -/
theorem zfar_eq_self {Z : ℝ} (hZ : 0 < Z) {z : ℝ} (hz : 2 * Z ≤ z) (f : F2) (θ : ℝ) :
    zfar Z f z θ = f z θ := by
  have hz0 : 0 ≤ z := by linarith
  have h2 : 2 ≤ z / Z := by rw [le_div_iff₀ hZ]; linarith
  have h : 2 ≤ |z / Z| := by rw [abs_of_nonneg (div_nonneg hz0 hZ.le)]; exact h2
  rw [zfar_apply, chi_eq_zero h]
  ring

/-! ## The far-field tail hypotheses -/

/-- **The `𝒲^{l,∞}` far-tail decay hypothesis**: every weighted derivative term of the far part
is dominated by `M/z` on `z ≥ Z`.  (This is the "profile's own `z^{-1}` decay" of the design, in
the `𝒲^{l,∞}` vocabulary.) -/
def FarTailSup (α : ℝ) (l : ℕ) (M Z : ℝ) (f : F2) : Prop :=
  (∀ k ≤ l, ∀ z ∈ Work.Spaces.Iz, Z ≤ z → ∀ θ ∈ Work.Spaces.Iθ,
      |(z + 1) ^ k * Work.Spaces.pzIter k (zfar Z f) z θ| ≤ M / z) ∧
    (∀ j ≤ l, ∀ k ≤ l, 1 ≤ j → k + j ≤ l → ∀ z ∈ Work.Spaces.Iz, Z ≤ z →
      ∀ θ ∈ Work.Spaces.Iθ,
        |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j (zfar Z f)) z θ
          * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))| ≤ M / z)

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
