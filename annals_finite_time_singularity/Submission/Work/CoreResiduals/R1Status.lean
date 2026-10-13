/-
# `Work.CoreResiduals.R1Status` — the exact status of residual R1

This module collects, in one place, the *complete* formal reduction of the delivered residual R1
(`VortEq α P`, the `ℝ³` vorticity equation for `u = BS ω` at a `ProfileData`) and the exact analytic
statement that remains.  Everything below is either a *proved* theorem of this area or a *named*
input; there is no `sorry` here.

## The reduction (all proved)

1. **The dictionary** (`VorticityEquation.vortEq_iff_scalar_of_decomposition`): R1 is equivalent to
   *the decomposition* (`u = Cyl.psiField ψ` for a stream function of class `C²` off the axis, and
   `ω = W(radial ·, axial ·, ·)·eTheta`) plus the **meridian scalar equation**
   `∂ₜW + (∂_zψ)∂_rW + (−(ψ/r) − ∂_rψ)∂_zW = ((∂_zψ)/r)W` off the axis
   (`Work.CoreResiduals.MeridianEq`, with residual `meridianResid`).

2. **The existence half of the dictionary is delivered**: `exists_psiField_eq_biotSavart` gives
   `u = Cyl.psiField ψ` for the Biot–Savart field of a swirl vorticity, and
   `Cyl.vorticity_psiField` gives the *local* elliptic law `ω^θ = −cylOp ψ` for that ψ.

3. **The chain-rule leg** (`SelfSimReduction.meridianEq_of_dynEqConst`, with
   `SelfSimReduction.meridianResid_algebra`): for the self-similar pair
   `W = λ⁻¹F(ρ^p/λ, Θ)`, `ψ = ρ²λ⁻¹Φ(ρ^p/λ, Θ)`,
   `meridianResid = (1/(2λ²))·[2κ·(F + D_zF) + UVR p F Φ]` at `(Z,Θ) = (ρ^p/λ, arctan(z/r))`.
   Hence the meridian equation holds as soon as the *profile* equation
   `DynEqConst p (2κ) 1 F Φ` holds (`λ' = −κ`).

4. **The rate bookkeeping** (`Model.model_rate_physical`, `model_rate_physical_eq_reference`): the
   delivered R1 is the *physical* equation (the paper's Setup equation, tex 268, coefficient `1` on
   `∂_tΩ`; the `1/2` of tex 1319 is a time dilation), so the effective rate of an ansatz
   `λ(t) = 1 − t/2` is `2·(1/2) = 1 = κ*`, the reference rate.  In particular the profile
   equation of R1 at the inhabitant is the **reference** profile equation
   `DynEqConst p 1 1 F Φ`, i.e. the equation `Construction.Fstar_stationary_identity` is about.

## What remains (the exact residual of R1)

By 1 + 3 + 4, at the inhabitant R1 holds iff

  (A) the stream function `ψ` of `BS(solVort P)` — whose *existence* is delivered, 2 — is the
      self-similar `ρ²·λ⁻¹·Φ(ρ^p/λ, Θ)` for a profile `Φ` with `bslOp p Φ = F_*` (the quantitative
      elliptic identification), and
  (B) the cut-off deficit vanishes: `χ(ρ/L)` is not a function of the self-similar variable, so the
      honest form of R1 for the *cut* field is `VortEqWithDeficit P (Work.Stability.Far)`
      (`vortEq_iff_noDeficit`), with the deficit carried by the design's `Far`
      (`Work.Stability.GEquationFar`), whose `gDynRHS` is *explicit*.

(B) is where the obstruction lies: for `g = 0` the cut-off is not compensated, and exhibiting the
deficit as nonzero requires the non-local velocity on the annulus `L < ρ < 2L` (equivalently the
quantitative `bslOp` inverse of (A)).  Both are hard analysis; neither is formalisable from the
statements currently in the tree.  All the *wiring* around them is proved.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.CoreResiduals.SelfSimReduction
import Submission.Work.CoreResiduals.meridianEq_of_dynEqConst
import Submission.Work.CoreResiduals.Model

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.CoreResiduals

/-- **The exact residual of R1, as a `Prop`**: the stream function of the constructed velocity is
the self-similar `ρ²λ⁻¹Φ(ρ^p/λ, Θ)` where

* `Φ` solves the **self-similar elliptic law** `Work.Elliptic.bslOp p Φ = F_*` (this is the
  quantitative half of the delivered `exists_psiField_eq_biotSavart`, whose local counterpart is
  `Cyl.vorticity_psiField`), and
* the **meridian equation** for the pair `(W, ψ) = (ssVort p lam F_*, ssPsi p lam Φ)` holds.

With `SelfSimReduction.meridianEq_of_dynEqConst`, the second clause is equivalent to the profile
equation at the effective rate `2·(-λ')`; at the inhabitant that rate is `1 = κ*`
(`r1_rate_is_reference`), so the profile equation in question is the reference one. -/
def SelfSimStreamFunction (p : ℝ) (lam : ℝ → ℝ) (Φ : ℝ → ℝ → ℝ) : Prop :=
  (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp p Φ z θ = Work.Construction.Fstar p z θ) ∧
    (∀ r z t : ℝ, 0 < r → 0 < z →
      meridianResid (ssVort p lam (fun z θ => Work.Construction.Fstar p z θ))
        (ssPsi p lam Φ) r z t = 0)

/-! ## The canonical deficit of R1 -/

/-- **The canonical deficit of R1**: the difference between the two sides of the `ℝ³` vorticity
equation for the constructed field.  This is an *explicit* function — `BS` is the explicit
Biot–Savart integral — and R1 is *definitionally* the statement that it vanishes. -/
noncomputable def r1Deficit {α : NNReal} (P : Work.ConstructionInstance.ProfileData α) :
    R3 → ℝ → R3 :=
  fun x t =>
    FiniteTimeSingularity.timeDeriv (solVort P) x t
      + FiniteTimeSingularity.directionalDeriv (solVort P)
          (fun x t => Work.LWP.biotSavart (fun y => solVort P y t) x) x t
      - FiniteTimeSingularity.directionalDeriv
          (fun x t => Work.LWP.biotSavart (fun y => solVort P y t) x) (solVort P) x t

/-- **R1 is the vanishing of the canonical deficit**, and the deficit form of the delivered residual
is a theorem with no hypothesis: `VortEqWithDeficit P (r1Deficit P)` holds by construction.  The
*content* of R1 is therefore exactly "the explicit function `r1Deficit P` vanishes identically";
for the honest modulation `g` of the construction (solving the `g`-equation
`Work.Stability.GEquationFar`, whose deficit is the design's `Far`) that vanishing is the
Construction/Stability content, and for `g = 0` it is what the cut-off obstructs. -/
theorem vortEq_iff_deficit_eq_zero {α : NNReal}
    (P : Work.ConstructionInstance.ProfileData α) :
    VortEq α P ↔ (∀ x t, r1Deficit P x t = 0) := by
  constructor
  · intro h x t
    have h1 : FiniteTimeSingularity.timeDeriv (solVort P) x t
        + FiniteTimeSingularity.directionalDeriv (solVort P)
            (fun x t => Work.LWP.biotSavart (fun y => solVort P y t) x) x t
        = FiniteTimeSingularity.directionalDeriv
            (fun x t => Work.LWP.biotSavart (fun y => solVort P y t) x) (solVort P) x t :=
      h x t
    simp only [r1Deficit]
    rw [h1, sub_self]
  · intro h x t
    have h1 := h x t
    simp only [r1Deficit] at h1
    exact sub_eq_zero.mp h1

/-- **The deficit form of R1 is inhabited unconditionally**: with the canonical deficit,
`VortEqWithDeficit P (r1Deficit P)` holds.  So the *deficit form* of the residual is not a
hypothesis but a theorem, and what remains — the vanishing of `r1Deficit` (i.e. R1 itself) or a proof
that it fails to vanish — is exactly what the two targets `R1UncutRoute` / `R1CutDeficitRoute` name. -/
theorem vortEqWithDeficit_canonical {α : NNReal}
    (P : Work.ConstructionInstance.ProfileData α) :
    VortEqWithDeficit P (r1Deficit P) := by
  intro x t
  -- `VortEqWithDeficit` is the same identity read as `LHS = RHS + Def` with `Def = LHS - RHS`
  simp only [r1Deficit]
  abel

/-- **Target (i) of R1 — the uncut route.**  There exists a self-similar stream function `Φ`
(e.g. the `Φ_*` of `Work.Construction.Fstar_stationary_identity`, whose Θ-part is
`Work.Construction.Theta`) making the meridian equation hold for the *uncut* ansatz at the
inhabitant's modulation.  `SelfSimReduction.meridianEq_of_dynEqConst` turns this into the *profile*
equation at the effective rate `2κ = 1 = κ*`, which is the rate
`Construction.Fstar_stationary_identity` is about. -/
def R1UncutRoute (p : ℝ) (lam : ℝ → ℝ) : Prop :=
  ∃ Φ : ℝ → ℝ → ℝ, SelfSimStreamFunction p lam Φ

/-- **Target (ii) of R1 — the refutation.**  `¬ VortEq α P` at the inhabitant.  Its *informative*
form is a point of the annulus `L < ρ < 2L` where the canonical deficit `r1Deficit P` fails to vanish
(`vortEq_iff_deficit_eq_zero`); because the deficit is an *explicit* function, the statement is a
plain inequality — but it involves the non-local `fderiv` of `BS(solVort P)`, hence a lower bound for
`BS((1−χ)·ω_ss)` (the χ'-correction of the cut-off), which is not available in this tree.

Note that the *deficit form* of the residual carries no information on its own:
`vortEqWithDeficit_canonical` proves `VortEqWithDeficit P (r1Deficit P)` unconditionally, and by
`vortEq_iff_deficit_eq_zero` the deficit is the canonical one exactly when `VortEq` holds.  The
content is therefore the *vanishing* of `r1Deficit` (= R1 itself) or its *failure*. -/
def R1CutDeficitRoute {α : NNReal} (P : Work.ConstructionInstance.ProfileData α) : Prop :=
  ¬ VortEq α P

/-- **The rate identity that settles the bookkeeping** of residual R1 at the inhabitant: the
effective rate of the profile equation of the *physical* equation (R1) equals the paper's reference
rate `κ*`.  (Restated here so that a reader of R1's reduction does not have to open `Model.lean`.) -/
theorem r1_rate_is_reference {α : NNReal} (I : Inhabitant α) :
    2 * (-(deriv I.P.lam 1)) = Work.Stability.kappaStar 0 :=
  model_rate_physical_eq_reference I
