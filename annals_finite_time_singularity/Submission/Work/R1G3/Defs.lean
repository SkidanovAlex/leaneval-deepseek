import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.R1G.All

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.R1G3

variable {α : NNReal}

/-! ## The cut, in the meridian and in the self-similar variables -/

/-- The cut-off factor `χ(ρP(r,z)/L)` in the meridian variables. -/
def chiAt (P : Work.ConstructionInstance.ProfileData α) (r z : ℝ) : ℝ :=
  Work.Stability.chi (Work.Cyl.rhoP r z / P.L)

@[simp] theorem chiAt_apply (P : Work.ConstructionInstance.ProfileData α) (r z : ℝ) :
    chiAt P r z = Work.Stability.chi (Work.Cyl.rhoP r z / P.L) := rfl

/-- **The cut-off factor in the self-similar radial variable.**  With `z = ρ^p/λ` one has
`ρ = (λ z)^{1/p}`, so the radial cut-off `χ(ρ/L)` reads `χ((λ(t)·z)^{1/p}/L)`.  This is where the
*t*`-dependence of the cut enters the elliptic problem — the reason the honest stream profile is
**not** stationary. -/
def chiAtSS (P : Work.ConstructionInstance.ProfileData α) (p : ℝ) (z t : ℝ) : ℝ :=
  Work.Stability.chi ((P.lam t * z) ^ (1 / p) / P.L)

@[simp] theorem chiAtSS_apply (P : Work.ConstructionInstance.ProfileData α) (p z t : ℝ) :
    chiAtSS P p z t = Work.Stability.chi ((P.lam t * z) ^ (1 / p) / P.L) := rfl

/-- The cut meridian vorticity profile `W_cut = χ(ρP(r,z)/L)·ssVort p λ F` of the constructed
field: the `e_θ`-coefficient of the delivered `Work.ConstructionInstance.solVort`. -/
def cutVort (P : Work.ConstructionInstance.ProfileData α) (p : ℝ) (F : ℝ → ℝ → ℝ) :
    ℝ → ℝ → ℝ → ℝ :=
  fun r z t => chiAt P r z * Work.CoreResiduals.ssVort p P.lam F r z t

@[simp] theorem cutVort_apply (P : Work.ConstructionInstance.ProfileData α) (p : ℝ)
    (F : ℝ → ℝ → ℝ) (r z t : ℝ) :
    cutVort P p F r z t = chiAt P r z * Work.CoreResiduals.ssVort p P.lam F r z t := rfl


/-! ## The self-similar normalization of a physical stream function -/


/-! ## The elliptic law, with the sign pinned -/




/-- **The cut elliptic law in the self-similar variables.**  The honest stream profile `ΦA`
(possibly `t`-dependent) solves the elliptic problem with the **cut** source: this is the first half
of the coupled problem, and it is *equivalent* to the Biot–Savart law for the constructed field
(see `Work.R1G3.cylOp_cutVort`). -/
def CutEllLaw (P : Work.ConstructionInstance.ProfileData α) (p : ℝ) (F : ℝ → ℝ → ℝ)
    (ΦA : ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ z θ t : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < t → t < P.T →
    Work.Elliptic.bslOp p (fun z θ => ΦA z θ t) z θ = - chiAtSS P p z t * F z θ

/-! ## The coupled (linear) operator and its explicit right-hand side -/

/-- **The coupled operator of R1**: the *linear* local operator on the correction `δ` of the stream
profile, evaluated at `(r,z,t)`.  It is `χ(ρ/L)` times the transport operator `UVR p F` of the
correction plus `2λ²` times the explicit cut-off deficit of the correction's stream function — i.e.
exactly the quantity that has to vanish for the constructed field to solve the meridian equation.

It is **linear in `δ`** (`Work.R1G3.coupOp_add`, `coupOp_smul`, `coupOp_zero`); the whole content of
route (i) is that R1 is the *linear* equation `coupOp = -coupConst`. -/
def coupOp (P : Work.ConstructionInstance.ProfileData α) (p : ℝ) (F : ℝ → ℝ → ℝ)
    (δ : ℝ → ℝ → ℝ → ℝ) (r z t : ℝ) : ℝ :=
  chiAt P r z * Work.Construction.UVR p F (fun z θ => δ z θ t)
      (Work.Cyl.rhoP r z ^ p / P.lam t) (Work.Cyl.thetaP r z)
    + 2 * (P.lam t) ^ 2 *
        Work.R1G.cutDeficit P (Work.CoreResiduals.ssPsi p P.lam (fun z θ => δ z θ t))
          (Work.CoreResiduals.ssVort p P.lam F) r z t

/-- **The explicit right-hand side of the coupled problem**: `χ` times the profile residual of the
base pair at the self-similar point, plus `2λ²` times the explicit cut-off deficit of the *base*
self-similar pair.  This is a *function* of the data — no unknown occurs in it. -/
def coupConst (P : Work.ConstructionInstance.ProfileData α) (p κ : ℝ) (F Φbase : ℝ → ℝ → ℝ)
    (r z t : ℝ) : ℝ :=
  chiAt P r z *
      Work.R1G.profileResidGen p κ F Φbase
        (Work.Cyl.rhoP r z ^ p / P.lam t) (Work.Cyl.thetaP r z)
    + 2 * (P.lam t) ^ 2 *
        Work.R1G.cutDeficit P (Work.CoreResiduals.ssPsi p P.lam Φbase)
          (Work.CoreResiduals.ssVort p P.lam F) r z t

/-- **THE NAMED RESIDUAL OF ROUTE (i) — the coupled problem.**  The *linear* local equation for the
correction `δ` of the stream profile,

  `coupOp δ = -coupConst`,

whose left-hand side is linear in `δ` and whose right-hand side is explicit.  By
`Work.R1G3.meridianResid_cutVort_eq` (the reduction chain) this is *exactly* the statement that the
constructed (cut) field, paired with the honest stream profile `Φ_base + δ`, solves the meridian
equation — i.e. exactly residual R1 at the constructed field.

The *second* half of the coupled problem, `CutEllLaw`, determines `δ` through the elliptic problem
with the cut source `-χ(λz)^{1/p}/L·F`; the coupled system is (E) + this equation. -/
def CoupledResidual (P : Work.ConstructionInstance.ProfileData α) (p κ : ℝ) (F Φbase : ℝ → ℝ → ℝ)
    (δ : ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ r z t : ℝ, 0 < r → 0 < z → t ∈ Set.Ioo 0 P.T →
    coupOp P p F δ r z t = - coupConst P p κ F Φbase r z t


/-! ## Abbreviations for the wiring -/



/-- **The honest meridian vorticity profile** of the constructed field: `solVort`'s
`e_θ`-coefficient is `χ(ρ/L)·λ(t)⁻¹·profile p P.g (ρ^p/λ(t)) θ` for **all** `θ`, where
`p = profExp α` and `Work.ConstructionInstance.profile` is the odd extension in `θ`.  This is the
meridian profile the dictionary `solVort = cutProfile P W · e_θ` really has as a *theorem*
(`Work.R1G3.solVort_eq_cutProfile_honestW`); it agrees with the formula `Work.R1G.profOf` on the
upper half-plane (`honestW_eq_ssVort_of_nonneg`), which is the half-plane where the profile equation
lives. -/
def honestW {α : NNReal} (P : Work.ConstructionInstance.ProfileData α) : ℝ → ℝ → ℝ → ℝ :=
  Work.CoreResiduals.ssVort (Work.ConstructionInstance.profExp α) P.lam
    (Work.ConstructionInstance.profile (Work.ConstructionInstance.profExp α) P.g)

@[simp] theorem honestW_apply {α : NNReal} (P : Work.ConstructionInstance.ProfileData α)
    (r z t : ℝ) :
    honestW P r z t = (P.lam t)⁻¹ *
      Work.ConstructionInstance.profile (Work.ConstructionInstance.profExp α) P.g
        (Work.Cyl.rhoP r z ^ Work.ConstructionInstance.profExp α / P.lam t)
        (Work.Cyl.thetaP r z) := rfl





/-! ## The coupled data of route (i) -/

/-- **The coupled data of route (i)**: the base self-similar pair `(F, Φ_base)` at which the profile
equation holds, the correction `δ` created by the *cut-off*, and the two halves of the coupled
problem —

* `hEll` (**the cut elliptic law**): `Φ_base + δ` solves the elliptic problem with the cut source
  `-χ((λ(t)z)^{1/p}/L)F`;
* `hRes` (**the coupled residual**, linear in `δ`): `coupOp δ = -coupConst`.

Given the ansatz dictionary (`Work.R1G.GRouteHyp`'s `hv`, `hω`), `hEll` is a *theorem*
(`Work.R1G3.cylOp_actual_of_dictionary` + `Work.R1G3.cylOp_ssPsi`), so the analytic content of
route (i) is `hRes` alone — the linear equation. -/
structure CoupledData (α : NNReal) where
  /-- the profile/modulation data of the construction -/
  P : Work.ConstructionInstance.ProfileData α
  /-- the modulation rate `κ = -λ̄'` (the paper's dilated-time rate) -/
  κ : ℝ
  /-- the rate of the modulation on the pre-window -/
  hrate : Work.R1G.EffRate P κ
  /-- the vorticity profile of the self-similar base pair -/
  F : ℝ → ℝ → ℝ
  /-- the stream profile of the self-similar base pair -/
  Φbase : ℝ → ℝ → ℝ
  /-- the correction of the stream profile created by the cut-off -/
  δ : ℝ → ℝ → ℝ → ℝ
  /-- the base pair solves the profile equation at the effective rate: the profile residual vanishes -/
  hFar : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
    Work.R1G.profileResidGen (Work.ConstructionInstance.profExp α) κ F Φbase z θ = 0
  /-- the vorticity profile is `C¹` on the quadrant (the regularity the chain rule consumes) -/
  hFreg : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
    ContDiffAt ℝ 1 (fun q : ℝ × ℝ => F q.1 q.2) (z, θ)
  /-- the base stream profile is `C²` on the quadrant -/
  hbasereg : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
    ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Φbase q.1 q.2) (z, θ)
  /-- the correction's slice is `C²` on the quadrant -/
  hδreg : ∀ z θ t : ℝ, (z, θ) ∈ Work.Construction.Qd →
    ContDiffAt ℝ 2 (fun q : ℝ × ℝ => δ q.1 q.2 t) (z, θ)
  /-- **the cut elliptic law** (half (E) of the coupled problem; a theorem from the dictionary) -/
  hEll : CutEllLaw P (Work.ConstructionInstance.profExp α) F
    (fun z θ t => Φbase z θ + δ z θ t)
  /-- **the coupled residual** (half (T) of the coupled problem; the named residual, linear in `δ`) -/
  hRes : CoupledResidual P (Work.ConstructionInstance.profExp α) κ F Φbase δ


end Work.R1G3
