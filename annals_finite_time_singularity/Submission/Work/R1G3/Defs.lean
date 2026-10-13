/-
# `Work.R1G3` — the **coupled elliptic problem** for the cut field's stream function

## What this area is

`Work.R1G` (stage 2) exhibits residual **R1** as the vanishing of the explicit annulus-supported
function `cutDeficit`, refutes the self-similar route
(`Work.R1G.selfSimRoute_residual_eq_cutDeficit`), and isolates **two remaining routes**:

* **(i)** *the coupled elliptic problem* — the paper's own mathematics at the actual data: the cut
  field's stream function `ψ_act` solves the elliptic problem **with the cut source**
  (`Work.R1G.vorticity_psiField_bslOp`), and the meridian equation is imposed on top;
* **(ii)** a lower bound for the non-local `BS((1-χ)·ω_ss)` on the annulus.

**This area is route (i).**  Its content is the *complete local reduction* of the coupled problem to
a **linear** equation for the *correction* of the stream profile relative to the self-similar pair,
with an **explicit** right-hand side.  Concretely, for the constructed (cut) field

  `W_cut(r,z,t) = χ(ρ(r,z)/L)·λ(t)⁻¹·F(ρ(r,z)^p/λ(t), θ(r,z))`

and the honest stream profile `Φ_act(z,θ,t) = Φ_base(z,θ) + δ(z,θ,t)` (the self-similar pair
`(F, Φ_base)` solving the profile equation, `δ` the correction created by the cut-off), the meridian
residual of the constructed field is

  `meridianResid W_cut (ssPsi p λ Φ_act) = (2λ²)⁻¹·(coupOp + coupConst)`

with `coupOp` **linear in `δ`** and `coupConst` **explicit** in the data, so that

  **R1 at the constructed field  ⟺  `coupOp = -coupConst`**,

a *linear* local equation.  This is the sharpest form of "solve the coupled problem": the elliptic
half contributes the *determination* of `δ` (the cut-off defect `(1-χ)F` as source), and the
transport half is the linear equation above.

## Conventions and signs (pinned here — this area owns the elliptic identification)

* the profile exponent is `p = profExp α`, the self-similar variables are `z = ρ^p/λ`, `θ`, and the
  self-similar pair is `Work.CoreResiduals.ssVort p λ F`, `ssPsi p λ Φ`;
* **the sign.**  The delivered curl identity `Work.Cyl.vorticity_psiField` together with
  `Work.Elliptic.cylOp_polar` gives, for `ψ = ρ²Φ(ρ^p,θ)`,
  `vorticity (psiField ψ) = -(bslOp p Φ)(ρ^p,θ)·e_θ`
  (`Work.R1G.vorticity_psiField_bslOp`).  Hence the elliptic law relating a **vorticity profile**
  `F` (the `e_θ`-coefficient of `vorticity`, in the Lean sign convention) to its **stream profile**
  `Φ` is

    `HonestEllLaw p F Φ  :⟺  bslOp p Φ = -F`,

  and **not** `bslOp p Φ = F` (`Work.Construction.StatEqPhi`, the paper's convention — the paper
  records the opposite sign convention in its footnote to (3dBSL)).  The two are related by
  `HonestEllLaw p F Φ ↔ Work.Construction.StatEqPhi p (-F) Φ`, i.e. `↔ StatEqPhi p F (-Φ)`; a caller
  who wants to use the Construction chapter's `Θ`(=`(1/(4α))sin2θ L₁₂(F)`) must therefore take it
  with the **opposite** sign.  This is finding 5 of `Work.R1G.NOTES.md`, made precise.
* the cut-off is `Work.Stability.chi` (`χ = 1` on `|x| ≤ 1`, `χ = 0` off `(-2,2)`), so the deficit is
  supported in the annulus `L ≤ ρ ≤ 2L` (`Work.R1G.cutDeficit_eq_zero_of_not_mem_annulus`).

-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Submission.Work.R1G.All
import Submission.Work.Elliptic.cylOp_polar
import Submission.Work.Elliptic.bslOp_add

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

/-- The cut meridian profile is the delivered `Work.R1G.cutProfile` of the self-similar profile. -/
theorem cutVort_eq_cutProfile (P : Work.ConstructionInstance.ProfileData α) (p : ℝ)
    (F : ℝ → ℝ → ℝ) :
    cutVort P p F = Work.R1G.cutProfile P (Work.CoreResiduals.ssVort p P.lam F) := rfl

/-! ## The self-similar normalization of a physical stream function -/

/-- **The self-similar normalization of a physical meridian stream function.**  If `ψ(r,x₃,t)` is a
meridian stream function (velocity `psiField (ψ · t)`) then in the self-similar variables
`z = ρ^p/λ`, `θ` the ansatz of the construction reads `ψ = ρ²λ⁻¹Φ(z,θ,t)`, i.e.

  `ssProfileOf p λ ψ z θ t = λ(t)·ψ((λ(t)z)^{1/p}cos θ, (λ(t)z)^{1/p}sin θ, t) / (λ(t)z)^{2/p}`.

`ssPsi_ssProfileOf` shows that this factorization is *lossless*: every meridian function is the
self-similar pair `ssPsi p λ (ssProfileOf p λ ψ ·,·,t)` of its own normalization.  In particular the
"the actual stream function is of self-similar-polar form" hypothesis of the coupled problem is not a
restriction. -/
def ssProfileOf (p : ℝ) (lam : ℝ → ℝ) (ψ : ℝ → ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ → ℝ :=
  fun z θ t =>
    lam t * ψ ((lam t * z) ^ (1 / p) * Real.cos θ) ((lam t * z) ^ (1 / p) * Real.sin θ) t
      / (lam t * z) ^ (2 / p)

/-! ## The elliptic law, with the sign pinned -/

/-- **The honest elliptic law** of the self-similar ansatz, in the sign convention forced by the
delivered curl identity `Work.Cyl.vorticity_psiField`: the stream profile `Φ` produces the vorticity
profile `F` iff `bslOp p Φ = -F`.

The sign is *not* a convention of this file: `HonestEllLaw p F Φ` is equivalent to the statement
that the `ℝ³` field `psiField (ρ²Φ(ρ^p,·))` has `e_θ`-coefficient of its vorticity equal to `F`
(`Work.R1G.vorticity_psiField_bslOp`).  See the module docstring. -/
def HonestEllLaw (p : ℝ) (F Φ : ℝ → ℝ → ℝ) : Prop :=
  ∀ z θ : ℝ, Work.Elliptic.bslOp p Φ z θ = -F z θ

/-- The paper's (and `Work.Construction`'s) sign convention, recalled: `StatEqPhi α F Φ` is
`bslOp α Φ = F`. -/
theorem honestEllLaw_iff_statEqPhi (p : ℝ) (F Φ : ℝ → ℝ → ℝ) :
    HonestEllLaw p F Φ ↔ Work.Construction.StatEqPhi p (fun z θ => -F z θ) Φ := Iff.rfl

/-- The honest elliptic law is the *negated* stream profile in the Construction convention. -/
theorem honestEllLaw_iff_statEqPhi_neg (p : ℝ) (F Φ : ℝ → ℝ → ℝ)
    (h : ∀ z θ : ℝ, Work.Elliptic.bslOp p (fun z θ => -Φ z θ) z θ
      = -Work.Elliptic.bslOp p Φ z θ) :
    HonestEllLaw p F Φ ↔ Work.Construction.StatEqPhi p F (fun z θ => -Φ z θ) := by
  constructor
  · intro hE z θ
    rw [h z θ, hE z θ]
    ring
  · intro hE z θ
    have := hE z θ
    rw [h z θ] at this
    linarith

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

/-- The coupled problem in the honest case, at the *self-similar* base pair: the profile residual
vanishes, so the right-hand side is the explicit deficit alone. -/
theorem coupledResidual_of_profileEq (P : Work.ConstructionInstance.ProfileData α) (p κ : ℝ)
    {F Φbase : ℝ → ℝ → ℝ} (hbase : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.R1G.profileResidGen p κ F Φbase z θ = 0)
    {δ : ℝ → ℝ → ℝ → ℝ} :
    CoupledResidual P p κ F Φbase δ ↔
      ∀ r z t : ℝ, 0 < r → 0 < z → t ∈ Set.Ioo 0 P.T →
        coupOp P p F δ r z t
          = - (2 * (P.lam t) ^ 2 *
              Work.R1G.cutDeficit P (Work.CoreResiduals.ssPsi p P.lam Φbase)
                (Work.CoreResiduals.ssVort p P.lam F) r z t) := by
  unfold CoupledResidual coupConst
  constructor
  · intro h r z t hr hz ht
    have h1 := h r z t hr hz ht
    have hZ : 0 < Work.Cyl.rhoP r z ^ p / P.lam t :=
      div_pos (Real.rpow_pos_of_pos (Work.Cyl.rhoP_pos hr z) _) (P.hlam t ⟨by linarith [ht.1], ht.2⟩)
    have hθ : (Work.Cyl.rhoP r z ^ p / P.lam t, Work.Cyl.thetaP r z) ∈ Work.Construction.Qd :=
      ⟨hZ, Real.arctan_pos.mpr (div_pos hz hr), Real.arctan_lt_pi_div_two _⟩
    rw [hbase _ _ hθ, mul_zero, zero_add] at h1
    exact h1
  · intro h r z t hr hz ht
    have h1 := h r z t hr hz ht
    have hZ : 0 < Work.Cyl.rhoP r z ^ p / P.lam t :=
      div_pos (Real.rpow_pos_of_pos (Work.Cyl.rhoP_pos hr z) _) (P.hlam t ⟨by linarith [ht.1], ht.2⟩)
    have hθ : (Work.Cyl.rhoP r z ^ p / P.lam t, Work.Cyl.thetaP r z) ∈ Work.Construction.Qd :=
      ⟨hZ, Real.arctan_pos.mpr (div_pos hz hr), Real.arctan_lt_pi_div_two _⟩
    rw [hbase _ _ hθ, mul_zero, zero_add, h1]

/-! ## Abbreviations for the wiring -/

/-- The **honest stream profile** of the coupled problem: the base self-similar profile plus the
correction. -/
def coupledProf {α : NNReal} (P : Work.ConstructionInstance.ProfileData α)
    (Φbase : ℝ → ℝ → ℝ) (δ : ℝ → ℝ → ℝ → ℝ) (t : ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Φbase z θ + δ z θ t

/-- The **honest stream function** of the coupled problem:
`ψ = ssPsi p λ (Φ_base + δ(·,·,t))`. -/
def coupledStream {α : NNReal} (P : Work.ConstructionInstance.ProfileData α) (p : ℝ)
    (Φbase : ℝ → ℝ → ℝ) (δ : ℝ → ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ → ℝ :=
  fun r z t => Work.CoreResiduals.ssPsi p P.lam (coupledProf P Φbase δ t) r z t

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

/-- **On the upper half-plane the honest profile is the self-similar profile of `F_* + g`** (the
odd extension of `profile` is the identity branch for `θ ≥ 0`). -/
theorem honestW_eq_ssVort_of_nonneg {α : NNReal} (P : Work.ConstructionInstance.ProfileData α)
    {r z t : ℝ} (hr : 0 < r) (hz : 0 ≤ z) :
    honestW P r z t = Work.CoreResiduals.ssVort (Work.ConstructionInstance.profExp α) P.lam
      (Work.R1G.profOf P) r z t := by
  have hθ : 0 ≤ Work.Cyl.thetaP r z := by
    rw [Work.Cyl.thetaP]
    exact Real.arctan_nonneg.mpr (div_nonneg hz (le_of_lt hr))
  simp only [honestW, Work.CoreResiduals.ssVort, Work.R1G.profOf,
    Work.ConstructionInstance.profile_of_nonneg hθ]

/-- The **cut meridian vorticity profile** of the constructed field at a `ProfileData`, with the
*honest* (odd-extension) profile: `χ(ρP/L)·ssVort p λ (profile p P.g)`, `p = profExp α`. -/
def cutVortOf {α : NNReal} (P : Work.ConstructionInstance.ProfileData α) : ℝ → ℝ → ℝ → ℝ :=
  cutVort P (Work.ConstructionInstance.profExp α)
    (Work.ConstructionInstance.profile (Work.ConstructionInstance.profExp α) P.g)

/-- The honest cut profile is the cut profile of `honestW`. -/
theorem cutVortOf_eq_cutProfile {α : NNReal} (P : Work.ConstructionInstance.ProfileData α) :
    cutVortOf P = Work.R1G.cutProfile P (honestW P) := by
  funext r z t
  simp only [cutVortOf, cutVort_apply, Work.R1G.cutProfile_apply, honestW, chiAt]

/-- On the upper half-plane the honest cut profile is the `profOf`-based one. -/
theorem cutVortOf_apply_eq_of_nonneg {α : NNReal} (P : Work.ConstructionInstance.ProfileData α)
    {r z t : ℝ} (hr : 0 < r) (hz : 0 ≤ z) :
    cutVortOf P r z t = cutVort P (Work.ConstructionInstance.profExp α)
      (Work.R1G.profOf P) r z t := by
  simp only [cutVortOf, cutVort_apply]
  congr 1
  simpa only [honestW] using honestW_eq_ssVort_of_nonneg P hr hz

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
