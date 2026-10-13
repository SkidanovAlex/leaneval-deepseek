/-
# `Work.R1G.MeridianDeficit` — the G-route's residual in meridian form

The residual of the G-route, stated in the meridian coordinates where the whole local computation of
`Work.R1G.CutDeficit` lives:

  `MeridianDeficitIdent P Ψ W`  ⟺  `∀ r z t, 0 < r → meridianResid W Ψ r z t = cutDeficit P Ψ W r z t`,

i.e. **the meridian residual of the constructed field is the explicit cut-off deficit**.  Unlike the
field-level form `Defs.DeficitIsGResidual` (which involves the non-local Biot–Savart velocity
through `Work.CoreResiduals.r1Deficit`), this is a *local* identity between explicit functions of
`(r,z,t)` — the form in which the residual can actually be attacked (and the form in which the
`CoreResiduals` findings are stated).

The equivalence with the field-level deficit form is
`vortEqWithDeficit_iff_meridianDeficitIdent`, a direct specialization of the delivered
`vortEqWithDeficit_iff_meridian_field`; and the *windowed* instance
`ModulatedData.meridianDeficitIdent_of_far_zero` is the theorem of `GEquation`
(`ModulatedData.meridianResid_cut_eq_cutDeficit`) — so the meridian form of the honest residual is
*proved* at the self-similar stream function, and the gap to the actual stream function of the
constructed field is exactly the elliptic identification (`NOTES.md` §5).
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.R1G.Defs
import Submission.Work.R1G.GEquation
import Submission.Work.R1G.vortEqWithDeficit_iff_meridian_field
import Submission.Work.R1G.Support

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.R1G

variable {α : NNReal}

/-- **The G-route's residual in meridian form.**  The meridian residual of the constructed (cut)
field, against its own meridian stream function `Ψ`, is the *explicit* cut-off deficit
`Defs.cutDeficit`: the local statement of the deficit cancellation. -/
def MeridianDeficitIdent (P : Work.ConstructionInstance.ProfileData α)
    (Ψ W : ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ r z t : ℝ, 0 < r →
    Work.CoreResiduals.meridianResid (cutProfile P W) Ψ r z t = cutDeficit P Ψ W r z t

/-- The field-level deficit form with the *explicit* cut-off deficit is equivalent to the meridian
form: this is `Work.R1G.vortEqWithDeficit_iff_meridian_field` with the deficit
`WD := cutDeficit P Ψ W`. -/
theorem vortEqWithDeficit_iff_meridianDeficitIdent (P : Work.ConstructionInstance.ProfileData α)
    {Ψ W : ℝ → ℝ → ℝ → ℝ}
    (hv : ∀ x t, Work.ConstructionInstance.ansatzV P x t = Work.Cyl.cylField
        (fun r z => Work.Cyl.pdZ (fun r z => Ψ r z t) r z)
        (fun r z => -(Ψ r z t / r) - Work.Cyl.pdR (fun r z => Ψ r z t) r z) x)
    (hω : ∀ x t, Work.ConstructionInstance.solVort P x t
      = cutProfile P W (Work.Cyl.radial x) (Work.Cyl.axial x) t • Work.Cyl.eTheta x)
    (hΨ : ∀ t r z : ℝ, 0 < r →
      ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Ψ q.1 q.2 t) (r, z))
    (hW : ∀ t r z : ℝ, 0 < r →
      Work.Cyl.DiffAt2 (fun r z => cutProfile P W r z t) r z) :
    Work.CoreResiduals.VortEqWithDeficit P
        (fun x t => cutDeficit P Ψ W (Work.Cyl.radial x) (Work.Cyl.axial x) t
          • Work.Cyl.eTheta x)
      ↔ MeridianDeficitIdent P Ψ W :=
  vortEqWithDeficit_iff_meridian_field P hv hω hΨ hW

/-- **The honest residual in meridian form gives the deficit form** of the `ℝ³` vorticity equation,
with the *explicit* cut-off deficit. -/
theorem honestR1_cutDeficit_of_meridianDeficitIdent (P : Work.ConstructionInstance.ProfileData α)
    {Ψ W : ℝ → ℝ → ℝ → ℝ}
    (hv : ∀ x t, Work.ConstructionInstance.ansatzV P x t = Work.Cyl.cylField
        (fun r z => Work.Cyl.pdZ (fun r z => Ψ r z t) r z)
        (fun r z => -(Ψ r z t / r) - Work.Cyl.pdR (fun r z => Ψ r z t) r z) x)
    (hω : ∀ x t, Work.ConstructionInstance.solVort P x t
      = cutProfile P W (Work.Cyl.radial x) (Work.Cyl.axial x) t • Work.Cyl.eTheta x)
    (hΨ : ∀ t r z : ℝ, 0 < r →
      ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Ψ q.1 q.2 t) (r, z))
    (hW : ∀ t r z : ℝ, 0 < r →
      Work.Cyl.DiffAt2 (fun r z => cutProfile P W r z t) r z)
    (h : MeridianDeficitIdent P Ψ W) :
    Work.CoreResiduals.VortEqWithDeficit P
      (fun x t => cutDeficit P Ψ W (Work.Cyl.radial x) (Work.Cyl.axial x) t
        • Work.Cyl.eTheta x) :=
  (vortEqWithDeficit_iff_meridianDeficitIdent P hv hω hΨ hW).mpr h

/-- **The meridian form of the residual is *proved* at the self-similar stream function.**  At a
`ModulatedData` whose `g`-equation has vanishing far-field term, the meridian residual of the
constructed (cut) field against the self-similar stream function is *exactly* the explicit cut-off
deficit, in the physical window.  (The gap to the *actual* stream function of the constructed field
is the elliptic identification — `NOTES.md` §5.) -/
theorem ModulatedData.meridianDeficitIdent_of_far_zero (D : ModulatedData α)
    (hΦ : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      ContDiffAt ℝ 2 (fun q : ℝ × ℝ => D.Φ q.1 q.2) (z, θ))
    (hF : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      ContDiffAt ℝ 1 (fun q : ℝ × ℝ => profOf D.P q.1 q.2) (z, θ))
    (hFar : ∀ z θ : ℝ, D.Far z θ = 0) :
    ∀ r z t : ℝ, 0 < r → 0 < z → t ∈ Set.Ioo 0 D.P.T →
      Work.CoreResiduals.meridianResid (cutProfile D.P (ssVortOf D.P)) (ssPsiOf D.P D.Φ) r z t
        = cutDeficit D.P (ssPsiOf D.P D.Φ) (ssVortOf D.P) r z t :=
  D.meridianResid_cut_eq_cutDeficit hΦ hF hFar


/-! ## The G-route's honest residual interface -/

/-- **The G-route's honest residual interface.**  The modulated data (`g ≠ 0` solving the `St2`/`St3`
`g`-equation with vanishing far-field term), the two halves of the ansatz dictionary (the velocity is
the stream-function field of `Ψ`, the vorticity is the cut meridian profile `χ(ρ/L)·W`), and the
**meridian residual** `MeridianDeficitIdent`: the constructed field's residual *is* the explicit
cut-off deficit.

Unlike `Defs.DeficitIsGResidual` (the strong field-level form used by `Check.GRouteHyp`, which forces
the deficit to be a function of the self-similar variable and is therefore *false* for a cut field),
this interface is non-vacuous and is exactly what the local computation of `Work.R1G.CutDeficit`
supports (`ModulatedData.meridianDeficitIdent_of_far_zero` proves its self-similar instance).  The
deficit it produces is **nonzero on the annulus** `L ≤ ρ ≤ 2L` (`Work.R1G.Support`), i.e. the
interface explains *why* the zero-deficit residual R1 fails at a cut field — and R1 *closes*
precisely when the modulation also cancels the annulus contribution. -/
structure GRouteResidual (α : NNReal) where
  /-- the modulated profile data (`g ≠ 0` solving the `g`-equation) -/
  D : ModulatedData α
  /-- the `g`-equation's far-field term vanishes (the modulation cancels the profile residual) -/
  hFar : ∀ z θ : ℝ, D.Far z θ = 0
  /-- the meridian stream function of the constructed velocity -/
  Ψ : ℝ → ℝ → ℝ → ℝ
  /-- the meridian profile of the *uncut* constructed vorticity -/
  W : ℝ → ℝ → ℝ → ℝ
  /-- the ansatz half of the dictionary: the velocity is the stream-function field of `Ψ` -/
  hv : ∀ x t, Work.ConstructionInstance.ansatzV D.P x t = Work.Cyl.cylField
    (fun r z => Work.Cyl.pdZ (fun r z => Ψ r z t) r z)
    (fun r z => -(Ψ r z t / r) - Work.Cyl.pdR (fun r z => Ψ r z t) r z) x
  /-- the ansatz half of the dictionary: the vorticity is the cut meridian profile -/
  hω : ∀ x t, Work.ConstructionInstance.solVort D.P x t
    = cutProfile D.P W (Work.Cyl.radial x) (Work.Cyl.axial x) t • Work.Cyl.eTheta x
  /-- the stream function is `C²` in the meridian variables -/
  hΨ : ∀ t r z : ℝ, 0 < r → ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Ψ q.1 q.2 t) (r, z)
  /-- the meridian profile is differentiable in the meridian variables -/
  hW : ∀ t r z : ℝ, 0 < r → Work.Cyl.DiffAt2 (fun r z => cutProfile D.P W r z t) r z
  /-- **the honest residual**: the meridian residual is the explicit cut-off deficit -/
  hMer : MeridianDeficitIdent D.P Ψ W

/-- **The G-route's honest residual, in deficit form.**  From `GRouteResidual`, the constructed field
satisfies the `ℝ³` vorticity equation **up to the explicit cut-off deficit** `cutDeficit·e_θ` — a
*nonzero* deficit, supported in the annulus `L ≤ ρ ≤ 2L`. -/
theorem deficitForm_of_gRouteResidual (G : GRouteResidual α) :
    Work.CoreResiduals.VortEqWithDeficit G.D.P
      (fun x t => cutDeficit G.D.P G.Ψ G.W (Work.Cyl.radial x) (Work.Cyl.axial x) t
        • Work.Cyl.eTheta x) :=
  honestR1_cutDeficit_of_meridianDeficitIdent G.D.P G.hv G.hω G.hΨ G.hW G.hMer

/-- **The residual is confined to the annulus.**  At a `GRouteResidual` the deficit field vanishes
wherever the cut-off is transparent (`ρ < L`) or the field vanishes (`ρ > 2L`); on the transparent
region the constructed field therefore satisfies the `ℝ³` vorticity equation *exactly*. -/
theorem deficitField_eq_zero_of_not_mem_annulus (G : GRouteResidual α) {x : R3} {t : ℝ}
    (h : Work.Cyl.rho x < G.D.P.L ∨ 2 * G.D.P.L < Work.Cyl.rho x) :
    cutDeficit G.D.P G.Ψ G.W (Work.Cyl.radial x) (Work.Cyl.axial x) t = 0 :=
  cutDeficit_eq_zero_of_not_mem_annulus G.D.P G.Ψ G.W (by
    rwa [rho_eq_rhoP x] at h)


/-! ## The deficit cancellation at the profile level -/

/-- **THE DEFICIT CANCELLATION, as the honest hypothesis for R1.**  If the modulation cancels the
explicit cut-off term *at the profile level*,

  `χ(ρP(r,z)/L)·meridianResid W Ψ = -cutDeficit P Ψ W`,

then the meridian residual of the **constructed (cut)** field vanishes — i.e. R1 holds in meridian
form, by the cut-off identity `Work.R1G.meridianResid_cut`.

This isolates exactly the two ingredients of the honest route: the *profile-level* statement (what
the `g`-equation controls, through `Work.R1G.ProfileEq` and the promotion) and the *explicit* cut-off
term (fixed by `χ`).  For the self-similar stream function `Ψ = ssPsiOf` the uncut residual vanishes
(`Meridian.meridianResid_ssVortOf_eq_zero`), so the cancellation forces `cutDeficit = 0` — i.e. it
can only hold where the cut-off is transparent; the honest construction needs the *actual*
(non-self-similar) stream function of the cut field, which is the elliptic identification. -/
theorem meridianResid_cutProfile_eq_zero_of_cancel {α : NNReal}
    (P : Work.ConstructionInstance.ProfileData α) {Ψ W : ℝ → ℝ → ℝ → ℝ} {r z t : ℝ} (hr : 0 < r)
    (hWr : DifferentiableAt ℝ (fun r' : ℝ => W r' z t) r)
    (hWz : DifferentiableAt ℝ (fun z' : ℝ => W r z' t) z)
    (hWt : DifferentiableAt ℝ (fun s : ℝ => W r z s) t)
    (hcancel : Work.Stability.chi (Work.Cyl.rhoP r z / P.L)
      * Work.CoreResiduals.meridianResid W Ψ r z t = - cutDeficit P Ψ W r z t) :
    Work.CoreResiduals.meridianResid (cutProfile P W) Ψ r z t = 0 := by
  have h := meridianResid_cut P (W := W) (ψ := Ψ) hr hWr hWz hWt
  show Work.CoreResiduals.meridianResid
      (fun r z t => Work.Stability.chi (Work.Cyl.rhoP r z / P.L) * W r z t) Ψ r z t = 0
  rw [h, hcancel]
  simp only [cutDeficit, chiRad]
  ring

end Work.R1G
