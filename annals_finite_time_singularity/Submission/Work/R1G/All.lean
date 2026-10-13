/-
# `Work.R1G` — the R1 G-route, in one import

```lean
import Submission.Work.R1G.All
```

The **G-route** to residual **R1** of the `fts` formalisation, as recommended by
`Submission/Work/CoreResiduals/NOTES.md` §13 / the final report §2: the delivered zero-deficit
residual `VortEq α P` fails at every delivered `ProfileData` (the `St1` cut-off is not a function of
the self-similar variable), so the honest interface carries the deficit explicitly with a **nonzero
modulation `g`** that cancels it (`Work.Stability.GEquationFar`).

## What this area delivers

* **Deliverable 1 — the modulated profile data** (`Defs.ModulatedData`): the Construction area's
  reference profile `F_*` plus a *nonzero* perturbation `g` whose equation is the `St2`/`St3`
  `g`-equation (`Defs.GEquationStat`), together with the derivation bundle `GDerivData`.  The
  **promotion** of the reduced identity `Work.Construction.Fstar_stationary_identity` to the full
  profile equation at the effective rate `2·(-λ̄')` is `GEquation.profileEq_of_gEquationStat`
  (`GEquationStat ⟺ ProfileEq`), through the `gDynRHS` identification
  `GEquation.profileResid_eq_gEqResidual` (the delegated `profileResid_eq_gEqResidual`).
* **Deliverable 2 — the deficit cancellation**: the meridian residual of the constructed (cut) field is *explicit*:
  `CutDeficit.meridianResid_cut_ssVortOf_eq` (the profile residual plus the explicit cut-off term)
  and, at a `ModulatedData`, `GEquation.ModulatedData.meridianResid_cut_eq` (the profile-level
  deficit `Far` plus the cut-off term) and
  `GEquation.ModulatedData.meridianResid_cut_eq_cutDeficit` (`Far = 0`: the deficit is *exactly* the
  explicit cut-off term `Defs.cutDeficit`).  `Support` localises the deficit to the annulus
  `L ≤ ρ ≤ 2L`, so the constructed field solves the meridian equation on the transparent region
  `ρ < L` (`Support.ModulatedData.meridianResid_cut_eq_zero_of_rho_lt`).
* **Deliverable 3 — the `hR1`-free check** (`Check`): the delivered end-to-end chain with the
  deficit-form residual in place of `VortEq` (`Check.GResiduals`, `Check.theorem1_of_gResiduals`,
  `Check.theorem1_of_model_data_deficitForm`,
  `Check.check_theorem_1_of_inputs_of_fixed_deficitForm` — mechanical via
  `Work.CoreResiduals.vortEq_iff_noDeficit`), and the honest end-to-end checks
  `Check.theorem1_of_honestR1`, `Check.theorem1_of_gRoute`, `Check.theorem1_of_modulated_data`,
  all `sorry`-free.  The honest *hypothesis* is `Check.GRouteHyp` — the modulated data, the ansatz
  dictionary, and the profile-level **deficit cancellation**
  `χ(ρP/L)·meridianResid W Ψ = -cutDeficit P Ψ W` (`MeridianDeficit.meridianResid_cutProfile_eq_zero_of_cancel`),
  which by the cut-off identity is exactly the vanishing of the constructed field's meridian
  residual, hence exactly R1.
* **The residual as a local statement** (`MeridianDeficit`): `MeridianDeficitIdent`,
  `vortEqWithDeficit_iff_meridianDeficitIdent`, the non-vacuous interface `GRouteResidual` with
  `deficitForm_of_gRouteResidual`, and the non-vacuity certificates
  `exists_chiRad_ne_zero_of_annulus`, `exists_cutDeficit_ne_zero`.

## The one named residual of the area

The **elliptic identification** of the constructed field's meridian stream function: its signed
*local* form is `Work.R1G.vorticity_psiField_bslOp`, its affine/interface form is
`Work.R1G.MeridianDeficitIdent` (equivalently `Defs.DeficitIsGResidual`), and it is the
non-local side of R1 (`Submission/Work/CoreResiduals/NOTES.md` §5(iv)).  Everything else in the
G-route is proved here; `NOTES.md` §5.3 gives the roadmap and the sign caution.
-/
import Mathlib.Tactic.MinImports
import Submission.Work.R1G.Defs
import Submission.Work.R1G.meridianResid_cut
import Submission.Work.R1G.meridianResid_ssVort_eq
import Submission.Work.R1G.meridianResid_cut_ssVort_eq
import Submission.Work.R1G.profileResid_eq_gEqResidual
import Submission.Work.R1G.profileResid_eq_gEqResidual_qd
import Submission.Work.R1G.gDerivDataQd_phi_zero
import Submission.Work.R1G.exists_profileData_g_visible
import Submission.Work.R1G.exists_profileData_g_ne_zero
import Submission.Work.R1G.ModulatedInstance
import Submission.Work.R1G.CutDeficit
import Submission.Work.R1G.Meridian
import Submission.Work.R1G.GEquation
import Submission.Work.R1G.vortEqWithDeficit_iff_meridian
import Submission.Work.R1G.vortEqWithDeficit_iff_meridian_field
import Submission.Work.R1G.cutDeficit_eq_zero_of_rho_lt
import Submission.Work.R1G.cutDeficit_eq_zero_of_two_mul_lt_rho
import Submission.Work.R1G.vorticity_psiField_bslOp
import Submission.Work.R1G.MeridianDeficit
import Submission.Work.R1G.exists_chiRad_ne_zero_of_annulus
import Submission.Work.R1G.exists_cutDeficit_ne_zero
import Submission.Work.R1G.Support
import Submission.Work.R1G.Check

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
