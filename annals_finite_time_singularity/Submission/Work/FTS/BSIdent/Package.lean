/-
# `Work.FTS.BSIdent.Package` — the identification in the shape of `blowupAtTop_of_regPkg'`

This module packages route A of `Work.FTS.BSIdent.Ident` (`hid_of_biotSavartInverse`) into the
exact statement required by the firing theorem of the design (`FTS_PHYS_BRIDGE.md` §1):

  `hid : ∀ t ∈ Ioo 0 C.T, ∀ x ∈ Uax, physVel (−physOmega α A B g C) x t
            = Cyl.psiField (fun r z => merPsi α A B Φ C r z t) x`.

The regularity package `hreg : ∀ S > 0, Work.FTS.Regularity.RegPkg α S A B g` supplies, *by
derivation* (no extra hypothesis),

* positivity of the clock on the relevant fake-time strip (`A (clockInv C t) > 0`,
  `B (clockInv C t) > 0`);
* the integrability of the reconstructed vorticity slice (`RegPkg.integrable_physVort_slice`),
  hence — via the curl identity of `Curl.lean` — the integrability of the vorticity of the ansatz
  field.

The remaining hypotheses are the ones the identification genuinely needs and which no other node
of the audit supplies in this form:

* `hBS` — the inverse Biot–Savart law of the LWP chapter (`Work.LWP.BiotSavartInverse`), the same
  input used by `Work.FTS.Physical.Ident.biotSavart_eq_psiField_of_bslOp`;
* `hlaw` — the elliptic law of the fake-time solution in self-similar variables (the `IsBslSol`
  conjunct of `IsDynGSolWith (IsBslSol p) p Φ g` of node N1/Open2, see the note in `NOTES.md`);
* `hsm`, `hsm2` — the `C²` regularity of the self-similar stream function and of the meridian
  stream function off the degenerate set;
* `hC1`, `hdec` — the **geometric bundle of the ansatz field**: `C¹` and decay `1/‖x‖` of
  `psiField (merPsi … · t)`.  This is the `psiField`-form analogue of node N7's
  `Work.FTS.Regularity.physVel_isContDiffHolder`; `Bundle.lean` records the axis-regular model
  case in which it is *proved* from bounds on the meridian profile, and exhibits an inhabitant.

See `NOTES.md` for the exact status of each hypothesis and for the (small) change this forces on
the signature of `blowupAtTop_of_regPkg'`: it must carry the `IsBslSol` conjunct of the dynamic
solution, which the design's §1 sketch leaves implicit.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.BSIdent.Ident
import Submission.Work.FTS.Physical.RegPkg.integrable_physVort_slice
import Submission.Work.FTS.BSIdent.Defs.contDiffAt_merPsi_slice
import Submission.Work.FTS.BSIdent.Defs.contDiffAt_Phi_of_merPsi

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set MeasureTheory
open scoped Topology Real NNReal

namespace Work.FTS.BSIdent

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **THE IDENTIFICATION `hid` OF `blowupAtTop_of_regPkg'`.**  On `Uax` and for `t ∈ (0,T)` the
reconstructed physical velocity `physVel (−physOmega α A B g C)` is the stream-function field
`psiField (merPsi α A B Φ C · · t)` of the fake-time solution. -/
theorem hid {α : ℝ≥0} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ} {C : Physical.PhysClock} {Φ : Fam}
    (hreg : ∀ S : ℝ, 0 < S → Work.FTS.Regularity.RegPkg (α : ℝ) S A B g)
    (hBS : Work.LWP.BiotSavartInverse)
    (hlaw : ∀ t ∈ Set.Ioo 0 C.T, ∀ w θ, 0 < w → 0 < θ → θ < π / 2 →
      Work.Elliptic.bslOp (Work.FTS.Regularity.pExp (α : ℝ))
          (fun z θ' => Φ z θ' (Physical.clockInv C t)) w θ
        = Work.Construction.Fstar (Work.FTS.Regularity.pExp (α : ℝ)) w θ
          + g w θ (Physical.clockInv C t))
    (hΨ : ∀ t ∈ Set.Ioo 0 C.T, ∀ r z, 0 < r → z ≠ 0 → ContDiffAt ℝ 2
      (fun p : ℝ × ℝ => merPsi (α : ℝ) A B Φ C p.1 p.2 t) (r, z))
    (hC1 : ∀ t ∈ Set.Ioo 0 C.T, ContDiff ℝ 1
      (Work.Cyl.psiField (fun r z => merPsi (α : ℝ) A B Φ C r z t)))
    (hdec : ∀ t ∈ Set.Ioo 0 C.T, ∃ D : ℝ, ∀ x : R3,
      ‖Work.Cyl.psiField (fun r z => merPsi (α : ℝ) A B Φ C r z t) x‖ ≤ D / (1 + ‖x‖)) :
    ∀ t ∈ Set.Ioo 0 C.T, ∀ x ∈ Uax,
      Physical.physVel (-(Physical.physOmega (α : ℝ) A B g C)) x t
        = Work.Cyl.psiField (fun r z => merPsi (α : ℝ) A B Φ C r z t) x := by
  intro t ht x hx
  -- the clock data and the integrability, from `RegPkg` on a strip containing `τ = clockInv C t`
  have htIco : t ∈ Set.Ico (0 : ℝ) C.T := ⟨ht.1.le, ht.2⟩
  have hτnn : 0 ≤ Physical.clockInv C t := Physical.clockInv_nonneg C htIco
  have hτmem : Physical.clockInv C t ∈ Set.Icc (0 : ℝ) (Physical.clockInv C t + 1) :=
    ⟨hτnn, by linarith⟩
  have hP := hreg (Physical.clockInv C t + 1) (by linarith)
  have hA : 0 < A (Physical.clockInv C t) := hP.hA _ hτmem
  have hB : 0 < B (Physical.clockInv C t) := hP.hB _ hτmem
  have hα : 0 < (α : ℝ) := hP.hα
  obtain ⟨hint, -⟩ := Physical.RegPkg.integrable_physVort_slice hP hτmem
  have hsm2 := hΨ t ht
  -- the interior `C²`-regularity of `Φ` is *derived* from the off-axis one of `merPsi`
  have hsm : ∀ w θ, 0 < w → 0 < θ → θ < π / 2 → ContDiffAt ℝ 2
      (fun p : ℝ × ℝ => Φ p.1 p.2 (Physical.clockInv C t)) (w, θ) :=
    fun w θ hw hθ hθ2 => Defs.contDiffAt_Phi_of_merPsi α A B Φ C t hα (ne_of_gt hA) hB hsm2 hw hθ hθ2
  exact hid_of_biotSavartInverse hBS hA hB (hlaw t ht) hsm hsm2 (hC1 t ht)
    (hdec t ht) hint.neg x hx

/-- **The identification from the elliptic law in `IsBslSol` form.**  This is `hid` with the raw
`bslOp`-law replaced by the paper's (PolarBSL) interface, in exactly the form in which node
N1/Open2 delivers it: the first conjunct of `Work.FTS.Galerkin.IsDynGSolWith (IsBslSol p) p Φ g`
is `∀ τ ≥ 0, IsBslSol p (Construction.Ftau p g τ) (slice Φ τ)`, and
`Work.Construction.Ftau p g τ z θ = F_*(p) z θ + g z θ τ` on the closed quadrant. -/
theorem hid_of_IsBslSol {α : ℝ≥0} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ} {C : Physical.PhysClock}
    {Φ : Fam}
    (hreg : ∀ S : ℝ, 0 < S → Work.FTS.Regularity.RegPkg (α : ℝ) S A B g)
    (hBS : Work.LWP.BiotSavartInverse)
    (hsol : ∀ t ∈ Set.Ioo 0 C.T, Work.Elliptic.IsBslSol (Work.FTS.Regularity.pExp (α : ℝ))
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp (α : ℝ)) g (Physical.clockInv C t))
      (fun z θ => Φ z θ (Physical.clockInv C t)))
    (hΨ : ∀ t ∈ Set.Ioo 0 C.T, ∀ r z, 0 < r → z ≠ 0 → ContDiffAt ℝ 2
      (fun p : ℝ × ℝ => merPsi (α : ℝ) A B Φ C p.1 p.2 t) (r, z))
    (hC1 : ∀ t ∈ Set.Ioo 0 C.T, ContDiff ℝ 1
      (Work.Cyl.psiField (fun r z => merPsi (α : ℝ) A B Φ C r z t)))
    (hdec : ∀ t ∈ Set.Ioo 0 C.T, ∃ D : ℝ, ∀ x : R3,
      ‖Work.Cyl.psiField (fun r z => merPsi (α : ℝ) A B Φ C r z t) x‖ ≤ D / (1 + ‖x‖)) :
    ∀ t ∈ Set.Ioo 0 C.T, ∀ x ∈ Uax,
      Physical.physVel (-(Physical.physOmega (α : ℝ) A B g C)) x t
        = Work.Cyl.psiField (fun r z => merPsi (α : ℝ) A B Φ C r z t) x :=
  hid hreg hBS (fun t ht w θ hw hθ hθ2 => (hsol t ht).1 w hw θ hθ hθ2) hΨ hC1 hdec

end Work.FTS.BSIdent
