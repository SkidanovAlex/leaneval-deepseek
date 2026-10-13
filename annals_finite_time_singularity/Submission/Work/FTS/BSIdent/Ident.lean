/-
# `Work.FTS.BSIdent.Ident` — the identification `BS(−physOmega) = psiField (merPsi)`

This module proves **audit §5 item 4**: on the open set `Uax = {x₃ ≠ 0, r ≠ 0}`, the reconstructed
physical velocity is the stream-function field of the fake-time solution,

  `physVel (−physOmega α A B g C) x t = Cyl.psiField (fun r z => merPsi α A B Φ C r z t) x`

— the statement `hid` of `blowupAtTop_of_regPkg'` (`FTS_PHYS_BRIDGE.md` §1).

## The route, and exactly what is assumed

The proof is a one-step Biot–Savart inversion.  Put `ω := −physOmega α A B g C · t` and
`v := psiField (merPsi … · t)`.  Then

* **`v` has vorticity `ω`** — this is `vorticity_psiField_merPsi` (`Curl.lean`), the mathematical
  content of the identification: the self-similar rescaling by `B`, the amplitude `A⁻¹`, the odd
  extension in `θ` and the sign of the design's correction 1 are all handled there;
* **`v` is in the class of the inverse Biot–Savart law**: it is `C¹` (`hC1`), divergence-free
  (`div_psiField_merPsi`, proved from the pointwise `Cyl.div_psiField` by density), its vorticity
  is integrable (`hint`, the integrability of the reconstructed vorticity slice — supplied by node
  N7's bundle), and it decays like `1/‖x‖` (`hdec`);
* applying `Work.LWP.BiotSavartInverse` to `v` and transporting the resulting a.e. equality
  `vorticity v =ᵐ ω` into the Biot–Savart integral (`biotSavart_congr_ae`) gives
  `biotSavart ω = v`, which is the claim.

The **only analytic inputs** (both named, both about objects *different* from the conclusion) are:

1. `Work.LWP.BiotSavartInverse` — the inverse Biot–Savart law of the LWP chapter ("a `C¹`,
   divergence-free, decaying field is recovered from its vorticity"), the same input the existing
   `Work.FTS.Physical.Ident.biotSavart_eq_psiField_of_bslOp` uses;
2. the **geometric bundle of the ansatz field** `v = psiField (merPsi … · t)`: `C¹`, decay
   `1/‖x‖`, integrability of its vorticity, and the `C²`-smoothness of the meridian stream function
   off the axis and the plane.  This is the `psiField`-form analogue of node N7's transfer theorem
   `Work.FTS.Regularity.physVel_isContDiffHolder` (which proves the corresponding bundle for
   `BS ω` instead of `psiField ψ`); the axis behaviour of the *stream function* form is where the
   paper's Hölder analysis at the axis lives.  `Bundle.lean` records the axis-regular model case
   (`ψ = r·V(r²,z)`) in which the bundle is *proved* from profile bounds, so the interface is
   inhabited and the shape of the remaining analytic input is explicit.

An alternative route — the lead's "Liouville on the difference of the fields" — is proved in
`Submission/Work/FTS/BSIdent/Liouville/Hid.lean` as `hid_of_divCurlLiouville`, taking the classical
div-curl Liouville input `Work.FTS.Physical.DivCurlLiouville` of node N8 plus the *forward*
Biot–Savart law at the swirl vorticity (design item 3, `BiotSavartSwirl`), in place of
`BiotSavartInverse`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.BSIdent.Curl
import Submission.Work.FTS.BSIdent.Cyl.div_psiField_merPsi
import Submission.Work.FTS.BSIdent.Liouville.biotSavart_congr_ae
import Submission.Work.FTS.BSIdent.Bundle

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set MeasureTheory
open scoped Topology Real

namespace Work.FTS.BSIdent

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Parity of the meridian stream function -/

/-- **`merPsi` is odd in the meridian axial coordinate**: `merPsi r (−z) t = −merPsi r z t`.  This
is the parity that makes `psiField (merPsi …)` an odd field (`Work.Cyl.isOdd_psiField_of_oddZ`),
i.e. component `i` odd in coordinate `i` and even in the other two. -/
theorem merPsi_oddZ (α : ℝ) (A B : ℝ → ℝ) (Φ : Fam) (C : Physical.PhysClock) (t : ℝ)
    (h0 : ∀ z τ, Φ z 0 τ = 0) (r z : ℝ) :
    merPsi α A B Φ C r (-z) t = -merPsi α A B Φ C r z t := by
  rw [merPsi_apply, merPsi_apply]
  have hρ : Work.Cyl.rhoP r (-z) = Work.Cyl.rhoP r z := by
    rw [Work.Cyl.rhoP, Work.Cyl.rhoP]; ring_nf
  have hθ : Work.Cyl.thetaP r (-z) = -Work.Cyl.thetaP r z := by
    rw [Work.Cyl.thetaP, Work.Cyl.thetaP, neg_div, Real.arctan_neg]
  rw [hρ, hθ, PhiOdd_neg_theta h0]
  ring

/-- The reconstruction's stream-function field is odd. -/
theorem isOdd_psiField_merPsi (α : ℝ) (A B : ℝ → ℝ) (Φ : Fam) (C : Physical.PhysClock) (t : ℝ)
    (h0 : ∀ z τ, Φ z 0 τ = 0) :
    IsOdd (Work.Cyl.psiField (fun r z => merPsi α A B Φ C r z t)) :=
  Work.Cyl.isOdd_psiField_of_oddZ (fun r z => merPsi_oddZ α A B Φ C t h0 r z)

variable {α : ℝ} {A B : ℝ → ℝ} {Φ : Fam} {C : Physical.PhysClock} {g : ℝ → ℝ → ℝ → ℝ} {t : ℝ}

/-- **The vorticity of the ansatz field is the re-signed physical vorticity**, on `Uax`, under the
hypotheses of `vorticity_psiField_merPsi`. -/
theorem vorticity_psiField_merPsi_apply (hA : 0 < A (Physical.clockInv C t))
    (hB : 0 < B (Physical.clockInv C t))
    (hlaw : ∀ w θ, 0 < w → 0 < θ → θ < π / 2 →
      Work.Elliptic.bslOp (Work.FTS.Regularity.pExp α)
          (fun z θ' => Φ z θ' (Physical.clockInv C t)) w θ
        = Work.Construction.Fstar (Work.FTS.Regularity.pExp α) w θ
          + g w θ (Physical.clockInv C t))
    (hsm : ∀ w θ, 0 < w → 0 < θ → θ < π / 2 → ContDiffAt ℝ 2
      (fun p : ℝ × ℝ => Φ p.1 p.2 (Physical.clockInv C t)) (w, θ))
    {x : R3} (hx : x ∈ Uax) :
    vorticity (Work.Cyl.psiField (fun r z => merPsi α A B Φ C r z t)) x
      = -(Physical.physOmega α A B g C x t) := by
  have h := vorticity_psiField_merPsi (α := α) (A := A) (B := B) (Φ := Φ) (C := C) (g := g)
    (t := t) hA hB hlaw hsm (x := x) hx
  rw [h]
  exact vorticity_psiField_merPsi_eq_neg_physOmega α A B C g t

/-- The a.e. equality of the vorticity of the ansatz field with `−physOmega`, as an `EventuallyEq`
over Lebesgue measure on `ℝ³`. -/
theorem vorticity_psiField_merPsi_ae (hA : 0 < A (Physical.clockInv C t))
    (hB : 0 < B (Physical.clockInv C t))
    (hlaw : ∀ w θ, 0 < w → 0 < θ → θ < π / 2 →
      Work.Elliptic.bslOp (Work.FTS.Regularity.pExp α)
          (fun z θ' => Φ z θ' (Physical.clockInv C t)) w θ
        = Work.Construction.Fstar (Work.FTS.Regularity.pExp α) w θ
          + g w θ (Physical.clockInv C t))
    (hsm : ∀ w θ, 0 < w → 0 < θ → θ < π / 2 → ContDiffAt ℝ 2
      (fun p : ℝ × ℝ => Φ p.1 p.2 (Physical.clockInv C t)) (w, θ)) :
    (fun x : R3 => vorticity (Work.Cyl.psiField (fun r z => merPsi α A B Φ C r z t)) x)
      =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure R3)]
      (fun x : R3 => -(Physical.physOmega α A B g C x t)) := by
  rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
  refine measure_mono_null (fun x hx => ?_) volume_Uax_compl
  simp only [Set.mem_setOf_eq] at hx
  intro hxu
  exact hx (vorticity_psiField_merPsi_apply hA hB hlaw hsm hxu)

/-- The vorticity of the ansatz field is integrable as soon as the reconstructed vorticity slice
is: the two agree off the null set `Uaxᶜ`. -/
theorem integrable_vorticity_psiField_merPsi (hA : 0 < A (Physical.clockInv C t))
    (hB : 0 < B (Physical.clockInv C t))
    (hlaw : ∀ w θ, 0 < w → 0 < θ → θ < π / 2 →
      Work.Elliptic.bslOp (Work.FTS.Regularity.pExp α)
          (fun z θ' => Φ z θ' (Physical.clockInv C t)) w θ
        = Work.Construction.Fstar (Work.FTS.Regularity.pExp α) w θ
          + g w θ (Physical.clockInv C t))
    (hsm : ∀ w θ, 0 < w → 0 < θ → θ < π / 2 → ContDiffAt ℝ 2
      (fun p : ℝ × ℝ => Φ p.1 p.2 (Physical.clockInv C t)) (w, θ))
    (hint : Integrable (fun x : R3 => -(Physical.physOmega α A B g C x t))) :
    Integrable (fun x : R3 =>
      vorticity (Work.Cyl.psiField (fun r z => merPsi α A B Φ C r z t)) x) :=
  hint.congr (vorticity_psiField_merPsi_ae hA hB hlaw hsm).symm

/-! ## The identification -/

/-- **THE IDENTIFICATION (audit §5 item 4), from the inverse Biot–Savart law.**  On `Uax` the
reconstructed physical velocity is the stream-function field of the fake-time solution:

  `physVel (−physOmega α A B g C) x t = psiField (merPsi α A B Φ C · · t) x`.

The hypotheses are the clock and elliptic data (`hA`, `hB`, `hlaw`, `hsm`), the inverse Biot–Savart
law `hInv`, the integrability of the reconstructed vorticity slice (`hint`) and the geometric
bundle of the ansatz field: `C¹` (`hC1`), decay `1/‖x‖` (`hdec`) and the off-axis slice smoothness
of the meridian stream function (`hsm2`, used only for the divergence-freeness of the field). -/
theorem hid_of_biotSavartInverse (hInv : Work.LWP.BiotSavartInverse)
    (hA : 0 < A (Physical.clockInv C t)) (hB : 0 < B (Physical.clockInv C t))
    (hlaw : ∀ w θ, 0 < w → 0 < θ → θ < π / 2 →
      Work.Elliptic.bslOp (Work.FTS.Regularity.pExp α)
          (fun z θ' => Φ z θ' (Physical.clockInv C t)) w θ
        = Work.Construction.Fstar (Work.FTS.Regularity.pExp α) w θ
          + g w θ (Physical.clockInv C t))
    (hsm : ∀ w θ, 0 < w → 0 < θ → θ < π / 2 → ContDiffAt ℝ 2
      (fun p : ℝ × ℝ => Φ p.1 p.2 (Physical.clockInv C t)) (w, θ))
    (hsm2 : ∀ r z, 0 < r → z ≠ 0 → ContDiffAt ℝ 2
      (fun p : ℝ × ℝ => merPsi α A B Φ C p.1 p.2 t) (r, z))
    (hC1 : ContDiff ℝ 1 (Work.Cyl.psiField (fun r z => merPsi α A B Φ C r z t)))
    (hdec : ∃ D : ℝ, ∀ x : R3,
      ‖Work.Cyl.psiField (fun r z => merPsi α A B Φ C r z t) x‖ ≤ D / (1 + ‖x‖))
    (hint : Integrable (fun x : R3 => -(Physical.physOmega α A B g C x t))) :
    ∀ x ∈ Uax, Physical.physVel (-(Physical.physOmega α A B g C)) x t
      = Work.Cyl.psiField (fun r z => merPsi α A B Φ C r z t) x := by
  intro x hx
  -- the field is divergence-free and its vorticity is integrable
  have hdiv : FiniteTimeSingularity.div
      (Work.Cyl.psiField (fun r z => merPsi α A B Φ C r z t)) = 0 :=
    Cyl.div_psiField_merPsi α A B Φ C t hC1 hsm2
  have hint' := integrable_vorticity_psiField_merPsi (g := g) hA hB hlaw hsm hint
  -- the inverse Biot–Savart law at the ansatz field
  have hself := hInv _ hC1 (fun y => congrFun hdiv y) hint' hdec x
  -- transport the a.e. equality into the Biot–Savart integral
  have hae : (fun y : R3 => vorticity (Work.Cyl.psiField (fun r z => merPsi α A B Φ C r z t)) y)
      =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure R3)]
      (fun y : R3 => -(Physical.physOmega α A B g C y t)) :=
    vorticity_psiField_merPsi_ae hA hB hlaw hsm
  have hcongr := Liouville.biotSavart_congr_ae hae x
  change Work.LWP.biotSavart (fun y : R3 => -(Physical.physOmega α A B g C y t)) x
      = Work.Cyl.psiField (fun r z => merPsi α A B Φ C r z t) x
  rw [← hcongr]
  exact hself

/-- **The identification from the named bundle.**  The same statement as
`hid_of_biotSavartInverse`, with the three geometric hypotheses on the ansatz field packaged as the
single predicate `AnsatzBundle` (`Bundle.lean`). -/
theorem hid_of_ansatzBundle (hInv : Work.LWP.BiotSavartInverse)
    (hA : 0 < A (Physical.clockInv C t)) (hB : 0 < B (Physical.clockInv C t))
    (hlaw : ∀ w θ, 0 < w → 0 < θ → θ < π / 2 →
      Work.Elliptic.bslOp (Work.FTS.Regularity.pExp α)
          (fun z θ' => Φ z θ' (Physical.clockInv C t)) w θ
        = Work.Construction.Fstar (Work.FTS.Regularity.pExp α) w θ
          + g w θ (Physical.clockInv C t))
    (hsm : ∀ w θ, 0 < w → 0 < θ → θ < π / 2 → ContDiffAt ℝ 2
      (fun p : ℝ × ℝ => Φ p.1 p.2 (Physical.clockInv C t)) (w, θ))
    (hint : Integrable (fun x : R3 => -(Physical.physOmega α A B g C x t)))
    (hb : AnsatzBundle (fun r z => merPsi α A B Φ C r z t)) :
    ∀ x ∈ Uax, Physical.physVel (-(Physical.physOmega α A B g C)) x t
      = Work.Cyl.psiField (fun r z => merPsi α A B Φ C r z t) x :=
  hid_of_biotSavartInverse hInv hA hB hlaw hsm (ansatzBundle_slice hb) (ansatzBundle_contDiff hb)
    (ansatzBundle_decay hb) hint

end Work.FTS.BSIdent
