/-
# `Work.FTS.BSIdent.Liouville.Hid` — the identification by div-curl Liouville (route B)

The lead's alternative for audit §5 item 4 (`FTS_PHYS_BRIDGE.md` §5):
"or by Liouville on the difference of the fields".

On `Uax` both `physVel (−physOmega α A B g C)` and `psiField (merPsi α A B Φ C · · t)` are
(`Curl.lean`) fields with the *same vorticity* `−physOmega …`, hence their difference is a
divergence-free curl-free field.  The classical Liouville input
`Work.FTS.Physical.DivCurlLiouville` (node N8's `Defs.lean`) makes two such fields equal as soon as
both have sublinear growth and their difference is odd.

Compared with route A (`Ident.hid_of_biotSavartInverse`) this replaces the *decay* `1/‖x‖` of the
ansatz field by mere *sublinearity* (weaker, and what `sublinear_axiField` supplies in the
axis-regular model case), at the price of needing:

* the **forward** Biot–Savart law at the reconstructed (swirl, compactly supported) vorticity —
  `hBS`, design item 3 (`BiotSavartSwirl`); note that the *false* `Work.LWP.BiotSavartLaw` is
  **not** used;
* the `C¹`-smoothness and sublinearity of *both* fields (`hC1u`, `hC1v`, `hsubu`, `hsubv`), and
  the divergence-freeness of the reconstructed velocity (`hdivu`, from the same Biot–Savart law);
* the oddness of `Φ` at `θ = 0` (`hodd0`, a `VanishTheta` conjunct of `RegPkg`), which makes
  `merPsi` odd in the meridian axial coordinate and hence the ansatz field odd.

The equality of the two curls *everywhere* (not merely on `Uax`) is derived here from the pointwise
identity on `Uax` together with the continuity of the two curl fields
(`Liouville.continuous_vorticity_of_contDiff`) and the density of `Uax` (`Defs.dense_Uax`).
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.FTS.BSIdent.Ident
import Submission.Work.FTS.BSIdent.Defs.dense_Uax
import Submission.Work.FTS.BSIdent.Parity.isOdd_sub
import Submission.Work.FTS.BSIdent.Liouville.continuous_vorticity_of_contDiff
import Submission.Work.FTS.Physical.Liouville

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

variable {α : ℝ} {A B : ℝ → ℝ} {Φ : Fam} {C : Physical.PhysClock} {g : ℝ → ℝ → ℝ → ℝ} {t : ℝ}

/-- **THE IDENTIFICATION, Liouville route.**  Under the elliptic data (`hA`, `hB`, `hlaw`, `hsm`),
the forward Biot–Savart law at the reconstructed swirl vorticity (`hBS`), the two `C¹`/sublinearity
bundles (`hC1u`, `hsubu`, `hC1v`, `hsubv`), the divergence-freeness of the reconstructed velocity
(`hdivu`) and the oddness of `Φ` at `θ = 0` (`hodd0`), the identification holds on `Uax`. -/
theorem hid_of_divCurlLiouville (hLiou : Physical.DivCurlLiouville)
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
    (hBS : ∀ x : R3, vorticity (fun y => Physical.physVel (-(Physical.physOmega α A B g C)) y t) x
      = -(Physical.physOmega α A B g C x t))
    (hC1v : ContDiff ℝ 1 (Work.Cyl.psiField (fun r z => merPsi α A B Φ C r z t)))
    (hC1u : ContDiff ℝ 1 (fun y => Physical.physVel (-(Physical.physOmega α A B g C)) y t))
    (hsubv : Physical.Sublinear (Work.Cyl.psiField (fun r z => merPsi α A B Φ C r z t)))
    (hsubu : Physical.Sublinear (fun y => Physical.physVel (-(Physical.physOmega α A B g C)) y t))
    (hdivu : FiniteTimeSingularity.div
      (fun y => Physical.physVel (-(Physical.physOmega α A B g C)) y t) = 0)
    (hoddU : IsOdd (fun y => Physical.physVel (-(Physical.physOmega α A B g C)) y t))
    (hodd0 : ∀ z τ, Φ z 0 τ = 0) :
    ∀ x ∈ Uax, Physical.physVel (-(Physical.physOmega α A B g C)) x t
      = Work.Cyl.psiField (fun r z => merPsi α A B Φ C r z t) x := by
  have hdiv : FiniteTimeSingularity.div
      (Work.Cyl.psiField (fun r z => merPsi α A B Φ C r z t)) = 0 :=
    Cyl.div_psiField_merPsi α A B Φ C t hC1v hsm2
  -- the two curls agree on all of `ℝ³`: they agree on the dense set `Uax` and are continuous
  have hcurl : ∀ y : R3,
      vorticity (fun z => Physical.physVel (-(Physical.physOmega α A B g C)) z t) y
        = vorticity (Work.Cyl.psiField (fun r z => merPsi α A B Φ C r z t)) y := by
    have heq : Set.EqOn
        (vorticity (fun y => Physical.physVel (-(Physical.physOmega α A B g C)) y t))
        (vorticity (Work.Cyl.psiField (fun r z => merPsi α A B Φ C r z t))) Uax := by
      intro y hy
      rw [hBS y, vorticity_psiField_merPsi_apply (g := g) hA hB hlaw hsm hy]
    have hcont := Continuous.ext_on Defs.dense_Uax
      (Liouville.continuous_vorticity_of_contDiff hC1u)
      (Liouville.continuous_vorticity_of_contDiff hC1v) heq
    exact fun y => congrFun hcont y
  have hodd : IsOdd (fun y => Physical.physVel (-(Physical.physOmega α A B g C)) y t
      - Work.Cyl.psiField (fun r z => merPsi α A B Φ C r z t) y) :=
    Parity.isOdd_sub hoddU (isOdd_psiField_merPsi α A B Φ C t hodd0)
  intro x _
  exact congrFun (Physical.eq_of_curl_eq hLiou hC1u hC1v hdivu hdiv hcurl hsubu hsubv hodd) x

end Work.FTS.BSIdent
