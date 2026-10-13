/-
# `Work.FTS.BSIdent.hid_of_pointwise` — route C of the identification (design §5 item 4)

The lead's route C (`FTS_HARD_DESIGN.md` §(C), message of 2026-10-08 01:30) for the identification
`hid` of `blowupAtTop_of_regPkg'` reverses the field `D := physVel (−physOmega) − v` and applies the
Weyl/Liouville principle with `q := 0`:

  `D` continuous, `D → 0` at infinity, `div D = 0` and `curl D = 0` in the sense of distributions
  ⟹ (Weyl) `D = ∇0 = 0` ⟹ `physVel (−physOmega) = v` on `Uax`.

It needs neither `Work.LWP.BiotSavartInverse` nor `Physical.DivCurlLiouville`, and — crucially — no
`C¹`-regularity of the ansatz field at the axis (which is *false* for the Lean field
`Cyl.psiField`, see `Weyl/Corrected.lean`).

This module assembles route C.  Everything except the geometric bundle of the corrected field `v`
is proved here from `RegPkg`:

* the Weyl principle is `Work.FTS.BSIdent.Weyl.weylPairPrinciple`, discharged from
  `Work.FTS.PressureOn.weyl_pair`;
* the two weak equations of `D` are reduced to *pointwise* identities off the two coordinate
  planes `x₀ = 0`, `x₂ = 0` (a Lebesgue-null set) by
  `Work.FTS.BSIdent.Weyl.weakGrad_zero_of_pointwise_div` and
  `Work.FTS.BSIdent.Weyl.weakCurl_zero_of_pointwise_curl`;
* the pointwise identities for `D` are those of its two summands, both proved elsewhere:
  * `physVel (−physOmega)`: `Work.FTS.BSIdent.Weyl.physVel_neg_physOmega_slice` (curl `= −physOmega`,
    divergence `= 0`, `C¹`, decay) — the Biot–Savart inversion for the compactly supported Hölder
    swirl field `−physVort`;
  * the ansatz field `v`: on `Uax` it coincides with `Cyl.psiField (merPsi … · t)`, whose curl is
    `−physOmega` by the elliptic law (`Work.FTS.BSIdent.vorticity_psiField_merPsi`) and whose
    divergence vanishes (`Work.Cyl.div_psiField`).

The **only** genuinely analytic hypothesis is the geometric bundle of `v`: continuity, decay and
the agreement with `Cyl.psiField (merPsi … · t)` on `Uax`.  For the canonical choice
`v t := psiFieldCorr (merPsi … · t) L` this bundle is the content of
`Work.FTS.BSIdent.Weyl.merPsi_corrected_bundle`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Trace
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.FTS.BSIdent.Weyl
import Submission.Work.FTS.BSIdent.Weyl.weylPairPrinciple
import Submission.Work.FTS.BSIdent.Weyl.weakGrad_zero_of_pointwise_div
import Submission.Work.FTS.BSIdent.Weyl.weakCurl_zero_of_pointwise_curl
import Submission.Work.FTS.BSIdent.Weyl.physVel_neg_physOmega_slice
import Submission.Work.FTS.BSIdent.Curl
import Submission.Work.FTS.BSIdent.Defs.contDiffAt_Phi_of_merPsi
import Submission.Work.FTS.BSIdent.Defs.contDiffAt_psiField_merPsi_of_mem_Uax
import Submission.Work.Cyl.div_psiField
import Submission.Work.FTS.BSSwirl.CrossAux

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

/-- `Uax` is open (it is the complement of the two coordinate hyperplanes `x₃ = 0` and `r = 0`). -/
theorem isOpen_Uax : IsOpen Uax := by
  have h1 : IsOpen {x : R3 | x 2 ≠ 0} :=
    (isOpen_ne (x := (0 : ℝ))).preimage (by fun_prop)
  have h2 : IsOpen {x : R3 | x 0 ^ 2 + x 1 ^ 2 ≠ 0} :=
    (isOpen_ne (x := (0 : ℝ))).preimage (by fun_prop)
  have hU : Uax = {x : R3 | x 2 ≠ 0} ∩ {x : R3 | x 0 ^ 2 + x 1 ^ 2 ≠ 0} := by
    ext x; simp [Uax]
  rw [hU]; exact h1.inter h2

/-- Every point with `x₀ ≠ 0` and `x₂ ≠ 0` lies in `Uax`. -/
theorem mem_Uax_of_coord (x : R3) (h0 : x 0 ≠ 0) (h2 : x 2 ≠ 0) : x ∈ Uax :=
  ⟨h2, by nlinarith [sq_pos_of_ne_zero h0]⟩

/-- `div` is additive in the field, at points where both summands are differentiable. -/
theorem div_sub_field (f g : R3 → R3) {x : R3} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    div (fun y => f y - g y) x = div f x - div g x := by
  have h : fderiv ℝ (fun y => f y - g y) x = fderiv ℝ f x - fderiv ℝ g x :=
    (hf.hasFDerivAt.sub hg.hasFDerivAt).fderiv
  unfold FiniteTimeSingularity.div
  rw [h]
  exact map_sub (LinearMap.trace ℝ R3) _ _

/-- The cross product is additive in its right argument. -/
theorem crossR3_sub_right (a b c : R3) :
    BSSwirl.crossR3 a (b - c) = BSSwirl.crossR3 a b - BSSwirl.crossR3 a c := by
  have : BSSwirl.crossR3 a (b - c) + BSSwirl.crossR3 a c = BSSwirl.crossR3 a b := by
    rw [← BSSwirl.crossR3_add_right, sub_add_cancel]
  exact eq_sub_of_add_eq this

/-- `vorticity` is additive in the field, at points where both summands are differentiable. -/
theorem vorticity_sub_field (f g : R3 → R3) {x : R3} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    vorticity (fun y => f y - g y) x = vorticity f x - vorticity g x := by
  have h : fderiv ℝ (fun y => f y - g y) x = fderiv ℝ f x - fderiv ℝ g x :=
    (hf.hasFDerivAt.sub hg.hasFDerivAt).fderiv
  rw [BSSwirl.vorticity_eq_sum_crossR3, BSSwirl.vorticity_eq_sum_crossR3,
    BSSwirl.vorticity_eq_sum_crossR3, h, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by
    rw [ContinuousLinearMap.sub_apply, crossR3_sub_right]

section

variable {α : ℝ≥0} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ} {C : Physical.PhysClock} {Φ : Fam}
  {v : ℝ → R3 → R3}

/-- **The route-C geometric bundle of the ansatz field.**  A field `v` with a meridian stream
function `ψ` is *Weyl-admissible* for `ψ` if it is continuous, tends to `0` at infinity and agrees
with `Cyl.psiField ψ` on `Uax`.  These are exactly the three hypotheses of `hid_of_pointwise` on the
field; for `v = psiFieldCorr ψ L` they are produced by `Weyl.merPsi_corrected_bundle` +
`psiFieldCorr_eq_psiField_of_mem_Uax`. -/
def AnsatzBundleWeyl (v : R3 → R3) (ψ : ℝ → ℝ → ℝ) : Prop :=
  Continuous v ∧ (∀ x ∈ Uax, v x = Work.Cyl.psiField ψ x) ∧
    Filter.Tendsto v (Filter.cocompact R3) (nhds 0)

/-- **THE IDENTIFICATION BY ROUTE C.**  Let `v t` be a field that agrees with the ansatz field
`Cyl.psiField (merPsi … · t)` on `Uax`, is continuous and tends to `0` at infinity.  Then, for every
`t ∈ (0,T)`, the reconstructed physical velocity `physVel (−physOmega α A B g C) · t` coincides
with the ansatz field on `Uax`.

The remaining hypotheses are the elliptic law `hlaw` (which makes the curl of the ansatz field equal
to `−physOmega`) and the off-axis `C²`-regularity `hΨ` of the meridian stream function. -/
theorem hid_of_pointwise
    (hreg : ∀ S : ℝ, 0 < S → Work.FTS.Regularity.RegPkg (α : ℝ) S A B g)
    (hlaw : ∀ t ∈ Set.Ioo 0 C.T, ∀ w θ, 0 < w → 0 < θ → θ < π / 2 →
      Work.Elliptic.bslOp (Work.FTS.Regularity.pExp (α : ℝ))
          (fun z θ' => Φ z θ' (Physical.clockInv C t)) w θ
        = Work.Construction.Fstar (Work.FTS.Regularity.pExp (α : ℝ)) w θ
          + g w θ (Physical.clockInv C t))
    (hΨ : ∀ t ∈ Set.Ioo 0 C.T, ∀ r z, 0 < r → z ≠ 0 → ContDiffAt ℝ 2
      (fun p : ℝ × ℝ => merPsi (α : ℝ) A B Φ C p.1 p.2 t) (r, z))
    (hv : ∀ t ∈ Set.Ioo 0 C.T, ∀ x ∈ Uax, v t x
      = Work.Cyl.psiField (fun r z => merPsi (α : ℝ) A B Φ C r z t) x)
    (hvcont : ∀ t ∈ Set.Ioo 0 C.T, Continuous (v t))
    (hvdec : ∀ t ∈ Set.Ioo 0 C.T, Filter.Tendsto (v t) (Filter.cocompact R3) (nhds 0)) :
    ∀ t ∈ Set.Ioo 0 C.T, ∀ x ∈ Uax,
      Physical.physVel (-(Physical.physOmega (α : ℝ) A B g C)) x t
        = Work.Cyl.psiField (fun r z => merPsi (α : ℝ) A B Φ C r z t) x := by
  intro t ht
  -- ## the clock data, from `RegPkg` on the strip `[0, clockInv C t + 1]`
  have htIco : t ∈ Set.Ico (0 : ℝ) C.T := ⟨ht.1.le, ht.2⟩
  have hτnn : 0 ≤ Physical.clockInv C t := Physical.clockInv_nonneg C htIco
  have hτmem : Physical.clockInv C t ∈ Set.Icc (0 : ℝ) (Physical.clockInv C t + 1) :=
    ⟨hτnn, by linarith⟩
  have hP := hreg (Physical.clockInv C t + 1) (by linarith)
  have hA : 0 < A (Physical.clockInv C t) := hP.hA _ hτmem
  have hB : 0 < B (Physical.clockInv C t) := hP.hB _ hτmem
  have hα : 0 < (α : ℝ) := hP.hα
  -- the interior `C²`-regularity of `Φ` (needed for the curl identity of the ansatz field)
  have hsm : ∀ w θ, 0 < w → 0 < θ → θ < π / 2 → ContDiffAt ℝ 2
      (fun p : ℝ × ℝ => Φ p.1 p.2 (Physical.clockInv C t)) (w, θ) :=
    fun w θ hw hθ hθ2 =>
      Defs.contDiffAt_Phi_of_merPsi (α : ℝ) A B Φ C t hα (ne_of_gt hA) hB (hΨ t ht) hw hθ hθ2
  -- ## the `physVel` side
  obtain ⟨hC1U, hvortU, hdivU, hdecU⟩ := Weyl.physVel_neg_physOmega_slice hP hτmem
  -- ## the difference
  let W : R3 → R3 := fun x => Physical.physVel (-(Physical.physOmega (α : ℝ) A B g C)) x t
  have hWHD : ∀ x : R3, HasFDerivAt W (fderiv ℝ W x) x :=
    fun x => ((hC1U.differentiable (by norm_num)) x).hasFDerivAt
  -- the ansatz field and its `C¹`-regularity off the axis
  have hψC1 : ∀ x ∈ Uax, ContDiffAt ℝ 1
      (Work.Cyl.psiField (fun r z => merPsi (α : ℝ) A B Φ C r z t)) x :=
    fun x hx => Defs.contDiffAt_psiField_merPsi_of_mem_Uax (α : ℝ) A B Φ C t hB hsm hx
  -- the `v`-side is `C¹` off the two planes
  have hVHD : ∀ x : R3, x 0 ≠ 0 → x 2 ≠ 0 →
      HasFDerivAt (v t)
        (fderiv ℝ (v t) x) x := by
    intro x hx0 hx2
    have hxU : x ∈ Uax := mem_Uax_of_coord x hx0 hx2
    have hψ : HasFDerivAt (Work.Cyl.psiField (fun r z => merPsi (α : ℝ) A B Φ C r z t))
        (fderiv ℝ (Work.Cyl.psiField (fun r z => merPsi (α : ℝ) A B Φ C r z t)) x) x :=
      ((hψC1 x hxU).differentiableAt (by norm_num)).hasFDerivAt
    have hveq : v t =ᶠ[𝓝 x]
        (Work.Cyl.psiField (fun r z => merPsi (α : ℝ) A B Φ C r z t)) := by
      filter_upwards [isOpen_Uax.mem_nhds hxU] with y hy
      exact hv t ht y hy
    have h1 : HasFDerivAt (v t)
        (fderiv ℝ (Work.Cyl.psiField (fun r z => merPsi (α : ℝ) A B Φ C r z t)) x) x :=
      hψ.congr_of_eventuallyEq hveq
    rwa [← hveq.fderiv_eq] at h1
  -- the derivative of the fact that `v t = psiField` near every point of `Uax`
  have hfderiv_eq : ∀ x ∈ Uax, fderiv ℝ (v t) x
      = fderiv ℝ (Work.Cyl.psiField (fun r z => merPsi (α : ℝ) A B Φ C r z t)) x := by
    intro x hxU
    have hveq : v t =ᶠ[𝓝 x]
        (Work.Cyl.psiField (fun r z => merPsi (α : ℝ) A B Φ C r z t)) := by
      filter_upwards [isOpen_Uax.mem_nhds hxU] with y hy
      exact hv t ht y hy
    exact hveq.fderiv_eq
  -- ## the two pointwise identities for `D = W − v t` off the planes
  have hDdiff : ∀ x : R3, x 0 ≠ 0 → x 2 ≠ 0 →
      HasFDerivAt (fun y => W y - v t y) (fderiv ℝ (fun y => W y - v t y) x) x := by
    intro x hx0 hx2
    have h : fderiv ℝ (fun y => W y - v t y) x = fderiv ℝ W x - fderiv ℝ (v t) x :=
      (hWHD x).sub (hVHD x hx0 hx2) |>.fderiv
    rw [h]
    exact (hWHD x).sub (hVHD x hx0 hx2)
  have hdiv0 : ∀ x : R3, x 0 ≠ 0 → x 2 ≠ 0 → div (fun y => W y - v t y) x = 0 := by
    intro x hx0 hx2
    have hxU : x ∈ Uax := mem_Uax_of_coord x hx0 hx2
    have hr : 0 < Work.Cyl.radial x := by
      rw [Work.Cyl.radial, Work.Cyl.radSq]
      exact Real.sqrt_pos.mpr (by nlinarith [sq_pos_of_ne_zero hx0])
    have hz : Work.Cyl.axial x ≠ 0 := by simpa [Work.Cyl.axial] using hx2
    have hC2 := hΨ t ht (Work.Cyl.radial x) (Work.Cyl.axial x) hr hz
    have hdv : div (v t) x
        = div (Work.Cyl.psiField (fun r z => merPsi (α : ℝ) A B Φ C r z t)) x := by
      rw [FiniteTimeSingularity.div, FiniteTimeSingularity.div, hfderiv_eq x hxU]
    rw [div_sub_field W (v t) (hWHD x).differentiableAt (hVHD x hx0 hx2).differentiableAt,
      hdivU x, hdv,
      Work.Cyl.div_psiField (fun r z => merPsi (α : ℝ) A B Φ C r z t) x hC2 hr]
    ring
  have hcurl0 : ∀ x : R3, x 0 ≠ 0 → x 2 ≠ 0 → vorticity (fun y => W y - v t y) x = 0 := by
    intro x hx0 hx2
    have hxU : x ∈ Uax := mem_Uax_of_coord x hx0 hx2
    have hWv : vorticity W x = -(Physical.physOmega (α : ℝ) A B g C x t) := hvortU x
    have hVv : vorticity (v t) x = -(Physical.physOmega (α : ℝ) A B g C x t) := by
      have hvt : vorticity (v t) x
          = vorticity (Work.Cyl.psiField (fun r z => merPsi (α : ℝ) A B Φ C r z t)) x := by
        rw [FiniteTimeSingularity.vorticity, FiniteTimeSingularity.vorticity, hfderiv_eq x hxU]
      rw [hvt, vorticity_psiField_merPsi (α : ℝ) A B Φ C g t hA hB (hlaw t ht) hsm hxU,
        vorticity_psiField_merPsi_eq_neg_physOmega (α : ℝ) A B C g t]
    rw [vorticity_sub_field W (v t) (hWHD x).differentiableAt (hVHD x hx0 hx2).differentiableAt,
      hWv, hVv, sub_self]
  -- ## Weyl on the difference
  have hdecD : Filter.Tendsto (fun y => W y - v t y) (Filter.cocompact R3) (nhds 0) := by
    have h := hdecU.sub (hvdec t ht)
    simpa using h
  refine hid_of_weyl (v := v t) (t := t) Weyl.weylPairPrinciple (hv t ht)
    (hC1U.continuous.sub (hvcont t ht)) hdecD ?_ ?_
  · intro φ hφ hφcs
    exact Weyl.weakGrad_zero_of_pointwise_div (D := fun y => W y - v t y)
      (hC1U.continuous.sub (hvcont t ht)) hDdiff hdiv0 (hφ 1) hφcs
  · intro Ψ hΨ' hΨcs
    exact Weyl.weakCurl_zero_of_pointwise_curl (D := fun y => W y - v t y)
      (hC1U.continuous.sub (hvcont t ht)) hDdiff hcurl0 hΨ' hΨcs

/-- **THE IDENTIFICATION BY ROUTE C, in bundle form.**  The same statement as `hid_of_pointwise`,
with the three hypotheses on the field `v` collected in `AnsatzBundleWeyl`. -/
theorem hid_of_ansatzBundleWeyl
    (hreg : ∀ S : ℝ, 0 < S → Work.FTS.Regularity.RegPkg (α : ℝ) S A B g)
    (hlaw : ∀ t ∈ Set.Ioo 0 C.T, ∀ w θ, 0 < w → 0 < θ → θ < π / 2 →
      Work.Elliptic.bslOp (Work.FTS.Regularity.pExp (α : ℝ))
          (fun z θ' => Φ z θ' (Physical.clockInv C t)) w θ
        = Work.Construction.Fstar (Work.FTS.Regularity.pExp (α : ℝ)) w θ
          + g w θ (Physical.clockInv C t))
    (hΨ : ∀ t ∈ Set.Ioo 0 C.T, ∀ r z, 0 < r → z ≠ 0 → ContDiffAt ℝ 2
      (fun p : ℝ × ℝ => merPsi (α : ℝ) A B Φ C p.1 p.2 t) (r, z))
    (hbun : ∀ t ∈ Set.Ioo 0 C.T, AnsatzBundleWeyl (v t)
      (fun r z => merPsi (α : ℝ) A B Φ C r z t)) :
    ∀ t ∈ Set.Ioo 0 C.T, ∀ x ∈ Uax,
      Physical.physVel (-(Physical.physOmega (α : ℝ) A B g C)) x t
        = Work.Cyl.psiField (fun r z => merPsi (α : ℝ) A B Φ C r z t) x :=
  hid_of_pointwise hreg hlaw hΨ (fun t ht => (hbun t ht).2.1)
    (fun t ht => (hbun t ht).1) (fun t ht => (hbun t ht).2.2)

/-- **THE IDENTIFICATION BY ROUTE C, from the `IsBslSol` interface.**  The same as
`hid_of_pointwise` with the elliptic law in the paper's (PolarBSL) form, exactly as node
N1/Open2 delivers it. -/
theorem hid_of_pointwise_of_IsBslSol
    (hreg : ∀ S : ℝ, 0 < S → Work.FTS.Regularity.RegPkg (α : ℝ) S A B g)
    (hsol : ∀ t ∈ Set.Ioo 0 C.T, Work.Elliptic.IsBslSol (Work.FTS.Regularity.pExp (α : ℝ))
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp (α : ℝ)) g (Physical.clockInv C t))
      (fun z θ => Φ z θ (Physical.clockInv C t)))
    (hΨ : ∀ t ∈ Set.Ioo 0 C.T, ∀ r z, 0 < r → z ≠ 0 → ContDiffAt ℝ 2
      (fun p : ℝ × ℝ => merPsi (α : ℝ) A B Φ C p.1 p.2 t) (r, z))
    (hv : ∀ t ∈ Set.Ioo 0 C.T, ∀ x ∈ Uax, v t x
      = Work.Cyl.psiField (fun r z => merPsi (α : ℝ) A B Φ C r z t) x)
    (hvcont : ∀ t ∈ Set.Ioo 0 C.T, Continuous (v t))
    (hvdec : ∀ t ∈ Set.Ioo 0 C.T, Filter.Tendsto (v t) (Filter.cocompact R3) (nhds 0)) :
    ∀ t ∈ Set.Ioo 0 C.T, ∀ x ∈ Uax,
      Physical.physVel (-(Physical.physOmega (α : ℝ) A B g C)) x t
        = Work.Cyl.psiField (fun r z => merPsi (α : ℝ) A B Φ C r z t) x :=
  hid_of_pointwise hreg
    (fun t ht w θ hw hθ hθ2 => (hsol t ht).1 w hw θ hθ hθ2) hΨ hv hvcont hvdec

end

end Work.FTS.BSIdent
