/-
# `Work.FTS.BSIdentP.hid_of_pointwise'` — route C with the corrected package `RegPkg'`

Port of `Work.FTS.BSIdent.hid_of_pointwise` (the assembly of route C: Weyl applied to the
difference `physVel (−physOmega) − v`, with the weak divergence and curl equations reduced to
pointwise identities off the two coordinate planes) to the corrected regularity package
`Work.FTS.RegPkgGal.RegPkg'`.

The only mathematical input that changes is the analytic half of the `physVel` side: the four
quantitative data of the negated vorticity slice now come from the `FireFix.Prime` vorticity
lemmas, i.e. from `Work.FTS.BSIdentP.physVel_neg_physOmega_slice'`.  The rest of the proof is the
original one; the ancillary lemmas of `BSIdent.hid_of_pointwise`
(`isOpen_Uax`, `mem_Uax_of_coord`, `div_sub_field`, `crossR3_sub_right`, `vorticity_sub_field`)
and `BSIdent.hid_of_weyl` are imported rather than restated.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Trace
import Submission.Work.FTS.BSIdent.hid_of_pointwise
import Submission.Work.FTS_BSIdentP.RegPkgPrime.PhysVelNegSlice

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set MeasureTheory
open scoped Topology Real NNReal

namespace Work.FTS.BSIdentP

open Work.FTS.BSIdent

set_option autoImplicit false

section

variable {α : ℝ≥0} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ} {C : Physical.PhysClock}
  {Φ : Work.FTS.BSIdent.Fam} {v : ℝ → Work.FTS.BSIdent.R3 → Work.FTS.BSIdent.R3}

/-- **THE IDENTIFICATION BY ROUTE C, FOR THE CORRECTED PACKAGE `RegPkg'`.**  Let `v t` be a field
that agrees with the ansatz field `Cyl.psiField (merPsi … · t)` on `Uax`, is continuous and tends
to `0` at infinity.  Then, for every `t ∈ (0,T)`, the reconstructed physical velocity
`physVel (−physOmega α A B g C) · t` coincides with the ansatz field on `Uax`.

The remaining hypotheses are the elliptic law `hlaw` (which makes the curl of the ansatz field
equal to `−physOmega`) and the off-axis `C²`-regularity `hΨ` of the meridian stream function. -/
theorem hid_of_pointwise'
    (hreg : ∀ S : ℝ, 0 < S → Work.FTS.RegPkgGal.RegPkg' (α : ℝ) S A B g)
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
    (hvdec : ∀ t ∈ Set.Ioo 0 C.T, Filter.Tendsto (v t) (Filter.cocompact Work.FTS.BSIdent.R3)
      (nhds 0)) :
    ∀ t ∈ Set.Ioo 0 C.T, ∀ x ∈ Uax,
      Physical.physVel (-(Physical.physOmega (α : ℝ) A B g C)) x t
        = Work.Cyl.psiField (fun r z => merPsi (α : ℝ) A B Φ C r z t) x := by
  intro t ht
  -- ## the clock data, from `RegPkg'` on the strip `[0, clockInv C t + 1]`
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
  -- ## the `physVel` side, from the `RegPkg'` vorticity data
  obtain ⟨hC1U, hvortU, hdivU, hdecU⟩ :=
    Work.FTS.BSIdentP.physVel_neg_physOmega_slice' hP hτmem
  -- ## the difference
  let W : Work.FTS.BSIdent.R3 → Work.FTS.BSIdent.R3 :=
    fun x => Physical.physVel (-(Physical.physOmega (α : ℝ) A B g C)) x t
  have hWHD : ∀ x : Work.FTS.BSIdent.R3, HasFDerivAt W (fderiv ℝ W x) x :=
    fun x => ((hC1U.differentiable (by norm_num)) x).hasFDerivAt
  -- the ansatz field and its `C¹`-regularity off the axis
  have hψC1 : ∀ x ∈ Uax, ContDiffAt ℝ 1
      (Work.Cyl.psiField (fun r z => merPsi (α : ℝ) A B Φ C r z t)) x :=
    fun x hx => Defs.contDiffAt_psiField_merPsi_of_mem_Uax (α : ℝ) A B Φ C t hB hsm hx
  -- the `v`-side is `C¹` off the two planes
  have hVHD : ∀ x : Work.FTS.BSIdent.R3, x 0 ≠ 0 → x 2 ≠ 0 →
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
  have hDdiff : ∀ x : Work.FTS.BSIdent.R3, x 0 ≠ 0 → x 2 ≠ 0 →
      HasFDerivAt (fun y => W y - v t y) (fderiv ℝ (fun y => W y - v t y) x) x := by
    intro x hx0 hx2
    have h : fderiv ℝ (fun y => W y - v t y) x = fderiv ℝ W x - fderiv ℝ (v t) x :=
      (hWHD x).sub (hVHD x hx0 hx2) |>.fderiv
    rw [h]
    exact (hWHD x).sub (hVHD x hx0 hx2)
  have hdiv0 : ∀ x : Work.FTS.BSIdent.R3, x 0 ≠ 0 → x 2 ≠ 0 →
      div (fun y => W y - v t y) x = 0 := by
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
  have hcurl0 : ∀ x : Work.FTS.BSIdent.R3, x 0 ≠ 0 → x 2 ≠ 0 →
      vorticity (fun y => W y - v t y) x = 0 := by
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
  have hdecD : Filter.Tendsto (fun y => W y - v t y) (Filter.cocompact Work.FTS.BSIdent.R3)
      (nhds 0) := by
    have h := hdecU.sub (hvdec t ht)
    simpa using h
  refine hid_of_weyl (v := v t) (t := t) Work.FTS.BSIdent.Weyl.weylPairPrinciple (hv t ht)
    (hC1U.continuous.sub (hvcont t ht)) hdecD ?_ ?_
  · intro φ hφ hφcs
    exact Work.FTS.BSIdent.Weyl.weakGrad_zero_of_pointwise_div (D := fun y => W y - v t y)
      (hC1U.continuous.sub (hvcont t ht)) hDdiff hdiv0 (hφ 1) hφcs
  · intro Ψ hΨ' hΨcs
    exact Work.FTS.BSIdent.Weyl.weakCurl_zero_of_pointwise_curl (D := fun y => W y - v t y)
      (hC1U.continuous.sub (hvcont t ht)) hDdiff hcurl0 hΨ' hΨcs

end

end Work.FTS.BSIdentP
