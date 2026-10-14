import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.EpsE4Thr.Leaves.regFromVolterra
import Submission.Work.FTS.StrongEps.EpsE4Thr.XBallIterExists
import Submission.Work.FTS.TransportS.t2SlotGuarded
import Submission.Work.FTS_EllLimOK.BoxDataH.boxDataH_of_hasPkgH
import Submission.Work.FTS_EllLimOK.PkgJets.pinBase
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.Trace
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.contDiffOn_two_of_sliceData
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.th2EgRate
import Submission.Work.FTS_EllLimOK.ProducerH.H2.BBlockAlt
import Submission.Work.FTS_EllLimOK.ProducerH.H2.Clause1Aux
import Submission.Work.FTS_EllLimOK.ProducerH.H2.bounds_rates
import Submission.Work.FTS_EllLimOK.ProducerH.MixedJets.mixed_jets_le_Xn6
import Submission.Work.FTS_EllLimOK.ProducerH.MixedJets.pkgCos_le4
import Submission.Work.FTS_EllLimOK.ProducerH.slotBd_phiTil
import Submission.Work.FTS_EllLimOK.RulingELF
import Submission.Work.FTS_EllLimOK.SmallAssemblyH
import Submission.Work.FTS_RegExport.RXVP3.velPkgOpen_of_vopLower
import Submission.Work.Spaces.BadTermSqBound
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.XStepAssemblyWired =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `EpsE4Thr/XStepAssemblyWired.lean` — the `X`-ball residual bundle over the **delegated** leaves

This is a copy of `EpsE4Thr/XStepAssemblyD.lean`'s `XStepInvariant_of_regD` in which the two
lead-installed open leaves

* LEAF-D  `EpsE4Thr.RegFromVolterraD.regFromVolterra'`
* LEAF-D2 `EpsE4Thr.RegDataOfXBall.regData_of_xball`

are replaced by their **delegated twins** `EpsE4Thr.Leaves.regFromVolterra` /
`EpsE4Thr.Leaves.regData_of_xball` (same statements, proved in a separate namespace so that the
lead's files can keep their `sorry`s during the parallel work).  The lead's leaf files are imported
only for the *definition* `E4R5.RegDataD` (a `def`, hence `sorry`-free); none of their `sorry`-carrying
theorems is used, so the declarations below do not acquire `sorryAx`.

The purpose is to give the registered target `Work.FTS.StrongEps.EpsE4Thr` a second, direct route to
`E4R3.LocalStepChapter3` that does **not** go through LEAF-A (`EpsFlowP`) and the `E4R5` assembly:

    `XStep.localStepChapter3_of_XStepInvariant`  ⟸  `XStepInvariant_of_regDW`  (this file)
      ⟸  `XBallIterExists` + `XBallLimExists` + `VolterraLimFam`
          + `Leaves.regData_of_xball` (LEAF-D2) + `Leaves.regFromVolterra` (LEAF-D).
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.XStepWired

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.EpsEngine (XBall Feps)
open Work.FTS.StrongEps.EpsLocalPStar (iter limFam)

set_option autoImplicit false

/-- LEAF-D in bundled form, over the delegated twin: `RegDataD` gives the three hypotheses of
`EpsE4Thr.Leaves.regFromVolterra` (joint continuity of the slab integrand, per-slice `C¹` on `Q0`,
joint continuity of the spatial `fderiv`). -/
theorem regFromVolterraWired {F : Fn → Fn} {h₀ : Fn} {δ : ℝ} (hδ : 0 < δ)
    (hsm0 : Work.FTS.EllipticEst.SmoothOpen h₀)
    (hvol : ∀ z θ τ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) → τ ∈ Set.Icc 0 δ →
      limFam F h₀ z θ τ
        = h₀ z θ + ∫ s in (0 : ℝ)..τ, F (slice (limFam F h₀) s) z θ)
    (hD : Work.FTS.StrongEps.EpsE4Thr.E4R5.RegDataD F h₀ δ) :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => limFam F h₀ p.1 p.2.1 p.2.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 δ) :=
  Work.FTS.StrongEps.EpsE4Thr.Leaves.regFromVolterra hδ hsm0 hvol hD.1 hD.2.1 hD.2.2

/-- **The `X`-ball residual bundle from the proved iterate/limit clauses, `VolterraLimFam`, and the
two delegated leaves** (`Leaves.regData_of_xball` + `Leaves.regFromVolterra`). -/
theorem XStepInvariant_of_regDW {Ce Cs C₀ : ℝ} {ρ : ℝ × ℝ → ℝ} (hC₀ : 0 < C₀)
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) :
    Work.FTS.StrongEps.EpsE4Thr.XStep.XStepInvariant Ce Cs C₀ ρ := by
  intro α hα ε hε Φs E hEll hstar hml M' hM'
  -- the iterate clause (with the datum's metric clauses)
  obtain ⟨δ₀, hδ₀pos, R, hRpos, hmain⟩ :=
    XBallIterExists (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs) (M' := M') (ρ := ρ) (Φs := Φs)
      (E := E) (ε := ε) hC₀ hα hρ hε.1 hε.2 hEll hstar hml hM'
  -- the two gates at the class radius `2 C₀`
  obtain ⟨L, hLpos, hLmem, hLlip⟩ :=
    Work.FTS.StrongEps.EpsLocalPStar.EpsRHSPLipX_Sq (α := α) (C₀ := 2 * C₀) (Ce := Ce) (Cs := Cs)
      (R := R) (ρ := ρ) (Φs := Φs) (E := E) (ε := ε) hα hρ hε.1 hε.2 hEll hstar hml hRpos.le
  obtain ⟨Cpt, hCptpos, hCpt⟩ :=
    Work.FTS.StrongEps.EpsLocalPStar.profRHS_sub_sup_le_Sq (α := α) (C₀ := 2 * C₀) (Ce := Ce)
      (Cs := Cs) (R := R) (ρ := ρ) (Φs := Φs) (E := E) (ε := ε) hα hρ hε.1 hε.2 hEll hstar hml
      hRpos.le
  -- shrink the horizon so that the engine's contraction condition `δ √L < 1` holds
  set δ : ℝ := min δ₀ (1 / (1 + Real.sqrt L)) with hδdef
  have hδpos : 0 < δ := lt_min hδ₀pos (by positivity)
  have hδle : δ ≤ δ₀ := min_le_left _ _
  have hsL : 0 ≤ Real.sqrt L := Real.sqrt_nonneg L
  have hδL : δ * Real.sqrt L < 1 := by
    have hle : δ ≤ 1 / (1 + Real.sqrt L) := min_le_right _ _
    have h1 : (1 / (1 + Real.sqrt L)) * Real.sqrt L < 1 := by
      rw [div_mul_eq_mul_div, div_lt_one (by positivity)]
      linarith
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hle hsL) h1
  refine ⟨δ, hδpos, R, hRpos, fun h₀ hsm hmem hM6 hcl hball => ?_⟩
  obtain ⟨hmem₀, hsq₀, hiter₀⟩ := hmain h₀ hsm hmem hM6 hcl hball
  have hiter : ∀ n : ℕ, ∀ τ : ℝ, τ ∈ Set.Icc 0 δ →
      XBall α ρ ε R (2 * C₀) (slice (iter (Feps α ρ ε Φs E) h₀ (n + 1)) τ) :=
    fun n τ hτ => hiter₀ n τ (Set.Icc_subset_Icc le_rfl hδle hτ)
  -- the gates in the `Feps`-normalisation
  have hbd : ∀ u : Fn, XBall α ρ ε R (2 * C₀) u →
      EpsMem α (Feps α ρ ε Φs E u) ∧ EpsSq α (Feps α ρ ε Φs E u) ≤ L := by
    intro u hu
    obtain ⟨hm, hb⟩ := hLmem u hu.smoothOpen hu.mem hu.sq_le hu.classC hu.ball
    rw [← Work.FTS.EpsEngine.Feps_eq_epsRHPSlice α ρ ε Φs E 0 u] at hm hb
    exact ⟨hm, hb⟩
  have hlip : ∀ u v : Fn, XBall α ρ ε R (2 * C₀) u → XBall α ρ ε R (2 * C₀) v →
      EpsMem α (fun z θ => u z θ - v z θ) →
      EpsSq α (fun z θ => Feps α ρ ε Φs E u z θ - Feps α ρ ε Φs E v z θ)
        ≤ L * EpsSq α (fun z θ => u z θ - v z θ) := by
    intro u v hu hv huv
    have h := hLlip u v hu.smoothOpen hv.smoothOpen hu.mem hu.sq_le hu.classC hu.ball
      hv.mem hv.sq_le hv.classC hv.ball huv
    rwa [← Work.FTS.EpsEngine.Feps_eq_epsRHPSlice α ρ ε Φs E 0 u,
      ← Work.FTS.EpsEngine.Feps_eq_epsRHPSlice α ρ ε Φs E 0 v] at h
  have hpt : ∀ u v : Fn, XBall α ρ ε R (2 * C₀) u → XBall α ρ ε R (2 * C₀) v →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Feps α ρ ε Φs E u z θ - Feps α ρ ε Φs E v z θ|
          ≤ Cpt * Real.sqrt (EpsSq α (fun z θ => u z θ - v z θ)) := by
    intro u v hu hv z θ hz hθ0 hθ2
    have h := hCpt hu.smoothOpen hv.smoothOpen hu.mem hu.sq_le hv.mem hv.sq_le hu.classC hv.classC
      hu.ball hv.ball z θ hz hθ0 hθ2
    rwa [← Work.FTS.EpsEngine.Feps_eq_epsRHPSlice α ρ ε Φs E 0 u,
      ← Work.FTS.EpsEngine.Feps_eq_epsRHPSlice α ρ ε Φs E 0 v] at h
  -- the limit clause and the limit slice's `ℋ⁶`-honesty
  obtain ⟨hlim, hlim6⟩ :=
    XBallLimExists (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs) (M' := M') (Cpt := Cpt) (L := L)
      (δ := δ) (R := R) (ρ := ρ) (Φs := Φs) (E := E) (ε := ε) (h₀ := h₀)
      hC₀ hα hρ hε.1 hε.2 hEll hstar hml hM' hLpos hδpos hδL hRpos hbd hlip hCptpos.le hpt
      hsm hmem hM6 hcl hball hmem₀ hsq₀ hiter
  -- the Volterra identity of the limit family (from the engine's data at this `δ`)
  have hvol := VolterraLimFam (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs) (M' := M') (Cpt := Cpt)
    (L := L) (δ := δ) (R := R) (ρ := ρ) (Φs := Φs) (E := E) (ε := ε) (h₀ := h₀)
    hC₀ hα hρ hε.1 hε.2 hEll hstar hml hM' hLpos hδpos hδL hRpos hbd hlip hCptpos.le hpt
    hsm hmem hM6 hcl hball hmem₀ hsq₀ hiter
  -- and the joint `C¹` of the family from LEAF-D2 (over the `τ`-Lipschitz bundle, `RegDataWired`)
  -- + LEAF-D `regFromVolterra`
  have hregfam : ContDiffOn ℝ 1
      (fun p : ℝ × ℝ × ℝ => limFam (Feps α ρ ε Φs E) h₀ p.1 p.2.1 p.2.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Icc 0 δ) :=
    regFromVolterraWired hδpos hsm hvol
      (Work.FTS.StrongEps.EpsE4Thr.RegDataWired.regData_of_xball_wired (C₀ := C₀) (Ce := Ce)
        (Cs := Cs) (M' := M') (Cpt := Cpt) (L := L) (δ := δ) (R := R) (ρ := ρ) (Φs := Φs)
        (E := E) (ε := ε) (h₀ := h₀)
        hC₀ hα hρ hε.1 hε.2 hEll hstar hml hM' hLpos hδpos hδL hRpos hbd hlip hCptpos.le hpt
        hsm hmem hM6 hcl hball hmem₀ hsq₀ hiter hlim hvol)
  exact ⟨hmem₀, hsq₀, hiter, hlim, hregfam,
    fun τ hτ => ⟨(hlim τ hτ).smoothOpen, hlim6 τ hτ, (hlim τ hτ).classC⟩⟩



end Work.FTS.StrongEps.EpsE4Thr.XStepWired
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ProducerH.H2.clause1 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.ProducerH.H2

theorem clause1 {α Ce : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hE : Work.FTS_EllLimOK.ProducerH.H2.Ctx α Ce E) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hdata : Work.FTS_EllLimOK.ProducerH.H2.BoxData α Ce E a b) :
    ∀ g : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α g →
      ContDiffOn ℝ 2 (Function.uncurry (E g)) (Work.FTS_EllLimOK.cbox a b) := by
  intro g hg
  -- the box data, unpacked once: the angular rate bound, the pointwise/rate bounds of the
  -- radial derivatives, the angular limits and the two-point Hölder modulus
  have hdata' : BoxData α Ce E a b := hdata
  obtain ⟨K, hK, β, hβ, hmodw, hrates, hlimw, hhol⟩ := hdata'
  obtain ⟨CL, hCL, hlimb⟩ := hlimw
  obtain ⟨L0, N0, L1, N1, hLim⟩ := hlimb g hg
  have hLimAt : LimitsAt (E g) (Work.FTS.StrongGlobal.Xn6 α g) CL a b L0 N0 L1 N1 := hLim
  -- the three blocks of slice data
  have hP := PsiBlock hα hα4 hE ha hab hdata g hg hLimAt
  have hQ := ABlock hα hα4 hE ha hab hdata g hg hLimAt
  have hR := BBlockAlt hα hα4 hE ha hab hdata g hg hLimAt
  -- the assembly: the seven functions `Ψ, A, B, A₁, A₂, B₁, B₂` with their within-slice
  -- derivatives, whence the closed-box `C²`-regularity
  exact Work.FTS_EllLimOK.ProducerH.BoxAux.contDiffOn_two_of_sliceData (le_of_lt hab)
    hP.1 hQ.1 hR.1 hQ.2.1 hR.2.1 hR.2.1 hR.2.2.1
    hP.2.1 hP.2.2 hQ.2.2.1 hQ.2.2.2 hR.2.2.2.1 hR.2.2.2.2

end Work.FTS_EllLimOK.ProducerH.H2
end
