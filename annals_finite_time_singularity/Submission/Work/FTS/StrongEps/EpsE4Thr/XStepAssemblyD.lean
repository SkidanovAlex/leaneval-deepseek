import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.StrongEps.EpsE4Thr.XStep
import Submission.Work.FTS.StrongEps.EpsE4Thr.XBallIterExists
import Submission.Work.FTS.StrongEps.EpsE4Thr.XBallLimExists
import Submission.Work.FTS.StrongEps.EpsE4Thr.VolterraLimFam
import Submission.Work.FTS.StrongEps.EpsE4Thr.RegFromVolterraD
import Submission.Work.FTS.StrongEps.EpsE4Thr.RegDataOfXBall

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `EpsE4Thr/XStepAssemblyD.lean` — `XStepInvariant` over the weaker regularity data (PROVED from
# LEAF-D + LEAF-D2)

curric-46 install 2026-10-12 (REVIEW F2).  `XStepInvariant_of_regD` is a copy of
`XStep.XStepInvariant_of_reg` (`EpsE4Thr/XStepAssembly.lean`, untouched) with
`RegFromVolterra … (RegInterface3 …)` — which over-asks `C¹` in the fake time of
`σ ↦ Feps (w_σ)` — replaced by `regFromVolterra'_of_regData … (regData_of_xball …)` (joint
continuity + continuous spatial derivative only).  The iterate/limit clauses and the Volterra
identity come from `XBallIterExists`, `XBallLimExists`, `VolterraLimFam` as before.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.E4R5

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.EpsEngine (XBall Feps)
open Work.FTS.StrongEps.EpsLocalPStar (iter limFam)

set_option autoImplicit false

/-- **The `X`-ball residual bundle from the proved iterate/limit clauses, `VolterraLimFam`, and the
weaker regularity data** (LEAF-D2 `regData_of_xball` ⟹ LEAF-D `regFromVolterra'`). -/
theorem XStepInvariant_of_regD {Ce Cs C₀ : ℝ} {ρ : ℝ × ℝ → ℝ} (hC₀ : 0 < C₀)
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) :
    XStep.XStepInvariant Ce Cs C₀ ρ := by
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
  -- and the joint `C¹` of the family from LEAF-D2 `regData_of_xball` + LEAF-D `regFromVolterra'`
  have hregfam : ContDiffOn ℝ 1
      (fun p : ℝ × ℝ × ℝ => limFam (Feps α ρ ε Φs E) h₀ p.1 p.2.1 p.2.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Icc 0 δ) :=
    regFromVolterra'_of_regData hδpos hsm hvol
      (regData_of_xball (C₀ := C₀) (Ce := Ce) (Cs := Cs) hα hρ hε.1 hε.2 hC₀ hEll hstar hml
        hδpos hRpos hsm hlim hvol)
  exact ⟨hmem₀, hsq₀, hiter, hlim, hregfam,
    fun τ hτ => ⟨(hlim τ hτ).smoothOpen, hlim6 τ hτ, (hlim τ hτ).classC⟩⟩

end Work.FTS.StrongEps.EpsE4Thr.E4R5
