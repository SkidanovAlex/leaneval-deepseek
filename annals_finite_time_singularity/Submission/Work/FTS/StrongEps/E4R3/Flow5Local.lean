import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.E4R3.Flow5
import Submission.Work.FTS.StrongEps.E4R3.Flow5Leaves.FlowOfXBall
import Submission.Work.FTS.StrongEps.EpsE4Thr.XStep

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `E4R3/Flow5Local.lean` — the flow-carrying local step (PROVED from LEAF-A + `XStepInvariant`)

curric-46 install 2026-10-12 (`cbc/fts_regularity_interface.lean` §6).  `localStepPF_of_XStepInvariant`
and `localStepChapter5_of_XStepInvariant` are copies of `XStep.localStepP_of_XStepInvariant` /
`localStepChapter3_of_XStepInvariant` whose solution also carries `EpsFlowP` (via LEAF-A
`epsFlowP_of_xball`, `E4R3/Flow5Leaves/FlowOfXBall.lean`).
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.E4R5

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.StrongGlobal (Xn6 concat)
open Work.FTS.VocabO (HQo)
open Work.FTS.StrongEps
open Work.FTS.StrongEps.EpsE4Thr
open Work.FTS.StrongEps.EpsE4Thr.E4R4 (rawE6 IP6o)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The flow-carrying local step from the `X`-ball residual bundle** (PROVED from LEAF-A; the
copy of `XStep.localStepP_of_XStepInvariant`, which already has the limit slices in
`XBall α ρ ε R (2 C₀)`). -/
theorem localStepPF_of_XStepInvariant {α C₀ Ce Cs : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {ε : ℝ} (hα : α ∈ Ioc 0 1) (hρ : IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : MuLamOK α (2 * C₀) Φs E) (hC₀ : 0 ≤ C₀)
    (hX : XStep.XStepInvariant Ce Cs C₀ ρ) :
    LocalStepPF α ρ ε Φs E C₀ := by
  intro M' hM'
  obtain ⟨δ, hδpos, R, hRpos, hdat⟩ := hX α hα ε ⟨hε, hε1⟩ hEll hstar hml (M' ^ 2) (sq_nonneg M')
  obtain ⟨L, hLpos, hLmem, hLlip⟩ :=
    Work.FTS.StrongEps.EpsLocalPStar.EpsRHSPLipX_Sq (α := α) (C₀ := 2 * C₀) (Ce := Ce) (Cs := Cs)
      (R := R) (ρ := ρ) (Φs := Φs) (E := E) (ε := ε) hα hρ hε hε1 hEll hstar hml hRpos.le
  obtain ⟨Cpt, hCptpos, hCpt⟩ :=
    Work.FTS.StrongEps.EpsLocalPStar.profRHS_sub_sup_le_Sq (α := α) (C₀ := 2 * C₀) (Ce := Ce)
      (Cs := Cs) (R := R) (ρ := ρ) (Φs := Φs) (E := E) (ε := ε) hα hρ hε hε1 hEll hstar hml
      hRpos.le
  have hCpt0 : 0 ≤ Cpt := hCptpos.le
  set δ' : ℝ := min δ (1 / (1 + Real.sqrt L)) with hδ'def
  have hden : 0 < 1 + Real.sqrt L := by positivity
  have hδ'pos : 0 < δ' := lt_min hδpos (by positivity)
  have hδ'le : δ' ≤ δ := min_le_left _ _
  have hsL : 0 ≤ Real.sqrt L := Real.sqrt_nonneg L
  have hδ'L : δ' * Real.sqrt L < 1 := by
    have hle : δ' ≤ 1 / (1 + Real.sqrt L) := min_le_right _ _
    have h1 : (1 / (1 + Real.sqrt L)) * Real.sqrt L < 1 := by
      rw [div_mul_eq_mul_div, div_lt_one hden]
      linarith
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hle hsL) h1
  have hIcc : Icc (0 : ℝ) δ' ⊆ Icc (0 : ℝ) δ := Icc_subset_Icc le_rfl hδ'le
  refine ⟨δ', hδ'pos, ?_⟩
  intro h₀ hd hball h6
  have hsm : Work.FTS.EllipticEst.SmoothOpen h₀ := hd.1
  have hmem6 : Work.Spaces.HkMem α 6 h₀ := hd.2.1
  have hcl : Work.FTS.ClassC.ClassC α (Pz (Jeps ρ ε h₀)) := hd.2.2
  have hXn : Work.FTS.Nonlin.Xn α (Pz (Jeps ρ ε h₀)) ≤ C₀ * α ^ 2 := hball
  have hM6 : Work.Spaces.HkSq α 6 h₀ ≤ M' ^ 2 := by
    have h1 : Xn6 α h₀ ≤ M' := h6
    have h2 : Real.sqrt (Work.Spaces.HkSq α 6 h₀) ≤ M' := h1
    have h3 : Real.sqrt (Work.Spaces.HkSq α 6 h₀) ^ 2 ≤ M' ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) h2 2
    rwa [Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 h₀)] at h3
  obtain ⟨hmem₀, hsq₀, hkeep, hlim, hreg, hdP⟩ := hdat h₀ hsm hmem6 hM6 hcl hXn
  have hα2 : 0 ≤ α ^ 2 := sq_nonneg α
  have hP₀ : Work.FTS.EpsEngine.XBall α ρ ε R (2 * C₀) h₀ :=
    ⟨hsm, hmem₀, hsq₀, hcl, le_trans hXn (mul_le_mul_of_nonneg_right (by linarith) hα2)⟩
  have hbd : ∀ u : Fn, Work.FTS.EpsEngine.XBall α ρ ε R (2 * C₀) u →
      EpsMem α (Work.FTS.EpsEngine.Feps α ρ ε Φs E u) ∧
        EpsSq α (Work.FTS.EpsEngine.Feps α ρ ε Φs E u) ≤ L := by
    intro u hu
    obtain ⟨hm, hb⟩ := hLmem u hu.smoothOpen hu.mem hu.sq_le hu.classC hu.ball
    rw [← Work.FTS.EpsEngine.Feps_eq_epsRHPSlice α ρ ε Φs E 0 u] at hm hb
    exact ⟨hm, hb⟩
  have hlip : ∀ u v : Fn, Work.FTS.EpsEngine.XBall α ρ ε R (2 * C₀) u →
      Work.FTS.EpsEngine.XBall α ρ ε R (2 * C₀) v →
      EpsMem α (fun z θ => u z θ - v z θ) →
      EpsSq α (fun z θ => Work.FTS.EpsEngine.Feps α ρ ε Φs E u z θ
          - Work.FTS.EpsEngine.Feps α ρ ε Φs E v z θ)
        ≤ L * EpsSq α (fun z θ => u z θ - v z θ) := by
    intro u v hu hv huv
    have h := hLlip u v hu.smoothOpen hv.smoothOpen hu.mem hu.sq_le hu.classC hu.ball
      hv.mem hv.sq_le hv.classC hv.ball huv
    rwa [← Work.FTS.EpsEngine.Feps_eq_epsRHPSlice α ρ ε Φs E 0 u,
      ← Work.FTS.EpsEngine.Feps_eq_epsRHPSlice α ρ ε Φs E 0 v] at h
  have hpt : ∀ u v : Fn, Work.FTS.EpsEngine.XBall α ρ ε R (2 * C₀) u →
      Work.FTS.EpsEngine.XBall α ρ ε R (2 * C₀) v →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.FTS.EpsEngine.Feps α ρ ε Φs E u z θ - Work.FTS.EpsEngine.Feps α ρ ε Φs E v z θ|
          ≤ Cpt * Real.sqrt (EpsSq α (fun z θ => u z θ - v z θ)) := by
    intro u v hu hv z θ hz hθ0 hθ2
    have h := hCpt hu.smoothOpen hv.smoothOpen hu.mem hu.sq_le hv.mem hv.sq_le hu.classC hv.classC
      hu.ball hv.ball z θ hz hθ0 hθ2
    rwa [← Work.FTS.EpsEngine.Feps_eq_epsRHPSlice α ρ ε Φs E 0 u,
      ← Work.FTS.EpsEngine.Feps_eq_epsRHPSlice α ρ ε Φs E 0 v] at h
  obtain ⟨hsolL, hregL⟩ :
      IsEpsSolP α ρ ε δ' Φs E h₀ (Work.FTS.StrongEps.EpsLocalPStar.limFam
          (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀) ∧
        EpsRegP α ρ ε δ' (Work.FTS.StrongEps.EpsLocalPStar.limFam
          (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀) := by
    obtain ⟨h0, hder⟩ :=
      Work.FTS.EpsEngine.exists_volterra_v4 (α := α) (F := Work.FTS.EpsEngine.Feps α ρ ε Φs E)
        (h₀ := h₀) (P := fun u => Work.FTS.EpsEngine.XBall α ρ ε R (2 * C₀) u)
        (Cpt := Cpt) (L := L) (δ := δ') hδ'pos hLpos hδ'L hCpt0 hP₀ hbd hlip hpt
        (fun u hu => (Work.FTS.EpsEngine.continuousOn_Feps_of_XBall (Ce := Ce) (Cs := Cs)
          hα hρ hε hEll hstar hu).1)
        (fun u hu => (Work.FTS.EpsEngine.continuousOn_Feps_of_XBall (Ce := Ce) (Cs := Cs)
          hα hρ hε hEll hstar hu).2)
        (fun n τ hτ => hkeep n τ (hIcc hτ)) (fun τ hτ => hlim τ (hIcc hτ))
    exact ⟨Work.FTS.EpsEngine.IsEpsSolP_of_v4 h0 hder,
      hreg.mono fun p hp => ⟨hp.1, hp.2.1, hIcc hp.2.2⟩, fun τ hτ => hdP τ (hIcc hτ)⟩
  exact ⟨_, hsolL, hregL, epsFlowP_of_xball (C₁ := 2 * C₀) (Ce := Ce) (Cs := Cs) hα hρ hε hε1
    hRpos.le hEll hstar hml hδ'pos hsolL hregL (fun τ hτ => hlim τ (hIcc hτ))⟩

/-- **The flow-carrying local-step chapter from the `X`-ball residual bundle** (PROVED; copy of
`XStep.localStepChapter3_of_XStepInvariant`). -/
theorem localStepChapter5_of_XStepInvariant {Ce Cs : ℝ} {ρ : ℝ × ℝ → ℝ}
    (hρ : IsSmoothKernel ρ)
    (hX : ∀ C₀ : ℝ, 2 ≤ C₀ → ∃ α₀ : ℝ, 0 < α₀ ∧ α₀ ≤ 1 ∧
      ∀ α ∈ Ioc 0 α₀, XStep.XStepInvariant Ce Cs C₀ ρ) :
    ∃ C : ℝ, ∀ C₀ : ℝ, C ≤ C₀ → LocalStepChapter5 Ce Cs C₀ ρ := by
  refine ⟨2, fun C₀ hC₀ => ?_⟩
  have hC₀0 : 0 ≤ C₀ := le_trans (by norm_num) hC₀
  obtain ⟨α₀, hα₀0, hα₀1, hres⟩ := hX C₀ hC₀
  obtain ⟨α₁, hα₁0, hml'⟩ :=
    MuLamOK_of_hEll_hstar (Ce := Ce) (Cs := Cs) (K := 2 * C₀) (by linarith)
  refine ⟨min α₀ α₁, lt_min hα₀0 hα₁0, le_trans (min_le_left _ _) hα₀1, ?_⟩
  intro α hα K Φs E g₀ hdata ε hε
  have hα0 : α ∈ Ioc 0 α₀ := ⟨hα.1, le_trans hα.2 (min_le_left _ _)⟩
  have hα1 : α ∈ Ioc 0 α₁ := ⟨hα.1, le_trans hα.2 (min_le_right _ _)⟩
  have hαIoc : α ∈ Ioc 0 1 := ⟨hα.1, le_trans hα.2 (le_trans (min_le_left _ _) hα₀1)⟩
  have hEll := hdata.2.2.1
  have hstar := hdata.2.2.2.1
  have hml : MuLamOK α (2 * C₀) Φs E := hml' α hα1 hEll hstar
  exact localStepPF_of_XStepInvariant hαIoc hρ hε.1 hε.2 hEll hstar hml hC₀0 (hres α hα0)

end Work.FTS.StrongEps.EpsE4Thr.E4R5
