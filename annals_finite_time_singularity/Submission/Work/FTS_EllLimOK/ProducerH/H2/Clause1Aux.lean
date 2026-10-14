import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_EllLimOK.ProducerH.H2.Slice
import Submission.Work.FTS_EllLimOK.ProducerH.MixedJets.pkgCos_le4
import Submission.Work.FTS_EllLimOK.ProducerH.slotBd_phiTil
import Submission.Work.FTS_EllLimOK.RulingELF
import Submission.Work.FTS_RegExport.RXVP3.velPkgOpen_of_vopLower
import Submission.Work.FTS_StreamBdry.Inputs.residual_slot_jetsB
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Flow5Local =====
section

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
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ProducerH.H2.Assembly =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.ProducerH

open scoped Real Topology
open MeasureTheory Set Filter

open Work.FTS.Galerkin (Fn)

/-- **The assembly of `PkgBoxH` from the box data and the three clauses.**

The three clauses of `RulingELF.PkgBoxH` are taken as hypotheses (they are produced by the H2
chapter from the endpooint data `H2.BoxData`); the content of this lemma is the box quantifier
bookkeeping: the non-degenerate box `a < b` is handled by the clauses, while the degenerate box
`a = b = {a} × [0,π/2]` carries only the `ContDiffOn` clause, which is obtained by monotonicity
from the non-degenerate box `cbox a (a+1) ⊇ cbox a a`. -/
theorem pkgBoxH_of_data {α Ce : ℝ} {E : Fn →ₗ[ℝ] Fn}
    (hboxdata : ∀ a b : ℝ, 0 < a → a ≤ b → H2.BoxData α Ce E a b)
    (hclause1 : ∀ a b : ℝ, 0 < a → a < b → H2.BoxData α Ce E a b →
      ∀ g : Fn, Work.FTS.ClassC.ClassC α g →
        ContDiffOn ℝ 2 (Function.uncurry (E g)) (Work.FTS_EllLimOK.cbox a b))
    (hclause2 : ∀ a b : ℝ, 0 < a → a < b → H2.BoxData α Ce E a b →
      (∀ g : Fn, Work.FTS.ClassC.ClassC α g →
        ContDiffOn ℝ 2 (Function.uncurry (E g)) (Work.FTS_EllLimOK.cbox a b)) →
      ∃ K : ℝ, 0 < K ∧ ∀ g : Fn, Work.FTS.ClassC.ClassC α g →
        ∀ k : ℕ, k ≤ 2 → ∀ p ∈ Work.FTS_EllLimOK.cbox a b,
          ‖iteratedFDerivWithin ℝ k (Function.uncurry (E g))
            (Work.FTS_EllLimOK.cbox a b) p‖
            ≤ K * Work.FTS.StrongGlobal.Xn6 α g)
    (hclause3 : ∀ a b : ℝ, 0 < a → a < b → H2.BoxData α Ce E a b →
      (∀ g : Fn, Work.FTS.ClassC.ClassC α g →
        ContDiffOn ℝ 2 (Function.uncurry (E g)) (Work.FTS_EllLimOK.cbox a b)) →
      ∃ K : ℝ, 0 < K ∧ ∃ β : ℝ, 0 < β ∧ ∀ g : Fn, Work.FTS.ClassC.ClassC α g →
        ∀ p ∈ Work.FTS_EllLimOK.cbox a b, ∀ q ∈ Work.FTS_EllLimOK.cbox a b,
          ‖iteratedFDerivWithin ℝ 2 (Function.uncurry (E g))
              (Work.FTS_EllLimOK.cbox a b) p
            - iteratedFDerivWithin ℝ 2 (Function.uncurry (E g))
              (Work.FTS_EllLimOK.cbox a b) q‖
            ≤ K * Work.FTS.StrongGlobal.Xn6 α g * ‖p - q‖ ^ β) :
    Work.FTS_EllLimOK.RulingELF.PkgBoxH α E := by
  intro a b ha hab
  by_cases hab' : a < b
  · -- ## the non-degenerate box: the three clauses
    obtain ⟨hdata, hc1, hc2, hc3⟩ :
        H2.BoxData α Ce E a b ∧
        (∀ g : Fn, Work.FTS.ClassC.ClassC α g →
          ContDiffOn ℝ 2 (Function.uncurry (E g)) (Work.FTS_EllLimOK.cbox a b)) ∧
        (∃ K : ℝ, 0 < K ∧ ∀ g : Fn, Work.FTS.ClassC.ClassC α g →
          ∀ k : ℕ, k ≤ 2 → ∀ p ∈ Work.FTS_EllLimOK.cbox a b,
            ‖iteratedFDerivWithin ℝ k (Function.uncurry (E g))
              (Work.FTS_EllLimOK.cbox a b) p‖
              ≤ K * Work.FTS.StrongGlobal.Xn6 α g) ∧
        (∃ K : ℝ, 0 < K ∧ ∃ β : ℝ, 0 < β ∧ ∀ g : Fn, Work.FTS.ClassC.ClassC α g →
          ∀ p ∈ Work.FTS_EllLimOK.cbox a b, ∀ q ∈ Work.FTS_EllLimOK.cbox a b,
            ‖iteratedFDerivWithin ℝ 2 (Function.uncurry (E g))
                (Work.FTS_EllLimOK.cbox a b) p
              - iteratedFDerivWithin ℝ 2 (Function.uncurry (E g))
                (Work.FTS_EllLimOK.cbox a b) q‖
              ≤ K * Work.FTS.StrongGlobal.Xn6 α g * ‖p - q‖ ^ β) :=
      ⟨hboxdata a b ha hab, hclause1 a b ha hab' (hboxdata a b ha hab),
        hclause2 a b ha hab' (hboxdata a b ha hab)
          (hclause1 a b ha hab' (hboxdata a b ha hab)),
        hclause3 a b ha hab' (hboxdata a b ha hab)
          (hclause1 a b ha hab' (hboxdata a b ha hab))⟩
    obtain ⟨K₂, hK₂, hc2'⟩ := hc2
    obtain ⟨K₃, hK₃, β₃, hβ₃, hc3'⟩ := hc3
    refine ⟨max K₂ K₃ + 1, β₃, by positivity, hβ₃, ?_⟩
    intro g hg
    refine ⟨hc1 g hg, fun _ => ?_, fun _ => ?_⟩
    · intro k hk p hp
      have h := hc2' g hg k hk p hp
      have hX : (0 : ℝ) ≤ Work.FTS.StrongGlobal.Xn6 α g := H2.Xn6_nonneg α g
      calc ‖iteratedFDerivWithin ℝ k (Function.uncurry (E g))
            (Work.FTS_EllLimOK.cbox a b) p‖
          ≤ K₂ * Work.FTS.StrongGlobal.Xn6 α g := h
        _ ≤ (max K₂ K₃ + 1) * Work.FTS.StrongGlobal.Xn6 α g :=
            mul_le_mul_of_nonneg_right (by linarith [le_max_left K₂ K₃]) hX
    · intro p hp q hq
      have h := hc3' g hg p hp q hq
      have hX : (0 : ℝ) ≤ Work.FTS.StrongGlobal.Xn6 α g := H2.Xn6_nonneg α g
      have hr : (0 : ℝ) ≤ ‖p - q‖ ^ β₃ := Real.rpow_nonneg (norm_nonneg _) _
      calc ‖iteratedFDerivWithin ℝ 2 (Function.uncurry (E g))
              (Work.FTS_EllLimOK.cbox a b) p
            - iteratedFDerivWithin ℝ 2 (Function.uncurry (E g))
              (Work.FTS_EllLimOK.cbox a b) q‖
          ≤ K₃ * Work.FTS.StrongGlobal.Xn6 α g * ‖p - q‖ ^ β₃ := h
        _ ≤ (max K₂ K₃ + 1) * Work.FTS.StrongGlobal.Xn6 α g * ‖p - q‖ ^ β₃ :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (by linarith [le_max_right K₂ K₃]) hX) hr
  · -- ## the degenerate box `a = b`: only the first clause is asked for, and the box sits
    -- inside the non-degenerate box `cbox a (a+1)`
    have hba : b = a := le_antisymm (not_lt.mp hab') hab
    rw [hba]
    have hdata : H2.BoxData α Ce E a (a + 1) := hboxdata a (a + 1) ha (by linarith)
    have hc1 : ∀ g : Fn, Work.FTS.ClassC.ClassC α g →
        ContDiffOn ℝ 2 (Function.uncurry (E g)) (Work.FTS_EllLimOK.cbox a (a + 1)) :=
      hclause1 a (a + 1) ha (by linarith) hdata
    refine ⟨1, 1, one_pos, one_pos, ?_⟩
    intro g hg
    refine ⟨?_, ?_, ?_⟩
    · exact (hc1 g hg).mono (fun p hp => by
        rw [Work.FTS_EllLimOK.mem_cbox] at hp ⊢
        exact ⟨⟨hp.1.1, by linarith [hp.1.2]⟩, hp.2⟩)
    · intro hcon
      exact absurd hcon (by linarith)
    · intro hcon
      exact absurd hcon (by linarith)

end Work.FTS_EllLimOK.ProducerH
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ProducerH.H2.Clause1Aux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.ProducerH.H2

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## The boundary-corrected slope functions -/

/-- The boundary-corrected θ-slope: `∂_θΨ` in the open strip and the one-sided limits at the
two angular endpoints. -/
def Bf (L0 L1 : ℝ → ℝ) (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => if θ = 0 then L0 z else if θ = π / 2 then L1 z else Work.Spaces.pth Ψ z θ

/-- The boundary-corrected mixed slope `∂_θ∂_zΨ`, with the one-sided limits at the two angular
endpoints. -/
def Mf (N0 N1 : ℝ → ℝ) (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ =>
    if θ = 0 then N0 z else if θ = π / 2 then N1 z else Work.Spaces.pth (Work.Spaces.pz Ψ) z θ

/-- The boundary-corrected `∂_θ²Ψ`, vanishing at both angular endpoints. -/
def B2f (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => if θ = 0 then 0 else if θ = π / 2 then 0 else Work.Spaces.pth (Work.Spaces.pth Ψ) z θ

@[simp] theorem Bf_zero (L0 L1 : ℝ → ℝ) (Ψ : ℝ → ℝ → ℝ) (z : ℝ) :
    Bf L0 L1 Ψ z 0 = L0 z := by
  simp [Bf]

theorem Bf_pi (L0 L1 : ℝ → ℝ) (Ψ : ℝ → ℝ → ℝ) (z : ℝ) :
    Bf L0 L1 Ψ z (π / 2) = L1 z := by
  have h0 : ¬ ((π : ℝ) / 2 = 0) := ne_of_gt (by positivity)
  simp [Bf, h0]

theorem Bf_of_mem_Ioo {L0 L1 : ℝ → ℝ} {Ψ : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) : Bf L0 L1 Ψ z θ = Work.Spaces.pth Ψ z θ := by
  have h0 : ¬ (θ = 0) := ne_of_gt hθ.1
  have h1 : ¬ (θ = (π : ℝ) / 2) := ne_of_lt hθ.2
  simp only [Bf, if_neg h0, if_neg h1]

@[simp] theorem Mf_zero (N0 N1 : ℝ → ℝ) (Ψ : ℝ → ℝ → ℝ) (z : ℝ) :
    Mf N0 N1 Ψ z 0 = N0 z := by
  simp [Mf]

theorem Mf_pi (N0 N1 : ℝ → ℝ) (Ψ : ℝ → ℝ → ℝ) (z : ℝ) :
    Mf N0 N1 Ψ z (π / 2) = N1 z := by
  have h0 : ¬ ((π : ℝ) / 2 = 0) := ne_of_gt (by positivity)
  simp [Mf, h0]

theorem Mf_of_mem_Ioo {N0 N1 : ℝ → ℝ} {Ψ : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Mf N0 N1 Ψ z θ = Work.Spaces.pth (Work.Spaces.pz Ψ) z θ := by
  have h0 : ¬ (θ = 0) := ne_of_gt hθ.1
  have h1 : ¬ (θ = (π : ℝ) / 2) := ne_of_lt hθ.2
  simp only [Mf, if_neg h0, if_neg h1]

@[simp] theorem B2f_zero (Ψ : ℝ → ℝ → ℝ) (z : ℝ) : B2f Ψ z 0 = 0 := by
  simp [B2f]

theorem B2f_pi (Ψ : ℝ → ℝ → ℝ) (z : ℝ) : B2f Ψ z (π / 2) = 0 := by
  have h0 : ¬ ((π : ℝ) / 2 = 0) := ne_of_gt (by positivity)
  simp [B2f, h0]

theorem B2f_of_mem_Ioo {Ψ : ℝ → ℝ → ℝ} {z θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    B2f Ψ z θ = Work.Spaces.pth (Work.Spaces.pth Ψ) z θ := by
  have h0 : ¬ (θ = 0) := ne_of_gt hθ.1
  have h1 : ¬ (θ = (π : ℝ) / 2) := ne_of_lt hθ.2
  simp only [B2f, if_neg h0, if_neg h1]

/-! ## The frozen `Limits` data -/

/-- The `Limits` data of `Data.lean` with the witnesses and the rate constant frozen: the two
one-sided angular limits of `∂_θΨ` and of `∂_z∂_θΨ`, their linear rates, continuity in `z` and
the identification of the `z`-derivative of the limit. -/
def LimitsAt (Ψ : ℝ → ℝ → ℝ) (X C a b : ℝ) (L0 N0 L1 N1 : ℝ → ℝ) : Prop :=
  (∀ z ∈ Set.Icc a b, Filter.Tendsto (fun θ => Work.Spaces.pth Ψ z θ)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (L0 z))) ∧
  (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Spaces.pth Ψ z θ - L0 z| ≤ C * X * θ) ∧
  (∀ z ∈ Set.Icc a b, Filter.Tendsto (fun θ => Work.Spaces.pz (Work.Spaces.pth Ψ) z θ)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (N0 z))) ∧
  (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Spaces.pz (Work.Spaces.pth Ψ) z θ - N0 z| ≤ C * X * θ) ∧
  (∀ z ∈ Set.Icc a b, Filter.Tendsto (fun θ => Work.Spaces.pth Ψ z θ)
      (nhdsWithin (π / 2) (Set.Iio (π / 2))) (nhds (L1 z))) ∧
  (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Spaces.pth Ψ z θ - L1 z| ≤ C * X * (π / 2 - θ)) ∧
  (∀ z ∈ Set.Icc a b, Filter.Tendsto (fun θ => Work.Spaces.pz (Work.Spaces.pth Ψ) z θ)
      (nhdsWithin (π / 2) (Set.Iio (π / 2))) (nhds (N1 z))) ∧
  (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Spaces.pz (Work.Spaces.pth Ψ) z θ - N1 z| ≤ C * X * (π / 2 - θ)) ∧
  ContinuousOn L0 (Set.Icc a b) ∧ ContinuousOn N0 (Set.Icc a b) ∧
  ContinuousOn L1 (Set.Icc a b) ∧ ContinuousOn N1 (Set.Icc a b) ∧
  (∀ z ∈ Set.Icc a b, HasDerivWithinAt L0 (N0 z) (Set.Icc a b) z) ∧
  (∀ z ∈ Set.Icc a b, HasDerivWithinAt L1 (N1 z) (Set.Icc a b) z)


/-! ## Generic one-variable analysis lemmas -/









/-- **Right-continuity on `[0,T]` from the right limit and the value at `0`.** -/
theorem continuousWithinAt_Icc_left {f : ℝ → ℝ} {T L : ℝ} (hT : 0 < T)
    (h : Filter.Tendsto f (nhdsWithin 0 (Set.Ioi 0)) (nhds L)) (h0 : f 0 = L) :
    ContinuousWithinAt f (Set.Icc 0 T) 0 := by
  rw [ContinuousWithinAt, h0, Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := (Metric.tendsto_nhdsWithin_nhds.mp h) ε hε
  refine ⟨δ, hδ, fun x hx hxd => ?_⟩
  rcases eq_or_lt_of_le hx.1 with hx0 | hx0
  · subst hx0
    rw [h0]
    simpa using hε
  · exact hδ' hx0 hxd

/-- **Left-continuity on `[0,T]` from the left limit and the value at `T`.** -/
theorem continuousWithinAt_Icc_right {f : ℝ → ℝ} {T L : ℝ} (hT : 0 < T)
    (h : Filter.Tendsto f (nhdsWithin T (Set.Iio T)) (nhds L)) (hT' : f T = L) :
    ContinuousWithinAt f (Set.Icc 0 T) T := by
  rw [ContinuousWithinAt, hT', Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := (Metric.tendsto_nhdsWithin_nhds.mp h) ε hε
  refine ⟨δ, hδ, fun x hx hxd => ?_⟩
  rcases eq_or_lt_of_le hx.2 with hx0 | hx0
  · subst hx0
    rw [hT']
    simpa using hε
  · exact hδ' hx0 hxd

/-- **Within-derivative at the left endpoint from the one-sided limit of the derivative.** -/
theorem hasDerivWithinAt_Icc_left {f f' : ℝ → ℝ} {T L : ℝ} (hT : 0 < T)
    (hcont : ContinuousOn f (Set.Icc 0 T))
    (hd : ∀ x ∈ Set.Ioo 0 T, HasDerivAt f (f' x) x)
    (hL : Filter.Tendsto f' (nhdsWithin 0 (Set.Ioi 0)) (nhds L)) :
    HasDerivWithinAt f L (Set.Icc 0 T) 0 := by
  have hdiff : DifferentiableOn ℝ f (Set.Ioo 0 T) :=
    fun x hx => (hd x hx).differentiableAt.differentiableWithinAt
  have hcont0 : ContinuousWithinAt f (Set.Ioo 0 T) 0 :=
    (hcont.continuousWithinAt (Set.left_mem_Icc.mpr hT.le)).mono Set.Ioo_subset_Icc_self
  have hmem : Set.Ioo 0 T ∈ nhdsWithin 0 (Set.Ioi 0) := Ioo_mem_nhdsGT hT
  have hd' : Filter.Tendsto (fun x => deriv f x) (nhdsWithin 0 (Set.Ioi 0)) (nhds L) :=
    hL.congr' (Filter.eventually_of_mem hmem fun x hx => (hd x hx).deriv.symm)
  exact (hasDerivWithinAt_Ici_of_tendsto_deriv hdiff hcont0 hmem hd').mono
    (fun x hx => hx.1)

/-- **Within-derivative at the right endpoint from the one-sided limit of the derivative.** -/
theorem hasDerivWithinAt_Icc_right {f f' : ℝ → ℝ} {T L : ℝ} (hT : 0 < T)
    (hcont : ContinuousOn f (Set.Icc 0 T))
    (hd : ∀ x ∈ Set.Ioo 0 T, HasDerivAt f (f' x) x)
    (hL : Filter.Tendsto f' (nhdsWithin T (Set.Iio T)) (nhds L)) :
    HasDerivWithinAt f L (Set.Icc 0 T) T := by
  have hdiff : DifferentiableOn ℝ f (Set.Ioo 0 T) :=
    fun x hx => (hd x hx).differentiableAt.differentiableWithinAt
  have hcontT : ContinuousWithinAt f (Set.Ioo 0 T) T :=
    (hcont.continuousWithinAt (Set.right_mem_Icc.mpr hT.le)).mono Set.Ioo_subset_Icc_self
  have hmem : Set.Ioo 0 T ∈ nhdsWithin T (Set.Iio T) := Ioo_mem_nhdsLT hT
  have hd' : Filter.Tendsto (fun x => deriv f x) (nhdsWithin T (Set.Iio T)) (nhds L) :=
    hL.congr' (Filter.eventually_of_mem hmem fun x hx => (hd x hx).deriv.symm)
  exact (hasDerivWithinAt_Iic_of_tendsto_deriv hdiff hcontT hmem hd').mono
    (fun x hx => hx.2)

/-- **Continuity of an angular slice on the closed interval** from continuity on the open
interval and the two traces (the general form, not requiring a `SmoothOpen` ambient function). -/
theorem continuousOn_thetaSlice_of_interior {f : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hint : ∀ θ ∈ Set.Ioo 0 T, ContinuousAt f θ)
    (h0 : Filter.Tendsto f (nhdsWithin 0 (Set.Ioi 0)) (nhds (f 0)))
    (hT' : Filter.Tendsto f (nhdsWithin T (Set.Iio T)) (nhds (f T))) :
    ContinuousOn f (Set.Icc 0 T) := by
  intro θ hθ
  rcases eq_or_lt_of_le hθ.1 with h | h
  · subst h
    exact continuousWithinAt_Icc_left hT h0 rfl
  rcases eq_or_lt_of_le hθ.2 with hp | hp
  · subst hp
    exact continuousWithinAt_Icc_right hT hT' rfl
  · exact (hint θ ⟨h, hp⟩).continuousWithinAt




end Work.FTS_EllLimOK.ProducerH.H2
end
end
