import Mathlib
import Submission.Work.Drive.psgFamilyDefs
import Submission.Work.Drive.exists_forall_good_and_notMem_family_multi
import Submission.Work.Drive.exists_forall_good_face_and_notMem_family
import Submission.Work.Drive.famMeet_regular_of_good_family
import Submission.Work.Drive.exists_compact_chart_cover
import Submission.Work.Drive.exists_pos_norm_le_mem_of_compact
import Submission.Work.Drive.chartDiffRangeBridge
import Submission.Work.Drive.sgPiecesDefs
import Submission.Work.Drive.germHavoidLoop
import Submission.Work.Drive.psgValDefs
import Submission.Work.Drive.sgAssembly
import Submission.Work.Drive.goodFaceMulti
import Submission.Work.Drive.contDiff_bump_of_isCompact_subset_isOpen
import Submission.Work.Drive.cornerSub_finrank
import Submission.Work.Drive.cornerPt_data
import Submission.Work.Drive.exists_pos_norm_subset_of_isCompact_subset_isOpen
import Submission.Work.Drive.exists_kernel_ne_zero_of_face_surjective
import Submission.Work.Drive.psg_fam_smoothness
import Submission.Work.Drive.sgSweepDefs
import Submission.Work.Drive.sgSystem

/-- Shortcut instance (Lean v4.34 port): on v4.34 Mathlib the generic search for
`ContinuousSMul ℝ E` on real normed spaces such as `EuclideanSpace ℝ (Fin n)` or products of them
detours through `PolynormableSpace.continuousSMul` and exhausts the synthesis budget. -/
private local instance (priority := high) normedSpace_continuousSMul_real_v434 {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] : ContinuousSMul ℝ E :=
  IsBoundedSMul.continuousSMul



namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

set_option maxHeartbeats 32000000
set_option backward.isDefEq.respectTransparency false

noncomputable section

/-- The differentiability order `⊤` is not zero. -/
private lemma ctop_ne_zero_psg : Ctop ≠ 0 := by
  rw [ne_eq, ← WithTop.coe_zero]
  intro h
  exact ENat.top_ne_zero (WithTop.coe_injective h)

/-! ## The value maps of the path family: smoothness and the charted parameter derivative

These four lemmas are the analytic inputs of the Sard construction below; they are proved here
(they are short corollaries of `psg_fam_smoothness`, `ChartPert` and `ChartBridge`). -/

open Work.Drive in
/-- **The loop value is jointly `C^∞`** in the chart shift and the box point. -/
lemma psgLoopVal_contMDiff {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (hΞ : ChartPert Q m Ξ) (hQ : IsChartData Q) :
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × Amb 4)) (𝓡 4) Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => psgLoopVal Ξ Q A B q.1 q.2) := by
  have hQsm : ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) Ctop Q := hQ.1
  have hexp : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × Amb 4)) (𝓘(ℝ, ℂ)) Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => psgLoopPt q.2) := by
    have hlin : ContDiff ℝ Ctop
        (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 =>
          (Real.pi : ℂ) * ((q.2 1 : ℝ) : ℂ) * Complex.I) := by
      have h1 : ContDiff ℝ Ctop
          (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => ((q.2 1 : ℝ) : ℂ)) :=
        Complex.ofRealCLM.contDiff.comp
          ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 5 => ℝ) 1).contDiff.comp
            (contDiff_snd (𝕜 := ℝ) (n := Ctop)))
      exact (contDiff_const.mul h1).mul contDiff_const
    exact Complex.contDiff_exp.contMDiff.comp (contMDiff_iff_contDiff.mpr hlin)
  have hpath : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × Amb 4)) (𝓡 m) Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => psgPathL A B (q.2 0) + q.1) := by
    rw [contMDiff_iff_contDiff]
    exact ((contDiff_psgPathL A B).comp
        ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 5 => ℝ) 0).contDiff.comp
          (contDiff_snd (𝕜 := ℝ) (n := Ctop)))).add (contDiff_fst (𝕜 := ℝ) (n := Ctop))
  exact hΞ.2.1.comp (hpath.prodMk (hQsm.comp hexp))

/-- **The chain value is `C^∞`** on the box. -/
lemma psgChainVal_contMDiff {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) (tA tB : ℝ)
    (τ₂ : EuclideanSpace ℝ (Fin m))
    (hΞ : ChartPert Q m Ξ) (hQ : IsChartData Q) :
    ContMDiff (𝓡 5) (𝓡 4) Ctop (psgChainVal Ξ Q c A B tA tB τ₂) :=
  FamBox.contMDiff_famChain _
    (psg_contMDiff_chain Ξ Q c hΞ hQ A B tA tB τ₂)

/-- The chart `chr p` is `C^∞` on its source. -/
private lemma contMDiffOn_chr_psg (p : CappingSpace) :
    ContMDiffOn (𝓡 4) (𝓡 4) Ctop (chr p) (chr p).source := by
  have h := contMDiffOn_extChartAt (I := 𝓡 4) (x := p) (n := Ctop)
  simpa [chr] using h

/-- A charted smooth map on the parameter space is jointly smooth where its value lies in the chart
source. -/
private lemma contDiffAt_chart_psg {m : ℕ}
    (f : EuclideanSpace ℝ (Fin m) × Amb 4 → CappingSpace)
    (hf : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × Amb 4)) (𝓡 4) Ctop f)
    (p : CappingSpace) (q₀ : EuclideanSpace ℝ (Fin m) × Amb 4)
    (hreg : f q₀ ∈ (chr p).source) :
    ContDiffAt ℝ Ctop (fun q => (chr p) (f q)) q₀ := by
  have h1 : ContMDiffAt (𝓡 4) (𝓡 4) Ctop (chr p) (f q₀) :=
    (contMDiffOn_chr_psg p).contMDiffAt ((chr p).open_source.mem_nhds hreg)
  exact contMDiffAt_iff_contDiffAt.mp (h1.comp q₀ hf.contMDiffAt)

/-- **Joint smoothness of the charted difference of the loop value and the chain value**, at a point
where both values lie in the chart source. -/
lemma contDiffAt_chartDif_psg {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) (tA tB : ℝ)
    (hΞ : ChartPert Q m Ξ) (hQ : IsChartData Q) (p : CappingSpace)
    {q₀ : EuclideanSpace ℝ (Fin m) × Amb 4}
    (hreg : psgLoopVal Ξ Q A B q₀.1 q₀.2 ∈ (chr p).source ∧
      psgChainVal Ξ Q c A B tA tB 0 q₀.2 ∈ (chr p).source) :
    ContDiffAt ℝ Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 =>
        FamBox.chartDif p (fun z => psgLoopVal Ξ Q A B q.1 z)
          (fun z => psgChainVal Ξ Q c A B tA tB 0 z) q.2) q₀ := by
  have h1 : ContDiffAt ℝ Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => (chr p) (psgLoopVal Ξ Q A B q.1 q.2)) q₀ :=
    contDiffAt_chart_psg (fun q => psgLoopVal Ξ Q A B q.1 q.2)
      (psgLoopVal_contMDiff Ξ Q A B hΞ hQ) p q₀ hreg.1
  have h2 : ContDiffAt ℝ Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => (chr p) (psgChainVal Ξ Q c A B tA tB 0 q.2)) q₀ := by
    refine contDiffAt_chart_psg (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 =>
      psgChainVal Ξ Q c A B tA tB 0 q.2) ?_ p q₀ hreg.2
    exact (psgChainVal_contMDiff Ξ Q c A B tA tB 0 hΞ hQ).comp
      ((ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin m)) (Amb 4)).contMDiff (n := Ctop))
  exact h1.sub h2

/-- **Global smoothness of the cut-off-scaled charted difference system** of the path family.  The
cut-off `χ` vanishes outside the region where both values lie in the chart source, which is the only
place the charted difference map is defined. -/
lemma contDiff_cutoff_chartDif_psg {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) (tA tB : ℝ)
    (hΞ : ChartPert Q m Ξ) (hQ : IsChartData Q) (p : CappingSpace)
    {χ : EuclideanSpace ℝ (Fin m) × Amb 4 → ℝ} (hχ : ContDiff ℝ Ctop χ)
    {U : Set (EuclideanSpace ℝ (Fin m) × Amb 4)}
    (hU : U ⊆ {q : EuclideanSpace ℝ (Fin m) × Amb 4 |
      psgLoopVal Ξ Q A B q.1 q.2 ∈ (chr p).source ∧
      psgChainVal Ξ Q c A B tA tB 0 q.2 ∈ (chr p).source})
    (hχsupp : tsupport χ ⊆ U) :
    ContDiff ℝ Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => χ q •
        FamBox.chartDif p (fun z => psgLoopVal Ξ Q A B q.1 z)
          (fun z => psgChainVal Ξ Q c A B tA tB 0 z) q.2) := by
  rw [contDiff_iff_contDiffAt]
  intro q₀
  by_cases h0 : q₀ ∈ tsupport χ
  · have hreg : psgLoopVal Ξ Q A B q₀.1 q₀.2 ∈ (chr p).source ∧
        psgChainVal Ξ Q c A B tA tB 0 q₀.2 ∈ (chr p).source := hU (hχsupp h0)
    have hcd : ContDiffAt ℝ Ctop
        (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 =>
          FamBox.chartDif p (fun z => psgLoopVal Ξ Q A B q.1 z)
            (fun z => psgChainVal Ξ Q c A B tA tB 0 z) q.2) q₀ :=
      contDiffAt_chartDif_psg Ξ Q c A B tA tB hΞ hQ p hreg
    exact hχ.contDiffAt.smul hcd
  · have hzero : ∀ᶠ q in 𝓝 q₀, χ q = 0 := by
      have hopen : IsOpen (tsupport χ)ᶜ := (isClosed_tsupport χ).isOpen_compl
      refine Filter.mem_of_superset (hopen.mem_nhds (by simpa using h0)) ?_
      intro q hq
      by_contra hne
      exact hq (subset_tsupport χ hne)
    refine (contDiffAt_const (c := (0 : Tgt 4))).congr_of_eventuallyEq ?_
    filter_upwards [hzero] with q hq
    rw [hq, zero_smul]

/-- **The charted parameter-derivative of the loop value is onto** wherever the value lies in the
chart's source: the content is that the composite of the chart (a local diffeomorphism) with the
submersion `t ↦ Ξ t p` (`ChartPert`'s third conjunct) is onto. -/
lemma hsurj_psgLoopVal_charted {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (hΞ : ChartPert Q m Ξ) (hQ : IsChartData Q)
    (p : CappingSpace) (q : EuclideanSpace ℝ (Fin m)) (z : Amb 4)
    (hsrc : psgLoopVal Ξ Q A B q z ∈ (chr p).source) :
    Function.Surjective (fderiv ℝ (fun q' : EuclideanSpace ℝ (Fin m) =>
      chr p (psgLoopVal Ξ Q A B q' z)) q) := by
  have hsrc' : Ξ (psgPathL A B (z 0) + q) (Q (psgLoopPt z)) ∈ (chr p).source := by
    simpa only [psgLoopVal] using hsrc
  have hsurj_inner : Function.Surjective
      (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) =>
        chr p (Ξ t' (Q (psgLoopPt z)))) (psgPathL A B (z 0) + q)) := by
    have h := hsurj_sgLoop Ξ Q hΞ hQ.1 p (psgPathL A B (z 0) + q) (mk2 (z 1) 0) (by
      simpa only [pertChart, psgLoopPt, mk2, WithLp.ofLp_toLp, Matrix.cons_val_zero]
        using hsrc')
    have hfun : (fun t' : EuclideanSpace ℝ (Fin m) => chr p (pertChart Ξ Q t'
          (Complex.exp ((Real.pi : ℂ) * (((mk2 (z 1) 0) 0 : ℝ) : ℂ) * Complex.I))))
        = (fun t' : EuclideanSpace ℝ (Fin m) => chr p (Ξ t' (Q (psgLoopPt z)))) := by
      funext t'
      simp only [pertChart, psgLoopPt, mk2, WithLp.ofLp_toLp, Matrix.cons_val_zero]
    rwa [hfun] at h
  have hfun : (fun q' : EuclideanSpace ℝ (Fin m) => chr p (psgLoopVal Ξ Q A B q' z))
      = (fun t' : EuclideanSpace ℝ (Fin m) => chr p (Ξ t' (Q (psgLoopPt z)))) ∘
        (fun q' : EuclideanSpace ℝ (Fin m) => psgPathL A B (z 0) + q') := by
    funext q'
    simp only [Function.comp_apply, psgLoopVal]
  rw [hfun]
  have hinner_sm : ContMDiff (𝓡 m) (𝓡 4) Ctop
      (fun t' : EuclideanSpace ℝ (Fin m) => Ξ t' (Q (psgLoopPt z))) :=
    hΞ.2.1.comp (contMDiff_id.prodMk contMDiff_const)
  have hcat : ContDiffAt ℝ Ctop
      (fun t' : EuclideanSpace ℝ (Fin m) => chr p (Ξ t' (Q (psgLoopPt z))))
      (psgPathL A B (z 0) + q) :=
    contMDiffAt_iff_contDiffAt.mp
      (((contMDiffOn_chr_psg p).contMDiffAt ((chr p).open_source.mem_nhds hsrc')).comp
        (psgPathL A B (z 0) + q) hinner_sm.contMDiffAt)
  have hd : HasFDerivAt (fun t' : EuclideanSpace ℝ (Fin m) => chr p (Ξ t' (Q (psgLoopPt z))))
      (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) => chr p (Ξ t' (Q (psgLoopPt z))))
        (psgPathL A B (z 0) + q)) (psgPathL A B (z 0) + q) :=
    (hcat.differentiableAt ctop_ne_zero_psg).hasFDerivAt
  have htrans : HasFDerivAt (fun q' : EuclideanSpace ℝ (Fin m) => psgPathL A B (z 0) + q')
      (1 : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) q :=
    (hasFDerivAt_id q).const_add _
  have hcomp := hd.comp q htrans
  rw [hcomp.fderiv]
  have hcomp_one : ((fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) =>
        chr p (Ξ t' (Q (psgLoopPt z)))) (psgPathL A B (z 0) + q)).comp
      (1 : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)))
      = fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) =>
        chr p (Ξ t' (Q (psgLoopPt z)))) (psgPathL A B (z 0) + q) := by
    ext v
    simp
  rw [hcomp_one]
  exact hsurj_inner
end


theorem psg_family_regular {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → Work.Drive.CappingSpace → Work.Drive.CappingSpace)
    (Q : ℂ → Work.Drive.CappingSpace) (c : ℝ) (hΞ : Work.Drive.ChartPert Q m Ξ)
    (hQ : Work.Drive.IsChartData Q)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) (tA tB : ℝ)
    {εbr : ℝ} (hεbr : 0 < εbr) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4)) Work.Drive.CappingSpace :=
      Work.Drive.cappingCharted
    letI : IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
        ((⊤ : ℕ∞) : WithTop ℕ∞) Work.Drive.CappingSpace := Work.Drive.isManifold_cappingCharted
    ∃ τ₁ τ₂ : EuclideanSpace ℝ (Fin m), ‖τ₁‖ < εbr ∧ ‖τ₂‖ < εbr ∧
      (∀ p ∈ Submission.Drive.unitBox 4,
        Work.Drive.famLoop (Work.Drive.psgLoopFam Ξ Q A B τ₁) p
          = Work.Drive.famChain (Work.Drive.psgChainFam Ξ Q c A B tA tB τ₂) p →
        Function.Surjective (fun v : EuclideanSpace ℝ (Fin 5) =>
          (show EuclideanSpace ℝ (Fin 4) from
              mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 5)))
                (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
                (Work.Drive.famLoop (Work.Drive.psgLoopFam Ξ Q A B τ₁)) p v)
            - (show EuclideanSpace ℝ (Fin 4) from
              mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 5)))
                (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
                (Work.Drive.famChain (Work.Drive.psgChainFam Ξ Q c A B tA tB τ₂)) p v))) ∧
      (∀ p ∈ Submission.Drive.unitBox 4,
        Work.Drive.famLoop (Work.Drive.psgLoopFam Ξ Q A B τ₁) p
          = Work.Drive.famChain (Work.Drive.psgChainFam Ξ Q c A B tA tB τ₂) p →
        p ∈ Submission.Drive.unitBoxBdry 4 →
        ∃ i : Fin 5, (p i = 0 ∨ p i = 1) ∧ (∀ j : Fin 5, j ≠ i → p j ∈ Set.Ioo (0 : ℝ) 1) ∧
          ∃ σ : EuclideanSpace ℝ (Fin 5),
            mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 5)))
              (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
              (Work.Drive.famLoop (Work.Drive.psgLoopFam Ξ Q A B τ₁)) p σ
              = mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 5)))
                (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
                (Work.Drive.famChain (Work.Drive.psgChainFam Ξ Q c A B tA tB τ₂)) p σ ∧
            σ i ≠ 0) := by
  classical
  -- ================================================================
  -- ## 0. the value maps and their smoothness
  -- ================================================================
  have hLVsm : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × Amb 4)) (𝓡 4) Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => psgLoopVal Ξ Q A B q.1 q.2) :=
    psgLoopVal_contMDiff Ξ Q A B hΞ hQ
  have hCVsm : ContMDiff (𝓡 5) (𝓡 4) Ctop (psgChainVal Ξ Q c A B tA tB 0) :=
    psgChainVal_contMDiff Ξ Q c A B tA tB 0 hΞ hQ
  have hLVcont : Continuous (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 =>
      psgLoopVal Ξ Q A B q.1 q.2) := hLVsm.continuous
  have hCVcont : Continuous (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 =>
      psgChainVal Ξ Q c A B tA tB 0 q.2) := hCVsm.continuous.comp continuous_snd
  -- ================================================================
  -- ## 1. the compact value set and the chart cover
  -- ================================================================
  have hValComp : IsCompact (psgLoopVal Ξ Q A B 0 '' Submission.Drive.unitBox 4 ∪
      psgChainVal Ξ Q c A B tA tB 0 '' Submission.Drive.unitBox 4) := by
    refine (isCompact_unitBox 4).image ?_ |>.union ((isCompact_unitBox 4).image ?_)
    · fun_prop
    · exact hCVsm.continuous
  obtain ⟨r, pch, C0, C1, hC0c, hC1c, hC0int, hC1sub, hcover⟩ :=
    exists_compact_chart_cover _ hValComp
  set S : Fin r → Set (EuclideanSpace ℝ (Fin m) × Amb 4) := fun i => {q | ‖q.1‖ ≤ 1 ∧
      q.2 ∈ Submission.Drive.unitBox 4 ∧
      psgLoopVal Ξ Q A B q.1 q.2 ∈ C0 i ∧ psgChainVal Ξ Q c A B tA tB 0 q.2 ∈ C1 i}
    with hS
  set U : Fin r → Set (EuclideanSpace ℝ (Fin m) × Amb 4) := fun i => {q |
      psgLoopVal Ξ Q A B q.1 q.2 ∈ (chr (pch i)).source ∧
      psgChainVal Ξ Q c A B tA tB 0 q.2 ∈ (chr (pch i)).source} with hU
  have hScomp : ∀ i, IsCompact (S i) := by
    intro i
    have hEq : S i = (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1 ×ˢ
          Submission.Drive.unitBox 4)
        ∩ ((fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => psgLoopVal Ξ Q A B q.1 q.2) ⁻¹' (C0 i))
        ∩ ((fun q : EuclideanSpace ℝ (Fin m) × Amb 4 =>
            psgChainVal Ξ Q c A B tA tB 0 q.2) ⁻¹' (C1 i)) := by
      ext q
      simp only [hS, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_prod, Set.mem_preimage,
        Metric.mem_closedBall, dist_zero_right]
      tauto
    refine IsCompact.of_isClosed_subset
      ((isCompact_closedBall 0 1).prod (isCompact_unitBox 4)) ?_ ?_
    · rw [hEq]
      exact (((Metric.isClosed_closedBall.prod (isClosed_unitBox 4)).inter
        ((hC0c i).isClosed.preimage hLVcont)).inter ((hC1c i).isClosed.preimage hCVcont))
    · intro q hq
      rw [hEq] at hq
      exact ⟨hq.1.1.1, hq.1.1.2⟩
  have hUopen : ∀ i, IsOpen (U i) := by
    intro i
    have hEq : U i = ((fun q : EuclideanSpace ℝ (Fin m) × Amb 4 =>
          psgLoopVal Ξ Q A B q.1 q.2) ⁻¹' ((chr (pch i)).source))
        ∩ ((fun q : EuclideanSpace ℝ (Fin m) × Amb 4 =>
            psgChainVal Ξ Q c A B tA tB 0 q.2) ⁻¹' ((chr (pch i)).source)) := by
      ext q; simp only [hU, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage]
    rw [hEq]
    exact ((chr (pch i)).open_source.preimage hLVcont).inter
      ((chr (pch i)).open_source.preimage hCVcont)
  have hSU : ∀ i, S i ⊆ U i := by
    intro i q hq
    rw [hS] at hq
    simp only [Set.mem_setOf_eq] at hq
    refine ⟨hC1sub i (interior_subset (hC0int i hq.2.2.1)), hC1sub i hq.2.2.2⟩
  have hthick : ∀ i, ∃ δ : ℝ, 0 < δ ∧ ∀ (q q' : EuclideanSpace ℝ (Fin m)) (z : Amb 4),
      (q, z) ∈ S i → ‖q' - q‖ ≤ δ → (q', z) ∈ U i := fun i =>
    exists_pos_norm_subset_of_isCompact_subset_isOpen (hScomp i) (hUopen i) (hSU i)
  choose δ hδpos hδ using hthick
  have hr : 0 < r := by
    by_contra h
    have hr0 : r = 0 := Nat.eq_zero_of_not_pos h
    have hmem : psgChainVal Ξ Q c A B tA tB 0 0 ∈ psgLoopVal Ξ Q A B 0 '' Submission.Drive.unitBox 4 ∪
        psgChainVal Ξ Q c A B tA tB 0 '' Submission.Drive.unitBox 4 :=
      Or.inr ⟨0, fun _ => ⟨le_refl 0, zero_le_one⟩, rfl⟩
    obtain ⟨i, -⟩ := Set.mem_iUnion.mp (hcover hmem)
    exact absurd i.isLt (by omega)
  set δ₀ : ℝ := Finset.univ.inf' ⟨⟨0, hr⟩, Finset.mem_univ _⟩ δ with hδ₀
  have hδ₀pos : 0 < δ₀ := by
    rw [hδ₀]
    exact (Finset.lt_inf'_iff ⟨⟨0, hr⟩, Finset.mem_univ _⟩).mpr (fun i _ => hδpos i)
  have hδ₀le : ∀ i, δ₀ ≤ δ i := by
    intro i
    rw [hδ₀]
    exact Finset.inf'_le δ (Finset.mem_univ i)
  -- the radius of the Sard argument
  set ε : ℝ := min (min εbr (δ₀ / 2)) (1 / 2) with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef]
    exact lt_min (lt_min hεbr (by linarith)) (by norm_num)
  have hεbr' : ε ≤ εbr := le_trans (min_le_left _ _) (min_le_left _ _)
  have hεδ : 2 * ε ≤ δ₀ := by
    have h1 : ε ≤ δ₀ / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
    linarith
  have hε1 : ε ≤ 1 := by
    have h1 : ε ≤ 1 / 2 := min_le_right _ _
    linarith
  have hεδi : ∀ i, 2 * ε ≤ δ i := fun i => le_trans hεδ (hδ₀le i)
  -- ================================================================
  -- ## 3. the compact Sard sets `K i` and the cut-offs
  -- ================================================================
  set K : Fin r → Set (Amb 4) := fun i => {z | ∃ q : EuclideanSpace ℝ (Fin m),
    ‖q‖ ≤ ε ∧ (q, z) ∈ S i} with hK
  have hKcomp : ∀ i, IsCompact (K i) := by
    intro i
    have hEq : K i = Prod.snd '' (S i ∩ {q : EuclideanSpace ℝ (Fin m) × Amb 4 | ‖q.1‖ ≤ ε}) := by
      ext z
      constructor
      · rintro ⟨q, hqε, hqS⟩
        exact ⟨(q, z), ⟨hqS, hqε⟩, rfl⟩
      · rintro ⟨q, ⟨hqS, hqε⟩, rfl⟩
        exact ⟨q.1, hqε, hqS⟩
    rw [hEq]
    have hclosed : IsClosed ({q : EuclideanSpace ℝ (Fin m) × Amb 4 | ‖q.1‖ ≤ ε}) :=
      isClosed_le (continuous_norm.comp continuous_fst) continuous_const
    exact ((hScomp i).inter_right hclosed).image continuous_snd
  have hKsub : ∀ i, (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) ε) ×ˢ K i ⊆ U i := by
    intro i
    rintro ⟨q, z⟩ ⟨hq, hz⟩
    obtain ⟨q₀, hq₀, hq₀S⟩ := hz
    have hqq : ‖q - q₀‖ ≤ δ i := by
      have hqε : ‖q‖ ≤ ε := by simpa [Metric.mem_closedBall, dist_zero_right] using hq
      have h1 : ‖q - q₀‖ ≤ ‖q‖ + ‖q₀‖ := norm_sub_le q q₀
      linarith [hεδi i]
    exact hδ i q₀ q z hq₀S hqq
  have hcut : ∀ i, ∃ χ : EuclideanSpace ℝ (Fin m) × Amb 4 → ℝ, ContDiff ℝ Ctop χ ∧
      (∀ q ∈ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) ε) ×ˢ K i, χ q = 1) ∧
      tsupport χ ⊆ U i := by
    intro i
    obtain ⟨χ, hχsm, -, hχ1, hχsupp⟩ := contDiff_bump_of_isCompact_subset_isOpen
      ((isCompact_closedBall 0 ε).prod (hKcomp i)) (hUopen i) (hKsub i)
    exact ⟨χ, hχsm, hχ1, hχsupp⟩
  choose χ hχsm hχone hχsupp using hcut
  -- ================================================================
  -- ## 4. the charted difference systems `Φ i`
  -- ================================================================
  set Φ : Fin r → EuclideanSpace ℝ (Fin m) × Amb 4 → Tgt 4 := fun i q =>
    χ i q • FamBox.chartDif (pch i) (fun z => psgLoopVal Ξ Q A B q.1 z)
      (fun z => psgChainVal Ξ Q c A B tA tB 0 z) q.2 with hΦ
  have hΦsm : ∀ i, ContDiff ℝ Ctop (Φ i) := by
    intro i
    refine contDiff_cutoff_chartDif_psg Ξ Q c A B tA tB hΞ hQ (pch i) (hχsm i) ?_ (hχsupp i)
    intro q hq
    rw [hU] at hq
    exact hq
  -- ================================================================
  -- ## 5. the corner pieces of the box
  -- ================================================================
  set ι : Type := {l : (Fin 5 × Fin 5) × (Fin 2 × Fin 2) // l.1.1 ≠ l.1.2} with hι
  have hιF : Fintype ι := by rw [hι]; infer_instance
  set Xc : Fin r → ι → Submodule ℝ (Amb 4) := fun _ l => cornerSub l.1.1.1 l.1.1.2 with hXc
  set Bc : (i : Fin r) → (l : ι) → (Xc i l) → Amb 4 := fun _ l y =>
    cornerPt l.1.1.1 l.1.1.2 (fin2Real l.1.2.1) (fin2Real l.1.2.2) y with hBc
  set K0 : (i : Fin r) → (l : ι) → Set (Xc i l) := fun i l => {y | Bc i l y ∈ K i} with hK0
  have hXfin : ∀ i l, Module.finrank ℝ (Xc i l) < 4 := by
    intro i l
    have h := cornerSub_finrank l.1.1.1 l.1.1.2 l.2
    rw [hXc]
    simp only [h]
    norm_num
  have hBsm : ∀ i l, ContDiff ℝ Ctop (Bc i l) := by
    intro i l
    have h1 : ContDiff ℝ Ctop (fun y : Xc i l =>
        (Submodule.subtypeL (Xc i l)) y + (fin2Real l.1.2.1) • e5 l.1.1.1) :=
      ((Submodule.subtypeL (Xc i l)).contDiff).add contDiff_const
    have h2 : ContDiff ℝ Ctop (fun y : Xc i l =>
        ((Submodule.subtypeL (Xc i l)) y + (fin2Real l.1.2.1) • e5 l.1.1.1)
          + (fin2Real l.1.2.2) • e5 l.1.1.2) :=
      h1.add contDiff_const
    exact h2
  have hK0comp : ∀ i l, IsCompact (K0 i l) := by
    intro i l
    rw [Metric.isCompact_iff_isClosed_bounded]
    refine ⟨?_, ?_⟩
    · rw [hK0]
      exact (hKcomp i).isClosed.preimage (hBsm i l).continuous
    · rw [hK0]
      obtain ⟨C, hC⟩ := (hKcomp i).isBounded.exists_norm_le
      refine isBounded_iff_forall_norm_le.mpr ⟨C + ‖(fin2Real l.1.2.1) • e5 l.1.1.1
        + (fin2Real l.1.2.2) • e5 l.1.1.2‖, ?_⟩
      intro y hy
      have hsub : Bc i l y - ((fin2Real l.1.2.1) • e5 l.1.1.1
          + (fin2Real l.1.2.2) • e5 l.1.1.2) = (y : Amb 4) := by
        rw [hBc]
        simp only [cornerPt]
        abel
      calc ‖y‖ = ‖(y : Amb 4)‖ := rfl
        _ = ‖Bc i l y - ((fin2Real l.1.2.1) • e5 l.1.1.1
              + (fin2Real l.1.2.2) • e5 l.1.1.2)‖ := by rw [hsub]
        _ ≤ ‖Bc i l y‖ + ‖(fin2Real l.1.2.1) • e5 l.1.1.1
              + (fin2Real l.1.2.2) • e5 l.1.1.2‖ := norm_sub_le _ _
        _ ≤ C + ‖(fin2Real l.1.2.1) • e5 l.1.1.1
              + (fin2Real l.1.2.2) • e5 l.1.1.2‖ := by linarith [hC (Bc i l y) hy]
  -- ================================================================
  -- ## 6. the parameter derivative of the systems is onto at their zeros
  -- ================================================================
  have hsurjΦ : ∀ (i : Fin r) (p : EuclideanSpace ℝ (Fin m)) (z : Amb 4), ‖p‖ < ε →
      (z ∈ K i ∨ ∃ l : ι, z ∈ Bc i l '' K0 i l) → Φ i (p, z) = 0 →
      Function.Surjective (fderiv ℝ (fun p' : EuclideanSpace ℝ (Fin m) => Φ i (p', z)) p) := by
    intro i p z hp hz hzero
    have hpK : (p, z) ∈ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) ε) ×ˢ K i := by
      refine ⟨?_, ?_⟩
      · rw [Metric.mem_closedBall, dist_zero_right]; exact le_of_lt hp
      rcases hz with h | ⟨l, y, hy, rfl⟩
      · exact h
      · exact hy
    have hχ1 : χ i (p, z) = 1 := hχone i (p, z) hpK
    have hUmem : (p, z) ∈ U i := hKsub i hpK
    have hcd0 : FamBox.chartDif (pch i) (fun z' => psgLoopVal Ξ Q A B p z')
        (fun z' => psgChainVal Ξ Q c A B tA tB 0 z') z = 0 := by
      have h0 : χ i (p, z) • FamBox.chartDif (pch i) (fun z' => psgLoopVal Ξ Q A B p z')
          (fun z' => psgChainVal Ξ Q c A B tA tB 0 z') z = 0 := hzero
      rwa [hχ1, one_smul] at h0
    -- the parameter derivative of the charted difference is onto
    have hcount : Function.Surjective (fderiv ℝ (fun p' : EuclideanSpace ℝ (Fin m) =>
        FamBox.chartDif (pch i) (fun z' => psgLoopVal Ξ Q A B p' z')
          (fun z' => psgChainVal Ξ Q c A B tA tB 0 z') z) p) := by
      have hfun : (fun p' : EuclideanSpace ℝ (Fin m) =>
            FamBox.chartDif (pch i) (fun z' => psgLoopVal Ξ Q A B p' z')
              (fun z' => psgChainVal Ξ Q c A B tA tB 0 z') z)
          = (fun p' : EuclideanSpace ℝ (Fin m) => chr (pch i) (psgLoopVal Ξ Q A B p' z)
              - chr (pch i) (psgChainVal Ξ Q c A B tA tB 0 z)) := rfl
      rw [hfun, fderiv_sub_const]
      exact hsurj_psgLoopVal_charted Ξ Q A B hΞ hQ (pch i) p z hUmem.1
    -- the derivative of the cut-off system is the same at the zero
    have hcdat : ContDiffAt ℝ Ctop (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 =>
        FamBox.chartDif (pch i) (fun z' => psgLoopVal Ξ Q A B q.1 z')
          (fun z' => psgChainVal Ξ Q c A B tA tB 0 z') q.2) (p, z) :=
      contDiffAt_chartDif_psg Ξ Q c A B tA tB hΞ hQ (pch i) hUmem
    have hχat : ContDiffAt ℝ Ctop (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => χ i q) (p, z) :=
      (hχsm i).contDiffAt
    have hpairp : ContDiffAt ℝ Ctop (fun p' : EuclideanSpace ℝ (Fin m) => (p', z)) p :=
      contDiffAt_id.prodMk contDiffAt_const
    have hχcomp : ContDiffAt ℝ Ctop
        ((fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => χ i q) ∘
          (fun p' : EuclideanSpace ℝ (Fin m) => (p', z))) p :=
      hχat.comp p hpairp
    have hχ_at_p : ContDiffAt ℝ Ctop (fun p' : EuclideanSpace ℝ (Fin m) => χ i (p', z)) p := hχcomp
    have hcdcomp : ContDiffAt ℝ Ctop
        ((fun q : EuclideanSpace ℝ (Fin m) × Amb 4 =>
            FamBox.chartDif (pch i) (fun z' => psgLoopVal Ξ Q A B q.1 z')
              (fun z' => psgChainVal Ξ Q c A B tA tB 0 z') q.2) ∘
          (fun p' : EuclideanSpace ℝ (Fin m) => (p', z))) p :=
      hcdat.comp p hpairp
    have hcd_at_p : ContDiffAt ℝ Ctop (fun p' : EuclideanSpace ℝ (Fin m) =>
        FamBox.chartDif (pch i) (fun z' => psgLoopVal Ξ Q A B p' z')
          (fun z' => psgChainVal Ξ Q c A B tA tB 0 z') z) p := hcdcomp
    have hχp : HasFDerivAt (fun p' : EuclideanSpace ℝ (Fin m) => χ i (p', z))
        (fderiv ℝ (fun p' : EuclideanSpace ℝ (Fin m) => χ i (p', z)) p) p :=
      (hχ_at_p.differentiableAt ctop_ne_zero_psg).hasFDerivAt
    have hχp2 : HasFDerivAt (fun p' : EuclideanSpace ℝ (Fin m) =>
        FamBox.chartDif (pch i) (fun z' => psgLoopVal Ξ Q A B p' z')
          (fun z' => psgChainVal Ξ Q c A B tA tB 0 z') z)
        (fderiv ℝ (fun p' : EuclideanSpace ℝ (Fin m) =>
          FamBox.chartDif (pch i) (fun z' => psgLoopVal Ξ Q A B p' z')
            (fun z' => psgChainVal Ξ Q c A B tA tB 0 z') z) p) p :=
      (hcd_at_p.differentiableAt ctop_ne_zero_psg).hasFDerivAt
    have hsmul := hχp.smul hχp2
    have h1 : (χ i (p, z)) • (fderiv ℝ (fun p' : EuclideanSpace ℝ (Fin m) =>
          FamBox.chartDif (pch i) (fun z' => psgLoopVal Ξ Q A B p' z')
            (fun z' => psgChainVal Ξ Q c A B tA tB 0 z') z) p)
        + (fderiv ℝ (fun p' : EuclideanSpace ℝ (Fin m) => χ i (p', z)) p).smulRight
            (FamBox.chartDif (pch i) (fun z' => psgLoopVal Ξ Q A B p z')
              (fun z' => psgChainVal Ξ Q c A B tA tB 0 z') z)
        = fderiv ℝ (fun p' : EuclideanSpace ℝ (Fin m) =>
          FamBox.chartDif (pch i) (fun z' => psgLoopVal Ξ Q A B p' z')
            (fun z' => psgChainVal Ξ Q c A B tA tB 0 z') z) p := by
      rw [hχ1, hcd0]
      simp
    rw [h1] at hsmul
    have hfd : fderiv ℝ (fun p' : EuclideanSpace ℝ (Fin m) =>
        χ i (p', z) • FamBox.chartDif (pch i) (fun z' => psgLoopVal Ξ Q A B p' z')
          (fun z' => psgChainVal Ξ Q c A B tA tB 0 z') z) p
        = fderiv ℝ (fun p' : EuclideanSpace ℝ (Fin m) =>
          FamBox.chartDif (pch i) (fun z' => psgLoopVal Ξ Q A B p' z')
            (fun z' => psgChainVal Ξ Q c A B tA tB 0 z') z) p := hsmul.fderiv
    show Function.Surjective (fderiv ℝ (fun p' : EuclideanSpace ℝ (Fin m) => Φ i (p', z)) p)
    rw [show (fun p' : EuclideanSpace ℝ (Fin m) => Φ i (p', z))
        = (fun p' : EuclideanSpace ℝ (Fin m) => χ i (p', z) •
            FamBox.chartDif (pch i) (fun z' => psgLoopVal Ξ Q A B p' z')
              (fun z' => psgChainVal Ξ Q c A B tA tB 0 z') z) from rfl]
    rw [hfd]
    exact hcount
  -- ================================================================
  -- ## 7. the multi-chart parametric Sard
  -- ================================================================
  obtain ⟨p, hp_lt, hregS, hfaceSys, havoidS⟩ :=
    goodFaceMulti (m := m) (n := 4) (r := r) (K := K) (hK := hKcomp)
      (ι := fun _ => ι) (X := fun i l => (↥(Xc i l)))
      (hX := fun i l => hXfin i l)
      (B := fun i l => Bc i l) (hB := fun i l => hBsm i l)
      (K₀ := fun i l => K0 i l) (hK₀ := fun i l => hK0comp i l)
      (Φ := Φ) (hΦ := hΦsm) (ε := ε) (hε := hεpos) (hsurj := hsurjΦ)
  -- ================================================================
  -- ## 8. the meeting-point analysis
  -- ================================================================
  have hmeet_chart : ∀ (q : EuclideanSpace ℝ (Fin m)) (z : Amb 4), ‖q‖ < ε →
      z ∈ Submission.Drive.unitBox 4 →
      famLoop (psgLoopFam Ξ Q A B q) z = famChain (psgChainFam Ξ Q c A B tA tB 0) z →
      ∃ i : Fin r, z ∈ K i ∧ (q, z) ∈ U i ∧
        FamBox.chartDif (pch i) (fun z' => psgLoopVal Ξ Q A B q z')
          (fun z' => psgChainVal Ξ Q c A B tA tB 0 z') z = 0 := by
    intro q z hq hz hmeet
    have hval : psgChainVal Ξ Q c A B tA tB 0 z ∈ psgLoopVal Ξ Q A B 0 '' Submission.Drive.unitBox 4 ∪
        psgChainVal Ξ Q c A B tA tB 0 '' Submission.Drive.unitBox 4 :=
      Or.inr ⟨z, hz, rfl⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hval)
    have hLVeq : psgLoopVal Ξ Q A B q z = psgChainVal Ξ Q c A B tA tB 0 z :=
      (psgLoopVal_eq_famLoop Ξ Q A B q z).symm.trans hmeet
    have hSq : (q, z) ∈ S i := by
      rw [hS]
      simp only [Set.mem_setOf_eq]
      refine ⟨le_trans (le_of_lt hq) hε1, hz, ?_, interior_subset (hC0int i hi)⟩
      rw [hLVeq]
      exact hi
    have hKq : z ∈ K i := ⟨q, le_of_lt hq, hSq⟩
    have hUq : (q, z) ∈ U i := by
      refine hKsub i ⟨?_, hKq⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      exact le_of_lt hq
    refine ⟨i, hKq, hUq, ?_⟩
    exact (FamBox.chartDif_eq_zero_iff hUq).mpr hLVeq
  -- ================================================================
  -- ## 9. the transversality clause
  -- ================================================================
  have htrans : ∀ z ∈ Submission.Drive.unitBox 4,
      famLoop (psgLoopFam Ξ Q A B p) z = famChain (psgChainFam Ξ Q c A B tA tB 0) z →
      Function.Surjective (FamBox.Lf (famLoop (psgLoopFam Ξ Q A B p))
        (famChain (psgChainFam Ξ Q c A B tA tB 0)) z) := by
    intro z hz hmeet
    obtain ⟨i, hKi, hUi, hcd0⟩ := hmeet_chart p z hp_lt hz hmeet
    have heq_z : psgLoopVal Ξ Q A B p z = psgChainVal Ξ Q c A B tA tB 0 z :=
      (psgLoopVal_eq_famLoop Ξ Q A B p z).symm.trans hmeet
    have hχ1 : χ i (p, z) = 1 := by
      refine hχone i (p, z) ⟨?_, hKi⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      exact le_of_lt hp_lt
    have hzero : Φ i (p, z) = 0 := by
      show χ i (p, z) • FamBox.chartDif (pch i) (fun z' => psgLoopVal Ξ Q A B p z')
        (fun z' => psgChainVal Ξ Q c A B tA tB 0 z') z = 0
      rw [hχ1, one_smul, hcd0]
    have hzd := hregS i z hKi hzero
    -- remove the cut-off from the `z`-derivative
    have hcdat : ContDiffAt ℝ Ctop (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 =>
        FamBox.chartDif (pch i) (fun z' => psgLoopVal Ξ Q A B q.1 z')
          (fun z' => psgChainVal Ξ Q c A B tA tB 0 z') q.2) (p, z) :=
      contDiffAt_chartDif_psg Ξ Q c A B tA tB hΞ hQ (pch i) hUi
    have hzpair : ContDiffAt ℝ Ctop (fun z' : Amb 4 => (p, z')) z :=
      contDiffAt_const.prodMk contDiffAt_id
    have hzpair : ContDiffAt ℝ Ctop (fun z' : Amb 4 => (p, z')) z :=
      contDiffAt_const.prodMk contDiffAt_id
    have hcdcomp : ContDiffAt ℝ Ctop
        ((fun q : EuclideanSpace ℝ (Fin m) × Amb 4 =>
            FamBox.chartDif (pch i) (fun z'' => psgLoopVal Ξ Q A B q.1 z'')
              (fun z'' => psgChainVal Ξ Q c A B tA tB 0 z'') q.2) ∘
          (fun z' : Amb 4 => (p, z'))) z :=
      hcdat.comp z hzpair
    have hcdat_z : ContDiffAt ℝ Ctop (fun z' : Amb 4 =>
        FamBox.chartDif (pch i) (fun z'' => psgLoopVal Ξ Q A B p z'')
          (fun z'' => psgChainVal Ξ Q c A B tA tB 0 z'') z') z := hcdcomp
    have hχcomp : ContDiffAt ℝ Ctop
        ((fun q : EuclideanSpace ℝ (Fin m) × Amb 4 => χ i q) ∘
          (fun z' : Amb 4 => (p, z'))) z :=
      (hχsm i).contDiffAt.comp z hzpair
    have hχat_z : ContDiffAt ℝ Ctop (fun z' : Amb 4 => χ i (p, z')) z := hχcomp
    have hχp : HasFDerivAt (fun z' : Amb 4 => χ i (p, z'))
        (fderiv ℝ (fun z' : Amb 4 => χ i (p, z')) z) z :=
      (hχat_z.differentiableAt ctop_ne_zero_psg).hasFDerivAt
    have hcdp : HasFDerivAt (fun z' : Amb 4 =>
        FamBox.chartDif (pch i) (fun z'' => psgLoopVal Ξ Q A B p z'')
          (fun z'' => psgChainVal Ξ Q c A B tA tB 0 z'') z')
        (fderiv ℝ (fun z' : Amb 4 =>
          FamBox.chartDif (pch i) (fun z'' => psgLoopVal Ξ Q A B p z'')
            (fun z'' => psgChainVal Ξ Q c A B tA tB 0 z'') z') z) z :=
      (hcdat_z.differentiableAt ctop_ne_zero_psg).hasFDerivAt
    have hsmul := hχp.smul hcdp
    have h1 : (χ i (p, z)) • (fderiv ℝ (fun z' : Amb 4 =>
          FamBox.chartDif (pch i) (fun z'' => psgLoopVal Ξ Q A B p z'')
            (fun z'' => psgChainVal Ξ Q c A B tA tB 0 z'') z') z)
        + (fderiv ℝ (fun z' : Amb 4 => χ i (p, z')) z).smulRight
            (FamBox.chartDif (pch i) (fun z'' => psgLoopVal Ξ Q A B p z'')
              (fun z'' => psgChainVal Ξ Q c A B tA tB 0 z'') z)
        = fderiv ℝ (fun z' : Amb 4 =>
          FamBox.chartDif (pch i) (fun z'' => psgLoopVal Ξ Q A B p z'')
            (fun z'' => psgChainVal Ξ Q c A B tA tB 0 z'') z') z := by
      rw [hχ1, hcd0]
      simp
    rw [h1] at hsmul
    have hfd : fderiv ℝ (fun z' : Amb 4 => χ i (p, z') •
        FamBox.chartDif (pch i) (fun z'' => psgLoopVal Ξ Q A B p z'')
          (fun z'' => psgChainVal Ξ Q c A B tA tB 0 z'') z') z
        = fderiv ℝ (fun z' : Amb 4 =>
          FamBox.chartDif (pch i) (fun z'' => psgLoopVal Ξ Q A B p z'')
            (fun z'' => psgChainVal Ξ Q c A B tA tB 0 z'') z') z := hsmul.fderiv
    have hzd' : Function.Surjective (fderiv ℝ (fun z' : Amb 4 =>
        FamBox.chartDif (pch i) (fun z'' => psgLoopVal Ξ Q A B p z'')
          (fun z'' => psgChainVal Ξ Q c A B tA tB 0 z'') z') z) := by
      rw [← hfd]
      exact hzd
    -- the charted difference is the change of coordinates applied to `Lf`
    have hLfsm : ContMDiff (𝓡 5) (𝓡 4) Ctop (fun z' : Amb 4 => psgLoopVal Ξ Q A B p z') :=
      (FamBox.contMDiff_famLoop (psgLoopFam Ξ Q A B p)
        (psg_contMDiff_loop Ξ Q hΞ hQ A B p)).congr
        (fun z' => (psgLoopVal_eq_famLoop Ξ Q A B p z').symm)
    have hCsm : ContMDiff (𝓡 5) (𝓡 4) Ctop
        (fun z' : Amb 4 => psgChainVal Ξ Q c A B tA tB 0 z') := hCVsm
    have heqfd : fderiv ℝ (FamBox.chartDif (pch i) (fun z' : Amb 4 => psgLoopVal Ξ Q A B p z')
          (fun z' : Amb 4 => psgChainVal Ξ Q c A B tA tB 0 z')) z
        = (tangentCoordChange (𝓡 4) (psgLoopVal Ξ Q A B p z) (pch i)
            (psgLoopVal Ξ Q A B p z)).comp
          (FamBox.Lf (fun z' : Amb 4 => psgLoopVal Ξ Q A B p z')
            (fun z' : Amb 4 => psgChainVal Ξ Q c A B tA tB 0 z') z) := by
      refine ContinuousLinearMap.ext fun v => ?_
      exact FamBox.fderiv_chartDif_eq_Lf (pch i) _ _ hLfsm hCsm (x := z) hUi heq_z v
    have hsurjComp : Function.Surjective
        ((tangentCoordChange (𝓡 4) (psgLoopVal Ξ Q A B p z) (pch i)
            (psgLoopVal Ξ Q A B p z)).comp
          (FamBox.Lf (fun z' : Amb 4 => psgLoopVal Ξ Q A B p z')
            (fun z' : Amb 4 => psgChainVal Ξ Q c A B tA tB 0 z') z)) := by
      rw [← heqfd]
      exact hzd'
    have hinj : Function.Injective
        (tangentCoordChange (𝓡 4) (psgLoopVal Ξ Q A B p z) (pch i)
          (psgLoopVal Ξ Q A B p z)) :=
      tangentCoordChange_injective (x := psgLoopVal Ξ Q A B p z) (y := pch i)
        (z := psgLoopVal Ξ Q A B p z)
        ⟨mem_extChartAt_source (I := 𝓡 4) _, by rw [extChartAt_source]; exact hUi.1⟩
    have hsurjLf : Function.Surjective (FamBox.Lf
        (fun z' : Amb 4 => psgLoopVal Ξ Q A B p z')
        (fun z' : Amb 4 => psgChainVal Ξ Q c A B tA tB 0 z') z) := by
      intro w
      obtain ⟨v, hv⟩ := hsurjComp (tangentCoordChange (𝓡 4) (psgLoopVal Ξ Q A B p z) (pch i)
        (psgLoopVal Ξ Q A B p z) w)
      exact ⟨v, hinj hv⟩
    exact hsurjLf
  -- ================================================================
  -- ## 10. the face clause
  -- ================================================================
  have hface : ∀ z ∈ Submission.Drive.unitBox 4,
      famLoop (psgLoopFam Ξ Q A B p) z = famChain (psgChainFam Ξ Q c A B tA tB 0) z →
      z ∈ Submission.Drive.unitBoxBdry 4 →
      ∃ i : Fin 5, (z i = 0 ∨ z i = 1) ∧ (∀ j : Fin 5, j ≠ i → z j ∈ Set.Ioo (0 : ℝ) 1) ∧
        ∃ σ : Amb 4,
          mfderiv (𝓡 5) (𝓡 4) (famLoop (psgLoopFam Ξ Q A B p)) z σ
            = mfderiv (𝓡 5) (𝓡 4) (famChain (psgChainFam Ξ Q c A B tA tB 0)) z σ ∧
          σ i ≠ 0 := by
    intro z hz hmeet hbd
    obtain ⟨i₀, hi₀⟩ := hbd.2
    obtain ⟨i, hKi, hUi, hcd0⟩ := hmeet_chart p z hp_lt hz hmeet
    have heq_z : psgLoopVal Ξ Q A B p z = psgChainVal Ξ Q c A B tA tB 0 z :=
      (psgLoopVal_eq_famLoop Ξ Q A B p z).symm.trans hmeet
    have hχ1 : χ i (p, z) = 1 := by
      refine hχone i (p, z) ⟨?_, hKi⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      exact le_of_lt hp_lt
    have hzero : Φ i (p, z) = 0 := by
      show χ i (p, z) • FamBox.chartDif (pch i) (fun z' => psgLoopVal Ξ Q A B p z')
        (fun z' => psgChainVal Ξ Q c A B tA tB 0 z') z = 0
      rw [hχ1, one_smul, hcd0]
    -- no two faces are on the meet: the corner pieces are avoided
    have hsingle : ∀ j : Fin 5, j ≠ i₀ → ¬ (z j = 0 ∨ z j = 1) := by
      intro j hj hface_j
      obtain ⟨aj, haj⟩ := exists_fin2Real (z j) hface_j
      obtain ⟨b₀, hb₀⟩ := exists_fin2Real (z i₀) hi₀
      set l : ι := ⟨((j, i₀), (aj, b₀)), hj⟩ with hl
      have hy := (cornerPt_data j i₀ hj).2 (z j) (z i₀) z rfl rfl
      obtain ⟨y, hyz⟩ := hy
      have hBcy : Bc i l y = cornerPt j i₀ (fin2Real aj) (fin2Real b₀) y := rfl
      have hcorner : cornerPt j i₀ (fin2Real aj) (fin2Real b₀) y = z := by
        rw [haj, hb₀]
        exact hyz
      have hyK : y ∈ K0 i l := by
        show Bc i l y ∈ K i
        rw [hBcy, hcorner]
        exact hKi
      have havoid := havoidS i l y hyK
      exact havoid (by rw [hBcy, hcorner]; exact hzero)
    -- the two surjectivity statements of the system at the face
    have hfull : Function.Surjective (fderiv ℝ (fun z' : Amb 4 => Φ i (p, z')) z) :=
      hregS i z hKi hzero
    have hface' : Function.Surjective (fun v : {v : Amb 4 // v i₀ = 0} =>
        fderiv ℝ (fun z' : Amb 4 => Φ i (p, z')) z v.1) :=
      hfaceSys i i₀ z hKi hzero hi₀
    -- remove the cut-off from both
    have hcdat : ContDiffAt ℝ Ctop (fun q : EuclideanSpace ℝ (Fin m) × Amb 4 =>
        FamBox.chartDif (pch i) (fun z' => psgLoopVal Ξ Q A B q.1 z')
          (fun z' => psgChainVal Ξ Q c A B tA tB 0 z') q.2) (p, z) :=
      contDiffAt_chartDif_psg Ξ Q c A B tA tB hΞ hQ (pch i) hUi
    have hzpair : ContDiffAt ℝ Ctop (fun z' : Amb 4 => (p, z')) z :=
      contDiffAt_const.prodMk contDiffAt_id
    have hcdat_z : ContDiffAt ℝ Ctop (fun z' : Amb 4 =>
        FamBox.chartDif (pch i) (fun z'' => psgLoopVal Ξ Q A B p z'')
          (fun z'' => psgChainVal Ξ Q c A B tA tB 0 z'') z') z :=
      hcdat.comp z hzpair
    have hχat_z : ContDiffAt ℝ Ctop (fun z' : Amb 4 => χ i (p, z')) z :=
      (hχsm i).contDiffAt.comp z hzpair
    have hχp : HasFDerivAt (fun z' : Amb 4 => χ i (p, z'))
        (fderiv ℝ (fun z' : Amb 4 => χ i (p, z')) z) z :=
      (hχat_z.differentiableAt ctop_ne_zero_psg).hasFDerivAt
    have hcdp : HasFDerivAt (fun z' : Amb 4 =>
        FamBox.chartDif (pch i) (fun z'' => psgLoopVal Ξ Q A B p z'')
          (fun z'' => psgChainVal Ξ Q c A B tA tB 0 z'') z')
        (fderiv ℝ (fun z' : Amb 4 =>
          FamBox.chartDif (pch i) (fun z'' => psgLoopVal Ξ Q A B p z'')
            (fun z'' => psgChainVal Ξ Q c A B tA tB 0 z'') z') z) z :=
      (hcdat_z.differentiableAt ctop_ne_zero_psg).hasFDerivAt
    have hsmul := hχp.smul hcdp
    have h1 : (χ i (p, z)) • (fderiv ℝ (fun z' : Amb 4 =>
          FamBox.chartDif (pch i) (fun z'' => psgLoopVal Ξ Q A B p z'')
            (fun z'' => psgChainVal Ξ Q c A B tA tB 0 z'') z') z)
        + (fderiv ℝ (fun z' : Amb 4 => χ i (p, z')) z).smulRight
            (FamBox.chartDif (pch i) (fun z'' => psgLoopVal Ξ Q A B p z'')
              (fun z'' => psgChainVal Ξ Q c A B tA tB 0 z'') z)
        = fderiv ℝ (fun z' : Amb 4 =>
          FamBox.chartDif (pch i) (fun z'' => psgLoopVal Ξ Q A B p z'')
            (fun z'' => psgChainVal Ξ Q c A B tA tB 0 z'') z') z := by
      rw [hχ1, hcd0]
      simp
    rw [h1] at hsmul
    have hfd : fderiv ℝ (fun z' : Amb 4 => χ i (p, z') •
        FamBox.chartDif (pch i) (fun z'' => psgLoopVal Ξ Q A B p z'')
          (fun z'' => psgChainVal Ξ Q c A B tA tB 0 z'') z') z
        = fderiv ℝ (fun z' : Amb 4 =>
          FamBox.chartDif (pch i) (fun z'' => psgLoopVal Ξ Q A B p z'')
            (fun z'' => psgChainVal Ξ Q c A B tA tB 0 z'') z') z := hsmul.fderiv
    have hfull' : Function.Surjective (fderiv ℝ (fun z' : Amb 4 =>
        FamBox.chartDif (pch i) (fun z'' => psgLoopVal Ξ Q A B p z'')
          (fun z'' => psgChainVal Ξ Q c A B tA tB 0 z'') z') z) := by
      rw [← hfd]; exact hfull
    have hface'' : Function.Surjective (fun v : {v : Amb 4 // v i₀ = 0} =>
        fderiv ℝ (fun z' : Amb 4 =>
          FamBox.chartDif (pch i) (fun z'' => psgLoopVal Ξ Q A B p z'')
            (fun z'' => psgChainVal Ξ Q c A B tA tB 0 z'') z') z v.1) := by
      rw [← hfd]; exact hface'
    -- the linear algebra: a kernel direction off the face
    obtain ⟨σ, hσ, hσi⟩ := exists_kernel_ne_zero_of_face_surjective _ i₀ hfull' hface''
    -- convert the charted kernel equation into `Lf σ = 0`
    have hLfsm : ContMDiff (𝓡 5) (𝓡 4) Ctop (fun z' : Amb 4 => psgLoopVal Ξ Q A B p z') :=
      (FamBox.contMDiff_famLoop (psgLoopFam Ξ Q A B p)
        (psg_contMDiff_loop Ξ Q hΞ hQ A B p)).congr
        (fun z' => (psgLoopVal_eq_famLoop Ξ Q A B p z').symm)
    have hCsm : ContMDiff (𝓡 5) (𝓡 4) Ctop
        (fun z' : Amb 4 => psgChainVal Ξ Q c A B tA tB 0 z') := hCVsm
    have heqσ := FamBox.fderiv_chartDif_eq_Lf (pch i) _ _ hLfsm hCsm (x := z) hUi heq_z σ
    have hinj : Function.Injective
        (tangentCoordChange (𝓡 4) (psgLoopVal Ξ Q A B p z) (pch i)
          (psgLoopVal Ξ Q A B p z)) :=
      tangentCoordChange_injective (x := psgLoopVal Ξ Q A B p z) (y := pch i)
        (z := psgLoopVal Ξ Q A B p z)
        ⟨mem_extChartAt_source (I := 𝓡 4) _, by rw [extChartAt_source]; exact hUi.1⟩
    have hLf0 : FamBox.Lf (fun z' : Amb 4 => psgLoopVal Ξ Q A B p z')
        (fun z' : Amb 4 => psgChainVal Ξ Q c A B tA tB 0 z') z σ = 0 := by
      apply hinj
      rw [← heqσ, map_zero, hσ]

    refine ⟨i₀, hi₀, ?_, σ, ?_, hσi⟩
    · intro j hj
      have hnot := hsingle j hj
      rw [Set.mem_Ioo]
      exact ⟨lt_of_le_of_ne (hz j).1 (fun h => hnot (Or.inl h.symm)),
        lt_of_le_of_ne (hz j).2 (fun h => hnot (Or.inr h))⟩
    · rw [FamBox.Lf_apply] at hLf0
      exact sub_eq_zero.mp hLf0
  -- ================================================================
  -- ## 11. the conclusion
  -- ================================================================
  refine ⟨p, 0, lt_of_lt_of_le hp_lt hεbr', by simpa using hεbr, ?_, ?_⟩
  · intro z hz hmeet
    exact htrans z hz hmeet
  · intro z hz hmeet hbd
    obtain ⟨i, hi, hother, σ, hσ, hσi⟩ := hface z hz hmeet hbd
    exact ⟨i, hi, hother, σ, hσ, hσi⟩

end Work.Drive
