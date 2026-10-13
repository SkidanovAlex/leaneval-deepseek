import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS_RegExport.RXT0.RXJets.slabDefs
import Submission.Work.FTS_RegExport.RXT0.RXJets.CJDefs
import Submission.Work.FTS_RegExport.RXT0.RXJets.CJShared
import Submission.Work.FTS_RegExport.RXT0.RXJets.jetBasic
import Submission.Work.FTS_RegExport.RXT.Sys.CoeffCore

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT0.RXJets.coeffVR` — the joint continuity of the jets of `VR`

The `VR` conjunct of `coeffJetsJointCont`.  `VR = (1-μ) + L₁₂(F_τ)·c2m + 2α·𝒱(Φ̃_τ)` with
`Φ̃_τ = Φ̃_* + Ξ_τ` on the open quadrant; each of the four pieces is handled by the generic
lemmas of `jetBasic` and the star/perturbation slot continuities, and the mixed jets are
expanded with the additivity `RXT.Sys.mixed_add_lam`.
-/

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXT0.RXJets

set_option autoImplicit false
set_option maxHeartbeats 3800000

open Work.FTS_RegExport.RXT (v2_PhiT v2_PhiStar v2_PhiPert)

/-- **The `VR` conjunct of `coeffJetsJointCont`.** -/
theorem coeffVR {α C₀ Ce Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (H : CJHyps α C₀ Ce Cs Φs E g) :
    ∀ S > 0, ∀ k l : ℕ, k + l ≤ 2 →
      ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed k l
        (fun z θ => Work.FTS.RegExportIface.RXT.VR α Φs E g z θ p.2.2) p.1 p.2.1)
        (Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S)) := by
  have hα := H.hα
  have hα13 := H.hα13
  have hEll := H.hEll
  have hEL3 := H.hEL3
  have hStar := H.hStar
  have hSol := H.hSol
  have hOK := H.hOK
  have hμ := H.hμ
  have hL12 := H.hL12
  have hSlot := H.hSlot
  obtain ⟨hMixedConst, hConstCont, hCdC2m, hCdSinsq, hDthAng, hRadialCont, hRadAngCont⟩ :=
    Work.FTS_RegExport.RXT0.RXJets.jetBasic
  have hStar3 := CJHyps.hStar3 H
  have hStar1 := CJHyps.hStar1 H
  have hPert3 := CJHyps.hPert3 H
  intro S hS k l hkl
  have hk2 : k ≤ 2 := by omega
  have hl2 : l ≤ 2 := by omega
  have hdzd := CJHyps.hdzd H S hS
  have hμRc := CJHyps.hμRc H S
  obtain ⟨hStarVop, hStarRop, hStarUdiv⟩ := CJHyps.hStarSlots H S k l hkl
  -- ## the `C²` facts of the VR pieces
  have hVRc2 : ∀ τ ∈ Set.Icc (0:ℝ) S,
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => (1 : ℝ)
        - Work.FTS.RegExportIface.RXT.μR α Φs E g τ
        + Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) τ) z * Work.Construction.c2m θ))
        Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.Construction.L12
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) τ) z * Work.Construction.c2m θ))
        Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => ((2 : ℝ) * Work.FTS.Regularity.pExp α)
          * Work.Construction.Vop (v2_PhiStar α Φs) z θ)) Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ => ((2 : ℝ) * Work.FTS.Regularity.pExp α)
          * Work.Construction.Vop (v2_PhiPert α E g τ) z θ)) Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun _ _ : ℝ => (1 : ℝ)
          - Work.FTS.RegExportIface.RXT.μR α Φs E g τ)) Work.FTS.EllipticEst.Q0 := by
    intro τ hτ
    obtain ⟨h1, -, h3, -, -, -, -, -, -, -, -, -, -⟩ :=
      Work.FTS_RegExport.RXT.Sys.coeff_pieces_contDiffOn (τ := τ) hα hα13 hEL3 hStar hOK hτ.1
    exact ⟨h1, h3,
      (contDiffOn_const (c := (2 : ℝ) * Work.FTS.Regularity.pExp α)).mul
        (Work.FTS_RegExport.RXT.contDiffOn_uncurry_Vop hStar3),
      (contDiffOn_const (c := (2 : ℝ) * Work.FTS.Regularity.pExp α)).mul
        (Work.FTS_RegExport.RXT.contDiffOn_uncurry_Vop (hPert3 τ hτ.1)),
      contDiffOn_const⟩
  refine ContinuousOn.congr (f := fun p : ℝ × ℝ × ℝ =>
      Work.Spaces.mixed k l (fun _ _ : ℝ => (1 : ℝ)
          - Work.FTS.RegExportIface.RXT.μR α Φs E g p.2.2) p.1 p.2.1
      + Work.Spaces.mixed k l (fun z θ => Work.Construction.L12
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z * Work.Construction.c2m θ) p.1 p.2.1
      + Work.Spaces.mixed k l (fun z θ => ((2 : ℝ) * Work.FTS.Regularity.pExp α)
          * Work.Construction.Vop (v2_PhiStar α Φs) z θ) p.1 p.2.1
      + Work.Spaces.mixed k l (fun z θ => ((2 : ℝ) * Work.FTS.Regularity.pExp α)
          * Work.Construction.Vop (v2_PhiPert α E g p.2.2) z θ) p.1 p.2.1) ?_ ?_
  · have hc0 : ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed k l
          (fun _ _ : ℝ => (1 : ℝ) - Work.FTS.RegExportIface.RXT.μR α Φs E g p.2.2) p.1 p.2.1)
          (Work.FTS_RegExport.RXT0.RXJets.slb S) :=
        hConstCont (c := fun τ : ℝ => (1 : ℝ) - Work.FTS.RegExportIface.RXT.μR α Φs E g τ)
          ((continuousOn_const (c := (1 : ℝ))).sub hμRc) k l
    have hc1 : ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed k l
          (fun z θ => Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z * Work.Construction.c2m θ)
          p.1 p.2.1) (Work.FTS_RegExport.RXT0.RXJets.slb S) :=
        hRadAngCont (a := fun z τ => Work.Construction.L12
            (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) τ) z) (b := Work.Construction.c2m)
          (hdzd k hk2).1 (hDthAng hCdC2m l hl2)
    have hc2 : ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed k l
          (fun z θ => ((2 : ℝ) * Work.FTS.Regularity.pExp α)
            * Work.Construction.Vop (v2_PhiStar α Φs) z θ) p.1 p.2.1)
          (Work.FTS_RegExport.RXT0.RXJets.slb S) :=
        (hStarVop.const_mul (2 * Work.FTS.Regularity.pExp α)).congr (fun p hp => by
          rw [Work.FTS_RegExport.RXT.Sys.coeff_mixed_const_mul])
    have hc3 : ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed k l
          (fun z θ => ((2 : ℝ) * Work.FTS.Regularity.pExp α)
            * Work.Construction.Vop (v2_PhiPert α E g p.2.2) z θ) p.1 p.2.1)
          (Work.FTS_RegExport.RXT0.RXJets.slb S) :=
        ((hSlot S hS k l hkl).1.const_mul (2 * Work.FTS.Regularity.pExp α)).congr
          (fun p hp => by
            rw [Work.FTS_RegExport.RXT.Sys.coeff_mixed_const_mul])
    exact ((hc0.add hc1).add hc2).add hc3
  · intro p hp
    show Work.Spaces.mixed k l (fun z θ =>
          Work.FTS.RegExportIface.RXT.VR α Φs E g z θ p.2.2) p.1 p.2.1
        = Work.Spaces.mixed k l (fun _ _ : ℝ => (1 : ℝ)
              - Work.FTS.RegExportIface.RXT.μR α Φs E g p.2.2) p.1 p.2.1
          + Work.Spaces.mixed k l (fun z θ => Work.Construction.L12
              (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z * Work.Construction.c2m θ)
              p.1 p.2.1
          + Work.Spaces.mixed k l (fun z θ => ((2 : ℝ) * Work.FTS.Regularity.pExp α)
              * Work.Construction.Vop (v2_PhiStar α Φs) z θ) p.1 p.2.1
          + Work.Spaces.mixed k l (fun z θ => ((2 : ℝ) * Work.FTS.Regularity.pExp α)
              * Work.Construction.Vop (v2_PhiPert α E g p.2.2) z θ) p.1 p.2.1
    obtain ⟨hz, hθ, hθ2, hτ0, hτS⟩ := mem_slb.mp hp
    have hzθ : (p.1, p.2.1) ∈ Work.FTS.EllipticEst.Q0 := ⟨hz, hθ, hθ2⟩
    have hC2τ := hVRc2 p.2.2 ⟨hτ0, hτS⟩
    have hPert1 := CJHyps.hPert1g H p.2.2 hτ0
    have hag := CJHyps.hagQ H p.2.2 hτ0
    have hsplit : Set.EqOn (Function.uncurry (fun z θ =>
          Work.FTS.RegExportIface.RXT.VR α Φs E g z θ p.2.2))
        (Function.uncurry (fun z θ => (((1 : ℝ)
            - Work.FTS.RegExportIface.RXT.μR α Φs E g p.2.2)
          + Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z * Work.Construction.c2m θ)
          + (((2 : ℝ) * Work.FTS.Regularity.pExp α) * Work.Construction.Vop (v2_PhiStar α Φs) z θ
            + ((2 : ℝ) * Work.FTS.Regularity.pExp α)
              * Work.Construction.Vop (v2_PhiPert α E g p.2.2) z θ)))
        Work.FTS.EllipticEst.Q0 := by
      intro q hq
      obtain ⟨hz', hθ', hθ2'⟩ := Work.FTS.EllipticEst.mem_Q0.mp hq
      simp only [Function.uncurry]
      have hVc := Work.FTS_RegExport.RXR5.Vop_congr_of_agreeOnQ hag hz' hθ' hθ2'
      have hVa : Work.Construction.Vop (v2_PhiStar α Φs + v2_PhiPert α E g p.2.2) q.1 q.2
          = Work.Construction.Vop (v2_PhiStar α Φs) q.1 q.2
            + Work.Construction.Vop (v2_PhiPert α E g p.2.2) q.1 q.2 :=
        Work.FTS_RegExport.RXT.v2_vop_add_at hStar1 hPert1 ⟨hz', hθ', hθ2'⟩
      rw [show Work.FTS.RegExportIface.RXT.VR α Φs E g q.1 q.2 p.2.2
          = (1 - Work.FTS.RegExportIface.RXT.μR α Φs E g p.2.2)
            + Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) q.1 * Work.Construction.c2m q.2
            + 2 * Work.FTS.Regularity.pExp α
              * Work.Construction.Vop (v2_PhiT α Φs E g p.2.2) q.1 q.2 from rfl]
      rw [hVc, hVa]
      ring
    have hstepA : Work.Spaces.mixed k l (fun z θ => (((1 : ℝ)
            - Work.FTS.RegExportIface.RXT.μR α Φs E g p.2.2)
          + Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z * Work.Construction.c2m θ)
          + (((2 : ℝ) * Work.FTS.Regularity.pExp α) * Work.Construction.Vop (v2_PhiStar α Φs) z θ
            + ((2 : ℝ) * Work.FTS.Regularity.pExp α)
              * Work.Construction.Vop (v2_PhiPert α E g p.2.2) z θ)) p.1 p.2.1
        = Work.Spaces.mixed k l (fun z θ => ((1 : ℝ)
              - Work.FTS.RegExportIface.RXT.μR α Φs E g p.2.2)
            + Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z * Work.Construction.c2m θ)
            p.1 p.2.1
          + Work.Spaces.mixed k l (fun z θ =>
              ((2 : ℝ) * Work.FTS.Regularity.pExp α) * Work.Construction.Vop (v2_PhiStar α Φs) z θ
              + ((2 : ℝ) * Work.FTS.Regularity.pExp α)
                * Work.Construction.Vop (v2_PhiPert α E g p.2.2) z θ) p.1 p.2.1 :=
      Work.FTS_RegExport.RXT.Sys.mixed_add_lam (f := fun z θ => ((1 : ℝ)
            - Work.FTS.RegExportIface.RXT.μR α Φs E g p.2.2)
            + Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z * Work.Construction.c2m θ)
        (h := fun z θ =>
            ((2 : ℝ) * Work.FTS.Regularity.pExp α) * Work.Construction.Vop (v2_PhiStar α Φs) z θ
            + ((2 : ℝ) * Work.FTS.Regularity.pExp α)
              * Work.Construction.Vop (v2_PhiPert α E g p.2.2) z θ)
        hC2τ.1 (hC2τ.2.2.1.add hC2τ.2.2.2.1) hkl hzθ
    have hstepB : Work.Spaces.mixed k l (fun z θ => ((1 : ℝ)
          - Work.FTS.RegExportIface.RXT.μR α Φs E g p.2.2)
          + Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z * Work.Construction.c2m θ) p.1 p.2.1
        = Work.Spaces.mixed k l (fun _ _ : ℝ => (1 : ℝ)
              - Work.FTS.RegExportIface.RXT.μR α Φs E g p.2.2) p.1 p.2.1
          + Work.Spaces.mixed k l (fun z θ => Work.Construction.L12
              (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z * Work.Construction.c2m θ)
              p.1 p.2.1 :=
      Work.FTS_RegExport.RXT.Sys.mixed_add_lam
        (f := fun _ _ : ℝ => (1 : ℝ) - Work.FTS.RegExportIface.RXT.μR α Φs E g p.2.2)
        (h := fun z θ => Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z * Work.Construction.c2m θ)
        hC2τ.2.2.2.2 hC2τ.2.1 hkl hzθ
    have hstepC : Work.Spaces.mixed k l (fun z θ =>
          ((2 : ℝ) * Work.FTS.Regularity.pExp α) * Work.Construction.Vop (v2_PhiStar α Φs) z θ
          + ((2 : ℝ) * Work.FTS.Regularity.pExp α)
            * Work.Construction.Vop (v2_PhiPert α E g p.2.2) z θ) p.1 p.2.1
        = Work.Spaces.mixed k l (fun z θ => ((2 : ℝ) * Work.FTS.Regularity.pExp α)
            * Work.Construction.Vop (v2_PhiStar α Φs) z θ) p.1 p.2.1
          + Work.Spaces.mixed k l (fun z θ => ((2 : ℝ) * Work.FTS.Regularity.pExp α)
            * Work.Construction.Vop (v2_PhiPert α E g p.2.2) z θ) p.1 p.2.1 :=
      Work.FTS_RegExport.RXT.Sys.mixed_add_lam
        (f := fun z θ => ((2 : ℝ) * Work.FTS.Regularity.pExp α)
            * Work.Construction.Vop (v2_PhiStar α Φs) z θ)
        (h := fun z θ => ((2 : ℝ) * Work.FTS.Regularity.pExp α)
            * Work.Construction.Vop (v2_PhiPert α E g p.2.2) z θ)
        hC2τ.2.2.1 hC2τ.2.2.2.1 hkl hzθ
    rw [Work.FTS_EllLimOK.mixed_congr_of_eqOn_isOpen Work.FTS.EllipticEst.isOpen_Q0 hsplit
      hzθ k l, hstepA, hstepB, hstepC]
    ring

end Work.FTS_RegExport.RXT0.RXJets
