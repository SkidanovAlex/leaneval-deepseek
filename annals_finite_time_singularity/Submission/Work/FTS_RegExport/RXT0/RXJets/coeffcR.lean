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
# `Work.FTS_RegExport.RXT0.RXJets.coeffcR` — the joint continuity of the jets of `cR`

The `cR` conjunct of `coeffJetsJointCont`.  `cs7 = (1+μ) - L₁₂(F_τ)/β + sin²θ·𝔽K(F_τ) - 2ℛ(Φ̃_τ)`
with `Φ̃_τ = Φ̃_* + Ξ_τ` on the open quadrant; the sum of the first three pieces, the two radial
pieces and the two `ℛ`-slots are handled separately.
-/

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXT0.RXJets

set_option autoImplicit false
set_option maxHeartbeats 3800000

open Work.FTS_RegExport.RXT (v2_PhiT v2_PhiStar v2_PhiPert)

/-- **The `cR` conjunct of `coeffJetsJointCont`.** -/
theorem coeffcR {α C₀ Ce Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (H : CJHyps α C₀ Ce Cs Φs E g) :
    ∀ S > 0, ∀ k l : ℕ, k + l ≤ 2 →
      ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed k l
        (fun z θ => Work.FTS.RegExportIface.RXT.cR α Φs E g z θ p.2.2) p.1 p.2.1)
        (Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S)) := by
  have hα := H.hα
  have hα13 := H.hα13
  have hEL3 := H.hEL3
  have hStar := H.hStar
  have hOK := H.hOK
  have hμRc := CJHyps.hμRc H
  obtain ⟨hMixedConst, hConstCont, hCdC2m, hCdSinsq, hDthAng, hRadialCont, hRadAngCont⟩ :=
    Work.FTS_RegExport.RXT0.RXJets.jetBasic
  have hStar3 := CJHyps.hStar3 H
  have hStar1 := CJHyps.hStar1 H
  have hPert3 := CJHyps.hPert3 H
  have hPert1g := CJHyps.hPert1g H
  have hagQ := CJHyps.hagQ H
  intro S hS k l hkl
  have hk2 : k ≤ 2 := by omega
  have hl2 : l ≤ 2 := by omega
  have hRegR := CJHyps.hRegR H S
  have hdzd := CJHyps.hdzd H S hS
  obtain ⟨hStarVop, hStarRop, hStarUdiv⟩ := CJHyps.hStarSlots H S k l hkl
  refine ContinuousOn.congr (f := fun p : ℝ × ℝ × ℝ =>
      Work.Spaces.mixed k l (fun _ _ : ℝ => (1 : ℝ)
          + Work.FTS.RegExportIface.RXT.μR α Φs E g p.2.2) p.1 p.2.1
      + Work.Spaces.mixed k l (fun z θ => (-(1 / Work.FTS.Regularity.pExp α))
          * Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z) p.1 p.2.1
      + Work.Spaces.mixed k l (fun z θ => Work.Construction.FK (Work.Construction.Ftau
            (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z
          * Real.sin θ ^ 2) p.1 p.2.1
      + Work.Spaces.mixed k l (fun z θ => (-2 : ℝ) * Work.Construction.Rop
          (Work.FTS.Regularity.pExp α) (v2_PhiStar α Φs) z θ) p.1 p.2.1
      + Work.Spaces.mixed k l (fun z θ => (-2 : ℝ) * Work.Construction.Rop
          (Work.FTS.Regularity.pExp α) (v2_PhiPert α E g p.2.2) z θ) p.1 p.2.1) ?_ ?_
  · have hP0 : ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed k l
          (fun _ _ : ℝ => (1 : ℝ) + Work.FTS.RegExportIface.RXT.μR α Φs E g p.2.2)
          p.1 p.2.1) (Work.FTS_RegExport.RXT0.RXJets.slb S) :=
        hConstCont (c := fun τ : ℝ => (1 : ℝ) + Work.FTS.RegExportIface.RXT.μR α Φs E g τ)
          ((continuousOn_const (c := (1 : ℝ))).add (hμRc S)) k l
    have hP1 : ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed k l
          (fun z θ => (-(1 / Work.FTS.Regularity.pExp α)) * Work.Construction.L12
            (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z) p.1 p.2.1)
          (Work.FTS_RegExport.RXT0.RXJets.slb S) :=
        hRadialCont (c := -(1 / Work.FTS.Regularity.pExp α))
          (a := fun z τ => Work.Construction.L12 (Work.Construction.Ftau
            (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) z)
          (hdzd k hk2).1 hkl
    have hP2 : ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed k l
          (fun z θ => Work.Construction.FK (Work.Construction.Ftau
            (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z
            * Real.sin θ ^ 2) p.1 p.2.1) (Work.FTS_RegExport.RXT0.RXJets.slb S) :=
        hRadAngCont (a := fun z τ => Work.Construction.FK (Work.Construction.Ftau
            (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) z)
          (b := fun θ => Real.sin θ ^ 2) (hdzd k hk2).2 (hDthAng hCdSinsq l hl2)
    have hP3 : ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed k l
          (fun z θ => (-2 : ℝ) * Work.Construction.Rop (Work.FTS.Regularity.pExp α)
            (v2_PhiStar α Φs) z θ) p.1 p.2.1) (Work.FTS_RegExport.RXT0.RXJets.slb S) :=
        (hStarRop.const_mul (-2)).congr (fun p hp => by
          rw [Work.FTS_RegExport.RXT.Sys.coeff_mixed_const_mul])
    have hP4 : ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed k l
          (fun z θ => (-2 : ℝ) * Work.Construction.Rop (Work.FTS.Regularity.pExp α)
            (v2_PhiPert α E g p.2.2) z θ) p.1 p.2.1)
          (Work.FTS_RegExport.RXT0.RXJets.slb S) :=
        ((H.hSlot S hS k l hkl).2.1.const_mul (-2)).congr (fun p hp => by
          rw [Work.FTS_RegExport.RXT.Sys.coeff_mixed_const_mul])
    exact (((hP0.add hP1).add hP2).add hP3).add hP4
  · intro p hp
    show Work.Spaces.mixed k l (fun z θ => Work.FTS.RegExportIface.RXT.cR α Φs E g z θ p.2.2)
          p.1 p.2.1
        = Work.Spaces.mixed k l (fun _ _ : ℝ => (1 : ℝ)
            + Work.FTS.RegExportIface.RXT.μR α Φs E g p.2.2) p.1 p.2.1
          + Work.Spaces.mixed k l (fun z θ => (-(1 / Work.FTS.Regularity.pExp α))
              * Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z) p.1 p.2.1
          + Work.Spaces.mixed k l (fun z θ => Work.Construction.FK (Work.Construction.Ftau
              (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z
              * Real.sin θ ^ 2) p.1 p.2.1
          + Work.Spaces.mixed k l (fun z θ => (-2 : ℝ) * Work.Construction.Rop
              (Work.FTS.Regularity.pExp α) (v2_PhiStar α Φs) z θ) p.1 p.2.1
          + Work.Spaces.mixed k l (fun z θ => (-2 : ℝ) * Work.Construction.Rop
              (Work.FTS.Regularity.pExp α) (v2_PhiPert α E g p.2.2) z θ) p.1 p.2.1
    obtain ⟨hz, hθ, hθ2, hτ0, hτS⟩ := mem_slb.mp hp
    have hzθ : (p.1, p.2.1) ∈ Work.FTS.EllipticEst.Q0 := ⟨hz, hθ, hθ2⟩
    have hP1b := hPert1g p.2.2 hτ0
    have hP0b : ContDiffOn ℝ 2 (Function.uncurry (fun _ _ : ℝ => (1 : ℝ)
          + Work.FTS.RegExportIface.RXT.μR α Φs E g p.2.2)) Work.FTS.EllipticEst.Q0 :=
      contDiffOn_const
    have hP1c : ContDiffOn ℝ 2 (Function.uncurry (fun z θ => (-(1 / Work.FTS.Regularity.pExp α))
          * Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z)) Work.FTS.EllipticEst.Q0 :=
      (contDiffOn_const (c := -(1 / Work.FTS.Regularity.pExp α))).mul
        (Work.FTS_RegExport.RXT.contDiffOn_slice_fst (hRegR p.2.2 ⟨hτ0, hτS⟩).1)
    have hP2c : ContDiffOn ℝ 2 (Function.uncurry (fun z θ => Work.Construction.FK
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z * Real.sin θ ^ 2))
        Work.FTS.EllipticEst.Q0 :=
      (Work.FTS_RegExport.RXT.contDiffOn_slice_fst (hRegR p.2.2 ⟨hτ0, hτS⟩).2).mul
        ((hCdSinsq.comp contDiffOn_snd (fun q hq => hq.2)).congr (fun q _ => rfl))
    have hP3b : ContDiffOn ℝ 2 (Function.uncurry (fun z θ => (-2 : ℝ)
          * Work.Construction.Rop (Work.FTS.Regularity.pExp α) (v2_PhiStar α Φs) z θ))
        Work.FTS.EllipticEst.Q0 :=
      (contDiffOn_const (c := (-2 : ℝ))).mul
        (Work.FTS_RegExport.RXT.contDiffOn_uncurry_Rop hStar3)
    have hP4b : ContDiffOn ℝ 2 (Function.uncurry (fun z θ => (-2 : ℝ)
          * Work.Construction.Rop (Work.FTS.Regularity.pExp α) (v2_PhiPert α E g p.2.2) z θ))
        Work.FTS.EllipticEst.Q0 :=
      (contDiffOn_const (c := (-2 : ℝ))).mul
        (Work.FTS_RegExport.RXT.contDiffOn_uncurry_Rop (hPert3 p.2.2 hτ0))
    have hsplit : Set.EqOn (Function.uncurry (fun z θ =>
          Work.FTS.RegExportIface.RXT.cR α Φs E g z θ p.2.2))
        (Function.uncurry (fun z θ => (((1 : ℝ)
            + Work.FTS.RegExportIface.RXT.μR α Φs E g p.2.2)
          + (-(1 / Work.FTS.Regularity.pExp α)) * Work.Construction.L12
              (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z)
          + Work.Construction.FK (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z * Real.sin θ ^ 2
          + ((-2 : ℝ) * Work.Construction.Rop (Work.FTS.Regularity.pExp α)
              (v2_PhiStar α Φs) z θ
            + (-2 : ℝ) * Work.Construction.Rop (Work.FTS.Regularity.pExp α)
                (v2_PhiPert α E g p.2.2) z θ))) Work.FTS.EllipticEst.Q0 := by
      intro q hq
      obtain ⟨hz', hθ', hθ2'⟩ := Work.FTS.EllipticEst.mem_Q0.mp hq
      simp only [Function.uncurry]
      have hRcT : Work.Construction.Rop (Work.FTS.Regularity.pExp α)
            (v2_PhiT α Φs E g p.2.2) q.1 q.2
          = Work.Construction.Rop (Work.FTS.Regularity.pExp α)
              (v2_PhiStar α Φs + v2_PhiPert α E g p.2.2) q.1 q.2 :=
        Work.FTS_RegExport.RXR5.Rop_congr_of_agreeOnQ (α := Work.FTS.Regularity.pExp α)
          (hagQ p.2.2 hτ0) hz' hθ' hθ2'
      have hRcB : Work.Construction.Rop (Work.FTS.Regularity.pExp α)
            (v2_PhiStar α Φs + v2_PhiPert α E g p.2.2) q.1 q.2
          = Work.Construction.Rop (Work.FTS.Regularity.pExp α) (v2_PhiStar α Φs) q.1 q.2
            + Work.Construction.Rop (Work.FTS.Regularity.pExp α)
                (v2_PhiPert α E g p.2.2) q.1 q.2 :=
        Work.FTS_RegExport.RXT.v2_rop_add_at (αG := Work.FTS.Regularity.pExp α)
          hStar1 hP1b ⟨hz', hθ', hθ2'⟩
      rw [show Work.FTS.RegExportIface.RXT.cR α Φs E g q.1 q.2 p.2.2
          = (1 + Work.FTS.RegExportIface.RXT.μR α Φs E g p.2.2)
            - Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) q.1 / Work.FTS.Regularity.pExp α
            + Real.sin q.2 ^ 2 * Work.Construction.FK (Work.Construction.Ftau
                (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) q.1
            - 2 * Work.Construction.Rop (Work.FTS.Regularity.pExp α)
                (v2_PhiT α Φs E g p.2.2) q.1 q.2 from rfl]
      rw [hRcT, hRcB]
      ring
    have hstepA : Work.Spaces.mixed k l (fun z θ => (((1 : ℝ)
            + Work.FTS.RegExportIface.RXT.μR α Φs E g p.2.2)
          + (-(1 / Work.FTS.Regularity.pExp α)) * Work.Construction.L12
              (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z)
          + Work.Construction.FK (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z * Real.sin θ ^ 2
          + ((-2 : ℝ) * Work.Construction.Rop (Work.FTS.Regularity.pExp α)
              (v2_PhiStar α Φs) z θ
            + (-2 : ℝ) * Work.Construction.Rop (Work.FTS.Regularity.pExp α)
                (v2_PhiPert α E g p.2.2) z θ)) p.1 p.2.1
        = Work.Spaces.mixed k l (fun z θ => ((1 : ℝ)
              + Work.FTS.RegExportIface.RXT.μR α Φs E g p.2.2)
            + (-(1 / Work.FTS.Regularity.pExp α)) * Work.Construction.L12
                (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                  (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z
            + Work.Construction.FK (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z * Real.sin θ ^ 2)
            p.1 p.2.1
          + Work.Spaces.mixed k l (fun z θ => (-2 : ℝ) * Work.Construction.Rop
              (Work.FTS.Regularity.pExp α) (v2_PhiStar α Φs) z θ
              + (-2 : ℝ) * Work.Construction.Rop (Work.FTS.Regularity.pExp α)
                  (v2_PhiPert α E g p.2.2) z θ) p.1 p.2.1 :=
      Work.FTS_RegExport.RXT.Sys.mixed_add_lam
        (f := fun z θ => ((1 : ℝ)
              + Work.FTS.RegExportIface.RXT.μR α Φs E g p.2.2)
            + (-(1 / Work.FTS.Regularity.pExp α)) * Work.Construction.L12
                (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                  (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z
            + Work.Construction.FK (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z * Real.sin θ ^ 2)
        (h := fun z θ => (-2 : ℝ) * Work.Construction.Rop (Work.FTS.Regularity.pExp α)
              (v2_PhiStar α Φs) z θ
            + (-2 : ℝ) * Work.Construction.Rop (Work.FTS.Regularity.pExp α)
                (v2_PhiPert α E g p.2.2) z θ)
        ((hP0b.add hP1c).add hP2c) (hP3b.add hP4b) hkl hzθ
    have hstepB : Work.Spaces.mixed k l (fun z θ => ((1 : ℝ)
              + Work.FTS.RegExportIface.RXT.μR α Φs E g p.2.2)
            + (-(1 / Work.FTS.Regularity.pExp α)) * Work.Construction.L12
                (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                  (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z
            + Work.Construction.FK (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z * Real.sin θ ^ 2)
            p.1 p.2.1
        = Work.Spaces.mixed k l (fun z θ => ((1 : ℝ)
              + Work.FTS.RegExportIface.RXT.μR α Φs E g p.2.2)
            + (-(1 / Work.FTS.Regularity.pExp α)) * Work.Construction.L12
                (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                  (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z) p.1 p.2.1
          + Work.Spaces.mixed k l (fun z θ => Work.Construction.FK
              (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z * Real.sin θ ^ 2)
              p.1 p.2.1 :=
      Work.FTS_RegExport.RXT.Sys.mixed_add_lam
        (f := fun z θ => ((1 : ℝ)
              + Work.FTS.RegExportIface.RXT.μR α Φs E g p.2.2)
            + (-(1 / Work.FTS.Regularity.pExp α)) * Work.Construction.L12
                (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                  (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z)
        (h := fun z θ => Work.Construction.FK (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z * Real.sin θ ^ 2)
        (hP0b.add hP1c) hP2c hkl hzθ
    have hstepC : Work.Spaces.mixed k l (fun z θ => ((1 : ℝ)
            + Work.FTS.RegExportIface.RXT.μR α Φs E g p.2.2)
          + (-(1 / Work.FTS.Regularity.pExp α)) * Work.Construction.L12
              (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z) p.1 p.2.1
        = Work.Spaces.mixed k l (fun _ _ : ℝ => (1 : ℝ)
              + Work.FTS.RegExportIface.RXT.μR α Φs E g p.2.2) p.1 p.2.1
          + Work.Spaces.mixed k l (fun z θ => (-(1 / Work.FTS.Regularity.pExp α))
              * Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z) p.1 p.2.1 :=
      Work.FTS_RegExport.RXT.Sys.mixed_add_lam
        (f := fun _ _ : ℝ => (1 : ℝ) + Work.FTS.RegExportIface.RXT.μR α Φs E g p.2.2)
        (h := fun z θ => (-(1 / Work.FTS.Regularity.pExp α)) * Work.Construction.L12
              (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z)
        hP0b hP1c hkl hzθ
    have hstepD : Work.Spaces.mixed k l (fun z θ => (-2 : ℝ) * Work.Construction.Rop
            (Work.FTS.Regularity.pExp α) (v2_PhiStar α Φs) z θ
          + (-2 : ℝ) * Work.Construction.Rop (Work.FTS.Regularity.pExp α)
              (v2_PhiPert α E g p.2.2) z θ) p.1 p.2.1
        = Work.Spaces.mixed k l (fun z θ => (-2 : ℝ) * Work.Construction.Rop
            (Work.FTS.Regularity.pExp α) (v2_PhiStar α Φs) z θ) p.1 p.2.1
          + Work.Spaces.mixed k l (fun z θ => (-2 : ℝ) * Work.Construction.Rop
              (Work.FTS.Regularity.pExp α) (v2_PhiPert α E g p.2.2) z θ) p.1 p.2.1 :=
      Work.FTS_RegExport.RXT.Sys.mixed_add_lam
        (f := fun z θ => (-2 : ℝ) * Work.Construction.Rop (Work.FTS.Regularity.pExp α)
            (v2_PhiStar α Φs) z θ)
        (h := fun z θ => (-2 : ℝ) * Work.Construction.Rop (Work.FTS.Regularity.pExp α)
            (v2_PhiPert α E g p.2.2) z θ)
        hP3b hP4b hkl hzθ
    rw [Work.FTS_EllLimOK.mixed_congr_of_eqOn_isOpen Work.FTS.EllipticEst.isOpen_Q0 hsplit
      hzθ k l, hstepA, hstepB, hstepC, hstepD]
    ring

end Work.FTS_RegExport.RXT0.RXJets
