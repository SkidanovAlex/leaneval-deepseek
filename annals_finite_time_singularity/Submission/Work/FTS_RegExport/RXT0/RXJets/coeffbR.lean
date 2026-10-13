import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_RegExport.RXT0.RXJets.slabDefs
import Submission.Work.FTS_RegExport.RXT0.RXJets.CJDefs
import Submission.Work.FTS_RegExport.RXT0.RXJets.CJShared
import Submission.Work.FTS_RegExport.RXT0.RXJets.jetBasic
import Submission.Work.FTS_RegExport.RXT.Sys.CoeffCore
import Submission.Work.FTS_RegExport.RXT.Sys.explicit_pieces_coeff

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT0.RXJets.coeffbR` — the joint continuity of the jets of `bR`

The `bR` conjunct of `coeffJetsJointCont`.  `bR = 2·𝒰(ΦR_τ)/sin 2θ` with
`ΦR_τ = Φ̃_τ + Θ(F_τ)` and `Φ̃_τ = Φ̃_* + Ξ_τ` on the open quadrant; the `Θ`-part is evaluated in
closed form with `Uop_Theta_div`, which reduces it to the radial combination
`-(3/(2β))·L₁₂(F_τ) + (1/2)·𝔽K(F_τ)`.
-/

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXT0.RXJets

set_option autoImplicit false
set_option maxHeartbeats 3800000

open Work.FTS_RegExport.RXT (v2_PhiT v2_PhiStar v2_PhiPert)

/-- **The `bR` conjunct of `coeffJetsJointCont`.** -/
theorem coeffbR {α C₀ Ce Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (H : CJHyps α C₀ Ce Cs Φs E g) :
    ∀ S > 0, ∀ k l : ℕ, k + l ≤ 2 →
      ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed k l
        (fun z θ => Work.FTS.RegExportIface.RXT.bR α Φs E g z θ p.2.2) p.1 p.2.1)
        (Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S)) := by
  have hα := H.hα
  have hα13 := H.hα13
  have hEL3 := H.hEL3
  have hStar := H.hStar
  have hOK := H.hOK
  obtain ⟨hMixedConst, hConstCont, hCdC2m, hCdSinsq, hDthAng, hRadialCont, hRadAngCont⟩ :=
    Work.FTS_RegExport.RXT0.RXJets.jetBasic
  have hStar3 := CJHyps.hStar3 H
  have hStar1 := CJHyps.hStar1 H
  have hPert3 := CJHyps.hPert3 H
  have hPert1g := CJHyps.hPert1g H
  have hagQ := CJHyps.hagQ H
  have hSliceFun := CJHyps.hSliceFun H
  intro S hS k l hkl
  have hk2 : k ≤ 2 := by omega
  have hl2 : l ≤ 2 := by omega
  have hResC3 := CJHyps.hResC3 H S
  have hRegR := CJHyps.hRegR H S
  have hderL12 := CJHyps.hderL12 H S
  have hdzd := CJHyps.hdzd H S hS
  obtain ⟨hStarVop, hStarRop, hStarUdiv⟩ := CJHyps.hStarSlots H S k l hkl
  refine ContinuousOn.congr (f := fun p : ℝ × ℝ × ℝ =>
      Work.Spaces.mixed k l (fun z θ => (2 : ℝ) * (Work.Construction.Uop
          (Work.FTS.Regularity.pExp α) (v2_PhiStar α Φs) z θ / Real.sin (2 * θ))) p.1 p.2.1
      + Work.Spaces.mixed k l (fun z θ => (2 : ℝ) * (Work.Construction.Uop
          (Work.FTS.Regularity.pExp α) (v2_PhiPert α E g p.2.2) z θ
          / Real.sin (2 * θ))) p.1 p.2.1
      + Work.Spaces.mixed k l (fun z θ => (2 : ℝ) * (Work.Construction.Uop
          (Work.FTS.Regularity.pExp α) (Work.Construction.Theta (Work.FTS.Regularity.pExp α)
            (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) p.2.2)) z θ
          / Real.sin (2 * θ))) p.1 p.2.1) ?_ ?_
  · have hQ0 : ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed k l
          (fun z θ => (2 : ℝ) * (Work.Construction.Uop (Work.FTS.Regularity.pExp α)
            (v2_PhiStar α Φs) z θ / Real.sin (2 * θ))) p.1 p.2.1)
          (Work.FTS_RegExport.RXT0.RXJets.slb S) :=
        (hStarUdiv.const_mul 2).congr (fun p hp => by
          rw [Work.FTS_RegExport.RXT.Sys.coeff_mixed_const_mul])
    have hQ1 : ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed k l
          (fun z θ => (2 : ℝ) * (Work.Construction.Uop (Work.FTS.Regularity.pExp α)
            (v2_PhiPert α E g p.2.2) z θ / Real.sin (2 * θ))) p.1 p.2.1)
          (Work.FTS_RegExport.RXT0.RXJets.slb S) :=
        ((H.hSlot S hS k l hkl).2.2.const_mul 2).congr (fun p hp => by
          rw [Work.FTS_RegExport.RXT.Sys.coeff_mixed_const_mul])
    have hQ2 : ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed k l
          (fun z θ => (2 : ℝ) * (Work.Construction.Uop (Work.FTS.Regularity.pExp α)
            (Work.Construction.Theta (Work.FTS.Regularity.pExp α)
              (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) p.2.2)) z θ / Real.sin (2 * θ)))
          p.1 p.2.1) (Work.FTS_RegExport.RXT0.RXJets.slb S) := by
      have hsum := (hRadialCont (c := (2 : ℝ) * (-(3 / (4 * Work.FTS.Regularity.pExp α))))
            (a := fun z τ => Work.Construction.L12 (Work.Construction.Ftau
              (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) z)
            (hdzd k hk2).1 hkl).add
          (hRadialCont (c := (2 : ℝ) * (1 / 4))
            (a := fun z τ => Work.Construction.FK (Work.Construction.Ftau
              (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) z)
            (hdzd k hk2).2 hkl)
      refine hsum.congr (fun p hp => ?_)
      obtain ⟨hz, hθ, hθ2, hτ0, hτS⟩ := mem_slb.mp hp
      have hzθ : (p.1, p.2.1) ∈ Work.FTS.EllipticEst.Q0 := ⟨hz, hθ, hθ2⟩
      show Work.Spaces.mixed k l (fun z θ => (2 : ℝ) * (Work.Construction.Uop
            (Work.FTS.Regularity.pExp α) (Work.Construction.Theta (Work.FTS.Regularity.pExp α)
              (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) p.2.2)) z θ
            / Real.sin (2 * θ))) p.1 p.2.1
        = Work.Spaces.mixed k l (fun z θ => ((2 : ℝ)
              * (-(3 / (4 * Work.FTS.Regularity.pExp α))))
              * Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z) p.1 p.2.1
          + Work.Spaces.mixed k l (fun z θ => ((2 : ℝ) * (1 / 4))
              * Work.Construction.FK (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z) p.1 p.2.1
      have hL2s : ContDiffOn ℝ 2 (Function.uncurry (fun z θ => ((2 : ℝ)
            * (-(3 / (4 * Work.FTS.Regularity.pExp α))))
            * Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z)) Work.FTS.EllipticEst.Q0 :=
        (contDiffOn_const (c := (2 : ℝ) * (-(3 / (4 * Work.FTS.Regularity.pExp α))))).mul
          (Work.FTS_RegExport.RXT.contDiffOn_slice_fst (hRegR p.2.2 ⟨hτ0, hτS⟩).1)
      have hF2s : ContDiffOn ℝ 2 (Function.uncurry (fun z θ => ((2 : ℝ) * (1 / 4))
            * Work.Construction.FK (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z)) Work.FTS.EllipticEst.Q0 :=
        (contDiffOn_const (c := (2 : ℝ) * (1 / 4))).mul
          (Work.FTS_RegExport.RXT.contDiffOn_slice_fst (hRegR p.2.2 ⟨hτ0, hτS⟩).2)
      have hcl : Set.EqOn (Function.uncurry (fun z θ => (2 : ℝ) * (Work.Construction.Uop
            (Work.FTS.Regularity.pExp α) (Work.Construction.Theta (Work.FTS.Regularity.pExp α)
              (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) p.2.2)) z θ / Real.sin (2 * θ))))
          (Function.uncurry (fun z θ => ((2 : ℝ)
              * (-(3 / (4 * Work.FTS.Regularity.pExp α))))
              * Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z
            + ((2 : ℝ) * (1 / 4)) * Work.Construction.FK (Work.Construction.Ftau
                (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z))
          Work.FTS.EllipticEst.Q0 := by
        intro q hq
        obtain ⟨hz', hθ', hθ2'⟩ := Work.FTS.EllipticEst.mem_Q0.mp hq
        simp only [Function.uncurry]
        rw [Work.FTS_RegExport.RXT.Sys.Uop_Theta_div (Work.FTS.Regularity.pExp_pos hα)
          hz' hθ' hθ2' (hderL12 p.2.2 ⟨hτ0, hτS⟩ q.1 hz')]
        ring
      have hstep : Work.Spaces.mixed k l (fun z θ => ((2 : ℝ)
              * (-(3 / (4 * Work.FTS.Regularity.pExp α))))
              * Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z
            + ((2 : ℝ) * (1 / 4)) * Work.Construction.FK (Work.Construction.Ftau
                (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z)
            p.1 p.2.1
          = Work.Spaces.mixed k l (fun z θ => ((2 : ℝ)
              * (-(3 / (4 * Work.FTS.Regularity.pExp α))))
              * Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z) p.1 p.2.1
            + Work.Spaces.mixed k l (fun z θ => ((2 : ℝ) * (1 / 4))
              * Work.Construction.FK (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z) p.1 p.2.1 :=
        Work.FTS_RegExport.RXT.Sys.mixed_add_lam hL2s hF2s hkl hzθ
      rw [Work.FTS_EllLimOK.mixed_congr_of_eqOn_isOpen Work.FTS.EllipticEst.isOpen_Q0 hcl
        hzθ k l, hstep]
    exact (hQ0.add hQ1).add hQ2
  · intro p hp
    show Work.Spaces.mixed k l (fun z θ =>
          Work.FTS.RegExportIface.RXT.bR α Φs E g z θ p.2.2) p.1 p.2.1
        = Work.Spaces.mixed k l (fun z θ => (2 : ℝ) * (Work.Construction.Uop
            (Work.FTS.Regularity.pExp α) (v2_PhiStar α Φs) z θ / Real.sin (2 * θ))) p.1 p.2.1
          + Work.Spaces.mixed k l (fun z θ => (2 : ℝ) * (Work.Construction.Uop
              (Work.FTS.Regularity.pExp α) (v2_PhiPert α E g p.2.2) z θ
              / Real.sin (2 * θ))) p.1 p.2.1
          + Work.Spaces.mixed k l (fun z θ => (2 : ℝ) * (Work.Construction.Uop
              (Work.FTS.Regularity.pExp α) (Work.Construction.Theta (Work.FTS.Regularity.pExp α)
                (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                  (Work.FTS.RegExportIface.RXT.GR α g) p.2.2)) z θ
              / Real.sin (2 * θ))) p.1 p.2.1
    obtain ⟨hz, hθ, hθ2, hτ0, hτS⟩ := mem_slb.mp hp
    have hzθ : (p.1, p.2.1) ∈ Work.FTS.EllipticEst.Q0 := ⟨hz, hθ, hθ2⟩
    have hag := hagQ p.2.2 hτ0
    have hP1 := hPert1g p.2.2 hτ0
    have hV2C1 : ContDiffOn ℝ 1 (Function.uncurry (v2_PhiT α Φs E g p.2.2))
        Work.FTS.EllipticEst.Q0 := (hResC3 p.2.2 ⟨hτ0, hτS⟩).1.of_le (by norm_num)
    have hThC1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Construction.Theta
        (Work.FTS.Regularity.pExp α) (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) p.2.2))) Work.FTS.EllipticEst.Q0 :=
      (hResC3 p.2.2 ⟨hτ0, hτS⟩).2.of_le (by norm_num)
    have hQ2c : ContDiffOn ℝ 2 (Function.uncurry (fun z θ => (2 : ℝ)
          * (Work.Construction.Uop (Work.FTS.Regularity.pExp α) (Work.Construction.Theta
              (Work.FTS.Regularity.pExp α) (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) p.2.2)) z θ / Real.sin (2 * θ))))
        Work.FTS.EllipticEst.Q0 :=
      (contDiffOn_const (c := (2 : ℝ))).mul
        (Work.FTS_RegExport.RXT.contDiffOn_uncurry_div_sin_two
          (Work.FTS_RegExport.RXT.contDiffOn_uncurry_Uop (hResC3 p.2.2 ⟨hτ0, hτS⟩).2))
    have hsplit : Set.EqOn (Function.uncurry (fun z θ =>
          Work.FTS.RegExportIface.RXT.bR α Φs E g z θ p.2.2))
        (Function.uncurry (fun z θ => ((2 : ℝ) * (Work.Construction.Uop
              (Work.FTS.Regularity.pExp α) (v2_PhiStar α Φs) z θ / Real.sin (2 * θ))
            + (2 : ℝ) * (Work.Construction.Uop (Work.FTS.Regularity.pExp α)
                (v2_PhiPert α E g p.2.2) z θ / Real.sin (2 * θ)))
          + (2 : ℝ) * (Work.Construction.Uop (Work.FTS.Regularity.pExp α)
              (Work.Construction.Theta (Work.FTS.Regularity.pExp α)
                (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                  (Work.FTS.RegExportIface.RXT.GR α g) p.2.2)) z θ / Real.sin (2 * θ))))
        Work.FTS.EllipticEst.Q0 := by
      intro q hq
      obtain ⟨hz', hθ', hθ2'⟩ := Work.FTS.EllipticEst.mem_Q0.mp hq
      simp only [Function.uncurry]
      have hUc := Work.FTS_RegExport.RXR5.Uop_congr_of_agreeOnQ
        (α := Work.FTS.Regularity.pExp α) hag hz' hθ' hθ2'
      have hSplit1 : Work.Construction.Uop (Work.FTS.Regularity.pExp α)
            (fun z θ => v2_PhiT α Φs E g p.2.2 z θ + Work.Construction.Theta
              (Work.FTS.Regularity.pExp α) (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) p.2.2) z θ) q.1 q.2
            / Real.sin (2 * q.2)
          = Work.Construction.Uop (Work.FTS.Regularity.pExp α) (v2_PhiT α Φs E g p.2.2) q.1 q.2
              / Real.sin (2 * q.2)
            + Work.Construction.Uop (Work.FTS.Regularity.pExp α) (Work.Construction.Theta
                (Work.FTS.Regularity.pExp α) (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                  (Work.FTS.RegExportIface.RXT.GR α g) p.2.2)) q.1 q.2
              / Real.sin (2 * q.2) :=
        Work.FTS_RegExport.RXT.v2_uop_div_add_at hV2C1 hThC1 ⟨hz', hθ', hθ2'⟩
      have hUa : Work.Construction.Uop (Work.FTS.Regularity.pExp α)
            (v2_PhiStar α Φs + v2_PhiPert α E g p.2.2) q.1 q.2 / Real.sin (2 * q.2)
          = Work.Construction.Uop (Work.FTS.Regularity.pExp α) (v2_PhiStar α Φs) q.1 q.2
              / Real.sin (2 * q.2)
            + Work.Construction.Uop (Work.FTS.Regularity.pExp α) (v2_PhiPert α E g p.2.2)
                q.1 q.2 / Real.sin (2 * q.2) :=
        Work.FTS_RegExport.RXT.v2_uop_div_add_at hStar1 hP1 ⟨hz', hθ', hθ2'⟩
      rw [show Work.FTS.RegExportIface.RXT.bR α Φs E g q.1 q.2 p.2.2
          = (2 * Work.Construction.Uop (Work.FTS.Regularity.pExp α)
              (Work.FTS.Galerkin.slice (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) p.2.2)
              q.1 q.2) / Real.sin (2 * q.2) from rfl]
      rw [mul_div_assoc]
      rw [hSliceFun p.2.2, hSplit1, hUc, hUa]
      ring
    have hQ0c : ContDiffOn ℝ 2 (Function.uncurry (fun z θ => (2 : ℝ)
          * (Work.Construction.Uop (Work.FTS.Regularity.pExp α) (v2_PhiStar α Φs) z θ
            / Real.sin (2 * θ)))) Work.FTS.EllipticEst.Q0 :=
      (contDiffOn_const (c := (2 : ℝ))).mul
        (Work.FTS_RegExport.RXT.contDiffOn_uncurry_div_sin_two
          (Work.FTS_RegExport.RXT.contDiffOn_uncurry_Uop hStar3))
    have hQ1c : ContDiffOn ℝ 2 (Function.uncurry (fun z θ => (2 : ℝ)
          * (Work.Construction.Uop (Work.FTS.Regularity.pExp α) (v2_PhiPert α E g p.2.2) z θ
            / Real.sin (2 * θ)))) Work.FTS.EllipticEst.Q0 :=
      (contDiffOn_const (c := (2 : ℝ))).mul
        (Work.FTS_RegExport.RXT.contDiffOn_uncurry_div_sin_two
          (Work.FTS_RegExport.RXT.contDiffOn_uncurry_Uop (hPert3 p.2.2 hτ0)))
    have hstepA : Work.Spaces.mixed k l (fun z θ =>
          ((2 : ℝ) * (Work.Construction.Uop (Work.FTS.Regularity.pExp α) (v2_PhiStar α Φs) z θ
              / Real.sin (2 * θ))
            + (2 : ℝ) * (Work.Construction.Uop (Work.FTS.Regularity.pExp α)
                (v2_PhiPert α E g p.2.2) z θ / Real.sin (2 * θ)))
          + (2 : ℝ) * (Work.Construction.Uop (Work.FTS.Regularity.pExp α)
              (Work.Construction.Theta (Work.FTS.Regularity.pExp α)
                (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                  (Work.FTS.RegExportIface.RXT.GR α g) p.2.2)) z θ / Real.sin (2 * θ)))
          p.1 p.2.1
        = Work.Spaces.mixed k l (fun z θ =>
            (2 : ℝ) * (Work.Construction.Uop (Work.FTS.Regularity.pExp α) (v2_PhiStar α Φs) z θ
              / Real.sin (2 * θ))
            + (2 : ℝ) * (Work.Construction.Uop (Work.FTS.Regularity.pExp α)
                (v2_PhiPert α E g p.2.2) z θ / Real.sin (2 * θ))) p.1 p.2.1
          + Work.Spaces.mixed k l (fun z θ => (2 : ℝ) * (Work.Construction.Uop
              (Work.FTS.Regularity.pExp α) (Work.Construction.Theta (Work.FTS.Regularity.pExp α)
                (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                  (Work.FTS.RegExportIface.RXT.GR α g) p.2.2)) z θ / Real.sin (2 * θ)))
            p.1 p.2.1 :=
      Work.FTS_RegExport.RXT.Sys.mixed_add_lam
        (f := fun z θ =>
            (2 : ℝ) * (Work.Construction.Uop (Work.FTS.Regularity.pExp α) (v2_PhiStar α Φs) z θ
              / Real.sin (2 * θ))
            + (2 : ℝ) * (Work.Construction.Uop (Work.FTS.Regularity.pExp α)
                (v2_PhiPert α E g p.2.2) z θ / Real.sin (2 * θ)))
        (h := fun z θ => (2 : ℝ) * (Work.Construction.Uop (Work.FTS.Regularity.pExp α)
            (Work.Construction.Theta (Work.FTS.Regularity.pExp α)
              (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
                (Work.FTS.RegExportIface.RXT.GR α g) p.2.2)) z θ / Real.sin (2 * θ)))
        (hQ0c.add hQ1c) hQ2c hkl hzθ
    have hstepB : Work.Spaces.mixed k l (fun z θ =>
            (2 : ℝ) * (Work.Construction.Uop (Work.FTS.Regularity.pExp α) (v2_PhiStar α Φs) z θ
              / Real.sin (2 * θ))
            + (2 : ℝ) * (Work.Construction.Uop (Work.FTS.Regularity.pExp α)
                (v2_PhiPert α E g p.2.2) z θ / Real.sin (2 * θ))) p.1 p.2.1
        = Work.Spaces.mixed k l (fun z θ => (2 : ℝ) * (Work.Construction.Uop
            (Work.FTS.Regularity.pExp α) (v2_PhiStar α Φs) z θ / Real.sin (2 * θ))) p.1 p.2.1
          + Work.Spaces.mixed k l (fun z θ => (2 : ℝ) * (Work.Construction.Uop
              (Work.FTS.Regularity.pExp α) (v2_PhiPert α E g p.2.2) z θ
              / Real.sin (2 * θ))) p.1 p.2.1 :=
      Work.FTS_RegExport.RXT.Sys.mixed_add_lam
        (f := fun z θ => (2 : ℝ) * (Work.Construction.Uop (Work.FTS.Regularity.pExp α)
            (v2_PhiStar α Φs) z θ / Real.sin (2 * θ)))
        (h := fun z θ => (2 : ℝ) * (Work.Construction.Uop (Work.FTS.Regularity.pExp α)
            (v2_PhiPert α E g p.2.2) z θ / Real.sin (2 * θ)))
        hQ0c hQ1c hkl hzθ
    rw [Work.FTS_EllLimOK.mixed_congr_of_eqOn_isOpen Work.FTS.EllipticEst.isOpen_Q0 hsplit
      hzθ k l, hstepA, hstepB]

end Work.FTS_RegExport.RXT0.RXJets
