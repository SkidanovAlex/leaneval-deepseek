import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS_RegExport.VPOpen
import Submission.Work.FTS_RegExport.RXT0.RXJets.coeffJetsJointCont
import Submission.Work.FTS_RegExport.RXT0.RXJets.L12FKJetsJointCont
import Submission.Work.FTS_RegExport.RXT0.slotJetsJointCont
import Submission.Work.FTS_RegExport.RXT.Sys.L12FK_family_jets
import Submission.Work.FTS_RegExport.RXT.SysAux.bR_decomp
import Submission.Work.FTS_RegExport.RXDiag.closedFormOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXVP3

theorem cont_open {α C₀ Ce Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) u →
      Work.FTS.Final.EllPkgGo (Work.FTS.Regularity.pExp α) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp α) 6 Ce u (E u))
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E)
    (hStar : Work.FTS.Final.StarPkgo2 (Work.FTS.Regularity.pExp α) Cs Φs)
    (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hdat : ∃ L β : ℝ, 1 ≤ L ∧ ∀ z θ, g z θ 0 =
      Work.FTS.LocData6.locG6 (Work.FTS.Regularity.pExp α) L β z θ)
    (hμ : Work.FTS.RegExportIface.ClockBd α Φs E g) :
    ∀ S > 0, ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      (Work.FTS.RegExportIface.Vz7 (Work.FTS.Regularity.pExp α)
          (Work.FTS.Final.maxMu (Work.FTS.Regularity.pExp α)
            (Work.FTS.Nonlin.PsiCan Φs E g) g)
          (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g))
          (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g)) p.1 p.2.1 p.2.2,
        Work.FTS.RegExportIface.Vθ7 (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g)) p.1 p.2.1 p.2.2,
        Work.FTS.RegExportIface.cs7 (Work.FTS.Regularity.pExp α)
          (Work.FTS.Final.maxMu (Work.FTS.Regularity.pExp α)
            (Work.FTS.Nonlin.PsiCan Φs E g) g)
          (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g))
          (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g)) p.1 p.2.1 p.2.2))
      (Set.Ioi (0:ℝ) ×ˢ Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S) := by
  -- The three coefficients are the `RXT`-abbreviations `VR`, `bR`, `cR` of the sanitised data
  -- `(gS α (tauExt g), psiR α Φs E (tauExt g))`.
  intro S hS
  have hL12 := Work.FTS_RegExport.RXT0.RXJets.L12FKJetsJointCont (C₀ := C₀) (Φs := Φs) (E := E)
    (g := g) hα hα13 hOK
  have hSlot := Work.FTS_RegExport.RXT0.slotJetsJointCont (C₀ := C₀) (Ce := Ce) (Cs := Cs)
    (Φs := Φs) (E := E) (g := g) hα hα13 hEll hEL3 hSol hOK
  have hcoeff := Work.FTS_RegExport.RXT0.RXJets.coeffJetsJointCont (C₀ := C₀) (Ce := Ce) (Cs := Cs)
    (Φs := Φs) (E := E) (g := g) hα hα13 hEll hEL3 hStar hSol hOK hμ hL12 hSlot
  have h00 := hcoeff S hS 0 0 (by omega)
  have hVz : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      Work.FTS.RegExportIface.Vz7 (Work.FTS.Regularity.pExp α)
        (Work.FTS.Final.maxMu (Work.FTS.Regularity.pExp α) (Work.FTS.Nonlin.PsiCan Φs E g) g)
        (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g))
        (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g)) p.1 p.2.1 p.2.2)
      (Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S)) := by
    simpa only [Work.Spaces.mixed_zero_right, Work.Spaces.DzIter_zero] using h00.1
  have hcs : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      Work.FTS.RegExportIface.cs7 (Work.FTS.Regularity.pExp α)
        (Work.FTS.Final.maxMu (Work.FTS.Regularity.pExp α) (Work.FTS.Nonlin.PsiCan Φs E g) g)
        (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g))
        (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g)) p.1 p.2.1 p.2.2)
      (Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S)) := by
    simpa only [Work.Spaces.mixed_zero_right, Work.Spaces.DzIter_zero] using h00.2.2
  -- `Vθ7 = bR · sin (2θ)` on the open slab (where `sin (2θ) ≠ 0`).
  have hVθ : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      Work.FTS.RegExportIface.Vθ7 (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g)) p.1 p.2.1 p.2.2)
      (Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S)) := by
    have hb : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
        Work.FTS.RegExportIface.RXT.bR α Φs E g p.1 p.2.1 p.2.2)
        (Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S)) := by
      simpa only [Work.Spaces.mixed_zero_right, Work.Spaces.DzIter_zero] using h00.2.1
    have hs : ContinuousOn (fun p : ℝ × ℝ × ℝ => Real.sin (2 * p.2.1))
        (Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S)) :=
      (Real.continuous_sin.comp (continuous_const.mul continuous_snd.fst)).continuousOn
    refine ContinuousOn.congr (hb.mul hs) (fun p hp => ?_)
    obtain ⟨hz, hθ, hτS⟩ := hp
    obtain ⟨hθ0, hθ1⟩ := hθ
    have hsinpos : 0 < Real.sin (2 * p.2.1) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    show Work.FTS.RegExportIface.Vθ7 (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g)) p.1 p.2.1 p.2.2
      = Work.FTS.RegExportIface.RXT.bR α Φs E g p.1 p.2.1 p.2.2 * Real.sin (2 * p.2.1)
    simp only [Work.FTS.RegExportIface.RXT.bR]
    rw [div_mul_cancel₀ _ (ne_of_gt hsinpos)]
  exact hVz.prodMk (hVθ.prodMk hcs)

end Work.FTS_RegExport.RXVP3
