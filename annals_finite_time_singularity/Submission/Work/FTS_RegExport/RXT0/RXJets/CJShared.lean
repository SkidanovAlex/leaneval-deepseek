import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_RegExport.RXT0.RXJets.slabDefs
import Submission.Work.FTS_RegExport.RXT0.RXJets.CJDefs
import Submission.Work.FTS_RegExport.RXT0.RXJets.starSlots
import Submission.Work.FTS_RegExport.RXT.Sys.CoeffSmooth
import Submission.Work.FTS_RegExport.RXT.Sys.pert_tilde_contDiffOn
import Submission.Work.FTS_RegExport.RXT.Sys.L12FK_family_jets
import Submission.Work.FTS_RegExport.RXT.C2Radial
import Submission.Work.FTS_RegExport.RXT.contDiffOn_two_integral_Itheta
import Submission.Work.FTS_RegExport.RXT.velVanish2Aux
import Submission.Work.FTS.PhiStar.CoreAux.fields_smooth

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT0.RXJets.CJShared` — the common facts about `CJHyps`

The `(z,θ)`-regularity of the star residual, the perturbation residual, `L₁₂(F_τ)`, `𝔽K(F_τ)`,
the split identity `Φ̃_τ = Φ̃_* + Ξ_τ` on the open quadrant, the clock `μR`, `hL12` in the
`DzdIter` shape, and the three star-slot jet continuities.  Everything is a theorem about the
hypothesis bundle `CJHyps`, so the three coefficient modules and the statement file share it.
-/

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXT0.RXJets

set_option autoImplicit false

open Work.FTS_RegExport.RXT (v2_PhiT v2_PhiStar v2_PhiPert v2_phiTil_split)

variable {α C₀ Ce Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
  {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}

/-- The star residual is `C³` on the open quadrant. -/
theorem CJHyps.hStar3 (H : CJHyps α C₀ Ce Cs Φs E g) :
    ContDiffOn ℝ 3 (Function.uncurry (v2_PhiStar α Φs)) Work.FTS.EllipticEst.Q0 := by
  have hαG : (0 : ℝ) < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos H.hα
  have hαG1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one H.hα13
  exact (Work.FTS.PhiStar.CoreAux.fields_smooth hαG hαG1 H.hStar.smooth).1.of_le
    (by simp [Work.Stability.smoothOrder])

theorem CJHyps.hStar1 (H : CJHyps α C₀ Ce Cs Φs E g) :
    ContDiffOn ℝ 1 (Function.uncurry (v2_PhiStar α Φs)) Work.FTS.EllipticEst.Q0 :=
  H.hStar3.of_le (by norm_num)

/-- The perturbation residual is `C³` on the open quadrant at every `τ ≥ 0`. -/
theorem CJHyps.hPert3 (H : CJHyps α C₀ Ce Cs Φs E g) :
    ∀ τ : ℝ, 0 ≤ τ → ContDiffOn ℝ 3 (Function.uncurry (v2_PhiPert α E g τ))
      Work.FTS.EllipticEst.Q0 := by
  intro τ hτ
  exact (Work.FTS_RegExport.RXT.Sys.pert_tilde_contDiffOn H.hα H.hα13 H.hEL3 H.hOK τ hτ).congr
    (fun q _ => rfl)

theorem CJHyps.hPert1g (H : CJHyps α C₀ Ce Cs Φs E g) :
    ∀ τ : ℝ, 0 ≤ τ → ContDiffOn ℝ 1 (Function.uncurry (v2_PhiPert α E g τ))
      Work.FTS.EllipticEst.Q0 :=
  fun τ hτ => (H.hPert3 τ hτ).of_le (by norm_num)

/-- `Φ̃_τ = Φ̃_* + Ξ_τ` on the open quadrant. -/
theorem CJHyps.hagQ (H : CJHyps α C₀ Ce Cs Φs E g) :
    ∀ τ : ℝ, 0 ≤ τ → Work.FTS_RegExport.RXR5.AgreeOnQ (v2_PhiT α Φs E g τ)
      (v2_PhiStar α Φs + v2_PhiPert α E g τ) := fun τ hτ z θ hz hθ hθ2 => by
  simp only [Pi.add_apply]
  exact v2_phiTil_split (C₀ := C₀) H.hα H.hα13 H.hOK hτ z θ ⟨hz, hθ, hθ2⟩

/-- `slice (ΦR) τ = Φ̃_τ + Θ(F_τ)` as functions. -/
theorem CJHyps.hSliceFun (H : CJHyps α C₀ Ce Cs Φs E g) (τ : ℝ) :
    Work.FTS.Galerkin.slice (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ
      = fun z θ => v2_PhiT α Φs E g τ z θ + Work.Construction.Theta (Work.FTS.Regularity.pExp α)
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) τ) z θ := by
  funext z θ
  simp only [Work.FTS.Galerkin.slice, v2_PhiT, Work.Construction.PhiTil]
  ring

/-- `Φ̃_τ` and `Θ(F_τ)` are `C³` on the open quadrant, uniformly on `[0,S]`. -/
theorem CJHyps.hResC3 (H : CJHyps α C₀ Ce Cs Φs E g) (S : ℝ) :
    ∀ τ ∈ Set.Icc (0:ℝ) S,
      ContDiffOn ℝ 3 (Function.uncurry (v2_PhiT α Φs E g τ)) Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 3 (Function.uncurry (Work.Construction.Theta (Work.FTS.Regularity.pExp α)
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) τ))) Work.FTS.EllipticEst.Q0 := by
  intro τ hτ
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h12, h13⟩ :=
    Work.FTS_RegExport.RXT.Sys.coeff_pieces_contDiffOn (τ := τ) H.hα H.hα13 H.hEL3 H.hStar
      H.hOK hτ.1
  exact ⟨h12, h13⟩

/-- `L₁₂(F_τ)` and `𝔽K(F_τ)` are `C²` on `(0,∞)`. -/
theorem CJHyps.hRegR (H : CJHyps α C₀ Ce Cs Φs E g) (S : ℝ) :
    ∀ τ ∈ Set.Icc (0:ℝ) S,
      ContDiffOn ℝ 2 (Work.Construction.L12 (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ)) (Set.Ioi 0) ∧
      ContDiffOn ℝ 2 (Work.Construction.FK (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ)) (Set.Ioi 0) := by
  intro τ hτ
  have hF2 := Work.FTS_RegExport.RXT.contDiffOn_Ftau_Q0 (C₀ := C₀) H.hα H.hα13 H.hOK τ hτ.1
  obtain ⟨Cf, hCf0, hbd⟩ := Work.FTS_RegExport.RXT.Ftau_bounds (C₀ := C₀) H.hα H.hα13 H.hOK τ hτ.1
  have hFK2 : ContDiffOn ℝ 2 (Work.Construction.FK (Work.Construction.Ftau
      (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ)) (Set.Ioi 0) :=
    Work.FTS_RegExport.RXT.contDiffOn_two_integral_Itheta (φ := Work.Spaces.K)
      Work.FTS_RegExport.RXT.Sys.sys_continuousOn_K_Iθ hF2
      (fun z θ hz hθ hθ2 => ⟨(hbd z θ hz hθ hθ2).1, (hbd z θ hz hθ hθ2).2.1,
        (hbd z θ hz hθ hθ2).2.2⟩)
  exact ⟨(Work.FTS_RegExport.RXT.contDiffOn_three_L12 hFK2).of_le (by norm_num), hFK2⟩

/-- `z ∂_z L₁₂(F_τ) = -𝔽K(F_τ)`. -/
theorem CJHyps.hderL12 (H : CJHyps α C₀ Ce Cs Φs E g) (S : ℝ) :
    ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z : ℝ, 0 < z →
      HasDerivAt (fun z' => Work.Construction.L12 (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) z')
        (-(Work.Construction.FK (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) τ) z) / z) z := by
  obtain ⟨CF, hCF0, -, -, hL12der, -, -⟩ :=
    Work.FTS_RegExport.RXT.Sys.L12FK_family_jets (C₀ := C₀) (Φs := Φs) (E := E) (g := g)
      H.hα H.hα13 H.hOK.2 (max S 1) (lt_max_of_lt_right zero_lt_one)
  intro τ hτ z hz
  have hτ' : τ ∈ Set.Icc (0:ℝ) (max S 1) := ⟨hτ.1, le_trans hτ.2 (le_max_left S 1)⟩
  have h0 := hL12der τ hτ' z hz
  have h2 : Work.Spaces.DzIter 1 (fun z _ => Work.Construction.L12 (Work.Construction.Ftau
      (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) z) z 0
      = z * deriv (fun z'' => Work.Construction.L12 (Work.Construction.Ftau
          (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) z'') z := by
    rw [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero]; rfl
  rw [h2] at h0
  have hd : deriv (fun z' => Work.Construction.L12 (Work.Construction.Ftau
      (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) z') z
      = -(Work.Construction.FK (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) τ) z) / z := by
    rw [eq_div_iff (ne_of_gt hz)]
    rw [mul_comm]
    exact h0
  have hdiff : DifferentiableAt ℝ (fun z' => Work.Construction.L12 (Work.Construction.Ftau
      (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) z') z :=
    ((H.hRegR S τ hτ).1.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds hz)
  rw [← hd]
  exact hdiff.hasDerivAt

/-- `hL12` in the `DzdIter` shape. -/
theorem CJHyps.hdzd (H : CJHyps α C₀ Ce Cs Φs E g) (S : ℝ) (hS : 0 < S) :
    ∀ j : ℕ, j ≤ 2 →
      ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.DzdIter j
        (fun z => Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) p.2) z) p.1)
        (Set.Ioi (0:ℝ) ×ˢ Set.Icc (0:ℝ) S) ∧
      ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.DzdIter j
        (fun z => Work.Construction.FK (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) p.2) z) p.1)
        (Set.Ioi (0:ℝ) ×ˢ Set.Icc (0:ℝ) S) := by
  intro j hj
  obtain ⟨h1, h2⟩ := H.hL12 S hS j hj
  exact ⟨h1.congr (fun p hp => (Work.Elliptic.DzIter_rad _ j p.1 0).symm),
         h2.congr (fun p hp => (Work.Elliptic.DzIter_rad _ j p.1 0).symm)⟩

/-- The clock `μR` is continuous on `[0,S]`. -/
theorem CJHyps.hμRc (H : CJHyps α C₀ Ce Cs Φs E g) (S : ℝ) :
    ContinuousOn (fun τ : ℝ => Work.FTS.RegExportIface.RXT.μR α Φs E g τ) (Set.Icc (0:ℝ) S) := by
  have hμRc' : ContinuousOn (fun τ : ℝ => Work.FTS.RegExportIface.RXT.μR α Φs E g τ)
      (Set.Ici 0) := by
    refine H.hμ.2.congr (fun τ hτ => ?_)
    show Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α)
        (Work.FTS.Nonlin.PsiCan Φs E g) g (max τ 0)
      = Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α)
        (Work.FTS.Nonlin.PsiCan Φs E g) g τ
    rw [max_eq_left (show (0 : ℝ) ≤ τ from hτ)]
  exact hμRc'.mono (fun τ hτ => hτ.1)

/-- The three star-slot jet continuities. -/
theorem CJHyps.hStarSlots (H : CJHyps α C₀ Ce Cs Φs E g) (S : ℝ) (k l : ℕ) (hkl : k + l ≤ 2) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed k l
        (fun z θ => Work.Construction.Vop (v2_PhiStar α Φs) z θ) p.1 p.2.1) (slb S) ∧
      ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed k l
        (fun z θ => Work.Construction.Rop (Work.FTS.Regularity.pExp α)
          (v2_PhiStar α Φs) z θ) p.1 p.2.1) (slb S) ∧
      ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed k l
        (fun z θ => Work.Construction.Uop (Work.FTS.Regularity.pExp α)
          (v2_PhiStar α Φs) z θ / Real.sin (2 * θ)) p.1 p.2.1) (slb S) :=
  Work.FTS_RegExport.RXT0.RXJets.starSlots H.hα H.hα13 H.hStar S k l hkl

end Work.FTS_RegExport.RXT0.RXJets
