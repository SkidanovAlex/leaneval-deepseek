import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.RegExportIface.Defs
import Submission.Work.FTS_RegExport.RXR7.Defs
import Submission.Work.FTS_RegExport.RXR7.r7Init
import Submission.Work.FTS_RegExport.RXR7.r7HEq
import Submission.Work.FTS_RegExport.RXR7.r7VelLip
import Submission.Work.FTS_RegExport.RXR7.r7Joint

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXR7

open scoped Real Topology NNReal
open Set Filter
open Work.FTS.Galerkin (Fn Fam slice IsDynGSolWith)
open Work.FTS.Nonlin (PsiCan)
open Work.FTS.Regularity (pExp Jet)
open Work.FTS.RegPkgGal (extG RegPkg' St1Class R5Parts Avort Bdyn)
open Work.FTS.FinalV2 (gS tauExt LimApprox DynOK' EllLimOK3 Sol)
open Work.FTS.RegExportIface

variable {α C₀ Cs : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn}

/-- **RX-R7, re-proved 2026-10-11** for the repaired `VelPkg` (open-θ + `thLip`) and the
edge-extended coefficients `edgeExt Vz7`, `Vθ7`, `edgeExt cs7` (`cbc/fts_velpkg_fix.md` + REVIEW):
`r7Init` (`hInit`, `Lz7`), `r7HEq` (`hEq`), `r7Joint` (`hFjoint`), `r7VelLip` (`hVlipU`) on the open
quadrant, and `RegExportIface.R7Block_edgeExt` (the engine of `R7Block_of_velPkgF`) for the
closed-box `hVjoint`/`hcscont`. The constants `a = b = c = max M 0` come from `bnd` at horizon 1,
which is `S`-free, so they are uniform in `S`. -/
theorem r7Block_proved (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {g : Fam} (hSol : Sol (pExp α) Φs E g) (hOK : DynOK' (pExp α) C₀ Φs E g)
    (hdat : ∃ L β : ℝ, 1 ≤ L ∧ ∀ z θ, g z θ 0 = Work.FTS.LocData6.locG6 (pExp α) L β z θ)
    (hμ : ClockBd α Φs E g)
    (hVP : ∀ S > 0, VelPkg (pExp α) (Work.FTS.Final.maxMu (pExp α) (PsiCan Φs E g) g)
      (gS α (tauExt g)) (psiR α Φs E (tauExt g)) S) :
    ∃ a b c Lz7 : ℝ, ∀ S > 0, R7Block α S (gS α (tauExt g))
      (edgeExt (Vz7 (pExp α) (Work.FTS.Final.maxMu (pExp α) (PsiCan Φs E g) g) (gS α (tauExt g))
        (psiR α Φs E (tauExt g))))
      (Vθ7 (pExp α) (psiR α Φs E (tauExt g)))
      (edgeExt (cs7 (pExp α) (Work.FTS.Final.maxMu (pExp α) (PsiCan Φs E g) g) (gS α (tauExt g))
        (psiR α Φs E (tauExt g))))
      a b c Lz7 := by
  -- 1. the initial support radius of the profile (the `hInit` field), and the `Lz7` of the block
  obtain ⟨Lz7, hLz7pos, hInit⟩ := r7Init (α := α) (g := g) hdat
  -- 2. a fake-time-uniform bound `M` on the three coefficients: `bnd` does not mention `S`
  obtain ⟨M, hbnd⟩ := (hVP 1 one_pos).bnd
  have hpi : (0:ℝ) < Real.pi / 4 ∧ Real.pi / 4 < Real.pi / 2 :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hMnn : 0 ≤ M :=
    le_trans (abs_nonneg _) ((hbnd 1 (Real.pi / 4) 0 one_pos hpi.1 hpi.2 le_rfl).1)
  have hMle : M ≤ max M 0 := le_max_left _ _
  have h0le : (0 : ℝ) ≤ max M 0 := le_max_right _ _
  refine ⟨max M 0, max M 0, max M 0, Lz7, fun S hS => ?_⟩
  have hEq := r7HEq (α := α) (C₀ := C₀) (Φs := Φs) (E := E) (g := g)
    hS hα hα13 hSol hOK hμ hVP
  have hVPS := hVP S hS
  have hcont := hVPS.cont
  refine R7Block_edgeExt (M := M)
    (r7Joint (α := α) (C₀ := C₀) (Φs := Φs) (E := E) (g := g) hS hα hα13 hSol hOK hμ hVP hEq)
    (ContinuousOn.prodMk (continuous_fst.comp_continuousOn hcont)
      ((continuous_fst.comp continuous_snd).comp_continuousOn hcont))
    ((continuous_snd.comp continuous_snd).comp_continuousOn hcont)
    hVPS.thHol
    (fun z θ τ hz h0 h1 hτ => (hbnd z θ τ hz h0 h1 hτ.1).2.1)
    (fun z τ hz hτ => hVPS.vth_ends z τ hz hτ.1)
    (r7VelLip (α := α) (C₀ := C₀) (Φs := Φs) (E := E) (g := g)
      hS hLz7pos hα hα13 hSol hOK hμ hVP)
    hEq
    (fun z θ τ hz h0 h1 hτ _ => hVPS.vz0 z θ τ hz h0 h1 hτ.le)
    (fun z θ τ hz h0 h1 hτ _ =>
      le_trans (le_trans (le_abs_self _) (hbnd z θ τ hz h0 h1 hτ.le).1) hMle)
    (fun z θ τ hz h0 h1 hτ _ => by
      have h1' := (hbnd z θ τ hz h0 h1 hτ.le).2.1
      have h4 : M * Real.sin (2 * θ) ≤ M := by
        simpa using mul_le_mul_of_nonneg_left (Real.sin_le_one (2 * θ)) hMnn
      exact le_trans (le_trans h1' h4) hMle)
    (fun z θ τ hz h0 h1 hτ _ => le_trans (hbnd z θ τ hz h0 h1 hτ.le).2.2 hMle)
    hInit hLz7pos.le h0le h0le h0le

end Work.FTS_RegExport.RXR7
