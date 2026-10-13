import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.RegExportIface.Defs
import Submission.Work.FTS_RegExport.RXT0.DtauFinal
import Submission.Work.FTS_RegExport.RXT0.SlabFlat
import Submission.Work.FTS_RegExport.RXT0.RHSJetsJointCont

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT0

open scoped Real Topology NNReal
open Set Filter
open Work.FTS.Galerkin (Fn Fam slice IsDynGSolWith)
open Work.FTS.Nonlin (PsiCan)
open Work.FTS.Regularity (pExp Jet)
open Work.FTS.RegPkgGal (extG St1Class)
open Work.FTS.FinalV2 (gS tauExt LimApprox DynOK' EllLimOK3 Sol)
open Work.FTS.RegExportIface

variable {α C₀ Ce Cs : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn}

theorem dtau_mixed_proved (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC (pExp α) u →
      Work.FTS.Final.EllPkgGo (pExp α) Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK (pExp α) 6 Ce u (E u))
    (hEL3 : EllLimOK3 (pExp α) E) (hStar : Work.FTS.Final.StarPkgo2 (pExp α) Cs Φs)
    {g : Fam} (hSol : Sol (pExp α) Φs E g) (hOK : DynOK' (pExp α) C₀ Φs E g)
    (hμ : ClockBd α Φs E g) :
    ∀ S > 0, ∀ b a : ℕ, a + b ≤ 2 →
      ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed b a (slice g p.2.2) p.1 p.2.1)
        (Set.Ioi (0:ℝ) ×ˢ Set.Ioo (0:ℝ) (π / 2) ×ˢ Set.Icc (0:ℝ) S) ∧
      ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < π / 2 → 0 < τ → τ ≤ S →
        HasDerivAt (fun s => Work.Spaces.mixed b a (slice g s) z θ)
          (Work.Spaces.mixed b a (Work.FTS.Galerkin.gdot g τ) z θ) τ :=
  dtau_mixed_proto (Ce := Ce) (Cs := Cs) (Φs := Φs) (E := E) (g := g)
    hα hα13 hEll hEL3 hStar hSol hOK hμ
    (fun S hS b a hba =>
      RHSJetsJointCont (C₀ := C₀) (Φs := Φs) (E := E) (g := g)
        hα hα13 hEll hEL3 hStar hSol hOK hμ S hS b a hba)
    (fun {S} hS {f} {A} {L} hA hId hd hL => slabC1Flat hS hA hId hd hL)

end Work.FTS_RegExport.RXT0
