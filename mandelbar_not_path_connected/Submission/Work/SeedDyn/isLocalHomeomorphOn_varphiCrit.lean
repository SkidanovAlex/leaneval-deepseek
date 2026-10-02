import Mathlib
import Submission.Work.SeedDyn.Defs
import Submission.Work.Bottcher.CritBottcherExists
import Submission.Work.NAKANE2.IFT.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedDyn

theorem isLocalHomeomorphOn_varphiCrit {c : ℂ} (hc : c ∈ LeanEval.ComplexAnalysis.Mandelbar)
    (h7 : ∀ z ∈ Work.SeedDyn.esc c, deriv (Work.Bottcher.varphiCrit c) z ≠ 0) :
    IsLocalHomeomorphOn (Work.Bottcher.varphiCrit c) (Work.SeedDyn.esc c) := by
  intro z hz
  have hzan : AnalyticAt ℂ (Work.Bottcher.varphiCrit c) z :=
    Work.SeedDyn.analyticOnNhd_varphiCrit_esc hc z hz
  have hsd : HasStrictDerivAt (Work.Bottcher.varphiCrit c)
      (deriv (Work.Bottcher.varphiCrit c) z) z := hzan.hasStrictDerivAt
  have hne : deriv (Work.Bottcher.varphiCrit c) z ≠ 0 := h7 z hz
  have hfd : HasStrictFDerivAt (Work.Bottcher.varphiCrit c)
      ((ContinuousLinearEquiv.unitsEquivAut ℂ) (Units.mk0 (deriv (Work.Bottcher.varphiCrit c) z) hne)
        : ℂ →L[ℂ] ℂ) z :=
    hsd.hasStrictFDerivAt_equiv hne
  refine ⟨HasStrictFDerivAt.toOpenPartialHomeomorph _ hfd, ?_, ?_⟩
  · exact HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source hfd
  · exact (HasStrictFDerivAt.toOpenPartialHomeomorph_coe hfd).symm

end Work.SeedDyn
