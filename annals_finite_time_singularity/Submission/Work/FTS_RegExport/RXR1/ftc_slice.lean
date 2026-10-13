import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.RegExportIface.Defs
import Submission.Work.FTS.RegPkgGal.R5Parts
import Submission.Work.FTS.Galerkin.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS_RegExport.RXR1

theorem ftc_slice {α : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    {θ z k : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hz : 0 < z)
    (hk : k ∈ Set.Icc (0:ℝ) 1)
    (hsol : Work.FTS.Galerkin.IsDynEqOn (Work.FTS.Regularity.pExp α)
      (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g))
      (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)))
    (hcont : ContinuousOn (fun s : ℝ => g z θ s) (Set.Ici 0))
    (hRcont : ContinuousOn (fun s : ℝ => Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α)
        (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) s z θ
      + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g))
        (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) s z θ) (Set.Icc (0:ℝ) 1)) :
    g z θ k - g z θ 0 = ∫ s in (0:ℝ)..k, (Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α)
        (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) s z θ
      + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g))
        (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) s z θ) := by
  have hθ : 0 ≤ θ ∧ θ ≤ Real.pi / 2 := ⟨hθ0.le, hθ1.le⟩
  have hzθ : (z, θ) ∈ Work.Construction.Qd := ⟨hz, hθ0, hθ1⟩
  -- the sanitiser and the right-Taylor extension are invisible on `τ ≥ 0`
  have hEq : ∀ s ∈ Set.Ici (0:ℝ), Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z θ s
      = g z θ s := by
    intro s hs
    rw [Work.FTS.FinalV2.gS, ite_eq_left hz, ite_eq_left hθ]
    exact Work.FTS.FinalV2.tauExt_of_nonneg g hs
  -- the one-sided equation of the datum, transferred to `g` itself
  have hderiv : ∀ x ∈ Set.Ioo (0:ℝ) k,
      HasDerivAt (fun s => g z θ s)
        (Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α)
            (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) x z θ
          + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g))
            (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) x z θ) x := by
    intro x hx
    have hd := hsol z θ x hx.1.le hzθ
    exact (hd.congr (fun s hs => (hEq s hs).symm) ((hEq x hx.1.le).symm)).hasDerivAt
      (Ici_mem_nhds hx.1)
  have hcontI : ContinuousOn (fun s : ℝ => g z θ s) (Set.Icc (0:ℝ) k) :=
    hcont.mono (fun x hx => hx.1)
  have hRcontI : ContinuousOn (fun s : ℝ => Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α)
        (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) s z θ
      + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g))
        (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) s z θ) (Set.Icc (0:ℝ) k) :=
    hRcont.mono (fun x hx => ⟨hx.1, le_trans hx.2 hk.2⟩)
  have hint : IntervalIntegrable (fun s : ℝ => Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α)
        (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) s z θ
      + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g))
        (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) s z θ) volume (0:ℝ) k := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hk.1]
    exact hRcontI
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hk.1 hcontI hderiv hint
  simpa using hFTC.symm

end Work.FTS_RegExport.RXR1
