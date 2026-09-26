import Mathlib
import Submission.Work.Asymptotics.FunnelAsm.psumData
import Submission.Work.Asymptotics.FunnelAsm.decomp
import Submission.Work.Asymptotics.E_seminorm
import Submission.Work.Asymptotics.tileLayerSeminormTS
import Submission.Work.Asymptotics.seminormK_cusp0_arc
import Submission.Work.Asymptotics.DomainD_cover_half
import Submission.Work.Asymptotics.punctured_iteratedDeriv
import Submission.Work.Asymptotics.highPart_seminorm_scaled
import Submission.Work.Asymptotics.GcuspInP
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.TSasm.layerSemi_Tregion
import Submission.Work.Asymptotics.TSasm.cuspOneLowHalfTile_TS
import Submission.Work.CKFinal.paperLayer_seminorm_assembly
import Submission.Work.CKFinal.paperLayer_semi_funnel
import Submission.Work.CKFinal.layer_semi_KEpsilon_clean
import Submission.Work.CKFinal.layer_semi_lowstrip
import Submission.Work.CKFinal.layer_semi_cuspHalf

namespace Work.CKFinal

open scoped ContDiff
open UpperHalfPlane Filter

/-- The layer is a smooth function of `r` at every point of `𝒟`, and all its weighted
`r`-seminorms have moderate growth on `𝒟`, uniformly in `r` (both dimensions, all `r`). -/
theorem paperLayer_seminorm_DomainD (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) :
    (∀ τ : UpperHalfPlane, τ ∈ Work.Asymptotics.DomainD →
      ContDiff ℝ ∞ (fun s : ℝ =>
        Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s)) ∧
    ∀ k l : ℕ, ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      ∀ τ : UpperHalfPlane, τ ∈ Work.Asymptotics.DomainD → ∀ r : ℝ,
        |r| ^ k * ‖iteratedDeriv l (fun s : ℝ =>
          Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s) r‖
          ≤ C * (Work.Kernels.scale τ) ^ N := by
  refine ⟨fun τ hτ => (Work.Asymptotics.ts_paperLayer_contDiff_at ℓ d hd τ hτ).of_le le_top, ?_⟩
  exact paperLayer_seminorm_DomainD_assembly ℓ d hd
    (paperLayer_semi_funnel ℓ d hd) (layer_semi_KEpsilon_clean ℓ d hd)
    (layer_semi_lowstrip ℓ d hd) (layer_semi_cuspHalf ℓ d hd)

end Work.CKFinal
