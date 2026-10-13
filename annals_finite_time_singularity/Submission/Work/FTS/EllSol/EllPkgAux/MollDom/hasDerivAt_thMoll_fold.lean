import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllSol.EllPkgAux.thMollTransfer2
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.slice_continuousOn
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.slice_deriv_bdd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux.MollDom

open Work.FTS.EllSol.PkgK5.K5c

set_option maxHeartbeats 1000000

theorem hasDerivAt_thMoll_fold (G : ℝ → ℝ → ℝ) (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G)
    {ε w : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) (hw : 0 < w) :
    ∀ θ ∈ Work.Spaces.Iθ,
      HasDerivAt (fun θ' : ℝ => Work.FTS.EllSol.PkgK5.K5c.thMoll G ε w θ')
        (∫ s in Work.Spaces.Iθ,
          Work.FTS.EllSol.EllPkgAux.Kern (deriv (Work.FTS.EllSol.PkgK5.K5c.sKer ε)) θ s
            * G w s) θ := by
  -- the slice `s ↦ G w s` is continuous on `Iθ` (this is where `0 < w` and the endpoint
  -- values/traces of `TraceClass` are used)
  have hgc : ContinuousOn (fun s : ℝ => G w s) Work.Spaces.Iθ :=
    slice_continuousOn G hT hw
  obtain ⟨-, h0, hp, -, -, -, -, -⟩ := hT
  -- the fold identity holds on the whole open window `(-1/4, π/2 + 1/4)` containing `Iθ`
  have hfold : ∀ θ' ∈ Set.Ioo (-(1 / 4 : ℝ)) (Real.pi / 2 + 1 / 4),
      thMoll G ε w θ' = ∫ s in (0 : ℝ)..(Real.pi / 2),
        Work.FTS.EllSol.EllPkgAux.Kern (sKer ε) θ' s * G w s := by
    intro θ' hθ'
    rw [Work.FTS.EllSol.EllPkgAux.thMoll_fold hε hε1 (h0 w) (hp w) hgc hθ'.1 hθ'.2,
      Work.FTS.EllSol.EllPkgAux.setIntegral_Iθ_eq_interval]
  obtain ⟨C, hC⟩ := Work.FTS.EllSol.EllPkgAux.exists_bound_deriv_sKer hε
  -- differentiation under the integral sign of the fold
  have hA := Work.FTS.EllSol.EllPkgAux.hasDerivAt_intervalIntegral_Kern
    (ρ := sKer ε) (ρ' := deriv (sKer ε)) (g := fun s : ℝ => G w s) (C := C)
    (a := 0) (b := Real.pi / 2)
    (fun t : ℝ => Work.FTS.EllSol.EllPkgAux.hasDerivAt_sKer ε t) hC (by
      rw [Set.uIcc_of_le (show (0 : ℝ) ≤ Real.pi / 2 by positivity)]
      exact hgc)
  intro θ hθ
  have h1 : -(1 / 4 : ℝ) < θ := by linarith [hθ.1]
  have h2 : θ < Real.pi / 2 + 1 / 4 := by linarith [hθ.2]
  have hfold_ev : (fun θ' : ℝ => thMoll G ε w θ') =ᶠ[𝓝 θ]
      (fun θ' : ℝ => ∫ s in (0 : ℝ)..(Real.pi / 2),
        Work.FTS.EllSol.EllPkgAux.Kern (sKer ε) θ' s * G w s) :=
    Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ⟨h1, h2⟩) hfold
  have hd1 : HasDerivAt (fun θ' : ℝ => thMoll G ε w θ')
      (∫ s in (0 : ℝ)..(Real.pi / 2),
        Work.FTS.EllSol.EllPkgAux.Kern (deriv (sKer ε)) θ s * G w s) θ :=
    (hA θ).congr_of_eventuallyEq hfold_ev
  simpa only [Work.FTS.EllSol.EllPkgAux.setIntegral_Iθ_eq_interval] using hd1

end Work.FTS.EllSol.EllPkgAux.MollDom
