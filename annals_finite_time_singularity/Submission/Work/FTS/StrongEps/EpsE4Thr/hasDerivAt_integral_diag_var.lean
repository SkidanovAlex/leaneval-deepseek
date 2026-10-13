import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Coercivity.Defs
import Submission.Work.FTS.StrongPersist.EnergyStep
import Submission.Work.FTS.StrongEps.EpsE4Thr.DiagAux
import Submission.Work.FTS.StrongEps.EpsE4Thr.DiagSlices
import Submission.Work.FTS.StrongEps.EpsE4Thr.DiagCross

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

namespace Work.FTS.StrongEps.EpsE4Thr

theorem hasDerivAt_integral_diag_var {ρ : ℝ → ℝ → ℝ} {u udot : ℝ → Work.FTS.Galerkin.Fn}
    {τ T : ℝ} (hT : 0 ≤ T) (hτ : τ ∈ Set.Ioo 0 T)
    (hρmeas : AEMeasurable (Function.uncurry ρ)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hρnn : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)), 0 ≤ ρ p.1 p.2)
    (hdiag : ∀ s ∈ Set.Icc (0 : ℝ) T, MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (u s p.1 p.2) ^ 2 * ρ p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hdiagd : ∀ s ∈ Set.Icc (0 : ℝ) T, MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (udot s p.1 p.2) ^ 2 * ρ p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hmeas : MeasureTheory.AEStronglyMeasurable
      (fun q : ℝ × (ℝ × ℝ) => u q.1 q.2.1 q.2.2)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))))
    (hmeasd : MeasureTheory.AEStronglyMeasurable
      (fun q : ℝ × (ℝ × ℝ) => udot q.1 q.2.1 q.2.2)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))))
    (hderiv : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      ∀ s ∈ Set.Ioo (0 : ℝ) T, HasDerivAt (fun t : ℝ => u t p.1 p.2) (udot s p.1 p.2) s)
    (hcont : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      ContinuousOn (fun s : ℝ => u s p.1 p.2) (Set.Icc 0 T))
    (hK : ∃ K : ℝ, 0 ≤ K ∧ ∀ σ ∈ Set.Icc (0 : ℝ) T,
      ∫ p : ℝ × ℝ, (udot σ p.1 p.2) ^ 2 * ρ p.1 p.2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ≤ K)
    (hcontU : Filter.Tendsto (fun σ : ℝ => ∫ p : ℝ × ℝ,
        (udot σ p.1 p.2 - udot τ p.1 p.2) ^ 2 * ρ p.1 p.2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))) (nhds τ) (nhds 0)) :
    HasDerivAt (fun s : ℝ => ∫ p : ℝ × ℝ, u s p.1 p.2 * u s p.1 p.2 * ρ p.1 p.2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      (2 * ∫ p : ℝ × ℝ, udot τ p.1 p.2 * u τ p.1 p.2 * ρ p.1 p.2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))) τ := by
  have hD : Work.FTS.StrongEps.EpsE4Thr.DiagData ρ u udot τ T :=
    Work.FTS.StrongEps.EpsE4Thr.DiagData.of_raw hT hτ hρmeas hρnn hdiag hdiagd hmeas hmeasd
      hderiv hcont hK hcontU
  have hS := Work.FTS.StrongEps.EpsE4Thr.diag_ae_slices hD
  have hA0 := Work.FTS.StrongEps.EpsE4Thr.diag_Arem0 hD hS
  have hBlim := Work.FTS.StrongEps.EpsE4Thr.diag_Blim hD hS
  have hDQ := Work.FTS.StrongEps.EpsE4Thr.diag_DQ hD
  have hlim : Filter.Tendsto (slope (Work.FTS.StrongEps.EpsE4Thr.diagPfun ρ u) τ)
      (nhdsWithin τ {τ}ᶜ) (nhds (2 * Work.FTS.StrongEps.EpsE4Thr.diagQval ρ u udot τ)) := by
    have h0 : Filter.Tendsto (fun s =>
        Work.FTS.StrongEps.EpsE4Thr.diagArem ρ u τ s
          + 2 * Work.FTS.StrongEps.EpsE4Thr.diagBrem ρ u τ s)
        (nhdsWithin τ {τ}ᶜ) (nhds (2 * Work.FTS.StrongEps.EpsE4Thr.diagQval ρ u udot τ)) := by
      have h1 := hA0.add (hBlim.const_mul 2)
      simpa using h1
    exact Tendsto.congr' hDQ.symm h0
  have hgoal : HasDerivAt (Work.FTS.StrongEps.EpsE4Thr.diagPfun ρ u)
      (2 * Work.FTS.StrongEps.EpsE4Thr.diagQval ρ u udot τ) τ :=
    (hasDerivAt_iff_tendsto_slope).mpr hlim
  have hP : Work.FTS.StrongEps.EpsE4Thr.diagPfun ρ u
      = fun s : ℝ => ∫ p : ℝ × ℝ, u s p.1 p.2 * u s p.1 p.2 * ρ p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    funext fun s => rfl
  have hQ : Work.FTS.StrongEps.EpsE4Thr.diagQval ρ u udot τ
      = ∫ p : ℝ × ℝ, udot τ p.1 p.2 * u τ p.1 p.2 * ρ p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := rfl
  rw [hP] at hgoal
  rw [hQ] at hgoal
  exact hgoal

end Work.FTS.StrongEps.EpsE4Thr
