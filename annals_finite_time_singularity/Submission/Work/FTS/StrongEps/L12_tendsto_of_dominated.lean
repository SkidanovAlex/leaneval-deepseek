import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Submission.Work.FM.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Construction.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps

theorem L12_tendsto_of_dominated {f : ℕ → ℝ → ℝ → ℝ} {g : ℝ → ℝ → ℝ} {M : ℝ → ℝ} {ρ : ℝ}
    (hmeas : ∀ n : ℕ,
      MeasureTheory.AEStronglyMeasurable (fun s => Work.FM.L12dens Work.Spaces.K (f n) s)
        (MeasureTheory.volume.restrict (Set.Ioi ρ)))
    (hconv : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi ρ)),
      Filter.Tendsto (fun n : ℕ => Work.FM.L12dens Work.Spaces.K (f n) s) Filter.atTop
        (nhds (Work.FM.L12dens Work.Spaces.K g s)))
    (hbdd : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi ρ)),
      ∀ n : ℕ, ‖Work.FM.L12dens Work.Spaces.K (f n) s‖ ≤ M s)
    (hM : MeasureTheory.Integrable M (MeasureTheory.volume.restrict (Set.Ioi ρ))) :
    Filter.Tendsto (fun n : ℕ => Work.Construction.L12 (f n) ρ) Filter.atTop
      (nhds (Work.Construction.L12 g ρ)) := by
  -- Swap the order of the quantifiers in the domination hypothesis: the `∀ n` sits
  -- outside the `∀ᵐ s` in `tendsto_integral_of_dominated_convergence`.
  have hbound : ∀ n : ℕ, ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi ρ)),
      ‖Work.FM.L12dens Work.Spaces.K (f n) s‖ ≤ M s :=
    fun n => hbdd.mono fun s hs => hs n
  -- `Work.Construction.L12 (f n) ρ = Work.FM.L12 Spaces.K (f n) ρ
  --    = ∫ s in Ioi ρ, L12dens Spaces.K (f n) s
  --    = ∫ s, L12dens Spaces.K (f n) s ∂(volume.restrict (Ioi ρ))`,
  -- so this is literally the dominated convergence theorem for the measure
  -- `volume.restrict (Ioi ρ)`.
  have h := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := MeasureTheory.volume.restrict (Set.Ioi ρ))
    (F := fun (n : ℕ) (s : ℝ) => Work.FM.L12dens Work.Spaces.K (f n) s)
    (f := fun s : ℝ => Work.FM.L12dens Work.Spaces.K g s)
    M hmeas hM hbound hconv
  simpa only [Work.Construction.L12, Work.FM.L12] using h

end Work.FTS.StrongEps
