import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsMem
import Submission.Work.FTS.StrongEps.EpsODE
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.PZeroAux.Pz_l12
import Submission.Work.FTS.ClassC.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Work

open Work.FTS.Galerkin (Fn Fam slice)

theorem epsUniformMem_Jeps_bound {α C₀ K : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {g₀ : Work.FTS.Galerkin.Fn} (hU : Work.FTS.StrongEps.EpsUniformMem α ρ Φs E g₀ C₀ K)
    (hd : ∀ ε : ℝ, 0 < ε → Work.FTS.StrongEps.EpsDatum α ρ ε g₀) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε ∈ Set.Ioc 0 ε₁,
      Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.Jeps ρ ε g₀) ≤ C₀ * α ^ 2 := by
  -- The uniform family of `ε`-solutions already controls the projected mollified slice at the
  -- fake time `τ = 0`; by the initial condition that slice is `P₀ (J_ε g₀)`, and the datum's
  -- `ClassC` clause forces `L₁₂ (J_ε g₀)(0) = 0`, so `P₀` acts trivially.
  obtain ⟨_, _, ε₁, hε₁, _, _, hg⟩ := hU.2.2 1 one_pos
  refine ⟨ε₁, hε₁, ?_⟩
  intro ε hε
  obtain ⟨g, hsol, hb⟩ := hg ε hε
  have hτ0 : (0 : ℝ) ∈ Set.Icc 0 1 := Set.mem_Icc.mpr ⟨le_refl 0, by norm_num⟩
  have hX : Work.FTS.Nonlin.Xn α (slice (JfamP ρ ε g) 0) ≤ C₀ * α ^ 2 :=
    (hb 0 hτ0).2.2.2.1
  have hsl : slice g 0 = g₀ := funext fun z => funext fun θ => IsEpsSolP.init hsol z θ
  have hPz : Pz (Jeps ρ ε g₀) = Jeps ρ ε g₀ :=
    Pz_self_of_l12 (Work.FTS.ClassC.ClassC.l12_zero (hd ε hε.1).2.2)
  have hslice : slice (JfamP ρ ε g) 0 = Jeps ρ ε g₀ := by
    rw [slice_JfamP ρ ε g 0, hsl, hPz]
  rwa [hslice] at hX

end Work.FTS.StrongEps.EpsE4Work
