import Mathlib.Basic.Real.Basic
import Submission.Work.FTS.StrongEps.EpsMem
import Submission.Work.FTS.StrongEps.EpsLimitDefsG
import Submission.Work.FTS.StrongEps.E5G.Defs
import Submission.Work.FTS.StrongEps.E5G.ExistsLimG_assembly
import Submission.Work.FTS.StrongPersist.L3DataFinal
import Submission.Work.FTS.StrongPersist.StarPkg6OfCore
import Submission.Work.FTS.PhiStar.StarPkgo2OfCore

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5G

theorem ExistsLimG_of_core {α₂ α₄ α C₀ K Ce Cs C3 Cpow : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g₀ : Work.FTS.Galerkin.Fn}
    (hα₂ : 0 < α₂) (hα₂1 : α₂ ≤ 1 / 4) (hα : α ∈ Set.Ioc (0 : ℝ) α₂)
    (hα₄ : α < α₄) (hα₄2 : α₄ ≤ α₂)
    (hL3 : Work.FTS.StrongPersist.L3Data α₂ Ce C3 Cpow)
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hELL3 : Work.FTS.StrongEps.EllLimOK3 α E) (hcore : Work.FTS.VocabO2.StarCore α Cs Φs)
    (hCs : 0 < Cs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E)
    (hU : Work.FTS.StrongEps.EpsUniformMem α ρ Φs E g₀ C₀ K) :
    Work.FTS.StrongEps.ExistsLimG α C₀ K Φs E g₀ := by
  -- ## the two star packages are *derived* from `StarCore`: the level-four package
  -- (`StarPkgo2OfCore`) and the level-six package (`StarPkg6OfCore`), each at a constant
  -- multiple of `Cs`, the constants being universal (the `α ≤ 1/4` range is what licenses
  -- them, and `α ∈ Ioc 0 α₂`, `α₂ ≤ 1/4` give it).
  obtain ⟨C₁, _hC₁, hP⟩ := Work.FTS.PhiStar.StarPkgo2OfCore
  obtain ⟨C₂, _hC₂, hP6⟩ := Work.FTS.StrongPersist.StarPkg6OfCore
  have hα0 : 0 < α := hα.1
  have hα14 : α ≤ 1 / 4 := le_trans hα.2 hα₂1
  exact ExistsLimG_assembly (Cs := C₁ * Cs) (Cs6 := C₂ * Cs)
    hα₂ hα₂1 hα hα₄ hα₄2 hL3 hρ hEll hELL3
    (hP α Cs Φs hα0 hα14 hCs hcore) (hP6 α Cs Φs hα0 hα14 hCs hcore) hml hU

end Work.FTS.StrongEps.E5G
