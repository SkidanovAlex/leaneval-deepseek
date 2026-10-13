/-
# `Work.FTS.Physical.BiotSavart.contDiffOn_uncurry_ico`

Joint `C¹` of the physical velocity `u = BS ω` on the half-open strip `ℝ³ × [0,T)`.

This is the *locality* step of the reconstruction: the space-time Schauder estimate
(`Work.CoreResiduals.BiotSavartSpaceTime`, proved in the workspace as
`biotSavartSpaceTime_holds`) gives `IsContDiffHolderOn ℝ α (physVel ω).uncurry` on every
compact strip `ℝ³ × [0,S]`, `S ∈ Ioo 0 T`, and its `ContDiffOn ℝ 1` conjunct transports to the
half-open strip `ℝ³ × [0,T)` because `ContDiffOn` is local: for a point `(x,t)` with `0 ≤ t < T`
the strip `ℝ³ × [0,S]` with `S = (t+T)/2` agrees with `ℝ³ × [0,T)` on a neighbourhood of `(x,t)`.

The half-open form is the one the challenge's predicate `IsLocalEulerEquationSolution` consumes.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.FTS.Physical.Defs
import Submission.Work.CoreResiduals.Defs
import Submission.Work.CoreResiduals.BiotSavart.biotSavartSpaceTime_holds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Filter
open scoped Topology

set_option linter.unusedVariables false

namespace Work.FTS.Physical.BiotSavart

/-- **Locality of `C¹` on time strips.**  If a space-time field on `ℝ³ × ℝ` is `C¹` on every
compact strip `ℝ³ × [0,S]`, `S < T`, then it is `C¹` on the half-open strip `ℝ³ × [0,T)`.

For `(x,t)` with `0 ≤ t < T` put `S = (t+T)/2`, so that `0 < S < T`; on the neighbourhood
`ℝ³ × Ioo (-1) S` of `(x,t)` the sets `ℝ³ × Icc 0 S` and `ℝ³ × Ico 0 T` coincide (both describe
`0 ≤ s < T` there), so `ContDiffWithinAt.congr_set` transfers the regularity. -/
private theorem contDiffOn_Ico_of_strips {T : ℝ}
    {f : Work.FTS.Physical.R3 × ℝ → Work.FTS.Physical.R3}
    (h : ∀ S ∈ Set.Ioo 0 T, ContDiffOn ℝ 1 f (Set.univ ×ˢ Set.Icc 0 S)) :
    ContDiffOn ℝ 1 f (Set.univ ×ˢ Set.Ico 0 T) := by
  intro x hx
  obtain ⟨a, t⟩ := x
  simp only [Set.mem_prod, Set.mem_univ, true_and] at hx
  set S : ℝ := (t + T) / 2 with hSdef
  have hST : t < S := by simp only [hSdef]; linarith [hx.2]
  have hS : S ∈ Set.Ioo (0 : ℝ) T :=
    ⟨by simp only [hSdef]; linarith [hx.1, hx.2], by simp only [hSdef]; linarith [hx.2]⟩
  have htS : t ∈ Set.Icc (0 : ℝ) S := ⟨hx.1, le_of_lt hST⟩
  have hEv : (Set.univ ×ˢ Set.Icc (0 : ℝ) S)
      =ᶠ[𝓝 ((a, t) : Work.FTS.Physical.R3 × ℝ)] (Set.univ ×ˢ Set.Ico (0 : ℝ) T) := by
    have hmem : (Set.univ ×ˢ Set.Ioo (-1 : ℝ) S) ∈ 𝓝 ((a, t) : Work.FTS.Physical.R3 × ℝ) := by
      rw [nhds_prod_eq, Filter.prod_mem_prod_iff]
      exact ⟨univ_mem, Ioo_mem_nhds (by linarith [hx.1]) hST⟩
    filter_upwards [hmem] with y hy
    obtain ⟨b, s⟩ := y
    simp only [Set.mem_prod, Set.mem_univ, true_and, Set.mem_Icc, Set.mem_Ico] at hy ⊢
    exact propext ⟨fun h' => ⟨h'.1, lt_of_le_of_lt h'.2 hS.2⟩,
      fun h' => ⟨h'.1, le_of_lt hy.2⟩⟩
  exact (h S hS (a, t) ⟨Set.mem_univ _, htS⟩).congr_set hEv

theorem contDiffOn_uncurry_ico {α : NNReal} (hα : 0 < ((α : NNReal) : ℝ)) (hα1 : ((α : NNReal) : ℝ) < 1) {ω : Work.FTS.Physical.R3 → ℝ → Work.FTS.Physical.R3} {R T : ℝ} (hT : 0 < T) (hbun : ∀ S ∈ Set.Ioo 0 T, Work.CoreResiduals.BSAdmissibleStripFull α ω R S) : ContDiffOn ℝ 1 (Work.FTS.Physical.physVel ω).uncurry (Set.univ ×ˢ Set.Ico (0 : ℝ) T) := by
  -- the space-time Schauder estimate, read as a `∀ ω R S` statement
  have hst :=
    (Work.CoreResiduals.BiotSavart.biotSavartSpaceTime_holds (α := α) hα hα1).2.2
  refine contDiffOn_Ico_of_strips (T := T)
    (f := (Work.FTS.Physical.physVel ω).uncurry) fun S hS => ?_
  -- `IsContDiffHolderOn` carries `ContDiffOn ℝ 1` as its first conjunct
  exact (hst ω R S hS.1 (hbun S hS)).1

end Work.FTS.Physical.BiotSavart
