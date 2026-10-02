/-
# EL nest, part 5 (N4): the intersection and the diameter of the nest at `b₂`

The two remaining clauses of the contract's N4
(`NOTES_LEAD_mandelbar_EL_F_contracts.md` §6): the closed nest has the single point `b₂` as its
intersection, and the diameters tend to `0`.  Both are corollaries of the shrinking
`Work.ELNest.Dnest_shrinks` together with the openness of the levels and `b₂ ∈ Δ̂ₙ`.
-/
import Mathlib
import Submission.Work.ELNest.Dnest_shrinks

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Set Topology Function
open scoped Topology ComplexConjugate

set_option linter.unusedVariables false

noncomputable section

namespace Work.ELNest

open Work.EL

variable {c : ℂ}

/-- **N4 (first clause)**: the intersection of the closures of the levels of the nest at `b₂` is
the single point `b₂`. -/
theorem Dnest_iInter (S : NestData c) : (⋂ n : ℕ, closure (S.D n)) = {S.b2} := by
  apply Set.Subset.antisymm
  · intro x hx
    rw [Set.mem_iInter] at hx
    have hxeq : x = S.b2 := by
      by_contra hne
      have hpos : 0 < dist x S.b2 := dist_pos.mpr hne
      obtain ⟨N, hN⟩ := Dnest_shrinks S (dist x S.b2 / 2) (by linarith)
      obtain ⟨y, hyD, hyx⟩ :=
        Metric.mem_closure_iff.mp (hx N) (dist x S.b2 / 2) (by linarith)
      have h1 : dist y S.b2 < dist x S.b2 / 2 := by
        simpa [Metric.mem_ball] using hN N le_rfl hyD
      have h2 : dist x y < dist x S.b2 / 2 := by simpa [dist_comm] using hyx
      linarith [dist_triangle x y S.b2]
    rw [hxeq]
    exact Set.mem_singleton _
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [Set.mem_iInter]
    intro n
    exact subset_closure (S.b2_mem_D n)

/-- **N4 (second clause)**: the diameters of the levels of the nest at `b₂` tend to `0`. -/
theorem Dnest_diam (S : NestData c) :
    Tendsto (fun n : ℕ => Metric.diam (S.D n)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := Dnest_shrinks S (ε / 4) (by linarith)
  refine ⟨N, fun n hn => ?_⟩
  have hsub : S.D n ⊆ Metric.ball S.b2 (ε / 4) := hN n hn
  have hbdd : Bornology.IsBounded (Metric.ball S.b2 (ε / 4)) := Metric.isBounded_ball
  have hdiam : Metric.diam (S.D n) ≤ 2 * (ε / 4) :=
    le_trans (Metric.diam_mono hsub hbdd) (Metric.diam_ball (by linarith))
  rw [Real.dist_eq, sub_zero, abs_of_nonneg Metric.diam_nonneg]
  linarith

end Work.ELNest
