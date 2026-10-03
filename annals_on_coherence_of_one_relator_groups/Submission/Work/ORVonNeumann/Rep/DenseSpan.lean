/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORVonNeumann area (N5 of the one-relator coherence project)

# The closed span of `{δ_g}` is all of `ℓ²(G)`

The orthonormal family `δ_g` (`Submission.Work.ORVonNeumann.Rep.Orthonormal`) spans a dense
subspace of `ℓ²(G)`: with respect to the counting measure every set of finite measure is finite,
so every element of the dense subspace of simple functions is a finite linear combination of the
`δ_g`, and the induction principle `MeasureTheory.Lp.induction` upgrades this to all of `ℓ²(G)`.

## Main result

* `Work.ORVonNeumann.Rep.dense_span_deltaG` —
  `⊤ ≤ (Submodule.span ℂ (Set.range deltaG)).topologicalClosure`.
-/
import Mathlib
import Submission.Work.ORVonNeumann.Rep
import Submission.Work.ORVonNeumann.Rep.Orthonormal

set_option autoImplicit false

namespace Work.ORVonNeumann.Rep

open MeasureTheory

variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [MeasurableMul G]

/-- The closed `ℂ`-span of the orthonormal family `{δ_g : g ∈ G}` is the whole Hilbert space
`ℓ²(G)`. -/
theorem dense_span_deltaG :
    ⊤ ≤ (Submodule.span ℂ (Set.range (deltaG (G := G)))).topologicalClosure := by
  intro f _
  have key : ∀ x : l2 G,
      x ∈ (Submodule.span ℂ (Set.range (deltaG (G := G)))).topologicalClosure := by
    intro x
    refine MeasureTheory.Lp.induction (p := 2) (E := ℂ)
      (μ := (Measure.count : Measure G)) (by norm_num)
      (motive := fun y => y ∈
        (Submodule.span ℂ (Set.range (deltaG (G := G)))).topologicalClosure)
      ?_ ?_ ?_ x
    · intro c s hs hμs
      have hfin : s.Finite := Measure.count_apply_lt_top.mp hμs
      rw [MeasureTheory.Lp.simpleFunc.coe_indicatorConst,
        indicatorConstLp_eq_sum_smul_deltaG hs hμs.ne c hfin.coe_toFinset]
      refine Submodule.sum_mem _ (fun g _ => ?_)
      exact Submodule.smul_mem _ c
        (Submodule.le_topologicalClosure _
          (Submodule.subset_span ⟨g, rfl⟩))
    · intro f g hf hg hdisj hfS hgS
      exact Submodule.add_mem _ hfS hgS
    · exact Submodule.isClosed_topologicalClosure _
  exact key f

end Work.ORVonNeumann.Rep
