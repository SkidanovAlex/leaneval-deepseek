import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Algebra.Support

namespace Commons.Topology.CompactSupport

open scoped BigOperators

/-- A `(ι → ℂ)`-valued function has compact support if each of its components does. -/
lemma hasCompactSupport_pi {ι X : Type*} [Fintype ι] [TopologicalSpace X] {F : X → (ι → ℂ)}
    (h : ∀ i, HasCompactSupport (fun x => F x i)) : HasCompactSupport F := by
  rw [hasCompactSupport_def]
  have hsupp : Function.support F = ⋃ i, Function.support (fun x => F x i) := by
    ext x
    simp only [Function.mem_support, Set.mem_iUnion]
    constructor
    · intro hx
      by_contra hc
      push Not at hc
      exact hx (funext hc)
    · rintro ⟨i, hi⟩ hFx
      exact hi (congrFun hFx i)
  rw [hsupp, closure_iUnion_of_finite]
  exact isCompact_iUnion fun i => hasCompactSupport_def.mp (h i)

end Commons.Topology.CompactSupport