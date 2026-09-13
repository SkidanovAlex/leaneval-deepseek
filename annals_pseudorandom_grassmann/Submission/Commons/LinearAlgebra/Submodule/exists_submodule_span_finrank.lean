import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.LinearAlgebra.Submodule

theorem exists_submodule_span_finrank {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Module.Finite K V] {n : ℕ} (hn : n ≤ Module.finrank K V) :
    ∃ W : Submodule K V, Module.finrank K W = n := by
  classical
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := K) (M := V) hn
  refine ⟨Submodule.span K (Set.range f), ?_⟩
  simpa using (finrank_span_eq_card (R := K) (M := V) hf)

end Commons.LinearAlgebra.Submodule