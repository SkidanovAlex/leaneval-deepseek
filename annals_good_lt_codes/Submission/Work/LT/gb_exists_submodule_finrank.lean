import Mathlib
import Submission.Work.LT.good_base_defs

namespace Work.LT

/-- Every subspace `V ≤ (Fin D → ZMod 2)` of dimension `≥ k` has a `k`-dimensional subspace. -/
theorem gb_exists_submodule_finrank {D : ℕ} (V : Submodule (ZMod 2) (Fin D → ZMod 2)) (k : ℕ)
    (hk : k ≤ GB.frk V) :
    ∃ W : Submodule (ZMod 2) (Fin D → ZMod 2), W ≤ V ∧ GB.frk W = k := by
  -- pick `k` linearly independent vectors of `V` (possible since `k ≤ finrank V`)
  obtain ⟨s, hscard, hslin⟩ :=
    exists_finset_linearIndependent_of_le_finrank (R := ZMod 2) (M := V) hk
  -- take their span, viewed inside the ambient space
  refine ⟨Submodule.span (ZMod 2) (Set.range (fun x : s => ((x : V) : Fin D → ZMod 2))), ?_, ?_⟩
  · rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact x.1.2
  · have hlin : LinearIndependent (ZMod 2) (fun x : s => ((x : V) : Fin D → ZMod 2)) :=
      hslin.map' (Submodule.subtype V) (Submodule.ker_subtype V)
    rw [GB.frk, finrank_span_eq_card hlin, Fintype.card_coe, hscard]

end Work.LT
