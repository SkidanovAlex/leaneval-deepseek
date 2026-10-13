import Mathlib.Analysis.InnerProductSpace.PiL2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.SolutionDelivery.Sup

theorem bddAbove_range_ciSup_mem {K : Set (EuclideanSpace ℝ (Fin 3))} (hKc : IsCompact K)
    {g : EuclideanSpace ℝ (Fin 3) → ℝ} (hg : ContinuousOn g K) :
    BddAbove (Set.range (fun x => ⨆ (_ : x ∈ K), g x)) := by
  refine BddAbove.mono (t := (g '' K) ∪ {sSup (∅ : Set ℝ)}) ?_ ?_
  · rintro y ⟨x, rfl⟩
    by_cases hx : x ∈ K
    · exact Or.inl ⟨x, hx, (ciSup_pos (f := fun _ : x ∈ K => g x) hx).symm⟩
    · refine Or.inr ?_
      rw [Set.mem_singleton_iff]
      exact ciSup_neg (f := fun _ : x ∈ K => g x) hx
  · exact BddAbove.union (hKc.bddAbove_image hg) bddAbove_singleton

end Work.SolutionDelivery.Sup
