import Mathlib.Analysis.InnerProductSpace.PiL2

namespace Commons.Analysis.Calculus.ContinuousOn

open scoped Topology in
/-- If `K` is relatively compact (its closure is compact) and `f` is continuous on `closure K`,
then `sSup (f '' K)` is the least upper bound of `f` on `K`: it bounds `f` from above on `K`,
and it is the smallest real number with that property. -/
theorem sSup_image_bounds {K : Set (EuclideanSpace ℝ (Fin 4))} {f : EuclideanSpace ℝ (Fin 4) → ℝ}
    (hKc : IsCompact (closure K)) (hf : ContinuousOn f (closure K)) (hne : K.Nonempty) :
    (∀ z ∈ K, f z ≤ sSup (f '' K)) ∧ (∀ M : ℝ, (∀ z ∈ K, f z ≤ M) → sSup (f '' K) ≤ M) := by
  -- `f '' closure K` is compact, hence bounded above; so `f '' K ⊆ f '' closure K` is bounded above.
  have hcomp : IsCompact (f '' closure K) := hKc.image_of_continuousOn hf
  have hbdd : BddAbove (f '' K) := hcomp.bddAbove.mono (Set.image_mono subset_closure)
  have hneK : (f '' K).Nonempty := hne.image f
  exact ⟨fun z hz => le_csSup hbdd (Set.mem_image_of_mem f hz),
    fun M hM => csSup_le hneK (by rintro _ ⟨z, hz, rfl⟩; exact hM z hz)⟩

end Commons.Analysis.Calculus.ContinuousOn