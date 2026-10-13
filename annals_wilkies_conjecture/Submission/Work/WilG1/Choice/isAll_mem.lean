import Mathlib
import Submission.Work.WilG1.Basic

namespace Work.WilG1.Choice

open WilkiesDesign

/-- The parameters whose vertical fibre lies entirely in `K` form an `Ω`-set with format
`a + 3`: `{l | ∀ s, Fin.snoc l s ∈ K}` is the complement of the projection of `Kᶜ`. -/
theorem isAll_mem {S : WilkiesDesign.SOMin} {p a D : ℕ} {b : Polynomial ℕ}
    {K : Set (Fin (p + 1) → ℝ)} (hK : K ∈ S.Ω a (b.eval D) (p + 1)) :
    {l : Fin p → ℝ | ∀ s : ℝ, Fin.snoc l s ∈ K} ∈ S.Ω (a + 3) (b.eval D) p := by
  have h1 : Kᶜ ∈ S.Ω (a + 1) (b.eval D) (p + 1) := S.compl hK
  have h2 : projLast Kᶜ ∈ S.Ω (a + 2) (b.eval D) p := S.proj h1
  have h3 : (projLast Kᶜ)ᶜ ∈ S.Ω ((a + 2) + 1) (b.eval D) p := S.compl h2
  have hset : {l : Fin p → ℝ | ∀ s : ℝ, Fin.snoc l s ∈ K} = (projLast Kᶜ)ᶜ := by
    ext l
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, projLast, not_exists, not_not]
  rw [hset]
  exact h3

end Work.WilG1.Choice
