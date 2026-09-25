import Mathlib
import Submission.Work.LT.Defs

namespace Work.LT

/-- Edge count as a bilinear form: the number of pairs `(g, j)` with `g ∈ S` and `g * B j ∈ T` equals
`∑ g, 1_S g * ∑ j, 1_T (g * B j)`. Pure Finset bookkeeping (namespace `Work.LT`). -/
theorem lr_mixing_count {G : Type} [Group G] [Fintype G] [DecidableEq G] {Δ : ℕ} (B : Fin Δ → G)
    (S T : Finset G) :
    ((S.sum fun g => (Finset.univ.filter (fun j : Fin Δ => g * B j ∈ T)).card : ℝ))
      = ∑ g : G, (if g ∈ S then (1:ℝ) else 0)
          * (∑ j : Fin Δ, (if g * B j ∈ T then (1:ℝ) else 0)) := by
  -- the inner sum is the cardinality of the fibre of `T` over `g * B j`
  have h1 : ∀ g : G, (∑ j : Fin Δ, (if g * B j ∈ T then (1:ℝ) else 0))
      = ((Finset.univ.filter (fun j : Fin Δ => g * B j ∈ T)).card : ℝ) := by
    intro g
    rw [Finset.sum_boole]
  simp only [h1]
  -- pull the indicator `1_S` inside the sum
  rw [show (∑ g : G, (if g ∈ S then (1:ℝ) else 0)
        * ((Finset.univ.filter (fun j : Fin Δ => g * B j ∈ T)).card : ℝ))
      = ∑ g : G,
          (if g ∈ S then ((Finset.univ.filter (fun j : Fin Δ => g * B j ∈ T)).card : ℝ) else 0) from
    Finset.sum_congr rfl (fun g _ => by by_cases h : g ∈ S <;> simp [h])]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

end Work.LT
