import Mathlib
import Submission.Work.LT.lr_class_ops

namespace Work.LT

/-- Splitting the quadratic form of `classOpA` into its two layers: with `u g = s (0,g)` and
`v g = s (1,g)`, the form is `∑ g, u g * POp A v g + ∑ g, v g * ROp A u g`. -/
theorem lr_class_split {G : Type} [Group G] [Fintype G] {Δ : ℕ} (A : Fin Δ → G)
    (s : Fin 2 × G → ℝ) :
    ∑ p : Fin 2 × G, s p * classOpA A s p =
      (∑ g, s (0, g) * POp A (fun g => s (1, g)) g) +
        (∑ g, s (1, g) * ROp A (fun g => s (0, g)) g) := by
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  congr 1

end Work.LT
