import Mathlib
import Submission.Work.WilG4a.CD.fibreLimitDefs

namespace Work.WilG4a.CD

/-- The pointwise normal form of `reading`: the two quadratic atoms `δ² > (t-c)²`,
`δ² > (t'-c)²` (with `δ > 0`) are the open-ball conditions `|t-c| < δ`, `|t'-c| < δ`, and the
disjunction `ε < v - v' ∨ ε < v' - v` is the negation of `|v - v'| ≤ ε`. -/
theorem reading_iff (p : ℕ) (A : Set (Fin (p + 2) → ℝ))
    (z : Fin (p + 1) → ℝ) (ε δ : ℝ) (hδ : 0 < δ) (t t' v v' : ℝ) :
    reading p A z ε δ t t' v v' ↔
      (t ≠ z (Fin.last p) ∧ t' ≠ z (Fin.last p) ∧
        |t - z (Fin.last p)| < δ ∧ |t' - z (Fin.last p)| < δ ∧
        Fin.snoc (Fin.snoc (Fin.init z) t) v ∈ A ∧
        Fin.snoc (Fin.snoc (Fin.init z) t') v' ∈ A ∧
        ¬ (|v - v'| ≤ ε)) := by
  have hsq : ∀ x : ℝ, (0 < δ ^ 2 - x ^ 2 ↔ |x| < δ) := by
    intro x
    rw [sub_pos, sq_lt_sq, abs_of_pos hδ]
  have hD : ∀ a b : ℝ, (ε < a - b ∨ ε < b - a) ↔ ¬ (|a - b| ≤ ε) := by
    intro a b
    rw [not_le, lt_abs, neg_sub]
  simp only [reading, hsq, hD]
  tauto

theorem reading_compl_iff (p : ℕ) (A : Set (Fin (p + 2) → ℝ))
    (z : Fin (p + 1) → ℝ) (ε δ : ℝ) (hδ : 0 < δ) :
    (∀ t t' v v' : ℝ, ¬ reading p A z ε δ t t' v v') ↔
      (∀ t t' : ℝ, t ≠ z (Fin.last p) → t' ≠ z (Fin.last p) →
        |t - z (Fin.last p)| < δ → |t' - z (Fin.last p)| < δ →
        ∀ v v' : ℝ, Fin.snoc (Fin.snoc (Fin.init z) t) v ∈ A →
          Fin.snoc (Fin.snoc (Fin.init z) t') v' ∈ A → |v - v'| ≤ ε) := by
  constructor
  · intro h t t' ht ht' h1 h2 v v' hp hp'
    by_contra hc
    exact h t t' v v' ((reading_iff p A z ε δ hδ t t' v v').mpr
      ⟨ht, ht', h1, h2, hp, hp', hc⟩)
  · intro h t t' v v' hr
    rw [reading_iff p A z ε δ hδ t t' v v'] at hr
    obtain ⟨ht, ht', h1, h2, hp, hp', hc⟩ := hr
    exact hc (h t t' ht ht' h1 h2 v v' hp hp')

end Work.WilG4a.CD
