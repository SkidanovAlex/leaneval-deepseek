import Mathlib
import Submission.Work.WilE9.Sharp.Main2
import Submission.Work.WilE9.Sharp.DomSet2_gen_aux
import Submission.Work.WilE9.Sharp.exSemiPf_deg_bound
import Submission.Work.WilE9.Sharp.Eset_bound_of_deg

namespace Work.WilE9.Sharp

theorem DomSet2_gen (hE2 : ∀ F : ℕ, ∃ p : Polynomial ℕ, ∀ (k : ℕ) (X : WilkiesDesign.E.SemiPf k),
      X.fmt ≤ F →
      ∃ s : Finset (Fin k → ℝ), s.card ≤ p.eval X.deg ∧ ↑s ⊆ X.set ∧
        ∀ x ∈ X.set, ∃ y ∈ s,
          connectedComponentIn X.set x = connectedComponentIn X.set y)
    (n a₀ : ℕ) : ∀ F₁ : ℕ, ∃ (a : ℕ) (b : MvPolynomial (Fin 4) ℕ),
    ∀ (D₁ k : ℕ) (f : (Fin n → ℝ) → ℝ)
      (S : List (Work.WilE9.Sharp.AEStratum n)) (D : ℕ),
      WilkiesDesign.E.Gen F₁ D₁ (n + 1) (WilkiesDesign.graphOf f) →
      S.length ≤ D + 1 →
      (∀ A ∈ S, A.E.X.fmt ≤ a₀) →
      (∀ A ∈ S, A.E.deg ≤ D) → (∀ A ∈ S, A.E.X.basics.length ≤ D + 1) →
      WilkiesDesign.E.Gen a (MvPolynomial.eval ![D₁, D, k, a₀] b) n
        (Work.WilE9.Sharp.DomSet2 n k S (WilkiesDesign.graphOf f)) := by
  obtain ⟨aE, bE, hEset⟩ := Eset_bound_of_deg hE2 n a₀ (exSemiPf_deg_bound n a₀)
  exact DomSet2_gen_core n a₀ aE bE hEset

end Work.WilE9.Sharp
