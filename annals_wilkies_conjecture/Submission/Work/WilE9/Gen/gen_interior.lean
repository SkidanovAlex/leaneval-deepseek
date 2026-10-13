import Mathlib
import Submission.Work.WilE9.Defs
import Submission.Work.WilE9.Gen.gen_closure

namespace Work.WilE9.Gen

open Classical Topology
open WilkiesDesign WilkiesDesign.E

/-- **`Gen` is closed under topological interior**, at the cost of a constant format budget and
a polynomial degree budget (same construction as `gen_closure`, via
`interior X = (closure Xᶜ)ᶜ`). -/
theorem gen_interior (F n : ℕ) : ∃ (a : ℕ) (b : Polynomial ℕ),
    ∀ (D : ℕ) (X : Set (Fin n → ℝ)),
      WilkiesDesign.E.Gen F D n X → WilkiesDesign.E.Gen a (b.eval D) n (interior X) := by
  -- `Gen` is closed under closure (proved in `gen_closure`) and under complement, and
  -- `interior X = (closure Xᶜ)ᶜ`: one format for the complement, none for the degree.
  obtain ⟨a₀, b₀, hcl⟩ := gen_closure (F + 1) n
  refine ⟨a₀ + 1, b₀, ?_⟩
  intro D X hX
  have h1 : WilkiesDesign.E.Gen (F + 1) D n Xᶜ := WilkiesDesign.E.Gen.compl hX
  have h2 : WilkiesDesign.E.Gen a₀ (b₀.eval D) n (closure Xᶜ) := hcl D Xᶜ h1
  have h3 : WilkiesDesign.E.Gen (a₀ + 1) (b₀.eval D) n (interior X) := by
    have h := WilkiesDesign.E.Gen.compl h2
    rwa [← interior_eq_compl_closure_compl] at h
  exact h3

end Work.WilE9.Gen
