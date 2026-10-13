/-
  The hypothesis standing in for BV Proposition 9 (`WilkiesDesign.E.E7_prop_main`):
  the sharp cell decomposition of *projections* of semi-Pfaffian families, with the
  SubPf track that area E0 consumes.  The four theorems of this area other than
  `E7_prop_main` itself are proved from this statement, together with the vocabulary
  in `Submission.Work.WilE7.Defs`.
-/
import Submission.Work.WilE7.Defs

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-- **BV Proposition 9** (the frozen `WilkiesDesign.E.E7_prop_main`, verbatim). -/
def Prop9 : Prop :=
  ∀ F n : ℕ, ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (c : Polynomial ℕ),
    ∀ (D k m : ℕ) (X : Fin k → SemiPf (n + m)),
      (∀ i, (X i).fmt ≤ F ∧ (X i).deg ≤ D) →
      ∃ C : Finset (Set (Fin n → ℝ)), IsCylDecompOn n (cubeC n) C ∧
        (∀ i, ∀ κ ∈ C, κ ⊆ projFirst n m '' (X i).set ∨
          Disjoint κ (projFirst n m '' (X i).set)) ∧
        C.card ≤ MvPolynomial.eval ![D, k] b ∧
        ∀ κ ∈ C, Star a (c.eval D) n κ ∧ SubPf n κ

end Work.WilE7
