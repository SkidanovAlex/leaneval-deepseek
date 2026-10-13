import Mathlib
import Submission.Work.Wilkies.Defs

namespace Work.WilG4a

theorem sharpCD_fintype (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (F n : ℕ) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (c : Polynomial ℕ),
      ∀ (D : ℕ) (ι : Type) [Fintype ι] (X : ι → Set (Fin n → ℝ)),
        (∀ i, X i ∈ S.Ω F D n) →
        ∃ C : Finset (Set (Fin n → ℝ)), WilkiesDesign.IsCylDecomp n C ∧
          (∀ i, ∀ κ ∈ C, κ ⊆ X i ∨ Disjoint κ (X i)) ∧
          C.card ≤ MvPolynomial.eval ![D, Fintype.card ι] b ∧
          ∀ κ ∈ C, κ ∈ S.Ω a (c.eval D) n := by
  -- `SharpCD` is stated for families indexed by `Fin k`.  A family indexed by an arbitrary
  -- finite type `ι` is transported along the equivalence `ι ≃ Fin (Fintype.card ι)`, so the
  -- same `a, b, c` work with `k` replaced by `Fintype.card ι`.
  obtain ⟨a, b, c, h⟩ := hcd F n
  refine ⟨a, b, c, ?_⟩
  intro D ι _ X hX
  obtain ⟨C, hC, hsub, hcard, hmem⟩ :=
    h D (Fintype.card ι) (fun j : Fin (Fintype.card ι) => X ((Fintype.equivFin ι).symm j))
      (fun j => hX _)
  refine ⟨C, hC, ?_, hcard, hmem⟩
  intro i κ hκ
  simpa using hsub (Fintype.equivFin ι i) κ hκ

end Work.WilG4a
