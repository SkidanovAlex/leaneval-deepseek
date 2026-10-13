import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.WilG4a.sharpCD_fintype
import Submission.Work.WilG4a.exists_cell_partition_refining

namespace Work.WilG4a.CD

/-- The refining cell decomposition of `Work.WilG4a.exists_cell_partition_refining` also
satisfies this variant, which additionally requires that the enumerated cells are pairwise
disjoint; here we simply drop that conjunct. -/
theorem cellDecomp_refining (S : WilkiesDesign.SOMin) (hcd : WilkiesDesign.SOMin.SharpCD S) (n F : ℕ) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (c : Polynomial ℕ),
      ∀ (D : ℕ) (ι : Type) [Fintype ι] (X : ι → Set (Fin n → ℝ)),
        (∀ i, X i ∈ S.Ω F D n) →
        ∃ (m : ℕ), m ≤ MvPolynomial.eval ![D, Fintype.card ι] b ∧
          ∃ κ : Fin m → Set (Fin n → ℝ),
            (∀ σ, κ σ ∈ S.Ω a (c.eval D) n) ∧
            (∀ σ, WilkiesDesign.IsCell n (κ σ)) ∧
            (∀ z : Fin n → ℝ, ∃ σ, z ∈ κ σ) ∧
            (∀ (i : ι) (σ : Fin m), Disjoint (κ σ) (X i) ∨ κ σ ⊆ X i) := by
  obtain ⟨a, b, c, H⟩ :=
    Work.WilG4a.exists_cell_partition_refining S hcd F n
  refine ⟨a, b, c, ?_⟩
  intro D ι _ X hX
  obtain ⟨m, hm, κ, hmem, hcell, hcover, _hdisj, hrefine⟩ := H D ι X hX
  exact ⟨m, hm, κ, hmem, hcell, hcover, hrefine⟩

end Work.WilG4a.CD
