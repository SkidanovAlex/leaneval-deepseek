import Mathlib
import Submission.Work.WilG4a.f1affine1_defs

namespace Work.WilG4a.locFallbackAux

/-- Locally, a finite cover of the open unit interval `I = (0,1)` by the fibres of a family of
cells each of which is good or degenerate must contain a good cell whose fibre is a genuine
interval `Ioo a b` with `a < b`.

Since `I` is infinite while a finite union of subsingletons is finite, some fibre fails to be a
subsingleton; the dichotomy then forces that cell to be good, and the corresponding interval is
non-degenerate (a degenerate `Ioo a b`, `a ≥ b`, is empty, hence a subsingleton). -/
theorem exists_nondegen_cell {p k r : ℕ} {F : Fin k → (Fin p → ℝ) → ℝ → ℝ} {m : ℕ}
    (κ : Fin m → Set (Fin (p + 1) → ℝ)) (l : Fin p → ℝ)
    (hdich : ∀ σ, Work.WilG4a.GoodCell_w k r F (κ σ) ∨ Work.WilG4a.DegCell (κ σ))
    (hcover : ∀ x ∈ Work.WilG4a.I, ∃ σ, Fin.snoc l x ∈ κ σ) :
    ∃ σ, Work.WilG4a.GoodCell_w k r F (κ σ) ∧
      ∃ a b : ℝ, a < b ∧ Work.WilG4a.fibre (κ σ) l = Set.Ioo a b := by
  by_contra hcon
  -- `hcon`: no good cell has a non-degenerate interval fibre.
  have key : ∀ σ, Work.WilG4a.GoodCell_w k r F (κ σ) → ∀ a b : ℝ,
      Work.WilG4a.fibre (κ σ) l = Set.Ioo a b → ¬ a < b := by
    intro σ hg a b hab hlt
    exact hcon ⟨σ, hg, a, b, hlt, hab⟩
  -- Every fibre is a subsingleton.
  have hsub : ∀ σ, (Work.WilG4a.fibre (κ σ) l).Subsingleton := by
    intro σ
    rcases hdich σ with hg | hd
    · rcases hg.2.1 l with hs | ⟨a, b, hab⟩
      · exact hs
      · rw [hab]
        intro x hx y hy
        exact absurd (lt_trans hx.1 hx.2) (key σ hg a b hab)
    · exact hd l
  -- The fibres cover `I`, so `I` is a subset of a finite set: contradiction.
  have hcover' : Work.WilG4a.I ⊆ ⋃ σ, Work.WilG4a.fibre (κ σ) l := by
    intro x hx
    obtain ⟨σ, hσ⟩ := hcover x hx
    exact Set.mem_iUnion.2 ⟨σ, hσ⟩
  have hfin : (⋃ σ, Work.WilG4a.fibre (κ σ) l).Finite := by
    simpa using Set.Finite.biUnion (Set.finite_univ : (Set.univ : Set (Fin m)).Finite)
      (fun σ _ => (hsub σ).finite)
  exact Set.Ioo_infinite (show (0 : ℝ) < 1 by norm_num) (hfin.subset hcover')

end Work.WilG4a.locFallbackAux
