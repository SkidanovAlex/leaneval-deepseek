import Mathlib
import Submission.Work.WilC2.BndDefs

namespace Work.WilC4

open Set

/-- Being a non-boundary point of `S` means having a neighbourhood contained in `S` or a
neighbourhood contained in `Sᶜ`; consequently an interval all of whose points are non-boundary
points of `S` lies entirely inside `S` or entirely inside `Sᶜ`. -/
theorem bnd_interval_dichotomy {S : Set ℝ} {p q : ℝ}
    (h : ∀ x ∈ Set.Ioo p q, ¬ Work.WilC2.IsBnd S x) :
    Set.Ioo p q ⊆ S ∨ Set.Ioo p q ⊆ Sᶜ := by
  -- `A` : points with a neighbourhood contained in `S`; `B` : points with one contained in `Sᶜ`.
  set A : Set ℝ := {x | ∃ ε : ℝ, 0 < ε ∧ Set.Ioo (x - ε) (x + ε) ⊆ S} with hAdef
  set B : Set ℝ := {x | ∃ ε : ℝ, 0 < ε ∧ Set.Ioo (x - ε) (x + ε) ⊆ Sᶜ} with hBdef
  have hAopen : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨ε, hε, hsub⟩ := hx
    have hhalf : 0 < ε / 2 := by linarith
    refine Filter.mem_of_superset
      ((isOpen_Ioo).mem_nhds (show x ∈ Set.Ioo (x - ε / 2) (x + ε / 2) from
        ⟨by linarith, by linarith⟩)) ?_
    intro y hy
    refine ⟨ε / 2, hhalf, fun t ht => hsub ?_⟩
    simp only [Set.mem_Ioo] at ht hy ⊢
    constructor <;> linarith
  have hBopen : IsOpen B := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨ε, hε, hsub⟩ := hx
    have hhalf : 0 < ε / 2 := by linarith
    refine Filter.mem_of_superset
      ((isOpen_Ioo).mem_nhds (show x ∈ Set.Ioo (x - ε / 2) (x + ε / 2) from
        ⟨by linarith, by linarith⟩)) ?_
    intro y hy
    refine ⟨ε / 2, hhalf, fun t ht => hsub ?_⟩
    simp only [Set.mem_Ioo] at ht hy ⊢
    constructor <;> linarith
  have hAB : Disjoint A B := by
    rw [Set.disjoint_left]
    rintro x ⟨ε₁, hε₁, hsub₁⟩ ⟨ε₂, hε₂, hsub₂⟩
    exact (hsub₂ (Work.WilC2.mem_Ioo_self hε₂)) (hsub₁ (Work.WilC2.mem_Ioo_self hε₁))
  have hcover : Set.Ioo p q ⊆ A ∪ B := by
    intro x hx
    have hh := h x hx
    rw [Work.WilC2.isBnd_iff] at hh
    rcases not_and_or.mp hh with h1 | h1
    · exact Or.inl (not_not.mp h1)
    · exact Or.inr (not_not.mp h1)
  have hAS : A ⊆ S := by
    rintro x ⟨ε, hε, hsub⟩
    exact hsub (Work.WilC2.mem_Ioo_self hε)
  have hBS : B ⊆ Sᶜ := by
    rintro x ⟨ε, hε, hsub⟩
    exact hsub (Work.WilC2.mem_Ioo_self hε)
  rcases IsPreconnected.subset_or_subset hAopen hBopen hAB hcover isPreconnected_Ioo with
    hsub | hsub
  · exact Or.inl fun x hx => hAS (hsub hx)
  · exact Or.inr fun x hx => hBS (hsub hx)

end Work.WilC4
