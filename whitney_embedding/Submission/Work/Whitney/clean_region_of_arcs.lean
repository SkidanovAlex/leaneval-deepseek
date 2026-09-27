import Mathlib
import Submission.Work.Whitney.DoublePoint
import Submission.Work.Whitney.CleanRegion

/-!
# The clean region of the Whitney cancellation, from arcs that avoid the double points

The Whitney cancellation `Work.Whitney.cancel_double_points_oriented` is performed inside an open set
`W` on which `f` is injective except at the four preimages of the two double points, and whose image
is separated from the image of its complement.  This file shows that

`W := M ∖ (D ∖ {p₁, p₂, q₁, q₂})`,  where `D = {y | ∃ z ≠ y, f z = f y}`

is such a region as soon as the two double points are *simple* (their values have no third
preimage, recorded here by `hpreP`, `hpreQ`).  Since `D` is finite (the double point set of `f` is),
`W` is open, contains the four points and meets `D` exactly in them; moreover every point of `W`
other than the four has a unique preimage.  In particular every arc whose interior avoids `D` lies
in `W`, so the arcs produced by `Work.Whitney.exists_disjoint_arcs_avoiding_finite` are admissible
for the cancellation.
-/

namespace Work.Whitney

open scoped Manifold ContDiff
open Topology

/-- **The clean region of the cancellation.** -/
theorem exists_clean_region {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [CompactSpace M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hfin : (Work.Whitney.doubleSet f).Finite)
    (p₁ p₂ q₁ q₂ : M)
    (h₁ : p₁ ≠ p₂) (h₂ : q₁ ≠ q₂) (h₃ : p₁ ≠ q₁) (h₄ : p₁ ≠ q₂)
    (h₅ : p₂ ≠ q₁) (h₆ : p₂ ≠ q₂)
    (hfp : f p₁ = f p₂) (hfq : f q₁ = f q₂)
    (hpreP : ∀ z : M, f z = f p₁ → z = p₁ ∨ z = p₂)
    (hpreQ : ∀ z : M, f z = f q₁ → z = q₁ ∨ z = q₂) :
    ∃ W : Set M,
      IsOpen W ∧ IsCompact (closure W) ∧
      p₁ ∈ W ∧ p₂ ∈ W ∧ q₁ ∈ W ∧ q₂ ∈ W ∧
      (∀ y : M, y ∈ W ↔ ¬ (∃ z : M, z ≠ y ∧ f z = f y) ∨
        y = p₁ ∨ y = p₂ ∨ y = q₁ ∨ y = q₂) ∧
      (∀ y z : M, y ∈ W → z ∈ W → f y = f z →
        y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = q₁ ∧ z = q₂) ∨
          (y = q₂ ∧ z = q₁)) ∧
      (∀ y z : M, y ∈ W → z ∉ W → f y ≠ f z) ∧
      (∀ y ∈ W, y ≠ p₁ → y ≠ p₂ → y ≠ q₁ → y ≠ q₂ →
        ¬ (∃ z : M, z ≠ y ∧ f z = f y)) := by
  classical
  set D : Set M := {y : M | ∃ z : M, z ≠ y ∧ f z = f y} with hDdef
  set F : Set M := ({p₁, p₂, q₁, q₂} : Set M) with hFdef
  have hmemD : ∀ y : M, y ∈ D ↔ ∃ z : M, z ≠ y ∧ f z = f y := fun y => Iff.rfl
  have hDfin : D.Finite := by
    have h1 : D = Prod.fst '' (Work.Whitney.doubleSet f) := by
      ext y
      constructor
      · rintro ⟨z, hzy, hfz⟩
        exact ⟨(y, z), ⟨hzy.symm, hfz.symm⟩, rfl⟩
      · rintro ⟨w, hw, rfl⟩
        exact ⟨w.2, hw.1.symm, hw.2.symm⟩
    rw [h1]
    exact hfin.image Prod.fst
  have hFour : ∀ y : M, y ∈ F ↔ y = p₁ ∨ y = p₂ ∨ y = q₁ ∨ y = q₂ := by
    intro y
    rw [hFdef]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  have hFW : ∀ y : M, y ∈ (D \ F)ᶜ → y ∈ D → y = p₁ ∨ y = p₂ ∨ y = q₁ ∨ y = q₂ := by
    intro y hy hyD
    have : y ∈ F := by
      by_contra hyF
      exact hy ⟨hyD, hyF⟩
    exact (hFour y).mp this
  have hWmem : ∀ y : M, y ∈ F → y ∈ (D \ F)ᶜ := by
    intro y hy h
    exact h.2 hy
  have hclean : ∀ y z : M, y ∈ (D \ F)ᶜ → z ∈ (D \ F)ᶜ → f y = f z →
      y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = q₁ ∧ z = q₂) ∨
        (y = q₂ ∧ z = q₁) :=
    (Work.Whitney.clean_region_conditions f D hmemD ((D \ F)ᶜ) p₁ p₂ q₁ q₂
      (hWmem p₁ (by rw [hFour]; exact Or.inl rfl))
      (hWmem p₂ (by rw [hFour]; exact Or.inr (Or.inl rfl)))
      (hWmem q₁ (by rw [hFour]; exact Or.inr (Or.inr (Or.inl rfl))))
      (hWmem q₂ (by rw [hFour]; exact Or.inr (Or.inr (Or.inr rfl))))
      hFW hfp hfq hpreP hpreQ h₁ h₂ h₃ h₄ h₅ h₆).1
  have hsepc : ∀ y z : M, y ∈ (D \ F)ᶜ → z ∉ (D \ F)ᶜ → f y ≠ f z :=
    (Work.Whitney.clean_region_conditions f D hmemD ((D \ F)ᶜ) p₁ p₂ q₁ q₂
      (hWmem p₁ (by rw [hFour]; exact Or.inl rfl))
      (hWmem p₂ (by rw [hFour]; exact Or.inr (Or.inl rfl)))
      (hWmem q₁ (by rw [hFour]; exact Or.inr (Or.inr (Or.inl rfl))))
      (hWmem q₂ (by rw [hFour]; exact Or.inr (Or.inr (Or.inr rfl))))
      hFW hfp hfq hpreP hpreQ h₁ h₂ h₃ h₄ h₅ h₆).2
  have hchar : ∀ y : M, y ∈ (D \ F)ᶜ ↔ ¬ (∃ z : M, z ≠ y ∧ f z = f y) ∨
      y = p₁ ∨ y = p₂ ∨ y = q₁ ∨ y = q₂ := by
    intro y
    constructor
    · intro hy
      by_cases hD : y ∈ D
      · exact Or.inr (hFW y hy hD)
      · exact Or.inl hD
    · rintro (h | h) ⟨hyD, hyF⟩
      · exact h hyD
      · exact hyF ((hFour y).mpr h)
  refine ⟨(D \ F)ᶜ, ((hDfin.subset Set.sdiff_subset).isClosed).isOpen_compl,
    isClosed_closure.isCompact, hWmem p₁ (by rw [hFour]; exact Or.inl rfl),
    hWmem p₂ (by rw [hFour]; exact Or.inr (Or.inl rfl)),
    hWmem q₁ (by rw [hFour]; exact Or.inr (Or.inr (Or.inl rfl))),
    hWmem q₂ (by rw [hFour]; exact Or.inr (Or.inr (Or.inr rfl))), hchar, hclean, hsepc, ?_⟩
  intro y hy hy1 hy2 hy3 hy4 hcon
  obtain ⟨z, hzy, hfz⟩ := hcon
  rcases hFW y hy ⟨z, hzy, hfz⟩ with h | h | h | h
  · exact hy1 h
  · exact hy2 h
  · exact hy3 h
  · exact hy4 h

end Work.Whitney
