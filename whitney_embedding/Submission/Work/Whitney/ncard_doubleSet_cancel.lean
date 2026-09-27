import Mathlib
import Submission.Work.Whitney.DoublePoint

namespace Work.Whitney

/-- Deleting the four ordered pairs determined by two distinct double points
`(p₁, p₂)`, `(q₁, q₂)` (all four points distinct) from a finite double point set lowers the
cardinality by exactly `4`. -/
theorem ncard_doubleSet_cancel {n : ℕ} {M : Type*} [TopologicalSpace M]
    (f f' : M → EuclideanSpace ℝ (Fin (2 * n))) (p₁ p₂ q₁ q₂ : M)
    (hp₁p₂ : p₁ ≠ p₂) (hq₁q₂ : q₁ ≠ q₂)
    (hp₁q₁ : p₁ ≠ q₁) (hp₁q₂ : p₁ ≠ q₂) (hp₂q₁ : p₂ ≠ q₁) (hp₂q₂ : p₂ ≠ q₂)
    (hfp : f p₁ = f p₂) (hfq : f q₁ = f q₂)
    (hfin : (Work.Whitney.doubleSet f).Finite)
    (h : Work.Whitney.doubleSet f' =
        Work.Whitney.doubleSet f \ {(p₁, p₂), (p₂, p₁), (q₁, q₂), (q₂, q₁)}) :
    (Work.Whitney.doubleSet f').ncard + 4 = (Work.Whitney.doubleSet f).ncard := by
  rw [h]
  -- the four deleted pairs are pairwise distinct
  have hS4 : ({(p₁, p₂), (p₂, p₁), (q₁, q₂), (q₂, q₁)} : Set (M × M)).ncard = 4 := by
    simp [Set.ncard_insert_of_notMem, Set.ncard_singleton, Prod.mk.injEq, *]
  -- and each of them is a double point of `f`
  have hSsub : ({(p₁, p₂), (p₂, p₁), (q₁, q₂), (q₂, q₁)} : Set (M × M)) ⊆
      Work.Whitney.doubleSet f := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rw [Work.Whitney.mem_doubleSet]
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨hp₁p₂, hfp⟩
    · exact ⟨hp₁p₂.symm, hfp.symm⟩
    · exact ⟨hq₁q₂, hfq⟩
    · exact ⟨hq₁q₂.symm, hfq.symm⟩
  have hSfin : ({(p₁, p₂), (p₂, p₁), (q₁, q₂), (q₂, q₁)} : Set (M × M)).Finite :=
    hfin.subset hSsub
  rw [Set.ncard_sdiff hSsub hSfin, hS4]
  have h4 : 4 ≤ (Work.Whitney.doubleSet f).ncard := by
    have := Set.ncard_le_ncard hSsub hfin
    omega
  omega

end Work.Whitney
