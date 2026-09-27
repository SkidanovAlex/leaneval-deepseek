import Mathlib
import Submission.Work.EKLContract.Interfaces

namespace Work.EKLComp

open Work.EKLContract

variable {X : Type} [mX : MeasurableSpace X]

/-- `Refines` is reflexive. -/
theorem partRefines_refl (P : FinPart X) : Refines P P := fun i => ⟨i, subset_rfl⟩

/-- `Refines` is transitive. -/
theorem partRefines_trans {P Q R : FinPart X} (h1 : Refines P Q) (h2 : Refines Q R) :
    Refines P R := by
  intro i
  obtain ⟨j, hj⟩ := h1 i
  obtain ⟨k, hk⟩ := h2 j
  exact ⟨k, hj.trans hk⟩

/-- If `Q` refines `P`, then the σ-algebra of `P` is contained in that of `Q`. -/
theorem partSigma_le_of_refines {P Q : FinPart X} (h : Refines Q P) :
    partSigma P ≤ partSigma Q := by
  change MeasurableSpace.generateFrom (Set.range P.parts) ≤
    MeasurableSpace.generateFrom (Set.range Q.parts)
  refine MeasurableSpace.generateFrom_le ?_
  rintro s ⟨j, rfl⟩
  have heq : P.parts j = ⋃ i : {i : Fin Q.n // Q.parts i ⊆ P.parts j}, Q.parts i.1 := by
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · intro hx
      have hxuniv : x ∈ ⋃ i, Q.parts i := by rw [Q.cover]; trivial
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxuniv
      obtain ⟨k, hk⟩ := h i
      have hxk : x ∈ P.parts k := hk hi
      have hkj : k = j := by
        by_contra hne
        have hd : Disjoint (P.parts k) (P.parts j) := P.disjoint hne
        exact Set.disjoint_left.mp hd hxk hx
      rw [hkj] at hk
      exact ⟨⟨i, hk⟩, hi⟩
    · rintro ⟨i, hi⟩
      exact i.2 hi
  rw [heq]
  exact MeasurableSet.iUnion fun i => MeasurableSpace.measurableSet_generateFrom ⟨i.1, rfl⟩

/-- `Refines (P b) (P a)` for `a ≤ b`, by induction. -/
theorem refines_of_le (P : ℕ → FinPart X) (hmono : ∀ m, Refines (P (m + 1)) (P m))
    {a b : ℕ} (h : a ≤ b) : Refines (P b) (P a) :=
  Nat.le_induction (partRefines_refl (P a))
    (fun n _ ih => partRefines_trans (hmono n) ih)
    b h

theorem partSigma_mono_iterate {X : Type} [mX : MeasurableSpace X]
    (P : ℕ → Work.EKLContract.FinPart X) (hmono : ∀ m, Work.EKLContract.Refines (P (m+1)) (P m))
    {a b : ℕ} (h : a ≤ b) : Work.EKLContract.partSigma (P a) ≤ Work.EKLContract.partSigma (P b) :=
  partSigma_le_of_refines (refines_of_le P hmono h)

end Work.EKLComp
