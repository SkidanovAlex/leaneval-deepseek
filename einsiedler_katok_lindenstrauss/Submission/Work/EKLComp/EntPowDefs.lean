import Submission.Work.EKLComp.Entropy

/-!
# The join partition `⋁_{j<n} T^{-j} P` as a `FinPart`

Auxiliary definitions for the proof of `Work.EKLComp.ent_pow`
(`ent μ (T^[n]) = n * ent μ T`).

`Work.EKLContract.joinSets` indexes the atoms of `⋁_{k<N} T^{-k}P` by the finite type
`Fin N → Fin P.n`, whereas a `Work.EKLContract.FinPart` must be indexed by `Fin m`.
`joinPart` bridges the gap using `finFunctionFinEquiv : (Fin n → Fin m) ≃ Fin (m ^ n)`.
-/

open MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

namespace Work.EKLComp

open Work.EKLContract

variable {X : Type*} [MeasurableSpace X]

/-- The partition `⋁_{j<n} T^{-j}P`, as a `FinPart` indexed by `Fin (P.n ^ n)`. -/
def joinPart {T : X → X} (hT : Measurable T) (P : FinPart X) (n : ℕ) : FinPart X where
  n := P.n ^ n
  parts := fun i => joinSets T P n ((finFunctionFinEquiv (m := P.n) (n := n)).symm i)
  measurable := fun i => Core.joinSets_measurable hT P n _
  disjoint := fun i j hij =>
    Core.joinSets_disjoint T P n
      (fun h => hij ((finFunctionFinEquiv (m := P.n) (n := n)).symm.injective h))
  cover := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    have h : x ∈ ⋃ w : Fin n → Fin P.n, joinSets T P n w := by
      rw [Core.joinSets_iUnion T P n]; trivial
    obtain ⟨w, hw⟩ := Set.mem_iUnion.mp h
    exact ⟨finFunctionFinEquiv w, by simpa using hw⟩

@[simp] theorem joinPart_n {T : X → X} (hT : Measurable T) (P : FinPart X) (n : ℕ) :
    (joinPart hT P n).n = P.n ^ n := rfl

@[simp] theorem joinPart_parts {T : X → X} (hT : Measurable T) (P : FinPart X) (n : ℕ)
    (i : Fin (P.n ^ n)) :
    (joinPart hT P n).parts i =
      joinSets T P n ((finFunctionFinEquiv (m := P.n) (n := n)).symm i) := rfl

end Work.EKLComp
