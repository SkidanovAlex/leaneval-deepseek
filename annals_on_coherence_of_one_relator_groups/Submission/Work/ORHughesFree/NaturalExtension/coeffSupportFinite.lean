import Mathlib

namespace Work.ORHughesFree.NaturalExtension

theorem coeffSupportFinite (R : Type*) [Ring R] [MulSemiringAction (Multiplicative ℤ) R] (k : ℕ)
    (Y : Matrix (Fin k) (Fin k) (SkewMonoidAlgebra R (Multiplicative ℤ))) :
    (Function.support fun m : Multiplicative ℤ =>
      Matrix.of fun i j : Fin k => (Y i j).coeff m).Finite := by
  -- Each entry `Y i j` has finitely supported coefficients, so the matrix of
  -- coefficients at `m` is nonzero only for `m` in the finite union of the
  -- coefficient supports of the entries.
  refine Set.Finite.subset
    (s := ⋃ i : Fin k, ⋃ j : Fin k,
      ↑((Y i j).coeff.support : Set (Multiplicative ℤ))) ?hS ?hsub
  · exact Set.finite_iUnion fun _ => Set.finite_iUnion fun _ => Finset.finite_toSet _
  · intro m hm
    by_contra h
    simp only [Set.mem_iUnion, not_exists, Finset.mem_coe] at h
    have h0 : ∀ i j : Fin k, (Y i j).coeff m = 0 := by
      intro i j
      by_contra hc
      exact h i j (by simpa using hc)
    apply hm
    ext i j
    simpa using h0 i j

end Work.ORHughesFree.NaturalExtension
