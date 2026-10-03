import Mathlib
import Submission.Work.ORHughesFree.StarRegular
import Submission.Work.ORHughesFree.StarRegular.vonNeumannRegularRing_matrix

set_option autoImplicit false

universe u

namespace Work.Section3.UniverseStenstrom

open Work.ORHughesFree

/-- **The von Neumann regular step.**  Suppose `d = X · f(P) · Y` where `X` is a row over `S`,
`P` a square matrix over the von Neumann regular ring `R`, `Y` a column over `S`, and both
`X · f(P)` and `f(P) · Y` are matrices over `f(R)`.  Then `d` is in the range of `f`.

This is the computation in [B. J. Gardner, *Epimorphisms of regular rings*, Comment. Math. Univ.
Carolineae **16** (1975), Theorem 1.6]. -/
theorem exists_preimage_of_matrix_eq {R S : Type u} [Ring R] [Ring S]
    [VonNeumannRegularRing R] (f : R →+* S) {n : ℕ}
    (X : Matrix (Fin 1) (Fin n) S) (P : Matrix (Fin n) (Fin n) R)
    (Y : Matrix (Fin n) (Fin 1) S)
    (hX : ∃ P' : Matrix (Fin 1) (Fin n) R, X * P.map f = P'.map f)
    (hY : ∃ Q' : Matrix (Fin n) (Fin 1) R, P.map f * Y = Q'.map f) :
    ∃ r : R, f r = (X * P.map f * Y) 0 0 := by
  obtain ⟨P', hP'⟩ := hX
  obtain ⟨Q', hQ'⟩ := hY
  obtain ⟨T, hT⟩ :=
    (StarRegular.vonNeumannRegularRing_matrix (U := R) n).exists_mul_inverse P
  have hmap : P.map f * T.map f * P.map f = P.map f := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, hT]
  have hmid : P.map f * (T.map f * (P.map f * Y)) = P.map f * Y := by
    rw [← Matrix.mul_assoc (P.map f) (T.map f) (P.map f * Y),
      ← Matrix.mul_assoc (P.map f * T.map f) (P.map f) Y, hmap]
  have keyeq : X * P.map f * Y = P'.map f * T.map f * Q'.map f := by
    rw [← hP', ← hQ']
    calc X * P.map f * Y
        = X * (P.map f * Y) := by rw [Matrix.mul_assoc]
      _ = X * (P.map f * (T.map f * (P.map f * Y))) := by rw [hmid]
      _ = X * P.map f * T.map f * (P.map f * Y) := by simp only [Matrix.mul_assoc]
  refine ⟨(P' * T * Q') 0 0, ?_⟩
  rw [keyeq, ← Matrix.map_mul, ← Matrix.map_mul, Matrix.map_apply]

end Work.Section3.UniverseStenstrom
