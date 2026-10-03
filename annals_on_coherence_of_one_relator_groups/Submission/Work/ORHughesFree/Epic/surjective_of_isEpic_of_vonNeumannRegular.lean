import Mathlib
import Submission.Work.ORHughesFree.Epic
import Submission.Work.ORHughesFree.StarRegular
import Submission.Work.ORHughesFree.DivisionClosure
import Submission.Work.ORHughesFree.StarRegular.vonNeumannRegularRing_matrix
import Submission.Work.ORHughesFree.Epic.isbellSilverMazet

namespace Work.ORHughesFree.Epic

open Matrix

/-!
# Epimorphisms out of a von Neumann regular ring are surjective

This file proves `surjective_of_isEpic_of_vonNeumannRegular`: if `R` is a von Neumann regular
ring and `f : R →+* S` is epic (right cancellable, `IsEpic f`), then `f` is surjective.

The mathematical input is the classical "dominion" criterion of Isbell--Silver--Mazet: for an
epic `f` and every `d : S` there are `n` and matrices `X` (`1 × n` over `S`), `P` (`n × n` over
`R`) and `Y` (`n × 1` over `S`) with

`d = X · f(P) · Y`,  `X · f(P)` a row over `f(R)`,  `f(P) · Y` a column over `f(R)`.

That criterion is recorded in the module `Submission.Work.ORHughesFree.Epic.isbellSilverMazet`.
Here we prove the *final* step of the argument, which is where von Neumann regularity of `R` is
used: since `Mat n R` is von Neumann regular, `P` has a weak inverse `T` (`P T P = P` over `R`)
and hence

`d = (X f(P)) · f(T) · (f(P) Y) = f((P' T Q') 0 0)`

for the matrices `P'`, `Q'` over `R` representing `X f(P)` and `f(P) Y`.  Thus `d` lies in the
range of `f`.
-/

/-- **The von Neumann regular step.**  Suppose `d = X · f(P) · Y` where `X` is a row over `S`,
`P` a square matrix over the von Neumann regular ring `R`, and `Y` a column over `S`, and suppose
moreover that `X · f(P)` is a row over `f(R)` and `f(P) · Y` a column over `f(R)`.  Then `d` is
in the range of `f`.

This is the computation in the proof of [B. J. Gardner, *Epimorphisms of regular rings*,
Commentationes Math. Univ. Carolinae 16 (1975), Theorem 1.6]. -/
theorem exists_preimage_of_matrix_eq {R S : Type} [Ring R] [Ring S]
    [VonNeumannRegularRing R] (f : R →+* S) {n : ℕ}
    (X : Matrix (Fin 1) (Fin n) S) (P : Matrix (Fin n) (Fin n) R)
    (Y : Matrix (Fin n) (Fin 1) S)
    (hX : ∃ P' : Matrix (Fin 1) (Fin n) R, X * P.map f = P'.map f)
    (hY : ∃ Q' : Matrix (Fin n) (Fin 1) R, P.map f * Y = Q'.map f) :
    ∃ r : R, f r = (X * P.map f * Y) 0 0 := by
  classical
  obtain ⟨P', hP'⟩ := hX
  obtain ⟨Q', hQ'⟩ := hY
  -- `Mat n R` is von Neumann regular, so `P` has a weak inverse `T` over `R`.
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

theorem surjective_of_isEpic_of_vonNeumannRegular {R S : Type} [Ring R] [Ring S]
    [VonNeumannRegularRing R] (f : R →+* S) (hf : IsEpic f) : Function.Surjective f := by
  intro d
  obtain ⟨n, X, P, Y, hX, hY, hd⟩ := isbellSilverMazet f hf d
  obtain ⟨r, hr⟩ := exists_preimage_of_matrix_eq f X P Y hX hY
  exact ⟨r, by rw [hd, hr]⟩

end Work.ORHughesFree.Epic
