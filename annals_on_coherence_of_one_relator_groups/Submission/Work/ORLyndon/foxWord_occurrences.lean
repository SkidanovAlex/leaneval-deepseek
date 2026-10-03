import Mathlib
import Submission.Work.ORLyndon.Fox

/-!
# The Fox derivative as a sum over occurrences of a letter

For a word `L` in the free group on `X` and a letter `x`, the Fox derivative `∂L/∂x` admits the
explicit expansion

`∂L/∂x = ∑_{i : Lᵢ = x} L.take i - ∑_{i : Lᵢ = x⁻¹} L.take (i+1)`,

one term per occurrence of the generator `x` (contributing the prefix *before* the occurrence)
and one per occurrence of its inverse `x⁻¹` (contributing the negative of the prefix *through*
the occurrence).

The proof is an induction on the word, using the recursion `∂(c :: L)/∂x = ∂c/∂x + c · ∂L/∂x`:
the first summand is exactly `foxLetter x c` and the tail is `c` times the corresponding sum for
`L`, via the multiplicativity of the prefix map `M ↦ FreeGroup.mk M`.
-/

namespace Work.ORLyndon

open MonoidAlgebra

/-- The `i`-th summand in the explicit occurrence expansion of the Fox derivative `∂·/∂x`:
`of (mk (L.take i))` when `Lᵢ = (x, true)`, `- of (mk (L.take (i+1)))` when `Lᵢ = (x, false)`,
and `0` otherwise. -/
noncomputable def foxOccSummand {X : Type*} [DecidableEq X] {K : Type*} [Field K] (x : X)
    (L : List (X × Bool)) (i : Fin L.length) : MonoidAlgebra K (FreeGroup X) :=
  if L.get i = (x, true) then
    MonoidAlgebra.of K (FreeGroup X) (FreeGroup.mk (L.take i.1))
  else if L.get i = (x, false) then
    - MonoidAlgebra.of K (FreeGroup X) (FreeGroup.mk (L.take (i.1 + 1)))
  else 0

/-- Prepending a letter to a word multiplies the corresponding prefix element on the left by the
letter group element. -/
theorem of_mk_cons {X : Type*} [DecidableEq X] {K : Type*} [Field K] (c : X × Bool)
    (L : List (X × Bool)) :
    MonoidAlgebra.of K (FreeGroup X) (FreeGroup.mk (c :: L)) =
      MonoidAlgebra.of K (FreeGroup X) (letterGroup c) *
        MonoidAlgebra.of K (FreeGroup X) (FreeGroup.mk L) := by
  rw [← map_mul, letterGroup_mul_mk]

/-- A summand of the expansion of `∂(c :: L)/∂x` at a non-initial position is the letter `c`
times the corresponding summand for `L`. -/
theorem foxOccSummand_succ {X : Type*} [DecidableEq X] {K : Type*} [Field K] (x : X)
    (c : X × Bool) (L : List (X × Bool)) (j : Fin L.length) :
    foxOccSummand (K := K) x (c :: L) j.succ =
      MonoidAlgebra.of K (FreeGroup X) (letterGroup c) * foxOccSummand (K := K) x L j := by
  rw [foxOccSummand, foxOccSummand]
  simp only [Fin.val_succ, List.take_succ_cons, List.get_eq_getElem, List.getElem_cons_succ]
  rw [of_mk_cons, of_mk_cons]
  split_ifs with h1 h2
  · rfl
  · rw [mul_neg]
  · rw [mul_zero]

/-- The initial summand of the expansion of `∂(c :: L)/∂x` is the single-letter Fox derivative
`∂c/∂x`. -/
theorem foxOccSummand_zero {X : Type*} [DecidableEq X] {K : Type*} [Field K] (x : X)
    (c : X × Bool) (L : List (X × Bool)) :
    foxOccSummand (K := K) x (c :: L) 0 = foxLetter (K := K) x c := by
  rw [foxOccSummand]
  obtain ⟨y, b⟩ := c
  cases b
  · rw [foxLetter_false]
    by_cases hy : y = x
    · subst hy; simp [mk_false]
    · simp [hy, Prod.mk.injEq]
  · rw [foxLetter_true]
    by_cases hy : y = x
    · subst hy; simp [← FreeGroup.one_eq_mk, ← MonoidAlgebra.one_def]
    · simp [hy, Prod.mk.injEq]

/-- The Fox derivative of a word, expanded as a sum over its letters. -/
theorem foxWord_eq_sum_foxOccSummand {X : Type*} [DecidableEq X] {K : Type*} [Field K] (x : X)
    (L : List (X × Bool)) :
    foxWord (K := K) x L = ∑ i : Fin L.length, foxOccSummand (K := K) x L i := by
  induction L with
  | nil => simp
  | cons c L ih =>
    rw [foxWord_cons]
    have hsum : (∑ i : Fin L.length, foxOccSummand (K := K) x (c :: L) i.succ) =
        (MonoidAlgebra.of K (FreeGroup X) (letterGroup c)) * foxWord (K := K) x L := by
      rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => foxOccSummand_succ (K := K) x c L i)]
      rw [← Finset.mul_sum, ← ih]
    have hsplit : (∑ i : Fin (c :: L).length, foxOccSummand (K := K) x (c :: L) i) =
        foxOccSummand (K := K) x (c :: L) 0 +
          ∑ i : Fin L.length, foxOccSummand (K := K) x (c :: L) i.succ := by
      simpa using (Fin.sum_univ_succ (f := fun i : Fin (L.length + 1) =>
        foxOccSummand (K := K) x (c :: L) i))
    rw [hsplit, foxOccSummand_zero, hsum]

theorem foxWord_occurrences {X : Type*} [DecidableEq X] {K : Type*} [Field K] (x : X)
    (L : List (X × Bool)) :
    foxWord (K := K) x L =
      ∑ i : Fin L.length,
        (if L.get i = (x, true) then
            MonoidAlgebra.of K (FreeGroup X) (FreeGroup.mk (L.take i.1))
          else if L.get i = (x, false) then
            - MonoidAlgebra.of K (FreeGroup X) (FreeGroup.mk (L.take (i.1 + 1)))
          else 0) := by
  exact foxWord_eq_sum_foxOccSummand (K := K) x L

end Work.ORLyndon
