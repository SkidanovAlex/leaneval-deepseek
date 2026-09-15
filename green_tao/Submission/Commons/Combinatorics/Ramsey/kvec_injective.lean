import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi

namespace Commons.Combinatorics.Ramsey

/-- The word in `[k+1]^n` associated with a word in `[k]^n`. -/
def kvec {k n : ℕ} (x : Fin n → Fin k) : Fin n → Fin (k+1) := fun j => Fin.castSucc (x j)

/-- Replace every occurrence of the largest letter `k+1` by the letter `i ∈ [k]`. -/
def replTop {k n : ℕ} (i : Fin k) (x : Fin n → Fin (k+1)) : Fin n → Fin (k+1) :=
  fun j => if x j = Fin.last k then Fin.castSucc i else x j

/-- A set is `(i, k+1)`-insensitive if membership is unchanged when the letters `i` and `k+1`
are interchanged in an arbitrary fashion. -/
def IsInsens {k n : ℕ} (i : Fin k) (D : Finset (Fin n → Fin (k+1))) : Prop :=
  ∀ x ∈ D, ∀ y : Fin n → Fin (k+1),
    (∀ j, y j = x j ∨ (x j = Fin.last k ∧ y j = Fin.castSucc i) ∨
      (y j = Fin.last k ∧ x j = Fin.castSucc i)) → y ∈ D

/-- The wildcard words over `Fin k` of length `n`, i.e. the index data of combinatorial lines. -/
def varWord (k n : ℕ) : Finset (Fin n → Option (Fin k)) :=
  Finset.univ.filter (fun g => ∃ i, g i = none)

/-- The point with wildcard value `v` on the line indexed by the word `g`. -/
def linePt {k n : ℕ} (g : Fin n → Option (Fin k)) (v : Fin k) : Fin n → Fin (k+1) :=
  fun j => Fin.castSucc ((g j).getD v)

theorem kvec_injective (k n : ℕ) : Function.Injective (kvec (k := k) (n := n)) := by
  intro x y h
  funext j
  exact Fin.castSucc_inj.mp (congrFun h j)

end Commons.Combinatorics.Ramsey