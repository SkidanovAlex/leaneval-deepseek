import Mathlib
import Submission.Work.Peluse.UControl.HistPhase1

/-!
# The initial state of the history-indexed PET chain

The chain starts from the configuration of `LambdaMD`: the slots `y^1, …, y^(d-1)` (with `d =
P.natDegree`, `d ≥ 2`) and the slot `P` itself, at the empty history.  This file fixes that state
(`petHistInit`) and proves that it satisfies the phase-1 invariant with `lc = P.leadingCoeff`.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl

noncomputable section

open Polynomial

lemma mvC_injective (σ : Type*) :
    Function.Injective (MvPolynomial.C : ℤ →+* MvPolynomial σ ℤ) :=
  MvPolynomial.C_injective σ ℤ

/-- The initial shift polynomials: `y^1, …, y^(d-1)` and `P` (at the empty history). -/
def petInitQ (P : Polynomial ℤ) : InitIdx P.natDegree → (Fin 0 → Bool) →
    Polynomial (MvPolynomial (Fin 0) ℤ) :=
  fun j _ => match j with
    | Sum.inl i => (Polynomial.X ^ (i.val + 1)).map (MvPolynomial.C)
    | Sum.inr _ => P.map (MvPolynomial.C)

/-- The initial state of the history-indexed chain. -/
def petHistInit (P : Polynomial ℤ) (hd : 1 ≤ P.natDegree) : HistData P.natDegree 0 where
  H := Finset.univ
  Q := petInitQ P
  hd := by
    intro x _
    rcases hx : x.1 with i | i
    · show (((Polynomial.X : Polynomial ℤ) ^ (i.val + 1)).map
        (MvPolynomial.C : ℤ →+* MvPolynomial (Fin 0) ℤ)).natDegree ≤ P.natDegree
      have h1 : ((Polynomial.X : Polynomial ℤ) ^ (i.val + 1)).natDegree = i.val + 1 :=
        Polynomial.natDegree_X_pow _
      have h2 : i.val + 1 ≤ P.natDegree - 1 := by
        have hi := i.isLt
        omega
      calc (((Polynomial.X : Polynomial ℤ) ^ (i.val + 1)).map
              (MvPolynomial.C : ℤ →+* MvPolynomial (Fin 0) ℤ)).natDegree
          ≤ ((Polynomial.X : Polynomial ℤ) ^ (i.val + 1)).natDegree :=
            Polynomial.natDegree_map_le
        _ = i.val + 1 := h1
        _ ≤ P.natDegree - 1 := h2
        _ ≤ P.natDegree := Nat.sub_le _ _
    · show (P.map (MvPolynomial.C : ℤ →+* MvPolynomial (Fin 0) ℤ)).natDegree ≤ P.natDegree
      exact Polynomial.natDegree_map_le
  hnc := by
    intro x _
    rcases hx : x.1 with i | i
    · show 1 ≤ (((Polynomial.X : Polynomial ℤ) ^ (i.val + 1)).map
        (MvPolynomial.C : ℤ →+* MvPolynomial (Fin 0) ℤ)).natDegree
      rw [Polynomial.natDegree_map_eq_of_injective (mvC_injective _),
        Polynomial.natDegree_X_pow]
      omega
    · show 1 ≤ (P.map (MvPolynomial.C : ℤ →+* MvPolynomial (Fin 0) ℤ)).natDegree
      rw [Polynomial.natDegree_map_eq_of_injective (mvC_injective _)]
      exact hd

/-- The initial state satisfies the phase-1 invariant. -/
theorem petHistInit_phase1 (P : Polynomial ℤ) (hd : 1 ≤ P.natDegree) :
    Phase1 P.natDegree 0 P.leadingCoeff (petHistInit P hd) := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g
    exact Finset.mem_univ _
  · intro g
    show (P.map (MvPolynomial.C : ℤ →+* MvPolynomial (Fin 0) ℤ)).natDegree = P.natDegree
    rw [Polynomial.natDegree_map_eq_of_injective (mvC_injective _)]
  · intro g
    show (P.map (MvPolynomial.C : ℤ →+* MvPolynomial (Fin 0) ℤ)).leadingCoeff
      = MvPolynomial.C P.leadingCoeff
    rw [Polynomial.leadingCoeff_map_of_injective (mvC_injective _)]
  · intro g
    have hg : g = 0 := Subsingleton.elim _ _
    rw [hg, HistData.shift_zero, mul_zero, add_zero]
  · intro x hx hxne
    obtain ⟨i, hi⟩ : ∃ i, x.1 = Sum.inl i := by
      rcases h : x.1 with i | i
      · exact ⟨i, rfl⟩
      · exact absurd (h.trans (by rw [Subsingleton.elim i 0])) hxne
    rw [hi]
    show (((Polynomial.X : Polynomial ℤ) ^ (i.val + 1)).map
        (MvPolynomial.C : ℤ →+* MvPolynomial (Fin 0) ℤ)).natDegree < P.natDegree
    rw [Polynomial.natDegree_map_eq_of_injective (mvC_injective _), Polynomial.natDegree_X_pow]
    have hi' := i.isLt
    omega

end

end Work.Peluse.UControl
