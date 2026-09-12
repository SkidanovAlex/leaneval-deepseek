/-
Base-case computations at the root quadruple (-3, 5, 8, 8): every coprime
co-occurring pair of coordinates has pairChi = -1 (which gives χ₂ = -1).
-/
import Submission.Apollo.KR
import Submission.Apollo.KsymTool
import Submission.Apollo.ChiCross
import Submission.Apollo.Defs
import Mathlib.Tactic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
set_option autoImplicit false
open scoped Pointwise
open LocalGlobalApollonianCirclePackings
open scoped NumberTheorySymbols

namespace Apollo

/-- values of the root quadruple. -/
@[simp] lemma q0v_zero : q0v 0 = -3 := by decide
@[simp] lemma q0v_one : q0v 1 = 5 := by decide
@[simp] lemma q0v_two : q0v 2 = 8 := by decide
@[simp] lemma q0v_three : q0v 3 = 8 := by decide

/-- No coordinate of the root quadruple is zero. -/
lemma q0v_ne_zero (i : Fin 4) : q0v i ≠ 0 := by
  fin_cases i <;> norm_num [q0v]

/-- product of any two root coordinates is nonzero. -/
lemma q0v_pair_ne_zero (i j : Fin 4) : q0v i * q0v j ≠ 0 := by
  exact mul_ne_zero (q0v_ne_zero i) (q0v_ne_zero j)

-- The six χ₂ values that occur on coprime pairs of coordinates of the root
-- quadruple (-3, 5, 8, 8).  (gcd 8 8 = 8, so the pair (8, 8) never occurs.)

@[simp] lemma pairChi_neg3_five : pairChi (-3) 5 = -1 := by norm_num [pairChi, ksym]
@[simp] lemma pairChi_neg3_eight : pairChi (-3) 8 = -1 := by norm_num [pairChi, ksym]
@[simp] lemma pairChi_five_neg3 : pairChi 5 (-3) = -1 := by norm_num [pairChi, ksym]
@[simp] lemma pairChi_five_eight : pairChi 5 8 = -1 := by norm_num [pairChi, ksym]

/-- (5 | 8) = (5 | 2) = -1, since 5 ≡ 5 mod 8. -/
@[simp] lemma pairChi_eight_five : pairChi 8 5 = -1 := by
  unfold pairChi
  calc
    ksym 5 8 = kronTwo 5 := ksym_8_odd 5 (by norm_num : (5 : ℤ) % 2 = 1)
    _ = -1 := kronTwo_neg_of_mod8_five (by norm_num : (5 : ℤ) % 8 = 5)

/-- ((-3) | 8) = ((-3) | 2) = -1, since -3 ≡ 5 mod 8. -/
@[simp] lemma pairChi_eight_neg3 : pairChi 8 (-3) = -1 := by
  unfold pairChi
  calc
    ksym (-3) 8 = kronTwo (-3) := ksym_8_odd (-3) (by norm_num : (-3 : ℤ) % 2 = 1)
    _ = -1 := kronTwo_neg_of_mod8_five (by norm_num : (-3 : ℤ) % 8 = 5)

/-- At the root quadruple, every coprime co-occurring pair of coordinates has
pairChi = -1. -/
theorem base_pairChi_all : ∀ i j : Fin 4, i ≠ j → (q0v j).gcd (q0v i) = 1 →
    pairChi (q0v i) (q0v j) = -1 := by
  intro i j hij hg
  fin_cases i <;> fin_cases j
  · exfalso; exact hij rfl                       -- (0,0)
  · simpa [q0v] using pairChi_neg3_five          -- (0,1)
  · simpa [q0v] using pairChi_neg3_eight         -- (0,2)
  · simpa [q0v] using pairChi_neg3_eight         -- (0,3)
  · simpa [q0v] using pairChi_five_neg3          -- (1,0)
  · exfalso; exact hij rfl                       -- (1,1)
  · simpa [q0v] using pairChi_five_eight         -- (1,2)
  · simpa [q0v] using pairChi_five_eight         -- (1,3)
  · simpa [q0v] using pairChi_eight_neg3         -- (2,0)
  · simpa [q0v] using pairChi_eight_five         -- (2,1)
  · exfalso; exact hij rfl                       -- (2,2)
  · exfalso; simp [q0v] at hg
  · simpa [q0v] using pairChi_eight_neg3         -- (3,0)
  · simpa [q0v] using pairChi_eight_five         -- (3,1)
  · exfalso; simp [q0v] at hg
  · exfalso; exact hij rfl                       -- (3,3)

theorem base_pairChi (i j : Fin 4) (hij : i ≠ j) (hg : (q0v j).gcd (q0v i) = 1) :
    pairChi (q0v i) (q0v j) = -1 :=
  base_pairChi_all i j hij hg

/-- At the root quadruple, every coprime co-occurring pair of coordinates has
pairChi = -1, phrased with gcd in either order. -/
theorem base_pairChi'_all : ∀ i j : Fin 4, i ≠ j → (q0v i).gcd (q0v j) = 1 →
    pairChi (q0v i) (q0v j) = -1 := by
  intro i j hij hg
  fin_cases i <;> fin_cases j
  · exfalso; exact hij rfl                       -- (0,0)
  · simpa [q0v] using pairChi_neg3_five          -- (0,1)
  · simpa [q0v] using pairChi_neg3_eight         -- (0,2)
  · simpa [q0v] using pairChi_neg3_eight         -- (0,3)
  · simpa [q0v] using pairChi_five_neg3          -- (1,0)
  · exfalso; exact hij rfl                       -- (1,1)
  · simpa [q0v] using pairChi_five_eight         -- (1,2)
  · simpa [q0v] using pairChi_five_eight         -- (1,3)
  · simpa [q0v] using pairChi_eight_neg3         -- (2,0)
  · simpa [q0v] using pairChi_eight_five         -- (2,1)
  · exfalso; exact hij rfl                       -- (2,2)
  · exfalso; simp [q0v] at hg
  · simpa [q0v] using pairChi_eight_neg3         -- (3,0)
  · simpa [q0v] using pairChi_eight_five         -- (3,1)
  · exfalso; simp [q0v] at hg
  · exfalso; exact hij rfl                       -- (3,3)

theorem base_pairChi' (i j : Fin 4) (hij : i ≠ j) (hg : (q0v i).gcd (q0v j) = 1) :
    pairChi (q0v i) (q0v j) = -1 :=
  base_pairChi'_all i j hij hg

end Apollo
