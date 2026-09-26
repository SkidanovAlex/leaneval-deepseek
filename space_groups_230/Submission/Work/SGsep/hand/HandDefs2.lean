import Submission.Work.SGsep.hand.HandDefs

/-! Second vocabulary module for the `hand_separates` development (definitions and trivial
lemmas only, so that the kernel-checked axis table of `HandDefs`/`AxisTab` stays frozen).

Names here avoid the `V3.`/`M3.` prefix so that they cannot be confused with the (opened)
namespace `Work.SGsep.Hand.Data.V3` / `...M3` of `HandDefs`. -/

namespace Work.SGsep.Hand

open Work.SG
open Work.SG.Data
open Work.SGsep.Hand.Data

/-- The integer vector as a real coordinate vector. -/
def toRealV (v : V3) : Fin 3 → ℝ := toRVec v.toFun

/-- gcd of the entries of an `IVec`. -/
def gcdIVec (v : IVec) : Nat := Nat.gcd (Nat.gcd (v 0).natAbs (v 1).natAbs) (v 2).natAbs

/-- Primitivity of an `IVec`, in Bézout form. -/
def PrimIVec (v : IVec) : Prop := ∃ β : IVec, β ⬝ᵥ v = 1

/-- The element of representative `k` with table index `i` (flat). -/
def A3n (k i : Nat) : M3 := (repArith k).elems.getD i M3.one

/-- The `i`-th standard basis vector of `ℝ³`. -/
def stdB (i : Fin 3) : Fin 3 → ℝ := fun j => if j = i then 1 else 0

/-- Determinant of the matrix whose *columns* are `u`, `v`, `w`. -/
noncomputable def detCols (u v w : Fin 3 → ℝ) : ℝ :=
  (Matrix.of ![u, v, w]).transpose.det

/-- The rank-one matrix `c wᵀ`. -/
def rankOne (c w : IVec) : IMat := fun i j => c i * w j

@[simp] theorem toRealV_eq (v : V3) : toRealV v = toRVec v.toFun := rfl

theorem gcdV_toFun (v : V3) : gcdIVec v.toFun = V3.gcdV v := by
  simp [gcdIVec, V3.gcdV, V3.toFun, Fin.isValue]

theorem dot_toFun (u v : V3) : V3.dot u v = u.toFun ⬝ᵥ v.toFun := by
  simp [V3.dot, V3.toFun, dotProduct, Fin.sum_univ_three]

/-- A standard basis vector of `ℝ³`, for the three `e3` values. -/
theorem e3_toReal : ∀ q : Nat, toRealV (e3 q) = stdB 0 ∨ toRealV (e3 q) = stdB 1 ∨
    toRealV (e3 q) = stdB 2 := by
  intro q
  unfold Work.SG.Data.e3
  split_ifs with h1 h2
  · exact Or.inl (funext fun i => by fin_cases i <;> simp [toRealV, toRVec, V3.toFun, stdB])
  · exact Or.inr (Or.inl (funext fun i => by fin_cases i <;> simp [toRealV, toRVec, V3.toFun, stdB]))
  · exact Or.inr (Or.inr (funext fun i => by fin_cases i <;> simp [toRealV, toRVec, V3.toFun, stdB]))

end Work.SGsep.Hand
