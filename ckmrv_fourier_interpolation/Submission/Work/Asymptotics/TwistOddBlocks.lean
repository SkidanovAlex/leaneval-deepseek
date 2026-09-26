/-
# The twisted odd carries of the atoms `T`, `S` and of the blocks `T^k`, `S T^k`

This file introduces the *candidate* twisted carries used in `Work.Asymptotics.carry_twist_odd`:

* `atomTA`, `atomTB` (and `atomSA`, `atomSB`) are the two components of the twisted carry of the
  atoms `T` and `S`; all of them are differences of group monomials:
  `atomTA = ((1-z)T⁻¹, (1-z)T⁻¹S, ±(1-z)T⁻¹S)` etc.;
* `TpowA n i`, `TpowB n i` are defined by the cocycle recursion
  `twist (T^{n+1}) = σ(T^n)·twist T + twist (T^n)·T`; they equal the flat sums
  `∑_{m<n} ∑_j (oddMT^{n-1-m})_{ij} • (atomTA j · T^m)` (`TpowA_flat`), which is what makes the
  support of the carries transparent;
* `TblockA k i`, `TblockB k i` extend this to all `k : ℤ` by the inversion law
  `twist (γ⁻¹) = -(σ(γ⁻¹)·twist γ)·γ⁻¹`;
* `STblockA k i`, `STblockB k i` are the carries of the blocks `S T^k`, obtained from the
  cocycle with the atom `S`.

The statements that these are the twisted carries (with polynomial bounds) are proved in
separate lemmas.
-/
import Mathlib
import Submission.Work.Asymptotics.TwistOddDefs

set_option maxHeartbeats 800000

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups MonoidAlgebra ModularForm

namespace Work.Asymptotics

open Work.Kernels

/-! ## The atoms -/

/-- The `(T-1)²`-component of the twisted carry of the atom `T` (zero except in rows `0`, `2`). -/
def atomTA : Fin 6 → R := fun i =>
  if i = 0 then (1 - Rneg) * R_Tinv
  else if i = 2 then (1 - Rneg) * R_Tinv * R_S
  else 0

/-- The `S(T-1)²`-component of the twisted carry of the atom `T` (zero except in rows `3`, `5`). -/
def atomTB : Fin 6 → R := fun i =>
  if i = 3 then (1 - Rneg) * R_Tinv
  else if i = 5 then -((1 - Rneg) * R_Tinv * R_S)
  else 0

/-- The `(T-1)²`-component of the twisted carry of the atom `S` (zero except in rows `1`, `5`). -/
def atomSA : Fin 6 → R := fun i =>
  if i = 1 then (1 - Rneg) * R_Tinv * R_S
  else if i = 5 then -((1 - Rneg) * R_Tinv)
  else 0

/-- The `S(T-1)²`-component of the twisted carry of the atom `S` (zero except in rows `2`, `4`). -/
def atomSB : Fin 6 → R := fun i =>
  if i = 2 then -((1 - Rneg) * R_Tinv)
  else if i = 4 then (1 - Rneg) * R_Tinv * R_S
  else 0

/-! ## The blocks `T^k` -/

/-- The `σ(T^k)`-rotated atom vector, `∑_j (oddMT^k)_{ij} • atomTA j`.  This is the first
term of the cocycle recursion for the carry of `T^{k+1}`. -/
def tvecA (k : ℕ) (i : Fin 6) : R := ∑ j : Fin 6, (oddMT ^ k) i j • atomTA j

/-- The `S(T-1)²`-component of the same rotated atom vector. -/
def tvecB (k : ℕ) (i : Fin 6) : R := ∑ j : Fin 6, (oddMT ^ k) i j • atomTB j

/-- The `(T-1)²`-component of the twisted carry of `T^n`, `n ≥ 0`, defined by the cocycle
recursion `twist (T^{n+1}) = σ(T^n)·twist T + twist (T^n)·T`.  It agrees with the flat formula
`∑_{m<n} ∑_j (oddMT^{n-1-m})_{ij} • (atomTA_j · T^m)` (`TpowA_flat`). -/
def TpowA : ℕ → Fin 6 → R
  | 0, _ => 0
  | k + 1, i => tvecA k i + TpowA k i * R_T

/-- The `S(T-1)²`-component of the twisted carry of `T^n`, `n ≥ 0`. -/
def TpowB : ℕ → Fin 6 → R
  | 0, _ => 0
  | k + 1, i => tvecB k i + TpowB k i * R_T

@[simp] lemma TpowA_zero (i : Fin 6) : TpowA 0 i = 0 := rfl
@[simp] lemma TpowB_zero (i : Fin 6) : TpowB 0 i = 0 := rfl

lemma TpowA_succ (k : ℕ) (i : Fin 6) : TpowA (k + 1) i = tvecA k i + TpowA k i * R_T := rfl
lemma TpowB_succ (k : ℕ) (i : Fin 6) : TpowB (k + 1) i = tvecB k i + TpowB k i * R_T := rfl

/-- The `(T-1)²`-component of the twisted carry of `T^k`, for every `k : ℤ`: for `k ≥ 0` the
flat formula, for `k < 0` the inversion law `twist (γ⁻¹) = -(σ(γ⁻¹)·twist γ)·γ⁻¹`. -/
def TblockA (k : ℤ) (i : Fin 6) : R :=
  if 0 ≤ k then TpowA k.toNat i
  else - (∑ j : Fin 6, (oddMTi ^ (-k).toNat) i j • TpowA (-k).toNat j) * R_Tinv ^ (-k).toNat

/-- The `S(T-1)²`-component of the twisted carry of `T^k`, for every `k : ℤ`. -/
def TblockB (k : ℤ) (i : Fin 6) : R :=
  if 0 ≤ k then TpowB k.toNat i
  else - (∑ j : Fin 6, (oddMTi ^ (-k).toNat) i j • TpowB (-k).toNat j) * R_Tinv ^ (-k).toNat

/-- The `(T-1)²`-component of the twisted carry of the block `S T^k`. -/
def STblockA (k : ℤ) (i : Fin 6) : R :=
  (∑ j : Fin 6, oddMS i j • TblockA k j) + atomSA i * ofSL (ModularGroup.T ^ k)

/-- The `S(T-1)²`-component of the twisted carry of the block `S T^k`. -/
def STblockB (k : ℤ) (i : Fin 6) : R :=
  (∑ j : Fin 6, oddMS i j • TblockB k j) + atomSB i * ofSL (ModularGroup.T ^ k)

/-! ## Elementary group-algebra identities for the group elements `T^k` -/

lemma ofSL_pow (γ : SL(2,ℤ)) (n : ℕ) : ofSL (γ ^ n) = (ofSL γ : R) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, ofSL_one]
  | succ k ih => rw [pow_succ, pow_succ, ofSL_mul, ih]

lemma R_T_eq_ofSL : (R_T : R) = ofSL ModularGroup.T := rfl

lemma R_Tinv_eq_ofSL : (R_Tinv : R) = ofSL (ModularGroup.T)⁻¹ := rfl

lemma R_T_pow (n : ℕ) : (R_T : R) ^ n = ofSL (ModularGroup.T ^ (n : ℤ)) := by
  rw [R_T_eq_ofSL, ← ofSL_pow, zpow_natCast]

lemma R_Tinv_pow (n : ℕ) :
    (R_Tinv : R) ^ n = ofSL (ModularGroup.T ^ (-(n : ℤ))) := by
  rw [R_Tinv_eq_ofSL, ← ofSL_pow]
  congr 1
  rw [_root_.zpow_neg, zpow_natCast, ← inv_pow]

end Work.Asymptotics
