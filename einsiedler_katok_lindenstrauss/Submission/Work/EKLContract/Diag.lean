import Submission.Work.EKLContract.Defs

/-!
# EKL contract — basic API for `SL3`, `aDiag`, `aPlus`, the root groups `Uij`

This module collects the elementary lemmas the glue and the fleet need.  Nothing here changes
the frozen interface of `Defs.lean`; it only makes its objects usable.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open LeanEval.Dynamics.EinsiedlerKatokLindenstrauss

set_option linter.unusedVariables false
set_option warn.classDefReducibility false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

noncomputable section

namespace Work.EKLContract

/-! ## The underlying matrix of an element of `SL₃(ℝ)`

`SL₃(ℝ)` is Mathlib's `Matrix.SpecialLinearGroup (Fin 3) ℝ`, a subtype of `Matrix (Fin 3) (Fin 3) ℝ`.
Lean's `Coe`/`CoeFun` handling of that subtype is fragile inside tactics (the type of the coercion
is only visible after unfolding a `def`), so we route every matrix-level computation through the
explicit function `toMat`. -/

/-- The underlying matrix of an element of `SL₃(ℝ)`.  An `abbrev`, so that it unfolds during
definitional-equality checks inside tactics. -/
abbrev toMat (A : SL3) : Matrix (Fin 3) (Fin 3) ℝ := A.val

@[simp] theorem toMat_mul (A B : SL3) : toMat (A * B) = toMat A * toMat B := rfl

@[simp] theorem toMat_one : toMat (1 : SL3) = 1 := rfl

@[simp] theorem toMat_pow (A : SL3) (n : ℕ) : toMat (A ^ n) = toMat A ^ n := rfl

theorem toMat_injective : Function.Injective toMat := fun A B h => Subtype.ext h

/-- Extensionality through `toMat`. -/
theorem ext_toMat {A B : SL3} (h : toMat A = toMat B) : A = B := Subtype.ext h

/-- Extensionality on entries. -/
theorem ext_apply {A B : SL3} (h : ∀ i j, A i j = B i j) : A = B :=
  Matrix.SpecialLinearGroup.ext A B h

theorem toMat_apply (A : SL3) (i j : Fin 3) : toMat A i j = A i j := rfl

/-! ## The diagonal elements `aDiag t` -/

/-- The underlying matrix of `aDiag t`. -/
theorem toMat_aDiag (t : Fin 3 → ℝ) :
    toMat (aDiag t) = Matrix.diagonal (fun i => Real.exp (t i - (∑ j, t j) / 3)) := rfl

/-- Entries of `aDiag t`. -/
theorem aDiag_apply (t : Fin 3 → ℝ) (i j : Fin 3) :
    (aDiag t : SL3) i j = if i = j then Real.exp (t i - (∑ k, t k) / 3) else 0 := rfl

/-- `t ↦ aDiag t` is a homomorphism (ROUTE_LEAD D3). -/
theorem aDiag_add (s t : Fin 3 → ℝ) : aDiag s * aDiag t = aDiag (s + t) := by
  apply ext_toMat
  rw [toMat_mul, toMat_aDiag, toMat_aDiag, toMat_aDiag, Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  rw [← Real.exp_add]
  congr 1
  simp only [Pi.mul_apply, Pi.add_apply, Finset.sum_add_distrib]
  ring_nf

/-- `aDiag 0 = 1`. -/
theorem aDiag_zero : aDiag (0 : Fin 3 → ℝ) = 1 := by
  apply ext_toMat
  rw [toMat_aDiag, toMat_one]
  rw [show Matrix.diagonal (fun i => Real.exp ((0 : Fin 3 → ℝ) i - (∑ j, (0 : Fin 3 → ℝ) j) / 3))
      = Matrix.diagonal (fun _ : Fin 3 => (1 : ℝ)) from by
    congr 1
    ext i
    simp]
  exact Matrix.diagonal_one

/-- `aDiag (-t) = (aDiag t)⁻¹`. -/
theorem aDiag_neg_mul (t : Fin 3 → ℝ) : aDiag (-t) * aDiag t = 1 := by
  have hv : (-t + t : Fin 3 → ℝ) = 0 := by funext i; simp
  rw [aDiag_add, hv, aDiag_zero]

/-- `aDiag t * aDiag (-t) = 1`. -/
theorem aDiag_mul_neg (t : Fin 3 → ℝ) : aDiag t * aDiag (-t) = 1 := by
  have hv : (t + -t : Fin 3 → ℝ) = 0 := by funext i; simp
  rw [aDiag_add, hv, aDiag_zero]

/-- The action of `aDiag` is a homomorphism for the action on `X₃`. -/
theorem aDiag_smul_mul (s t : Fin 3 → ℝ) (x : X3) :
    aDiag s • (aDiag t • x) = aDiag (s + t) • x := by
  rw [← mul_smul, aDiag_add]

/-- `aDiag (-t)` inverts the action of `aDiag t`. -/
theorem aDiag_neg_smul (t : Fin 3 → ℝ) (x : X3) : aDiag (-t) • (aDiag t • x) = x := by
  rw [← mul_smul, aDiag_neg_mul, one_smul]

theorem aDiag_mul_neg_smul (t : Fin 3 → ℝ) (x : X3) : aDiag t • (aDiag (-t) • x) = x := by
  rw [← mul_smul, aDiag_mul_neg, one_smul]

/-! ## The semigroup elements `aPlus r s` and `a₀` -/

/-- `aPlus 0 0 = 1`. -/
theorem aPlus_zero : aPlus 0 0 = 1 := by
  have hv : (![(-(0 : ℝ)) - 0, (0 : ℝ), (0 : ℝ)] : Fin 3 → ℝ) = 0 := by
    funext i; fin_cases i <;> simp
  rw [aPlus, hv, aDiag_zero]

/-- `a₀ = aPlus 1 1`. -/
theorem a0_eq_aPlus : a0 = aPlus 1 1 := by
  have hv : (![-2, (1 : ℝ), (1 : ℝ)] : Fin 3 → ℝ) = ![-1 - 1, (1 : ℝ), (1 : ℝ)] := by
    funext i; fin_cases i <;> norm_num
  rw [a0, aPlus, hv]

/-- `aPlus r s * a0 = aPlus (r+1) (s+1)`: the `a₀`-forward invariance of `Drho ρ`. -/
theorem aPlus_mul_a0 (r s : ℝ) : aPlus r s * a0 = aPlus (r + 1) (s + 1) := by
  rw [aPlus, a0, aPlus, aDiag_add]
  congr 1
  funext i
  fin_cases i <;> simp <;> ring

/-- `aPlus r s • (a0 • x) = aPlus (r+1) (s+1) • x`. -/
theorem aPlus_a0_smul (r s : ℝ) (x : X3) : aPlus r s • (a0 • x) = aPlus (r + 1) (s + 1) • x := by
  rw [← mul_smul, aPlus_mul_a0]

/-! ## The shear matrix of EKL's `U_(ab)` -/

/-- The 3×3 shear matrix `[[1,p,q],[0,1,0],[0,r,1]]`: the general element of EKL's
`U_(12) = ⟨U_12, U_13, U_32⟩` (EKL Lemma 4.4(1), §4.5). -/
def Hmat (p q r : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![1, p, q; 0, 1, 0; 0, r, 1]

end Work.EKLContract
