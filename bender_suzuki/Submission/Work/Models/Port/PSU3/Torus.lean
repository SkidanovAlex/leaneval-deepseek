/-
The maximal torus `T` of `SU(3, 2^n)`: the diagonal matrices
`diag(a, a^(q-1), a^(-q))` with `a ∈ GF(q^2)^×`, a cyclic group of order `q^2 - 1`.

Everything is parametrised by a unit `a` of the field, so the torus is isomorphic to
`(GF(2^(2n)))^×` and has order `2^(2n) - 1`.
-/
import Mathlib
import ChallengeDeps
import Submission.Work.Models.Port.PSU3.Unipotent

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 3200000
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
set_option linter.unnecessarySeqFocus false

open Matrix LeanEval.GroupTheory.Defs

namespace Submission.PSU3

/-- The diagonal matrix `diag(a, a^(q-1), a^(-q))`. -/
noncomputable def suTmat (n : ℕ) (a : (F n)ˣ) : Matrix (Fin 3) (Fin 3) (F n) :=
  Matrix.diagonal ![↑a, (↑a) ^ (2 ^ n - 1), ((↑a) ^ (2 ^ n))⁻¹]

lemma suTmat_det (n : ℕ) (a : (F n)ˣ) : (suTmat n a).det = 1 := by
  rw [suTmat, Matrix.det_diagonal, Fin.prod_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  have ha : (a : F n) ≠ 0 := Units.ne_zero a
  rw [← pow_succ', Nat.sub_add_cancel Nat.one_le_two_pow,
    mul_inv_cancel₀ (pow_ne_zero _ ha)]

/-- `diag(a, a^(q-1), a^(-q))` as an element of `GL(3, 2^(2n))`. -/
noncomputable def suTg (n : ℕ) (a : (F n)ˣ) : GL (Fin 3) (F n) :=
  Matrix.GeneralLinearGroup.mk'' (suTmat n a) (by rw [suTmat_det]; exact isUnit_one)

@[simp] lemma suTg_coe (n : ℕ) (a : (F n)ˣ) :
    ((suTg n a : GL (Fin 3) (F n)) : Matrix (Fin 3) (Fin 3) (F n)) = suTmat n a :=
  Matrix.GeneralLinearGroup.val_mk'' _ _

/-- `diag(a, a^(q-1), a^(-q))` is special-unitary. -/
lemma suTg_isSU3 (n : ℕ) (a : (F n)ˣ) : IsSU3 (suTg n a) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ha : (a : F n) ≠ 0 := Units.ne_zero a
  have hqq : ((a : F n) ^ (2 ^ n)) ^ (2 ^ n) = (a : F n) := by
    rw [← pow_mul, show 2 ^ n * 2 ^ n = 2 ^ (2 * n) by rw [← pow_add]; ring, pow_card_sq]
  have h11 : ((a : F n) ^ (2 ^ n - 1)) ^ (2 ^ n) * (a : F n) ^ (2 ^ n - 1) = 1 := by
    rcases eq_or_ne n 0 with rfl | hn'
    · norm_num
    · rw [← pow_mul, ← pow_add, exp_identity n (by omega)]
      have h2 : 2 ^ (2 * n) ≠ 0 := pow_ne_zero _ (by norm_num)
      have h3 : (a : F n) ^ (2 ^ (2 * n) - 1) * (a : F n) = 1 * (a : F n) := by
        rw [one_mul, pow_sub_one_mul h2, pow_card_sq]
      exact mul_right_cancel₀ ha h3
  have h20 : (((a : F n) ^ (2 ^ n)) ^ (2 ^ n))⁻¹ * (a : F n) = 1 := by
    rw [hqq, inv_mul_cancel₀ ha]
  have h02 : (a : F n) ^ (2 ^ n) * ((a : F n) ^ (2 ^ n))⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ ha)
  refine ⟨?_, ?_⟩
  · show herm (suTmat n a) * J3 * suTmat n a = J3
    rw [suTmat, herm_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [J3, Matrix.diagonal, Matrix.mul_apply, Fin.sum_univ_three,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
        Matrix.tail_cons, h02, h11, h20]
  · show GeneralLinearGroup.det (suTg n a) = 1
    apply Units.ext
    show ((suTg n a : GL (Fin 3) (F n)) : Matrix (Fin 3) (Fin 3) (F n)).det = 1
    rw [suTg_coe, suTmat_det]

/-- Multiplication of torus elements. -/
lemma suTg_one (n : ℕ) : suTg n 1 = 1 := by
  apply Units.ext
  rw [suTg_coe, suTmat, Matrix.GeneralLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_apply, Matrix.one_apply]

/-- Multiplication of torus elements. -/
lemma suTg_mul (n : ℕ) (a b : (F n)ˣ) : suTg n a * suTg n b = suTg n (a * b) := by
  apply Units.ext
  simp only [Matrix.GeneralLinearGroup.coe_mul, suTg_coe]
  rw [suTmat, suTmat, suTmat, Matrix.diagonal_mul_diagonal, Matrix.diagonal_eq_diagonal_iff]
  intro i
  fin_cases i <;> simp [Units.val_mul, mul_pow] <;> ring

/-- The maximal torus `T ≤ SU(3, 2^n)`. -/
noncomputable def suT (n : ℕ) : Subgroup (GL (Fin 3) (F n)) where
  carrier := {A | ∃ a : (F n)ˣ, A = suTg n a}
  mul_mem' := by
    rintro A B ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a * b, suTg_mul n a b⟩
  one_mem' := ⟨1, (suTg_one n).symm⟩
  inv_mem' := by
    rintro A ⟨a, rfl⟩
    exact ⟨a⁻¹, by rw [inv_eq_iff_mul_eq_one, suTg_mul, mul_inv_cancel, suTg_one]⟩

lemma suT_le_SU3 (n : ℕ) : suT n ≤ SU3 n := by
  rintro A ⟨a, rfl⟩
  exact suTg_isSU3 n a

/-- `suTg` is injective, so the torus is isomorphic to `(GF(2^(2n)))^×`. -/
lemma suTg_injective (n : ℕ) : Function.Injective (suTg n) := by
  intro a b h
  have h' : ((suTg n a : GL (Fin 3) (F n)) : Matrix (Fin 3) (Fin 3) (F n)) =
      suTg n b := congrArg (fun x : GL (Fin 3) (F n) =>
        ((x : GL (Fin 3) (F n)) : Matrix (Fin 3) (Fin 3) (F n))) h
  rw [suTg_coe, suTg_coe, suTmat, suTmat, Matrix.diagonal_eq_diagonal_iff] at h'
  exact Units.ext (by simpa using h' 0)

/-- The maximal torus is cyclic of order `q^2 - 1 = 2^(2n) - 1`. -/
theorem card_suT (n : ℕ) (hn : 1 ≤ n) : Nat.card ↥(suT n) = 2 ^ (2 * n) - 1 := by
  have hbij : Function.Bijective (fun a : (F n)ˣ => (⟨suTg n a, ⟨a, rfl⟩⟩ : ↥(suT n))) :=
    ⟨fun a b h => suTg_injective n (Subtype.ext_iff.mp h),
      fun A => A.2.imp fun a ha => by apply Subtype.ext; exact ha.symm⟩
  have hcard := Nat.card_congr (Equiv.ofBijective _ hbij)
  rw [← hcard, Nat.card_units, GaloisField.card 2 (2 * n) (by omega)]

end Submission.PSU3
