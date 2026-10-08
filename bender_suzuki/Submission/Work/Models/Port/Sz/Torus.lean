/-
The maximal torus of `Sz(2^(2n+1))`.

The diagonal matrices `t(x)`, `x ∈ Fˣ`, form a subgroup of `SzModel n` isomorphic to `Fˣ`;
in particular `SzModel n` contains a cyclic subgroup of order `|F| - 1`.
-/
import Mathlib
import ChallengeDeps
import Submission.Work.Models.Port.Sz.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 1000000
set_option linter.unnecessarySeqFocus false
set_option linter.style.haveILetI false

open Matrix LeanEval.GroupTheory.Defs

namespace Submission.Sz

lemma szTg_mul (n : ℕ) (x y : (SzField n)ˣ) :
    szTg n x * szTg n y = szTg n (x * y) := by
  apply Units.ext
  simp only [Matrix.GeneralLinearGroup.coe_mul, szTg_coe]
  rw [szT_eq_diagonal, szT_eq_diagonal, szT_eq_diagonal, Matrix.diagonal_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal, Units.val_mul, mul_pow, _root_.mul_inv_rev] <;> ring

lemma szTg_one (n : ℕ) : szTg n 1 = 1 := by
  apply Units.ext
  simp only [szTg_coe, Matrix.GeneralLinearGroup.coe_one]
  rw [szT_eq_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

/-- The torus of `Sz(2^(2n+1))` as a monoid homomorphism `Fˣ → GL(4, F)`. -/
noncomputable def szTgHom (n : ℕ) : (SzField n)ˣ →* GL (Fin 4) (SzField n) where
  toFun := szTg n
  map_one' := szTg_one n
  map_mul' := fun x y => (szTg_mul n x y).symm

@[simp] lemma szTgHom_apply (n : ℕ) (x : (SzField n)ˣ) :
    szTgHom n x = szTg n x := rfl

lemma szTg_injective (n : ℕ) : Function.Injective (szTg n) := by
  intro x y h
  apply Units.ext
  have h11 : (x : SzField n) ^ (2 ^ n) = (y : SzField n) ^ (2 ^ n) := by
    have hc := congrArg (fun u : GL (Fin 4) (SzField n) =>
      ((u : Matrix (Fin 4) (Fin 4) (SzField n)))) h
    have h2 := congrFun (congrFun hc 1) 1
    simpa [szTg_coe, szT_eq_diagonal, Matrix.diagonal] using h2
  have h2 : (2 : SzField n) = 0 := CharP.cast_eq_zero (SzField n) 2
  have hyy : (y : SzField n) + (y : SzField n) = 0 := by rw [← two_mul, h2, zero_mul]
  have hzero : ((x : SzField n) + (y : SzField n)) ^ (2 ^ n) = 0 := by
    rw [add_pow_char_pow, h11]
    rw [← two_mul, h2, zero_mul]
  have hxy : (x : SzField n) + (y : SzField n) = 0 :=
    (pow_eq_zero_iff (by positivity : 2 ^ n ≠ 0)).mp hzero
  have key : ((x : SzField n) + y) + y = x := by rw [add_assoc, hyy, add_zero]
  rw [← key, hxy, zero_add]

lemma szTgHom_injective (n : ℕ) : Function.Injective (szTgHom n) := szTg_injective n

/-- The torus of `Sz(2^(2n+1))` sits inside `SzModel n`. -/
lemma szTgHom_range_le_szModel (n : ℕ) : (szTgHom n).range ≤ SzModel n := by
  rintro _ ⟨x, rfl⟩
  exact szTg_mem_szModel n x

/-- `SzModel n` contains a copy of `Fˣ`, hence a cyclic subgroup of order `|F| - 1`. -/
theorem exists_orderOf_eq_card_sub_one_szModel (n : ℕ) :
    ∃ g ∈ SzModel n, orderOf g = Nat.card (SzField n) - 1 := by
  obtain ⟨x, hx⟩ := IsCyclic.exists_generator (α := (SzField n)ˣ)
  refine ⟨szTg n x, szTg_mem_szModel n x, ?_⟩
  change orderOf (szTgHom n x) = Nat.card (SzField n) - 1
  rw [orderOf_injective (szTgHom n) (szTgHom_injective n) x,
    orderOf_eq_card_of_forall_mem_zpowers hx]
  exact Nat.card_units (SzField n)

end Submission.Sz
