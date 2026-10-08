/-
The Suzuki 2-group `Sz(2^(2n+1))` as a subgroup of `GL(4, 2^(2n+1))`.

The set `{u(a,b) : a, b ∈ F}` of root elements of `Sz(2^(2n+1))` is a subgroup of order
`|F|^2`, with multiplication law

  `u(a,b) * u(c,d) = u(a+c, b+d+a·c^(2^(n+1)))`.

This is the Sylow `2`-subgroup of `Sz(2^(2n+1))`; the multiplication law is
`Commons.GroupTheory.Suzuki.szU_mul`.
-/
import Mathlib
import ChallengeDeps
import Submission.Work.Models.Port.Sz.Basic
import Submission.Work.Models.Port.Commons.GroupTheory.Suzuki.szU_mul
import Submission.Work.Models.Port.Commons.FieldTheory.FiniteField.exists_pow_two_pow_ne_self
import Submission.Work.Models.Port.Commons.GroupTheory.Suzuki.szU_sq

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unnecessarySeqFocus false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open Matrix LeanEval.GroupTheory.Defs

namespace Submission.Sz

/-- In `GF(2^(2n+1))`, `2 = 0`. -/
lemma szField_two_eq_zero (n : ℕ) : (2 : SzField n) = 0 :=
  CharP.cast_eq_zero (SzField n) 2

/-! ## The multiplication law at the level of `GL` -/

lemma szUg_mul (n : ℕ) (a b c d : SzField n) :
    szUg n a b * szUg n c d = szUg n (a + c) (b + d + a * c ^ (2 ^ (n + 1))) := by
  apply Units.ext
  simp only [Matrix.GeneralLinearGroup.coe_mul, szUg_coe]
  exact Commons.GroupTheory.Suzuki.szU_mul n a b c d

lemma szUg_zero (n : ℕ) : szUg n 0 0 = 1 := by
  apply Units.ext
  simp only [szUg_coe]
  exact szU_zero n

lemma szUg_inv (n : ℕ) (a b : SzField n) :
    szUg n a (b + a ^ (1 + 2 ^ (n + 1))) = (szUg n a b)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one]
  have h2 : (2 : SzField n) = 0 := szField_two_eq_zero n
  have h1 : a + a = 0 := by rw [← two_mul, h2, zero_mul]
  have hx : a * a ^ (2 ^ (n + 1)) = a ^ (1 + 2 ^ (n + 1)) := by
    rw [show (1 : ℕ) + 2 ^ (n + 1) = 2 ^ (n + 1) + 1 from by ring]
    exact (pow_succ' a (2 ^ (n + 1))).symm
  have h3 : b + a ^ (1 + 2 ^ (n + 1)) + b + a * a ^ (2 ^ (n + 1)) = 0 := by
    rw [hx]
    ring_nf
    rw [h2]
    ring
  rw [szUg_mul, h1, h3, szUg_zero]

lemma szUg_injective (n : ℕ) :
    Function.Injective (fun p : SzField n × SzField n => szUg n p.1 p.2) := by
  intro p q h
  apply szU_injective n
  have := congrArg (fun u : GL (Fin 4) (SzField n) =>
    ((u : Matrix (Fin 4) (Fin 4) (SzField n)))) h
  simpa using this

/-! ## The Suzuki 2-group -/

/-- The Suzuki 2-group: the set of root elements `u(a,b)` inside `GL(4, F)`. -/
noncomputable def szTwoGroup (n : ℕ) : Subgroup (GL (Fin 4) (SzField n)) where
  carrier := {A | ∃ a b, A = szUg n a b}
  one_mem' := ⟨0, 0, (szUg_zero n).symm⟩
  mul_mem' := by
    rintro A B ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    exact ⟨a + c, b + d + a * c ^ (2 ^ (n + 1)), szUg_mul n a b c d⟩
  inv_mem' := by
    rintro A ⟨a, b, rfl⟩
    exact ⟨a, b + a ^ (1 + 2 ^ (n + 1)), (szUg_inv n a b).symm⟩

lemma szTwoGroup_le_szModel (n : ℕ) : szTwoGroup n ≤ SzModel n := by
  intro A hA
  obtain ⟨a, b, rfl⟩ := hA
  exact szUg_mem_szModel n a b

/-- The root elements are parametrised bijectively by `F × F`. -/
noncomputable def szTwoEquiv (n : ℕ) : (SzField n × SzField n) ≃ szTwoGroup n :=
  Equiv.ofBijective
    (fun p => (⟨szUg n p.1 p.2, p.1, p.2, rfl⟩ : szTwoGroup n))
    ⟨fun p q h => szUg_injective n (Subtype.ext_iff.mp h),
      fun A => by
        obtain ⟨a, b, hab⟩ := A.2
        exact ⟨(a, b), Subtype.ext hab.symm⟩⟩

lemma card_szTwoGroup (n : ℕ) :
    Nat.card (szTwoGroup n) = Nat.card (SzField n) ^ 2 := by
  rw [← Nat.card_congr (szTwoEquiv n), Nat.card_prod, sq]

lemma card_szField (n : ℕ) : Nat.card (SzField n) = 2 ^ (2 * n + 1) :=
  GaloisField.card 2 (2 * n + 1) (by omega)

lemma card_szTwoGroup_eq (n : ℕ) : Nat.card (szTwoGroup n) = 2 ^ (4 * n + 2) := by
  rw [card_szTwoGroup, card_szField, ← pow_mul]
  congr 1
  ring

lemma isPGroup_szTwoGroup (n : ℕ) : IsPGroup 2 (szTwoGroup n) := by
  apply IsPGroup.of_card (n := 4 * n + 2)
  rw [card_szTwoGroup_eq]

/-! ## An element of order four -/

lemma szUg_one_zero_sq (n : ℕ) : (szUg n 1 0) ^ 2 = szUg n 0 1 := by
  have h2 : (2 : SzField n) = 0 := szField_two_eq_zero n
  have h : (szUg n 1 0) * (szUg n 1 0) = szUg n 0 1 := by
    rw [szUg_mul,
      show (1 : SzField n) + 1 = 0 by rw [← two_mul, h2, zero_mul],
      show (0 : SzField n) + 0 + 1 * 1 ^ (2 ^ (n + 1)) = 1 by simp]
  rw [pow_two, h]

lemma szUg_zero_one_sq (n : ℕ) : (szUg n 0 1) ^ 2 = 1 := by
  have h2 : (2 : SzField n) = 0 := szField_two_eq_zero n
  have h : (szUg n 0 1) * (szUg n 0 1) = 1 := by
    rw [szUg_mul, show (0 : SzField n) + 0 = 0 from rfl,
      show (1 : SzField n) + 1 + 0 * 0 ^ (2 ^ (n + 1)) = 0 by
        rw [← two_mul, h2, zero_mul, zero_mul, add_zero],
      szUg_zero]
  rw [pow_two, h]

lemma orderOf_szUg_one_zero (n : ℕ) : orderOf (szUg n 1 0) = 4 := by
  have h4' : (szUg n 1 0) ^ (2 * 2) = 1 := by
    rw [pow_mul, szUg_one_zero_sq, szUg_zero_one_sq]
  have h4 : (szUg n 1 0) ^ 4 = 1 := by simpa using h4'
  have h2 : (szUg n 1 0) ^ 2 ≠ 1 := by
    rw [szUg_one_zero_sq]
    intro h
    have hp : ((0 : SzField n), (1 : SzField n)) = ((0 : SzField n), (0 : SzField n)) :=
      szUg_injective n (by show szUg n 0 1 = szUg n 0 0; rw [h, szUg_zero])
    exact one_ne_zero (Prod.ext_iff.mp hp).2
  have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := szUg n 1 0)
    (by simpa using h2) (by simpa using h4)
  exact h.trans (by norm_num)

/-- `SzModel n` contains an element of order `4`. -/
lemma exists_orderOf_four_szModel (n : ℕ) :
    ∃ g ∈ SzModel n, orderOf g = 4 :=
  ⟨szUg n 1 0, szUg_mem_szModel n 1 0, orderOf_szUg_one_zero n⟩


/-! ## `SzModel n` is not abelian (for `n ≥ 1`) -/

/-- For `n ≥ 1` the Suzuki group is not abelian: the root elements `u(x,0)` and `u(1,0)` fail
to commute, because `x ↦ x^(2^(n+1))` is not the identity on `GF(2^(2n+1))`. -/
theorem exists_not_commutative_szModel (n : ℕ) (hn : 1 ≤ n) :
    ∃ A B : SzModel n, A * B ≠ B * A := by
  obtain ⟨x, hx⟩ := Commons.FieldTheory.FiniteField.exists_pow_two_pow_ne_self n hn
  refine ⟨⟨szUg n x 0, szUg_mem_szModel n x 0⟩,
    ⟨szUg n 1 0, szUg_mem_szModel n 1 0⟩, ?_⟩
  intro h
  have h2 : szUg n x 0 * szUg n 1 0 = szUg n 1 0 * szUg n x 0 := Subtype.ext_iff.mp h
  rw [szUg_mul, szUg_mul] at h2
  have hcomp2 : (x + 1, 0 + 0 + x * 1 ^ (2 ^ (n + 1))) =
      (1 + x, 0 + 0 + 1 * x ^ (2 ^ (n + 1))) := szUg_injective n h2
  have hcomp := (Prod.ext_iff.mp hcomp2).2
  simp at hcomp
  exact hx hcomp.symm


/-! ## The Suzuki 2-group has exponent dividing four -/

lemma szU_zero_param (n : ℕ) (c : SzField n) :
    szU n 0 c =
      !![1, 0, c, c ^ (2 ^ (n + 1));
         0, 1, 0, c;
         0, 0, 1, 0;
         0, 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [szU]

lemma szU_sq_eq (n : ℕ) (a b : SzField n) :
    szU n a b * szU n a b = szU n 0 (a ^ (1 + 2 ^ (n + 1))) := by
  rw [szU_zero_param]
  exact Commons.GroupTheory.Suzuki.szU_sq n a b

lemma szUg_sq (n : ℕ) (a b : SzField n) :
    (szUg n a b) ^ 2 = szUg n 0 (a ^ (1 + 2 ^ (n + 1))) := by
  apply Units.ext
  rw [pow_two, Matrix.GeneralLinearGroup.coe_mul, szUg_coe, szU_sq_eq, szUg_coe]

lemma szUg_pow_four (n : ℕ) (a b : SzField n) : (szUg n a b) ^ 4 = 1 := by
  have h : (szUg n a b) ^ (2 * 2) = 1 := by
    rw [pow_mul, szUg_sq, szUg_sq,
      zero_pow (show 1 + 2 ^ (n + 1) ≠ 0 by positivity), szUg_zero]
  simpa using h

lemma orderOf_szUg_dvd_four (n : ℕ) (a b : SzField n) : orderOf (szUg n a b) ∣ 4 :=
  orderOf_dvd_iff_pow_eq_one.mpr (szUg_pow_four n a b)

/-- Every element of the Suzuki 2-group has order dividing `4`. -/
lemma szTwoGroup_orderOf_dvd_four (n : ℕ) (A : szTwoGroup n) : orderOf A ∣ 4 := by
  obtain ⟨a, b, hab⟩ := A.2
  have hA : A = (⟨szUg n a b, a, b, rfl⟩ : szTwoGroup n) := Subtype.ext hab
  have hord : orderOf (⟨szUg n a b, a, b, rfl⟩ : szTwoGroup n) = orderOf (szUg n a b) :=
    (Subgroup.orderOf_coe _).symm
  rw [hA, hord]
  exact orderOf_szUg_dvd_four n a b

end Submission.Sz
