/-
The unipotent radical `U` of `SU(3, 2^n)`, i.e. the group of "upper unitriangular" matrices
preserving the Hermitian form `J3`.  Writing `q = 2^n` and using that the Hermitian form has
antidiagonal Gram matrix, an element of `U` has the shape

  `u(b,c) = !![1, b, c; 0, 1, b^q; 0, 0, 1]`   with   `c + c^q = b^(q+1)`.

`U` is a subgroup of `SU(3, 2^n)` of order `q^3`.
-/
import Mathlib
import ChallengeDeps
import Submission.Work.Models.Port.PSU3.Herm
import Submission.Work.Models.Port.Commons.FieldTheory.FiniteField.trace_surjective_galoisField_even
import Submission.Work.Models.Port.Commons.FieldTheory.Finite.fixed_card_pow_two

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 3200000
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

open Matrix LeanEval.GroupTheory.Defs

namespace Submission.PSU3

/-- The matrix `u(b,c) = !![1, b, c; 0, 1, b^q; 0, 0, 1]`. -/
noncomputable def suUmat (n : ℕ) (b c : F n) : Matrix (Fin 3) (Fin 3) (F n) :=
  !![1, b, c; 0, 1, b ^ (2 ^ n); 0, 0, 1]

lemma suUmat_det (n : ℕ) (b c : F n) : (suUmat n b c).det = 1 := by
  rw [suUmat, Matrix.det_fin_three]
  simp

/-- `u(b,c)` as an element of `GL(3, 2^(2n))`. -/
noncomputable def suUg (n : ℕ) (b c : F n) : GL (Fin 3) (F n) :=
  Matrix.GeneralLinearGroup.mk'' (suUmat n b c) (by rw [suUmat_det]; exact isUnit_one)

@[simp] lemma suUg_coe (n : ℕ) (b c : F n) :
    ((suUg n b c : GL (Fin 3) (F n)) : Matrix (Fin 3) (Fin 3) (F n)) = suUmat n b c :=
  Matrix.GeneralLinearGroup.val_mk'' _ _

lemma suUg_injective (n : ℕ) :
    Function.Injective (fun p : F n × F n => suUg n p.1 p.2) := by
  intro p q h
  have h' := congrArg (fun g : GL (Fin 3) (F n) =>
    ((g : GL (Fin 3) (F n)) : Matrix (Fin 3) (Fin 3) (F n))) h
  simp only [suUg_coe] at h'
  have h01 := congrFun (congrFun h' 0) 1
  have h02 := congrFun (congrFun h' 0) 2
  simp [suUmat] at h01 h02
  exact Prod.ext h01 (by
    have h12 := congrFun (congrFun h' 1) 2
    simp [suUmat] at h12
    -- h12 : b p ^ 2^n = b q ^ 2^n  ... gives c? no. Use (0,2) for c.
    exact h02)

/-- The multiplication law of `U`. -/
lemma suUg_mul (n : ℕ) (b c b' c' : F n) :
    suUg n b c * suUg n b' c' = suUg n (b + b') (c + c' + b * b' ^ (2 ^ n)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply Units.ext
  simp only [Matrix.GeneralLinearGroup.coe_mul, suUg_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [suUmat, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals try ring
  rw [add_pow_char_pow]

/-- `b ^ (2 ^ (2n)) = b` for every element of `GF(2^(2n))`. -/
lemma pow_card_sq (n : ℕ) (b : F n) : b ^ (2 ^ (2 * n)) = b := by
  rcases eq_or_ne n 0 with rfl | hn
  · norm_num
  · exact Commons.FieldTheory.FiniteField.galoisField_pow_card_pow_self (p := 2) (2 * n) (by omega) b

/-- `u(b,c)` is special-unitary when `c + c^q = b^(q+1)`. -/
lemma suUg_isSU3 (n : ℕ) (b c : F n)
    (hc : c + c ^ (2 ^ n) = b ^ (2 ^ n + 1)) : IsSU3 (suUg n b c) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbq : b ^ (2 ^ (2 * n)) = b := pow_card_sq n b
  have hbqq : (b ^ (2 ^ n)) ^ (2 ^ n) = b := by
    rw [← pow_mul, show 2 ^ n * 2 ^ n = 2 ^ (2 * n) by rw [← pow_add]; ring, hbq]
  refine ⟨?_, ?_⟩
  · show herm (suUmat n b c) * J3 * suUmat n b c = J3
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [herm, J3, suUmat, Matrix.mul_apply, Fin.sum_univ_three, frob_apply]
    · exact CharTwo.add_self_eq_zero (b ^ (2 ^ n))
    · rw [hbqq]; exact CharTwo.add_self_eq_zero b
    · rw [hbqq, ← pow_succ', ← hc]
      rw [show c + (c + c ^ 2 ^ n) + c ^ 2 ^ n = (c + c) + (c ^ 2 ^ n + c ^ 2 ^ n) by ring,
        CharTwo.add_self_eq_zero c, CharTwo.add_self_eq_zero (c ^ 2 ^ n), add_zero]
  · show GeneralLinearGroup.det (suUg n b c) = 1
    apply Units.ext
    show ((suUg n b c : GL (Fin 3) (F n)) : Matrix (Fin 3) (Fin 3) (F n)).det = 1
    rw [suUg_coe, suUmat_det]

lemma suUg_zero (n : ℕ) : suUg n 0 0 = 1 := by
  apply Units.ext
  simp only [suUg_coe, suUmat, Matrix.GeneralLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The inverse of `u(b,c)` is `u(b, c + b^(q+1))`. -/
lemma suUg_inv (n : ℕ) (b c : F n) :
    suUg n b (c + b ^ (2 ^ n + 1)) = (suUg n b c)⁻¹ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [eq_inv_iff_mul_eq_one, suUg_mul]
  have h1 : b + b = 0 := CharTwo.add_self_eq_zero b
  have h2 : c + b ^ (2 ^ n + 1) + c + b * b ^ (2 ^ n) = 0 := by
    rw [← pow_succ' b (2 ^ n),
      show c + b ^ (2 ^ n + 1) + c + b ^ (2 ^ n + 1) =
        (c + c) + (b ^ (2 ^ n + 1) + b ^ (2 ^ n + 1)) by ring,
      CharTwo.add_self_eq_zero c, CharTwo.add_self_eq_zero (b ^ (2 ^ n + 1)), add_zero]
  rw [h1, h2]
  exact suUg_zero n

/-- The condition on the parameters is preserved under multiplication. -/
lemma suU_cond_mul (n : ℕ) (b c b' c' : F n)
    (hc : c + c ^ (2 ^ n) = b ^ (2 ^ n + 1))
    (hc' : c' + c' ^ (2 ^ n) = b' ^ (2 ^ n + 1)) :
    (c + c' + b * b' ^ (2 ^ n)) + (c + c' + b * b' ^ (2 ^ n)) ^ (2 ^ n) =
      (b + b') ^ (2 ^ n + 1) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hb'q : ((b' ^ (2 ^ n)) ^ (2 ^ n)) = b' := by
    rw [← pow_mul, show 2 ^ n * 2 ^ n = 2 ^ (2 * n) by rw [← pow_add]; ring, pow_card_sq]
  have key : (c + c' + b * b' ^ (2 ^ n)) ^ (2 ^ n) =
      c ^ (2 ^ n) + c' ^ (2 ^ n) + b ^ (2 ^ n) * b' := by
    rw [show c + c' + b * b' ^ (2 ^ n) = (c + c') + b * b' ^ (2 ^ n) by ring,
      add_pow_char_pow, add_pow_char_pow, mul_pow, hb'q]
  have hbb' : (b + b') ^ (2 ^ n + 1) = b ^ (2 ^ n) * b + b ^ (2 ^ n) * b'
      + b' ^ (2 ^ n) * b + b' ^ (2 ^ n) * b' := by
    rw [pow_succ', add_pow_char_pow]
    ring
  rw [key, hbb',
    show c + c' + b * b' ^ (2 ^ n) + (c ^ (2 ^ n) + c' ^ (2 ^ n) + b ^ (2 ^ n) * b') =
      (c + c ^ (2 ^ n)) + (c' + c' ^ (2 ^ n)) + b * b' ^ (2 ^ n) + b ^ (2 ^ n) * b' by ring,
    hc, hc']
  rw [pow_succ]
  ring

/-- The condition on the parameters is preserved under inversion. -/
lemma suU_cond_inv (n : ℕ) (b c : F n) (hc : c + c ^ (2 ^ n) = b ^ (2 ^ n + 1)) :
    (c + b ^ (2 ^ n + 1)) + (c + b ^ (2 ^ n + 1)) ^ (2 ^ n) = b ^ (2 ^ n + 1) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbfix : (b ^ (2 ^ n + 1)) ^ (2 ^ n) = b ^ (2 ^ n + 1) := by
    rw [← pow_mul, show (2 ^ n + 1) * 2 ^ n = 2 ^ (2 * n) + 2 ^ n by ring, pow_add,
      pow_card_sq, ← pow_succ']
  rw [add_pow_char_pow, hbfix,
    show c + b ^ (2 ^ n + 1) + (c ^ (2 ^ n) + b ^ (2 ^ n + 1)) =
      (c + c ^ (2 ^ n)) + (b ^ (2 ^ n + 1) + b ^ (2 ^ n + 1)) by ring,
    hc, CharTwo.add_self_eq_zero (b ^ (2 ^ n + 1)), add_zero]

/-- The unipotent radical `U ≤ SU(3, 2^n)`. -/
noncomputable def suU (n : ℕ) : Subgroup (GL (Fin 3) (F n)) where
  carrier := {A | ∃ b c : F n, c + c ^ (2 ^ n) = b ^ (2 ^ n + 1) ∧ A = suUg n b c}
  mul_mem' := by
    rintro A B ⟨b, c, hc, rfl⟩ ⟨b', c', hc', rfl⟩
    exact ⟨b + b', c + c' + b * b' ^ (2 ^ n), suU_cond_mul n b c b' c' hc hc',
      by rw [suUg_mul]⟩
  one_mem' := ⟨0, 0, by
    rw [zero_pow (pow_ne_zero _ (by norm_num)), zero_pow (by positivity), add_zero],
    (suUg_zero n).symm⟩
  inv_mem' := by
    rintro A ⟨b, c, hc, rfl⟩
    exact ⟨b, c + b ^ (2 ^ n + 1), suU_cond_inv n b c hc, (suUg_inv n b c).symm⟩

lemma suU_le_SU3 (n : ℕ) : suU n ≤ SU3 n := by
  rintro A ⟨b, c, hc, rfl⟩
  exact suUg_isSU3 n b c hc

/-- The tautological map from the solution set to `U`. -/
noncomputable def suUOfSol (n : ℕ) :
    {p : F n × F n // p.2 + p.2 ^ (2 ^ n) = p.1 ^ (2 ^ n + 1)} → ↥(suU n) :=
  fun p => ⟨suUg n p.1.1 p.1.2, ⟨p.1.1, p.1.2, p.2, rfl⟩⟩

lemma suUOfSol_injective (n : ℕ) : Function.Injective (suUOfSol n) := by
  intro p q h
  have h' : (suUOfSol n p : GL (Fin 3) (F n)) = suUOfSol n q := congrArg Subtype.val h
  apply Subtype.ext
  exact suUg_injective n h'

lemma suUOfSol_surjective (n : ℕ) : Function.Surjective (suUOfSol n) := by
  rintro ⟨A, b, c, hc, rfl⟩
  exact ⟨⟨(b, c), hc⟩, rfl⟩

/-! ## The order of `U` -/

lemma pow_fix_q_succ (n : ℕ) (b : F n) : (b ^ (2 ^ n + 1)) ^ (2 ^ n) = b ^ (2 ^ n + 1) := by
  rw [← pow_mul, show (2 ^ n + 1) * 2 ^ n = 2 ^ (2 * n) + 2 ^ n by ring, pow_add,
    pow_card_sq, ← pow_succ']

/-- A base solution `c_b` of `c + c^q = b^(q+1)`. -/
noncomputable def suCb (n : ℕ) (hn : 1 ≤ n) (b : F n) : F n :=
  Classical.choose (Commons.FieldTheory.FiniteField.trace_surjective_galoisField_even n hn
    (b ^ (2 ^ n + 1)) (pow_fix_q_succ n b))

lemma suCb_spec (n : ℕ) (hn : 1 ≤ n) (b : F n) :
    suCb n hn b + (suCb n hn b) ^ (2 ^ n) = b ^ (2 ^ n + 1) :=
  Classical.choose_spec (Commons.FieldTheory.FiniteField.trace_surjective_galoisField_even n hn
    (b ^ (2 ^ n + 1)) (pow_fix_q_succ n b))

lemma suU_cond_of_fixed (n : ℕ) (hn : 1 ≤ n) (b k : F n) (hk : k ^ (2 ^ n) = k) :
    (suCb n hn b + k) + (suCb n hn b + k) ^ (2 ^ n) = b ^ (2 ^ n + 1) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [show (suCb n hn b + k) + (suCb n hn b + k) ^ (2 ^ n) =
      suCb n hn b + (suCb n hn b) ^ (2 ^ n) + (k + k ^ (2 ^ n)) by
    rw [add_pow_char_pow]; ring,
    suCb_spec n hn b, hk, CharTwo.add_self_eq_zero k, add_zero]

/-- The solution set of `c + c^q = b^(q+1)` is in bijection with `F × GF(2^n)`. -/
noncomputable def suUSolEquiv (n : ℕ) (hn : 1 ≤ n) :
    (F n × {k : F n // k ^ (2 ^ n) = k}) ≃
      {p : F n × F n // p.2 + p.2 ^ (2 ^ n) = p.1 ^ (2 ^ n + 1)} := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine Equiv.ofBijective
    (fun q : F n × {k : F n // k ^ (2 ^ n) = k} =>
      (⟨(q.1, suCb n hn q.1 + q.2.1), suU_cond_of_fixed n hn q.1 q.2.1 q.2.2⟩ :
        {p : F n × F n // p.2 + p.2 ^ (2 ^ n) = p.1 ^ (2 ^ n + 1)})) ⟨?_, ?_⟩
  · rintro ⟨b, k⟩ ⟨b', k'⟩ h
    have h' : (b, suCb n hn b + k.1) = (b', suCb n hn b' + k'.1) :=
      congrArg Subtype.val h
    simp only [Prod.mk.injEq] at h'
    obtain ⟨hb, hk⟩ := h'
    subst hb
    refine Prod.ext rfl (Subtype.ext ?_)
    exact add_left_cancel hk
  · rintro ⟨⟨b, c⟩, hc⟩
    refine ⟨(b, ⟨c + suCb n hn b, ?_⟩), ?_⟩
    · -- c + suCb b is fixed by Frobenius
      have hk : (c + suCb n hn b) + (c + suCb n hn b) ^ (2 ^ n) = 0 := by
        rw [show (c + suCb n hn b) + (c + suCb n hn b) ^ (2 ^ n) =
          (c + c ^ (2 ^ n)) + (suCb n hn b + (suCb n hn b) ^ (2 ^ n)) by
            rw [add_pow_char_pow]; ring,
          hc, suCb_spec n hn b, CharTwo.add_self_eq_zero (b ^ (2 ^ n + 1))]
      have h2 : (c + suCb n hn b) ^ (2 ^ n) = (c + suCb n hn b) := by
        calc (c + suCb n hn b) ^ (2 ^ n) = 0 + (c + suCb n hn b) ^ (2 ^ n) := by rw [zero_add]
          _ = ((c + suCb n hn b) + (c + suCb n hn b) ^ (2 ^ n)) +
                (c + suCb n hn b) ^ (2 ^ n) := by rw [hk]
          _ = (c + suCb n hn b) +
                ((c + suCb n hn b) ^ (2 ^ n) + (c + suCb n hn b) ^ (2 ^ n)) := by
                rw [add_assoc]
          _ = (c + suCb n hn b) + 0 := by rw [CharTwo.add_self_eq_zero]
          _ = c + suCb n hn b := by rw [add_zero]
      exact h2
    · apply Subtype.ext
      show (b, suCb n hn b + (c + suCb n hn b)) = (b, c)
      rw [Prod.mk.injEq]
      refine ⟨rfl, ?_⟩
      rw [show suCb n hn b + (c + suCb n hn b) =
          (suCb n hn b + suCb n hn b) + c by ring,
        CharTwo.add_self_eq_zero (suCb n hn b), zero_add]

/-- `|U| = q^3`. -/
theorem card_suU (n : ℕ) (hn : 1 ≤ n) : Nat.card ↥(suU n) = 2 ^ (3 * n) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : Nat.card ↥(suU n) = Nat.card
      {p : F n × F n // p.2 + p.2 ^ (2 ^ n) = p.1 ^ (2 ^ n + 1)} :=
    Nat.card_congr (Equiv.ofBijective _
      ⟨suUOfSol_injective n, suUOfSol_surjective n⟩).symm
  rw [h1, ← Nat.card_congr (suUSolEquiv n hn), Nat.card_prod]
  rw [GaloisField.card 2 (2 * n) (by omega),
    Commons.FieldTheory.Finite.fixed_card_pow_two n (by omega)]
  rw [← pow_add]
  congr 1
  ring

end Submission.PSU3
