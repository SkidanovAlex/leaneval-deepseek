/-
The Borel subgroup `B = U ⋊ T` of `SU(3, 2^n)`.

Here `U` is the unipotent radical (`|U| = q^3`) and `T` the maximal torus (`|T| = q^2 - 1`).
The torus acts on `U` by conjugation,
`t(a) · u(b,c) · t(a)⁻¹ = u(a·b·β⁻¹, a·c·a^q)`, with `β = a^(q-1)`.
We deduce `U ⊓ T = ⊥`, that `T` normalises `U`, and hence
`|B| = |U| · |T| = q^3 (q^2 - 1)`.
-/
import Mathlib
import ChallengeDeps
import Submission.Work.Models.Port.PSU3.Torus
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.card_sup_of_inf_eq_bot_of_le_normalizer

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

/-! ## Scalar identities for the exponents -/

/-- `(2^n - 1)(2^n + 1) = 2^(2n) - 1`. -/
lemma two_pow_sub_one_mul_add_one (n : ℕ) :
    (2 ^ n - 1) * (2 ^ n + 1) = 2 ^ (2 * n) - 1 := by
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hs : 1 ≤ (2 ^ n) ^ 2 := by nlinarith [h1]
  have hsq : 2 ^ (2 * n) = (2 ^ n) ^ 2 := by rw [← pow_mul, Nat.mul_comm]
  rw [hsq]
  zify [hs, h1]
  ring

/-- `β^(q+1) = 1` where `β = a^(q-1)`. -/
lemma suTmat_beta_pow (n : ℕ) (a : (F n)ˣ) :
    ((a : F n) ^ (2 ^ n - 1)) ^ (2 ^ n + 1) = 1 := by
  rw [← pow_mul, two_pow_sub_one_mul_add_one]
  have h2 : 2 ^ (2 * n) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h3 : (a : F n) ^ (2 ^ (2 * n) - 1) * (a : F n) = 1 * (a : F n) := by
    rw [one_mul, pow_sub_one_mul h2, pow_card_sq]
  exact mul_right_cancel₀ (Units.ne_zero a) h3

/-- `(β^q)⁻¹ = β`. -/
lemma suTmat_beta_inv_pow (n : ℕ) (a : (F n)ˣ) :
    (((a : F n) ^ (2 ^ n - 1)) ^ (2 ^ n))⁻¹ = (a : F n) ^ (2 ^ n - 1) :=
  inv_eq_of_mul_eq_one_left (by rw [← pow_succ', suTmat_beta_pow])

/-- `a^(q²) = a`. -/
lemma suTmat_alpha_q_sq (n : ℕ) (a : (F n)ˣ) :
    ((a : F n) ^ (2 ^ n)) ^ (2 ^ n) = (a : F n) := by
  rw [← pow_mul, show 2 ^ n * 2 ^ n = 2 ^ (2 * n) by rw [← pow_add]; ring, pow_card_sq]

/-- `(a·b·β⁻¹)^q · (a^q)⁻¹ = β · b^q`. -/
lemma suTmat_conj_second (n : ℕ) (a : (F n)ˣ) (b : F n) :
    ((a : F n) * b * ((a : F n) ^ (2 ^ n - 1))⁻¹) ^ (2 ^ n) *
        ((a : F n) ^ (2 ^ n))⁻¹ =
      (a : F n) ^ (2 ^ n - 1) * b ^ (2 ^ n) := by
  have hβ : (a : F n) ^ (2 ^ n - 1) ≠ 0 := pow_ne_zero _ (Units.ne_zero a)
  rw [mul_pow, mul_pow, inv_pow, suTmat_beta_inv_pow]
  field_simp


/-! ## The action of the torus on the unipotent radical -/

/-- `t(a)·u(b,c) = u(a·b·β⁻¹, a·c·a^q)·t(a)`. -/
lemma suTg_mul_suUg (n : ℕ) (a : (F n)ˣ) (b c : F n) :
    suTg n a * suUg n b c =
      suUg n ((a : F n) * b * ((a : F n) ^ (2 ^ n - 1))⁻¹)
            ((a : F n) * c * (a : F n) ^ (2 ^ n)) * suTg n a := by
  apply Units.ext
  simp only [Matrix.GeneralLinearGroup.coe_mul]
  ext i j
  simp only [suTg_coe, suUg_coe, suTmat, suUmat, Matrix.diagonal_mul, Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;> simp
  · exact (suTmat_conj_second n a b).symm

/-- Conjugation action of the torus on the unipotent radical. -/
lemma suTg_conj_suUg (n : ℕ) (a : (F n)ˣ) (b c : F n) :
    suTg n a * suUg n b c * (suTg n a)⁻¹ =
      suUg n ((a : F n) * b * ((a : F n) ^ (2 ^ n - 1))⁻¹)
            ((a : F n) * c * (a : F n) ^ (2 ^ n)) := by
  rw [suTg_mul_suUg, mul_assoc, mul_inv_cancel, mul_one]

/-! ## The condition `c + c^q = b^(q+1)` is preserved -/

lemma suU_cond_conj (n : ℕ) (a : (F n)ˣ) (b c : F n)
    (hc : c + c ^ (2 ^ n) = b ^ (2 ^ n + 1)) :
    ((a : F n) * c * (a : F n) ^ (2 ^ n)) +
        ((a : F n) * c * (a : F n) ^ (2 ^ n)) ^ (2 ^ n) =
      ((a : F n) * b * ((a : F n) ^ (2 ^ n - 1))⁻¹) ^ (2 ^ n + 1) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hβ : (a : F n) ^ (2 ^ n - 1) ≠ 0 := pow_ne_zero _ (Units.ne_zero a)
  have hA : ((a : F n) * c * (a : F n) ^ (2 ^ n)) +
        ((a : F n) * c * (a : F n) ^ (2 ^ n)) ^ (2 ^ n) =
      (a : F n) ^ (2 ^ n) * (a : F n) * (c + c ^ (2 ^ n)) := by
    rw [mul_pow, mul_pow, suTmat_alpha_q_sq]
    ring
  have hB : ((a : F n) * b * ((a : F n) ^ (2 ^ n - 1))⁻¹) ^ (2 ^ n + 1) =
      (a : F n) ^ (2 ^ n) * (a : F n) * b ^ (2 ^ n + 1) := by
    rw [pow_succ, mul_pow, mul_pow, inv_pow, suTmat_beta_inv_pow]
    field_simp
    ring
  rw [hA, hB, hc]

/-! ## The Borel subgroup -/

/-- The unipotent radical and the torus meet trivially. -/
lemma suU_inf_suT (n : ℕ) : suU n ⊓ suT n = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro A hA
  obtain ⟨hU, hT⟩ := hA
  obtain ⟨b, c, hc, rfl⟩ := hU
  obtain ⟨a, ha⟩ := hT
  -- compare the `(0,0)` entries: `1 = a`
  have hmat : suUmat n b c = suTmat n a := by
    have h := congrArg (fun u : GL (Fin 3) (F n) =>
      ((u : GL (Fin 3) (F n)) : Matrix (Fin 3) (Fin 3) (F n))) ha
    simpa only [suUg_coe, suTg_coe] using h
  have h00 := congrFun (congrFun hmat 0) 0
  simp only [suUmat, suTmat, Matrix.diagonal_apply, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.head_cons, Fin.isValue, ↓reduceIte] at h00
  have ha1 : a = 1 := Units.ext h00.symm
  rw [ha1, suTg_one] at ha
  exact ha

/-- The torus normalises the unipotent radical. -/
lemma suT_le_normalizer_suU (n : ℕ) :
    suT n ≤ Subgroup.normalizer (suU n : Set (GL (Fin 3) (F n))) := by
  rw [Subgroup.le_normalizer_iff]
  intro t ht u hu
  obtain ⟨a, rfl⟩ := ht
  obtain ⟨b, c, hc, rfl⟩ := hu
  exact ⟨(a : F n) * b * ((a : F n) ^ (2 ^ n - 1))⁻¹,
    (a : F n) * c * (a : F n) ^ (2 ^ n),
    suU_cond_conj n a b c hc, suTg_conj_suUg n a b c⟩

/-- The Borel subgroup `B = U ⋊ T ≤ SU(3, 2^n)`. -/
noncomputable def suB (n : ℕ) : Subgroup (GL (Fin 3) (F n)) := suU n ⊔ suT n

lemma suB_le_SU3 (n : ℕ) : suB n ≤ SU3 n :=
  sup_le (suU_le_SU3 n) (suT_le_SU3 n)

/-- The Borel subgroup normalises `U`. -/
lemma suB_le_normalizer_suU (n : ℕ) :
    suB n ≤ Subgroup.normalizer (suU n : Set (GL (Fin 3) (F n))) :=
  sup_le Subgroup.le_normalizer (suT_le_normalizer_suU n)

/-- The unipotent radical `U` is a `2`-group. -/
lemma isPGroup_suU (n : ℕ) (hn : 1 ≤ n) : IsPGroup 2 ↥(suU n) := by
  apply IsPGroup.of_card (n := 3 * n)
  rw [card_suU n hn]

/-- The Borel subgroup has order `q^3 (q^2 - 1)`. -/
theorem card_suB (n : ℕ) (hn : 1 ≤ n) :
    Nat.card ↥(suB n) = 2 ^ (3 * n) * (2 ^ (2 * n) - 1) := by
  rw [suB, Commons.GroupTheory.Subgroup.card_sup_of_inf_eq_bot_of_le_normalizer
    (suU n) (suT n) (suT_le_normalizer_suU n) (suU_inf_suT n),
    card_suU n hn, card_suT n hn]

end Submission.PSU3
