/-
The Bruhat decomposition of `SU(3, 2^n)` with respect to `B = U ⋊ T` and the Weyl element
`w = suSg n`, and the strong embedding of `B`.
-/
import Mathlib
import ChallengeDeps
import Submission.Work.Models.Port.PSU3.UAction

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
open scoped Pointwise

namespace Submission.PSU3

/-! ## Decomposing elements of `B = U ⋊ T` -/

/-- Every element of `H ⊔ K` is `h * k` with `h ∈ H`, `k ∈ K`, when `K` normalises `H`. -/
lemma mem_sup_mul {G : Type*} [Group G] (H K : Subgroup G)
    (h : K ≤ Subgroup.normalizer (H : Set G)) {x : G} (hx : x ∈ H ⊔ K) :
    ∃ a ∈ H, ∃ b ∈ K, x = a * b := by
  have hconj : ∀ k ∈ K, ∀ a ∈ H, k * a * k⁻¹ ∈ H := (Subgroup.le_normalizer_iff).mp h
  let S : Subgroup G :=
    { carrier := {x | ∃ a ∈ H, ∃ b ∈ K, x = a * b}
      mul_mem' := by
        rintro x y ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        exact ⟨a * (b * a' * b⁻¹), H.mul_mem ha (hconj b hb a' ha'), b * b',
          K.mul_mem hb hb', by group⟩
      one_mem' := ⟨1, H.one_mem, 1, K.one_mem, by group⟩
      inv_mem' := by
        rintro x ⟨a, ha, b, hb, rfl⟩
        exact ⟨b⁻¹ * a⁻¹ * b, by simpa using hconj b⁻¹ (K.inv_mem hb) a⁻¹ (H.inv_mem ha),
          b⁻¹, K.inv_mem hb, by group⟩ }
  have hS : H ⊔ K ≤ S := by
    apply sup_le
    · intro a ha; exact ⟨a, ha, 1, K.one_mem, by group⟩
    · intro b hb; exact ⟨1, H.one_mem, b, hb, by group⟩
  exact hS hx

/-- Every element of the Borel subgroup is `u * t` with `u ∈ U`, `t ∈ T`. -/
lemma suB_mem_decomp (n : ℕ) {A : GL (Fin 3) (F n)} (hA : A ∈ suB n) :
    ∃ u ∈ suU n, ∃ t ∈ suT n, A = u * t :=
  mem_sup_mul (suU n) (suT n) (suT_le_normalizer_suU n)
    (show A ∈ suU n ⊔ suT n from hA)

lemma suB_apply_10 (n : ℕ) {A : GL (Fin 3) (F n)} (hA : A ∈ suB n) :
    (A : Matrix (Fin 3) (Fin 3) (F n)) 1 0 = 0 := by
  obtain ⟨u, hu, t, ht, rfl⟩ := suB_mem_decomp n hA
  obtain ⟨b, c, hbc, rfl⟩ := hu
  obtain ⟨a, rfl⟩ := ht
  rw [Matrix.GeneralLinearGroup.coe_mul, suUg_coe, suTg_coe, suUmat, suTmat]
  simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply]

lemma suB_apply_20 (n : ℕ) {A : GL (Fin 3) (F n)} (hA : A ∈ suB n) :
    (A : Matrix (Fin 3) (Fin 3) (F n)) 2 0 = 0 := by
  obtain ⟨u, hu, t, ht, rfl⟩ := suB_mem_decomp n hA
  obtain ⟨b, c, hbc, rfl⟩ := hu
  obtain ⟨a, rfl⟩ := ht
  rw [Matrix.GeneralLinearGroup.coe_mul, suUg_coe, suTg_coe, suUmat, suTmat]
  simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply]

/-! ## The Weyl element and its conjugation action -/

lemma suSg_notMem_suB (n : ℕ) : suSg n ∉ suB n := by
  intro h
  have := suB_apply_20 n h
  rw [suSg_coe, J3] at this
  simp at this

lemma suSg_inv (n : ℕ) : (suSg n)⁻¹ = suSg n := by
  rw [inv_eq_iff_mul_eq_one, suSg_mul_self]

lemma suSg_conj_apply_10 (n : ℕ) (A : GL (Fin 3) (F n)) :
    ((suSg n * A * suSg n : GL (Fin 3) (F n)) : Matrix (Fin 3) (Fin 3) (F n)) 1 0 =
      (A : Matrix (Fin 3) (Fin 3) (F n)) 1 2 := by
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, suSg_coe, J3]
  simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three]

lemma suSg_conj_apply_20 (n : ℕ) (A : GL (Fin 3) (F n)) :
    ((suSg n * A * suSg n : GL (Fin 3) (F n)) : Matrix (Fin 3) (Fin 3) (F n)) 2 0 =
      (A : Matrix (Fin 3) (Fin 3) (F n)) 0 2 := by
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, suSg_coe, J3]
  simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three]

lemma suSg_conj_apply (n : ℕ) (y : GL (Fin 3) (F n)) :
    (MulAut.conj (suSg n)).toMonoidHom y = suSg n * y * suSg n := by
  change suSg n * y * (suSg n)⁻¹ = suSg n * y * suSg n
  rw [suSg_inv]

lemma suSg_conj_inv (n : ℕ) (y : GL (Fin 3) (F n)) :
    suSg n * (suSg n * y * suSg n) * suSg n = y := by
  rw [show suSg n * (suSg n * y * suSg n) * suSg n =
    (suSg n * suSg n) * y * (suSg n * suSg n) by group, suSg_mul_self,
    one_mul, mul_one]

lemma suSg_conj_mem_iff (n : ℕ) (A : GL (Fin 3) (F n)) :
    A ∈ (suB n).map (MulAut.conj (suSg n)).toMonoidHom ↔
      suSg n * A * suSg n ∈ suB n := by
  constructor
  · intro h
    obtain ⟨y, hy, hyA⟩ := Subgroup.mem_map.mp h
    have hy' : y = suSg n * A * suSg n := by rw [← hyA, suSg_conj_apply, suSg_conj_inv]
    rwa [hy'] at hy
  · intro h
    refine Subgroup.mem_map.mpr ⟨suSg n * A * suSg n, h, ?_⟩
    rw [suSg_conj_apply, suSg_conj_inv]

lemma suUT_apply_12 (n : ℕ) (b c : F n) (a : (F n)ˣ) :
    ((suUmat n b c * suTmat n a) : Matrix (Fin 3) (Fin 3) (F n)) 1 2 =
      b ^ (2 ^ n) * ((a : F n) ^ (2 ^ n))⁻¹ := by
  rw [suUmat, suTmat]
  simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply]

lemma suUT_apply_02 (n : ℕ) (b c : F n) (a : (F n)ˣ) :
    ((suUmat n b c * suTmat n a) : Matrix (Fin 3) (Fin 3) (F n)) 0 2 =
      c * ((a : F n) ^ (2 ^ n))⁻¹ := by
  rw [suUmat, suTmat]
  simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply]

/-! ## `B ∩ w B w = T` -/

lemma exp_two_pow (n : ℕ) : (2 ^ n - 1) + 2 ^ n * (2 ^ n - 1) = 2 ^ (2 * n) - 1 := by
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hsq : 2 ^ n * 2 ^ n = 2 ^ (2 * n) := by rw [← pow_add]; ring
  have h2 : 2 ^ n ≤ 2 ^ (2 * n) := by
    rw [← hsq]
    calc 2 ^ n = 2 ^ n * 1 := (mul_one _).symm
      _ ≤ 2 ^ n * 2 ^ n := Nat.mul_le_mul_left _ h1
  rw [Nat.mul_sub_left_distrib, mul_one, hsq]
  omega

lemma su_unit_pow_card_sub_one (n : ℕ) (a : (F n)ˣ) : ((a : F n)) ^ (2 ^ (2 * n) - 1) = 1 := by
  have h1 : ((a : F n)) ^ (2 ^ (2 * n) - 1) * (a : F n) = (a : F n) := by
    rw [← pow_succ, Nat.sub_add_cancel Nat.one_le_two_pow, pow_card_sq]
  exact mul_right_cancel₀ (Units.ne_zero a) (by rw [h1, one_mul])

lemma suSg_mul_suTg_mul_suSg (n : ℕ) (a : (F n)ˣ) :
    suSg n * suTg n a * suSg n = suTg n ((a ^ (2 ^ n))⁻¹) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, suSg_coe, J3]
  rw [suTg_coe, suTg_coe, suTmat, suTmat]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three,
      Units.val_inv_eq_inv_val]
  · refine eq_inv_of_mul_eq_one_right ?_
    rw [← pow_mul, ← pow_add, add_comm, exp_two_pow]
    exact su_unit_pow_card_sub_one n a
  · rw [← pow_mul, show 2 ^ n * 2 ^ n = 2 ^ (2 * n) by rw [← pow_add]; ring, pow_card_sq]

theorem suB_inf_map_conj_suSg (n : ℕ) :
    suB n ⊓ (suB n).map (MulAut.conj (suSg n)).toMonoidHom = suT n := by
  apply le_antisymm ?_ ?_
  · intro A hA
    obtain ⟨hAB, hABw⟩ := hA
    obtain ⟨u, hu, t, ht, rfl⟩ := suB_mem_decomp n hAB
    obtain ⟨b, c, hbc, rfl⟩ := hu
    obtain ⟨a, rfl⟩ := ht
    have hwAw : suSg n * (suUg n b c * suTg n a) * suSg n ∈ suB n :=
      (suSg_conj_mem_iff n _).mp hABw
    have hgne : ((a : F n) ^ (2 ^ n))⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ (Units.ne_zero a))
    have hb0 : b = 0 := by
      have h10 := suB_apply_10 n hwAw
      rw [suSg_conj_apply_10, Matrix.GeneralLinearGroup.coe_mul, suUg_coe, suTg_coe,
        suUT_apply_12] at h10
      rcases mul_eq_zero.mp h10 with h | h
      · exact pow_two_pow_eq_zero h
      · exact absurd h hgne
    have hc0 : c = 0 := by
      have h20 := suB_apply_20 n hwAw
      rw [suSg_conj_apply_20, Matrix.GeneralLinearGroup.coe_mul, suUg_coe, suTg_coe,
        suUT_apply_02] at h20
      rcases mul_eq_zero.mp h20 with h | h
      · exact h
      · exact absurd h hgne
    rw [hb0, hc0]
    exact ⟨a, by rw [suUg_zero, one_mul]⟩
  · intro A hA
    obtain ⟨a, rfl⟩ := hA
    refine ⟨?_, ?_⟩
    · show suTg n a ∈ suU n ⊔ suT n
      exact Subgroup.mem_sup_right (show suTg n a ∈ suT n from ⟨a, rfl⟩)
    · refine Subgroup.mem_map.mpr ⟨suSg n * suTg n a * suSg n, ?_, ?_⟩
      · rw [suSg_mul_suTg_mul_suSg]
        show suTg n ((a ^ (2 ^ n))⁻¹) ∈ suU n ⊔ suT n
        exact Subgroup.mem_sup_right
          (show suTg n ((a ^ (2 ^ n))⁻¹) ∈ suT n from ⟨_, rfl⟩)
      · rw [suSg_conj_apply, suSg_conj_inv]

end Submission.PSU3
