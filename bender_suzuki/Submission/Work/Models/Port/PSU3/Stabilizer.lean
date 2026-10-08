/-
The stabiliser in `SU(3, q)` of the line `[e_0]` is the Borel subgroup `B = U ⋊ T`.

Strategy.  We introduce the subgroup `Stab ≤ GL(3,F)` of matrices sending `e_0` into the
line `⟨e_0⟩`.  The unipotent radical `U` fixes `e_0` and the torus `T = diag(a, a^(q-1), a^(-q))`
sends `e_0` to `a·e_0`, so both lie in `Stab`; hence `B = U ⊔ T ≤ Stab`.

Conversely, if `A ∈ SU(3,q)` and `A·e_0 = x·e_0` with `x ≠ 0`, then `t := diag(x, x^(q-1), x^(-q))`
also sends `e_0` to `x·e_0`, so `t⁻¹·A` fixes `e_0` and therefore lies in the unipotent radical
`U` (the stabiliser of the vector `e_0`, proved in `Order.lean`); thus `A = t·(t⁻¹A) ∈ T·U ⊆ B`.

Consequently `[SU(3,q) : B] = q^3 + 1`, the number of isotropic points (Hermitian curve).
-/
import Mathlib
import ChallengeDeps
import Submission.Work.Models.Port.PSU3.Borel
import Submission.Work.Models.Port.PSU3.Order

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

/-- `x • w = v` with `x ≠ 0` determines `w = x⁻¹ • v`. -/
lemma eq_inv_smul_of_smul_eq (n : ℕ) {x : F n} (hx : x ≠ 0) {w v : Fin 3 → F n}
    (h : x • w = v) : w = x⁻¹ • v := by
  rw [← h, smul_smul, inv_mul_cancel₀ hx, one_smul]

/-- The stabiliser in `GL(3,F)` of the line spanned by the first basis vector `e_0`. -/
noncomputable def suStab (n : ℕ) : Subgroup (GL (Fin 3) (F n)) where
  carrier := {A | ∃ x : F n, x ≠ 0 ∧
    (A : Matrix (Fin 3) (Fin 3) (F n)) *ᵥ suE0 n = x • suE0 n}
  mul_mem' := by
    rintro A B ⟨x, hx, hA⟩ ⟨y, hy, hB⟩
    refine ⟨y * x, mul_ne_zero hy hx, ?_⟩
    rw [Matrix.GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hB, Matrix.mulVec_smul, hA,
      smul_smul]
  one_mem' := by
    refine ⟨1, one_ne_zero, ?_⟩
    rw [Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
    ext i; fin_cases i <;> simp [suE0, Pi.smul_apply]
  inv_mem' := by
    rintro A ⟨x, hx, hA⟩
    refine ⟨x⁻¹, inv_ne_zero hx, ?_⟩
    have h4 : (((A⁻¹ : GL (Fin 3) (F n))) : Matrix (Fin 3) (Fin 3) (F n)) *ᵥ (x • suE0 n) =
        suE0 n := by
      rw [← hA, Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
    have h5 : x • ((((A⁻¹ : GL (Fin 3) (F n))) : Matrix (Fin 3) (Fin 3) (F n)) *ᵥ suE0 n) =
        suE0 n := by
      rw [← Matrix.mulVec_smul]; exact h4
    exact eq_inv_smul_of_smul_eq n hx h5

/-- The unipotent radical fixes `e_0`. -/
lemma suU_le_suStab (n : ℕ) : suU n ≤ suStab n := by
  intro A hA
  obtain ⟨b, c, hc, rfl⟩ := hA
  refine ⟨1, one_ne_zero, ?_⟩
  rw [suUg_coe, suUmat_mulVec_suE0]
  ext i; fin_cases i <;> simp [suE0, Pi.smul_apply]

/-- The torus sends `e_0` to `a·e_0`. -/
lemma suT_le_suStab (n : ℕ) : suT n ≤ suStab n := by
  intro A hA
  obtain ⟨a, rfl⟩ := hA
  refine ⟨(a : F n), Units.ne_zero a, ?_⟩
  rw [suTg_mulVec_suE0]
  ext i; fin_cases i <;> simp [suE0, Pi.smul_apply]

/-- The Borel subgroup stabilises the line `[e_0]`. -/
lemma suB_le_suStab (n : ℕ) : suB n ≤ suStab n :=
  sup_le (suU_le_suStab n) (suT_le_suStab n)

/-- The torus element `diag(x, x^(q-1), x^(-q))` sends `e_0` to `x • e_0`. -/
lemma suTg_mulVec_suE0_eq_smul (n : ℕ) (x : F n) (hx : x ≠ 0) :
    ((suTg n (Units.mk0 x hx) : GL (Fin 3) (F n)) : Matrix (Fin 3) (Fin 3) (F n)) *ᵥ
      suE0 n = x • suE0 n := by
  rw [suTg_mulVec_suE0]
  ext i; fin_cases i <;> simp [suE0, Pi.smul_apply]

/-- **The point stabiliser of `[e_0]` in `SU(3,2^n)` is the Borel subgroup.** -/
theorem mem_suB_iff_smul (n : ℕ) (A : GL (Fin 3) (F n)) (hA : A ∈ SU3 n) :
    A ∈ suB n ↔ ∃ x : F n, x ≠ 0 ∧
      (A : Matrix (Fin 3) (Fin 3) (F n)) *ᵥ suE0 n = x • suE0 n := by
  constructor
  · intro h
    exact suB_le_suStab n h
  · rintro ⟨x, hx, hAx⟩
    have h1 : ((suTg n (Units.mk0 x hx) : GL (Fin 3) (F n)) :
        Matrix (Fin 3) (Fin 3) (F n)) *ᵥ suE0 n = x • suE0 n :=
      suTg_mulVec_suE0_eq_smul n x hx
    have hcan2 : (((suTg n (Units.mk0 x hx))⁻¹ : GL (Fin 3) (F n)) :
        Matrix (Fin 3) (Fin 3) (F n)) *ᵥ (x • suE0 n) = suE0 n := by
      rw [← h1, Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
    have hsub : (suTg n (Units.mk0 x hx))⁻¹ * A ∈ suU n := by
      rw [← mulVec_suE0_iff_mem_suU n _
          ((SU3 n).mul_mem ((SU3 n).inv_mem (suTg_isSU3 n _)) hA)]
      rw [Matrix.GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]
      show (((suTg n (Units.mk0 x hx))⁻¹ : GL (Fin 3) (F n)) :
          Matrix (Fin 3) (Fin 3) (F n)) *ᵥ ((A : GL (Fin 3) (F n)) :
          Matrix (Fin 3) (Fin 3) (F n)) *ᵥ suE0 n = suE0 n
      rw [hAx, hcan2]
    have heq : A = suTg n (Units.mk0 x hx) * ((suTg n (Units.mk0 x hx))⁻¹ * A) := by
      rw [← mul_assoc, mul_inv_cancel, one_mul]
    rw [heq]
    exact (suB n).mul_mem
      (Subgroup.mem_sup_right (show suTg n (Units.mk0 x hx) ∈ suT n from ⟨Units.mk0 x hx, rfl⟩))
      (Subgroup.mem_sup_left hsub)

/-- The index `[SU(3,2^n) : B]` is the number `q^3 + 1` of isotropic points. -/
theorem card_suStab_SU3 (n : ℕ) (hn : 1 ≤ n) :
    Nat.card ↥(suB n) * (2 ^ (3 * n) + 1) = Nat.card ↥(SU3 n) :=
  card_suB_mul_index n hn

end Submission.PSU3
