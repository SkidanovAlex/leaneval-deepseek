import Mathlib
import Submission.Grassmann.Laplacian

/-!
# The averaging operator `𝔢` (arXiv:2209.04243, Lemma 5.2 / `lem:EVV'`)

For a "quotient" matrix `Q : Matrix (Fin n') (Fin n) 𝔽₂` (representing the projection
`V → V/V'` with `V' = ker Q`) the *averaging operator* `eOp Q` averages a function on
`L(V,W) = Matrix (Fin m) (Fin n) 𝔽₂` over the shifts `A ↦ A + B * Q`, `B` ranging over all
`m × n'` matrices.

The main result is the **Fourier formula**
`eOp Q f = lapMulN (fun X => Q * X = 0) f`: the averaging operator keeps exactly the
characters `mchar X` with "image contained in `V'`" (i.e. `Q * X = 0`), and kills the rest.
This is Lemma 5.2 (`lem:EVV'`) of the paper.
-/

open Finset BigOperators
open Classical

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission.Grassmann

noncomputable section

/-! ## Linearity of the normalised Laplacians -/

lemma fhat_sum {m n : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) (X : Matrix (Fin n) (Fin m) (ZMod 2)) :
    fhat (∑ i ∈ s, f i) X = ∑ i ∈ s, fhat (f i) X := by
  simp only [fhat, Finset.sum_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [Finset.sum_mul]

lemma lapMulN_add {m n : ℕ} (P : Matrix (Fin n) (Fin m) (ZMod 2) → Prop)
    (f g : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) :
    lapMulN P (f + g) = lapMulN P f + lapMulN P g := by
  funext A
  simp only [lapMulN, lapMul, Pi.add_apply, fhat_add, add_mul]
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun X _ => ?_
  by_cases hX : P X <;> simp [hX]

lemma lapMulN_smul {m n : ℕ} (P : Matrix (Fin n) (Fin m) (ZMod 2) → Prop) (c : ℂ)
    (f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) : lapMulN P (c • f) = c • lapMulN P f := by
  funext A
  simp only [lapMulN, lapMul, Pi.smul_apply, smul_eq_mul, fhat_smul]
  have hkey : ∀ X : Matrix (Fin n) (Fin m) (ZMod 2),
      (if P X then c * fhat f X * mchar X A else 0)
        = c * (if P X then fhat f X * mchar X A else 0) := by
    intro X; by_cases hX : P X <;> simp [hX, mul_assoc]
  rw [Finset.sum_congr rfl (fun X _ => hkey X), ← Finset.mul_sum]
  ring

lemma lapMulN_sum {m n : ℕ} (P : Matrix (Fin n) (Fin m) (ZMod 2) → Prop) {ι : Type*}
    (s : Finset ι) (f : ι → Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) :
    lapMulN P (∑ i ∈ s, f i) = ∑ i ∈ s, lapMulN P (f i) := by
  funext A
  simp only [lapMulN, lapMul, Finset.sum_apply, fhat_sum]
  have h1 : ∀ X : Matrix (Fin n) (Fin m) (ZMod 2),
      (if P X then (∑ i ∈ s, fhat (f i) X) * mchar X A else 0)
        = ∑ i ∈ s, (if P X then fhat (f i) X * mchar X A else 0) := by
    intro X
    by_cases hX : P X
    · simp only [if_pos hX, Finset.sum_mul]
    · simp only [if_neg hX, Finset.sum_const_zero]
  rw [Finset.sum_congr rfl (fun X _ => h1 X)]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]

/-! ## The averaging operator -/

/-- The number of `m × n` matrices over `𝔽₂` is `2 ^ (m * n)`. -/
lemma natCard_matrix_zmod_two (m n : ℕ) :
    Nat.card (Matrix (Fin m) (Fin n) (ZMod 2)) = 2 ^ (m * n) := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Matrix (Fin m) (Fin n) (ZMod 2)),
    Module.finrank_matrix]
  simp [ZMod.card]

/-- The **averaging operator** `𝔢_{V/V'}`: average `f` over the shifts `A ↦ A + B * Q`. -/
def eOp {m n n' : ℕ} (Q : Matrix (Fin n') (Fin n) (ZMod 2))
    (f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ :=
  fun A => ((Nat.card (Matrix (Fin m) (Fin n') (ZMod 2)) : ℂ))⁻¹ *
    ∑ B : Matrix (Fin m) (Fin n') (ZMod 2), f (A + B * Q)

lemma eOp_apply {m n n' : ℕ} (Q : Matrix (Fin n') (Fin n) (ZMod 2))
    (f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) (A : Matrix (Fin m) (Fin n) (ZMod 2)) :
    eOp Q f A = ((Nat.card (Matrix (Fin m) (Fin n') (ZMod 2)) : ℂ))⁻¹ *
      ∑ B : Matrix (Fin m) (Fin n') (ZMod 2), f (A + B * Q) := rfl

lemma eOp_add {m n n' : ℕ} (Q : Matrix (Fin n') (Fin n) (ZMod 2))
    (f g : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) : eOp Q (f + g) = eOp Q f + eOp Q g := by
  funext A
  simp only [eOp, Pi.add_apply, Finset.sum_add_distrib, mul_add]

lemma eOp_smul {m n n' : ℕ} (Q : Matrix (Fin n') (Fin n) (ZMod 2)) (c : ℂ)
    (f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) : eOp Q (c • f) = c • eOp Q f := by
  funext A
  simp only [eOp, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun B _ => by ring

lemma eOp_sum {m n n' : ℕ} (Q : Matrix (Fin n') (Fin n) (ZMod 2)) {ι : Type*}
    (s : Finset ι) (f : ι → Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) :
    eOp Q (∑ i ∈ s, f i) = ∑ i ∈ s, eOp Q (f i) := by
  funext A
  simp only [eOp, Finset.sum_apply]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

/-! ## The character identity and the Fourier formula -/

/-- The character `mchar X` evaluated at the shift `B * Q` is the character `mchar (Q * X)`
evaluated at `B` (cyclicity of the trace). -/
lemma mchar_mul_matrix {m n n' : ℕ} (X : Matrix (Fin n) (Fin m) (ZMod 2))
    (B : Matrix (Fin m) (Fin n') (ZMod 2)) (Q : Matrix (Fin n') (Fin n) (ZMod 2)) :
    mchar X (B * Q) = mchar (Q * X) B := by
  rw [mchar_eq_trace, mchar_eq_trace]
  congr 1
  rw [← Matrix.mul_assoc X B Q, Matrix.trace_mul_cycle X B Q]

/-- **Lemma 5.2 (`lem:EVV'`) on characters**: the averaging operator keeps exactly the
characters whose dual matrix satisfies `Q * X = 0`. -/
theorem eOp_mchar {m n n' : ℕ} (Q : Matrix (Fin n') (Fin n) (ZMod 2))
    (X : Matrix (Fin n) (Fin m) (ZMod 2)) (A : Matrix (Fin m) (Fin n) (ZMod 2)) :
    eOp Q (mchar X) A = if Q * X = 0 then mchar X A else 0 := by
  rw [eOp]
  have hterm : ∀ B : Matrix (Fin m) (Fin n') (ZMod 2),
      mchar X (A + B * Q) = mchar X A * mchar (Q * X) B := by
    intro B
    rw [mchar_add_right, mchar_mul_matrix]
  rw [Finset.sum_congr rfl (fun B _ => hterm B), ← Finset.mul_sum, mchar_sum_eq,
    natCard_matrix_zmod_two]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  have hc : ((2 : ℂ) ^ (m * n')) ≠ 0 := pow_ne_zero _ (by norm_num)
  by_cases h : Q * X = 0
  · rw [if_pos h, if_pos h, mul_comm (mchar X A) ((2 : ℂ) ^ (m * n')), ← mul_assoc,
      inv_mul_cancel₀ hc, one_mul]
  · rw [if_neg h, if_neg h, mul_zero, mul_zero]

/-- The Fourier coefficient of a character. -/
lemma fhat_mchar {m n : ℕ} (X Y : Matrix (Fin n) (Fin m) (ZMod 2)) :
    fhat (mchar X) Y = if X = Y then (2 : ℂ) ^ (m * n) else 0 := by
  rw [fhat]
  exact mchar_orthogonal X Y

/-- A normalised Laplacian acts on a character by keeping it (up to the predicate). -/
lemma lapMulN_mchar {m n : ℕ} (P : Matrix (Fin n) (Fin m) (ZMod 2) → Prop)
    (X : Matrix (Fin n) (Fin m) (ZMod 2)) :
    lapMulN P (mchar X) = (if P X then (1 : ℂ) else 0) • mchar X := by
  funext A
  rw [lapMulN, lapMul, Pi.smul_apply, smul_eq_mul]
  have hc : ((2 : ℂ) ^ (m * n)) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [Finset.sum_eq_single X]
  · rw [fhat_mchar, if_pos rfl]
    by_cases hP : P X
    · rw [if_pos hP, if_pos hP, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    · rw [if_neg hP, if_neg hP, mul_zero, zero_mul]
  · intro Y _ hYX
    by_cases hP : P Y
    · rw [if_pos hP, fhat_mchar, if_neg (fun h : X = Y => hYX h.symm), zero_mul]
    · rw [if_neg hP]
  · intro h
    exact absurd (Finset.mem_univ X) h

/-- **Lemma 5.2 (`lem:EVV'`)**, operator form: the averaging operator is the normalised
Laplacian keeping the characters `X` with `Q * X = 0`. -/
theorem eOp_eq_lapMulN {m n n' : ℕ} (Q : Matrix (Fin n') (Fin n) (ZMod 2))
    (f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) :
    eOp Q f = lapMulN (fun X : Matrix (Fin n) (Fin m) (ZMod 2) => Q * X = 0) f := by
  have hc : ((2 : ℂ) ^ (m * n)) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hf : f = ((2 : ℂ) ^ (m * n))⁻¹ •
      (∑ X : Matrix (Fin n) (Fin m) (ZMod 2), fhat f X • mchar X) := by
    funext A
    rw [Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
    rw [show (∑ X : Matrix (Fin n) (Fin m) (ZMod 2), (fhat f X • mchar X) A)
        = ∑ X : Matrix (Fin n) (Fin m) (ZMod 2), fhat f X * mchar X A from
      Finset.sum_congr rfl fun X _ => by rw [Pi.smul_apply, smul_eq_mul]]
    rw [fhat_inversion, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  rw [hf, eOp_smul, eOp_sum, lapMulN_smul, lapMulN_sum]
  congr 1
  refine Finset.sum_congr rfl fun X _ => ?_
  rw [eOp_smul, lapMulN_smul]
  congr 1
  funext A
  rw [eOp_mchar, lapMulN_mchar, Pi.smul_apply, smul_eq_mul]
  by_cases h : Q * X = 0
  · rw [if_pos h, if_pos h]; ring
  · rw [if_neg h, if_neg h, zero_mul]

end

end Submission.Grassmann
