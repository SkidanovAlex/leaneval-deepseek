import Mathlib
import Submission.Grassmann.CombinatorialLaplacian
import Submission.Grassmann.BilinearDegree

/-!
# Homogeneous functions and the combinatorial interpretation of the Laplacian

This file continues the development of arXiv:2209.04243 §5.6 around the combinatorial
Laplacian `𝓔_v = eOpV v` defined in `Submission/Grassmann/CombinatorialLaplacian.lean`.

* `fhat_eOpV` — the Fourier coefficient of `𝓔_v f`: the character `mchar X` is multiplied by
  `2^{-rank X}` unless `v ∈ Im X`, in which case it is killed.
* `eOpV_projPure` — on the *homogeneous* part `f^{=i}` the weight `2^{-rank X}` is the constant
  `2^{-i}`, so `𝓔_v` acts as `2^{-i}` times the projection onto the characters with `v ∉ Im X`.
* `prop_five_four` — **Prop. 5.4 of arXiv:2209.04243**: for a function homogeneous of degree `i`
  the hybrid Laplacian `L_U` (`U = span v`) satisfies `L_U[f] = f - q^i 𝓔_v[f]`.
-/

open Finset BigOperators
open Classical

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission.Grassmann

noncomputable section

variable {m n : ℕ}

/-! ## The Fourier coefficients of `𝓔_v` -/

/-- Unfolding of the combinatorial Laplacian. -/
lemma eOpV_apply {m n : ℕ} (v : Fin n → ZMod 2)
    (f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) :
    eOpV v f = ((Nat.card {φ : Module.Dual (ZMod 2) (Fin n → ZMod 2) // φ v = 1} : ℂ))⁻¹ •
      ∑ φ : {φ : Module.Dual (ZMod 2) (Fin n → ZMod 2) // φ v = 1},
        eOp (linRow φ.1) f := rfl

/-- **The Fourier coefficients of the combinatorial Laplacian**: `𝓔_v` multiplies the
character `mchar X` by `2^{-rank X}` unless `v ∈ Im X`. -/
theorem fhat_eOpV {m n : ℕ} (v : Fin n → ZMod 2) (hv : v ≠ 0)
    (f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) (Y : Matrix (Fin n) (Fin m) (ZMod 2)) :
    fhat (eOpV v f) Y =
      (if v ∈ LinearMap.range (Matrix.mulVecLin Y) then 0 else ((2 : ℂ) ^ Y.rank)⁻¹) *
        fhat f Y := by
  classical
  rw [eOpV_apply, fhat_smul, fhat_sum]
  have hterm : ∀ φ : {φ : Module.Dual (ZMod 2) (Fin n → ZMod 2) // φ v = 1},
      fhat (eOp (linRow φ.1) f) Y =
        (if LinearMap.range (Matrix.mulVecLin Y) ≤ LinearMap.ker φ.1 then (1 : ℂ) else 0) *
          fhat f Y := by
    intro φ
    rw [eOp_eq_lapMulN, fhat_lapMulN]
    have hiff : linRow φ.1 * Y = 0 ↔
        LinearMap.range (Matrix.mulVecLin Y) ≤ LinearMap.ker φ.1 := by
      rw [Commons.LinearAlgebra.Matrix.mul_eq_zero_iff_range_le_ker, ker_mulVecLin_linRow]
    by_cases h : linRow φ.1 * Y = 0
    · rw [if_pos h, if_pos (hiff.mp h), one_mul]
    · rw [if_neg h, if_neg (fun hc => h (hiff.mpr hc)), zero_mul]
  rw [Finset.sum_congr rfl (fun φ _ => hterm φ), ← Finset.sum_mul, Finset.sum_boole]
  have hsub : ((Finset.univ.filter (fun φ : {φ : Module.Dual (ZMod 2) (Fin n → ZMod 2) //
        φ v = 1} => LinearMap.range (Matrix.mulVecLin Y) ≤ LinearMap.ker φ.1)).card : ℂ) =
      (Nat.card {φ : Module.Dual (ZMod 2) (Fin n → ZMod 2) //
        φ v = 1 ∧ LinearMap.range (Matrix.mulVecLin Y) ≤ LinearMap.ker φ} : ℂ) := by
    rw [Nat.card_eq_fintype_card]
    congr 1
    rw [show Fintype.card {φ : Module.Dual (ZMod 2) (Fin n → ZMod 2) //
          φ v = 1 ∧ LinearMap.range (Matrix.mulVecLin Y) ≤ LinearMap.ker φ} =
        Fintype.card {φ : {φ : Module.Dual (ZMod 2) (Fin n → ZMod 2) // φ v = 1} //
          LinearMap.range (Matrix.mulVecLin Y) ≤ LinearMap.ker φ.1} from
      Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
        (fun φ : Module.Dual (ZMod 2) (Fin n → ZMod 2) => φ v = 1)
        (fun φ : Module.Dual (ZMod 2) (Fin n → ZMod 2) =>
          LinearMap.range (Matrix.mulVecLin Y) ≤ LinearMap.ker φ)).symm]
    rw [Fintype.card_subtype]
  rw [hsub]
  have hcast : (Nat.card {φ : Module.Dual (ZMod 2) (Fin n → ZMod 2) // φ v = 1} : ℂ) =
      (2 : ℂ) ^ (n - 1) := by
    rw [natCard_dual_apply_eq_one v hv]; push_cast; ring
  rw [hcast]
  by_cases hY : v ∈ LinearMap.range (Matrix.mulVecLin Y)
  · rw [natCard_dual_apply_eq_one_and_le_ker (LinearMap.range (Matrix.mulVecLin Y)) v, if_pos hY,
      if_pos hY]
    ring
  · rw [natCard_dual_apply_eq_one_and_le_ker (LinearMap.range (Matrix.mulVecLin Y)) v, if_neg hY,
      if_neg hY]
    have hfin : Module.finrank (ZMod 2) (LinearMap.range (Matrix.mulVecLin Y)) = Y.rank := rfl
    rw [hfin]
    simp only [Nat.cast_pow, Nat.cast_ofNat]
    have hr : Y.rank ≤ n - 1 := by
      by_contra h
      have hle : Y.rank ≤ n := by
        have h := Submodule.finrank_mono
          (show LinearMap.range (Matrix.mulVecLin Y) ≤ ⊤ from le_top)
        rw [finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
        rwa [hfin] at h
      have hfull : Y.rank = n := by omega
      have hUt : LinearMap.range (Matrix.mulVecLin Y) = ⊤ :=
        Submodule.eq_top_of_finrank_eq (by
          rw [hfin, hfull, Module.finrank_fintype_fun_eq_card, Fintype.card_fin])
      exact hY (by rw [hUt]; exact Submodule.mem_top)
    have hpow : ((2 : ℂ) ^ (n - 1))⁻¹ * (2 : ℂ) ^ (n - Y.rank - 1) =
        ((2 : ℂ) ^ Y.rank)⁻¹ := by
      have h1 : n - Y.rank - 1 = n - 1 - Y.rank := by omega
      have hne2 : ((2 : ℂ) ^ (n - 1 - Y.rank)) ≠ 0 := pow_ne_zero _ (by norm_num)
      have hsplit : (2 : ℂ) ^ (n - 1) =
          (2 : ℂ) ^ Y.rank * (2 : ℂ) ^ (n - 1 - Y.rank) := by
        rw [← pow_add]; congr 1; omega
      rw [h1, hsplit, mul_inv]
      rw [show ((2 : ℂ) ^ Y.rank)⁻¹ * ((2 : ℂ) ^ (n - 1 - Y.rank))⁻¹ *
            (2 : ℂ) ^ (n - 1 - Y.rank)
          = ((2 : ℂ) ^ Y.rank)⁻¹ * (((2 : ℂ) ^ (n - 1 - Y.rank))⁻¹ *
            (2 : ℂ) ^ (n - 1 - Y.rank)) by ring,
        inv_mul_cancel₀ hne2, mul_one]
    rw [show ((2 : ℂ) ^ (n - 1))⁻¹ * ((2 : ℂ) ^ (n - Y.rank - 1) * fhat f Y)
        = (((2 : ℂ) ^ (n - 1))⁻¹ * (2 : ℂ) ^ (n - Y.rank - 1)) * fhat f Y by ring, hpow]

/-! ## Homogeneous functions: the combinatorial interpretation of the Laplacian -/

lemma inv_pow_two_mul (i : ℕ) : ((2 : ℂ)⁻¹) ^ i * 2 ^ i = 1 := by
  rw [← mul_pow, inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_pow]

/-- On a function that is homogeneous of degree `i`, the weight `2^{-rank X}` of the
combinatorial Laplacian is the constant `2^{-i}`. -/
theorem eOpV_projPure {m n : ℕ} (v : Fin n → ZMod 2) (hv : v ≠ 0) (i : ℕ)
    (f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) :
    eOpV v (projPure i f) = ((2 : ℂ) ^ i)⁻¹ •
      lapMulN (fun X : Matrix (Fin n) (Fin m) (ZMod 2) =>
        v ∉ LinearMap.range (Matrix.mulVecLin X)) (projPure i f) := by
  refine eq_of_fhat_eq fun Y => ?_
  rw [fhat_eOpV v hv (projPure i f) Y, fhat_smul, fhat_lapMulN, fhat_projPure]
  by_cases hi : Y.rank = i
  · rw [hi]
    by_cases hvY : v ∈ LinearMap.range (Matrix.mulVecLin Y)
    · simp [hvY]
    · simp [hvY]
  · simp [hi]

/-- **Prop. 5.4 of arXiv:2209.04243**: for a function homogeneous of degree `i`, the hybrid
Laplacian `L_U` associated with the line `U = span v` satisfies
`L_U[f] = f - q^i 𝓔_v[f]`. -/
theorem prop_five_four {m n : ℕ} (v : Fin n → ZMod 2) (hv : v ≠ 0) (i : ℕ)
    (f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) :
    lapMulN (fun X : Matrix (Fin n) (Fin m) (ZMod 2) =>
        v ∈ LinearMap.range (Matrix.mulVecLin X)) (projPure i f) =
      projPure i f - ((2 : ℂ) ^ i) • eOpV v (projPure i f) := by
  refine eq_of_fhat_eq fun Y => ?_
  rw [fhat_sub, fhat_smul, fhat_eOpV v hv (projPure i f) Y, fhat_lapMulN, fhat_projPure]
  by_cases hi : Y.rank = i
  · rw [hi]
    by_cases hvY : v ∈ LinearMap.range (Matrix.mulVecLin Y)
    · simp [hvY]
    · simp [hvY, inv_pow_two_mul i]
  · simp [hi]

end

end Submission.Grassmann
