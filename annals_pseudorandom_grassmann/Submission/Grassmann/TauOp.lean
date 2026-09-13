import Mathlib
import Submission.Grassmann.Homogeneous

/-!
# The operator `𝒯_{i,U}` of arXiv:2209.04243, §5.7

For a vector `v ≠ 0` and `i ≥ 1` the paper sets

  `𝒯_{i,v} f = f - (q^i + q^{i-1}) 𝓔_v f + q^{2i-1} 𝓔_v² f`,

and proves that `𝒯_{i,v}` acts on the homogeneous components of degree `i` and `i-1` as the
hybrid Laplacian `L_U` (`U = span v`):

  `L_U[f^{=i}] = (𝒯_{i,v} f)^{=i}`,   `L_U[f^{=i-1}] = (𝒯_{i,v} f)^{=i-1}`.

These are the Fourier formulas underpinning Lemma 5.5 (`lem:inductive step`).
-/

open Finset BigOperators
open Classical

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission.Grassmann

noncomputable section

variable {m n : ℕ}

/-- The operator `𝒯_{i,v} = 1 - (q^i+q^{i-1})𝓔_v + q^{2i-1}𝓔_v²`. -/
def TOp (v : Fin n → ZMod 2) (i : ℕ) (f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) :
    Matrix (Fin m) (Fin n) (ZMod 2) → ℂ :=
  f - (((2 : ℂ) ^ i + (2 : ℂ) ^ (i - 1))) • eOpV v f +
    ((2 : ℂ) ^ (2 * i - 1)) • eOpV v (eOpV v f)

/-- The Fourier coefficients of `𝒯_{i,v}`. -/
theorem fhat_TOp (v : Fin n → ZMod 2) (hv : v ≠ 0) (i : ℕ)
    (f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) (Y : Matrix (Fin n) (Fin m) (ZMod 2)) :
    fhat (TOp v i f) Y =
      (1 - (((2 : ℂ) ^ i + (2 : ℂ) ^ (i - 1)) *
            (if v ∈ LinearMap.range (Matrix.mulVecLin Y) then 0
              else ((2 : ℂ) ^ Y.rank)⁻¹))
          + ((2 : ℂ) ^ (2 * i - 1)) *
            ((if v ∈ LinearMap.range (Matrix.mulVecLin Y) then 0
                else ((2 : ℂ) ^ Y.rank)⁻¹) *
             (if v ∈ LinearMap.range (Matrix.mulVecLin Y) then 0
                else ((2 : ℂ) ^ Y.rank)⁻¹))) * fhat f Y := by
  rw [TOp, fhat_add, fhat_sub, fhat_smul, fhat_smul, fhat_eOpV v hv (eOpV v f) Y,
    fhat_eOpV v hv f Y]
  ring

/-- The arithmetic underlying `𝒯_{i,v}` on the level `i`. -/
lemma tau_bracket_self (i : ℕ) (hi : 1 ≤ i) :
    1 - (((2 : ℂ) ^ i + (2 : ℂ) ^ (i - 1)) * ((2 : ℂ) ^ i)⁻¹)
      + ((2 : ℂ) ^ (2 * i - 1)) * (((2 : ℂ) ^ i)⁻¹ * ((2 : ℂ) ^ i)⁻¹) = 0 := by
  rw [pow_sub₀ (2 : ℂ) (by norm_num) hi, pow_sub₀ (2 : ℂ) (by norm_num) (by omega : 1 ≤ 2 * i)]
  have h2i : (2 : ℂ) ^ (2 * i) = ((2 : ℂ) ^ i) ^ 2 := by rw [mul_comm 2 i, pow_mul]
  rw [h2i]
  have hne : ((2 : ℂ) ^ i) ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp
  ring

/-- The arithmetic underlying `𝒯_{i,v}` on the level `i - 1`. -/
lemma tau_bracket_pred (i : ℕ) (hi : 1 ≤ i) :
    1 - (((2 : ℂ) ^ i + (2 : ℂ) ^ (i - 1)) * ((2 : ℂ) ^ (i - 1))⁻¹)
      + ((2 : ℂ) ^ (2 * i - 1)) * (((2 : ℂ) ^ (i - 1))⁻¹ * ((2 : ℂ) ^ (i - 1))⁻¹) = 0 := by
  have h1 : (2 : ℂ) ^ i = 2 * (2 : ℂ) ^ (i - 1) := by
    conv_lhs => rw [show i = (i - 1) + 1 from by omega]
    rw [pow_succ]
    ring
  have h2 : (2 : ℂ) ^ (2 * i - 1) = 2 * ((2 : ℂ) ^ (i - 1)) ^ 2 := by
    conv_lhs => rw [show 2 * i - 1 = 2 * (i - 1) + 1 from by omega]
    rw [pow_succ, mul_comm 2 (i - 1), pow_mul]
    ring
  rw [h1, h2]
  have hne : ((2 : ℂ) ^ (i - 1)) ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp
  ring

/-- **The action of `𝒯_{i,v}` on the level `i`**: it equals the hybrid Laplacian `L_U`. -/
theorem TOp_projPure (v : Fin n → ZMod 2) (hv : v ≠ 0) (i : ℕ) (hi : 1 ≤ i)
    (f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) :
    lapMulN (fun X : Matrix (Fin n) (Fin m) (ZMod 2) =>
        v ∈ LinearMap.range (Matrix.mulVecLin X)) (projPure i f) =
      projPure i (TOp v i f) := by
  refine eq_of_fhat_eq fun Y => ?_
  rw [fhat_lapMulN, fhat_projPure, fhat_projPure, fhat_TOp v hv i f Y]
  by_cases hri : Y.rank = i
  · rw [hri]
    by_cases hvY : v ∈ LinearMap.range (Matrix.mulVecLin Y)
    · simp only [if_pos hvY]
      ring
    · simp only [if_neg hvY, tau_bracket_self i hi]
      ring
  · simp only [if_neg hri]
    ring

/-- **The action of `𝒯_{i,v}` on the level `i - 1`**: it equals the hybrid Laplacian `L_U`. -/
theorem TOp_projPure_pred (v : Fin n → ZMod 2) (hv : v ≠ 0) (i : ℕ) (hi : 1 ≤ i)
    (f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) :
    lapMulN (fun X : Matrix (Fin n) (Fin m) (ZMod 2) =>
        v ∈ LinearMap.range (Matrix.mulVecLin X)) (projPure (i - 1) f) =
      projPure (i - 1) (TOp v i f) := by
  refine eq_of_fhat_eq fun Y => ?_
  rw [fhat_lapMulN, fhat_projPure, fhat_projPure, fhat_TOp v hv i f Y]
  by_cases hri : Y.rank = i - 1
  · rw [hri]
    by_cases hvY : v ∈ LinearMap.range (Matrix.mulVecLin Y)
    · simp only [if_pos hvY]
      ring
    · simp only [if_neg hvY, tau_bracket_pred i hi]
      ring
  · simp only [if_neg hri]
    ring

end

end Submission.Grassmann
