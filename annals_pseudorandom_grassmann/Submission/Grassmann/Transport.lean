import Submission.Grassmann.SwitchingRoles
import Submission.Grassmann.SpectralSSE
import Submission.Grassmann.Convolution

/-!
# Transporting Fourier multipliers along restrictions

A Fourier multiplier `lapMulN P` on `L(V,W)` can be moved across a restriction
`restr Q ι` by transporting the predicate `P`:

  `restr Q ι (lapMulN (fun X => P' (Q * X * ι)) f) = lapMulN P' (restr Q ι f)`.

This is the identity that lets one write the "`X`-derivatives" of arXiv:2209.04243 §8
(`D_X = (L_X)_{(V₁,W₁)}`) either as a restriction of a Laplacian of the big space or as a
Laplacian of the small space; it is what makes the second restriction
`restr Qsup Isub` composable with the first one.

We also record that shifts commute with Fourier multipliers (`lapMulN_shift`), which is what
turns an averaged derivative `E_T D_{V,W,T}[f]` into a plain multiplier applied to `f`.
-/

open Finset BigOperators Matrix
open Classical

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission.Grassmann

noncomputable section

local notation "𝔽₂" => ZMod 2

/-- The Fourier transform of a shifted function: `\hat{Δ_T f}(X) = u_X(T) · \hat f(X)`. -/
theorem fhat_shift {m n : ℕ} (T : Matrix (Fin m) (Fin n) 𝔽₂)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) (X : Matrix (Fin n) (Fin m) 𝔽₂) :
    fhat (shift T f) X = mchar X T * fhat f X := by
  have h1 : (∑ A : Matrix (Fin m) (Fin n) 𝔽₂, f (A + T) * mchar X A) =
      ∑ B : Matrix (Fin m) (Fin n) 𝔽₂, f B * mchar X (B + T) :=
    Fintype.sum_equiv (Equiv.addLeft T) (fun A => f (A + T) * mchar X A)
      (fun B => f B * mchar X (B + T)) (fun A => by
        have h : (T + A) + T = A := by
          rw [add_assoc, add_comm A T, ← add_assoc, mtx_add_self, zero_add]
        simp only [Equiv.coe_addLeft, h]
        rw [add_comm T A])
  simp only [fhat, shift]
  rw [h1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun B _ => ?_
  rw [mchar_add_right X B T]
  ring

/-- The normalised Fourier coefficient of a shifted function. -/
theorem fcoeff_shift {m n : ℕ} (T : Matrix (Fin m) (Fin n) 𝔽₂)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) (X : Matrix (Fin n) (Fin m) 𝔽₂) :
    fcoeff (shift T f) X = mchar X T * fcoeff f X := by
  rw [fcoeff_eq, fcoeff_eq, fhat_shift]
  ring

/-- **Shifts commute with Fourier multipliers**: `Δ_T ∘ L_P = L_P ∘ Δ_T`. -/
theorem lapMulN_shift {m n : ℕ} (P : Matrix (Fin n) (Fin m) 𝔽₂ → Prop)
    (T : Matrix (Fin m) (Fin n) 𝔽₂) (g : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    lapMulN P (shift T g) = shift T (lapMulN P g) := by
  refine eq_of_fcoeff_eq fun X => ?_
  have h1 : fcoeff (lapMulN P (shift T g)) X =
      (if P X then 1 else 0) * (mchar X T * fcoeff g X) := by
    rw [fcoeff_lapMulN, fcoeff_shift]
  have h2 : fcoeff (shift T (lapMulN P g)) X =
      mchar X T * ((if P X then 1 else 0) * fcoeff g X) := by
    rw [fcoeff_shift, fcoeff_lapMulN]
  rw [h1, h2]
  by_cases hP : P X <;> simp [hP] <;> ring

/-- **Transport of a Fourier multiplier across a restriction**: restricting the multiplier
whose predicate is `P' ∘ (Q * · * ι)` gives the multiplier `P'` of the restricted function. -/
theorem restr_lapMulN_comp {m n m' n' : ℕ} (Q : Matrix (Fin n') (Fin n) 𝔽₂)
    (ι : Matrix (Fin m) (Fin m') 𝔽₂) (P' : Matrix (Fin n') (Fin m') 𝔽₂ → Prop)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    restr Q ι (lapMulN (fun X : Matrix (Fin n) (Fin m) 𝔽₂ => P' (Q * X * ι)) f) =
      lapMulN P' (restr Q ι f) := by
  refine eq_of_fcoeff_eq fun Y => ?_
  rw [fcoeff_restr]
  rw [Finset.sum_congr rfl (fun X _ => fcoeff_lapMulN _ f X)]
  rw [fcoeff_lapMulN, fcoeff_restr, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun X hX => ?_)
  simp only [Finset.mem_filter] at hX
  have hiff : P' (Q * X * ι) ↔ P' Y := by rw [hX.2]
  by_cases hP : P' Y
  · simp only [if_pos hP, if_pos (hiff.mpr hP), one_mul]
  · simp only [if_neg hP, if_neg (fun hc => hP (hiff.mp hc)), zero_mul]

end

end Submission.Grassmann
