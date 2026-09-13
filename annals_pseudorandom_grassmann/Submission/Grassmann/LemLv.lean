import Mathlib
import Submission.Grassmann.RestrictionFourier
import Submission.Grassmann.TauOp
import Submission.Grassmann.Laplacian

/-!
# `lem:lv`: the order-one derivative of `f^{=d}` (arXiv:2209.04243, §3.6, §7)

For the *order-one* restriction `(V₁, W₁) = (span v, W)` — i.e. `V₁ = ker Q` with
`ker Q = span v` and `W₁ = W` (encoded by `range ι = ⊤`) — the paper proves

  `D_{U→T}[f^{=i}] = ((𝒯_{i,U}[f])_{U→T})^{=i-1}`,

i.e. the level-`(i-1)` part of the restriction of `𝒯_{i,U}[f]` is the order-one derivative of
the pure level-`i` part of `f`.

This is the identity that drives `lem:inductive step`: it identifies the function obtained by
the *convexity/concentration* argument (`Submission.Grassmann.InductiveStep`) with a genuine
derivative of `f^{=i}`.
-/

open Finset BigOperators Matrix
open Classical

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission.Grassmann

noncomputable section

local notation "𝔽₂" => ZMod 2

/-! ## The normalised level projection -/

/-- The **normalised** pure-level-`d` projection of `f`: the function whose normalised Fourier
coefficients are those of `f` on characters of rank `d` and zero elsewhere.  It is
`2^{-mn} • projPure d f`. -/
def nprojPure {m n : ℕ} (d : ℕ) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    Matrix (Fin m) (Fin n) 𝔽₂ → ℂ :=
  ((2 : ℂ) ^ (m * n))⁻¹ • projPure d f

/-- The normalised Fourier coefficients of `nprojPure d f`. -/
lemma fcoeff_nprojPure {m n : ℕ} (d : ℕ) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ)
    (X : Matrix (Fin n) (Fin m) 𝔽₂) :
    fcoeff (nprojPure d f) X = (if X.rank = d then 1 else 0) * fcoeff f X := by
  rw [nprojPure, fcoeff, fhat_smul, fhat_projPure, fcoeff]
  by_cases hX : X.rank = d
  · rw [if_pos hX, if_pos hX]
    field_simp
  · rw [if_neg hX, if_neg hX]
    ring

/-! ## The normalised coefficients of `TOp v d f` -/

/-- If `v ∈ range X` then `𝒯_{d,v}` does not change the coefficient at `X`. -/
lemma fcoeff_TOp_of_mem {m n : ℕ} (v : Fin n → 𝔽₂) (hv : v ≠ 0) (i : ℕ)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) (X : Matrix (Fin n) (Fin m) 𝔽₂)
    (hX : v ∈ LinearMap.range X.mulVecLin) :
    fcoeff (TOp v i f) X = fcoeff f X := by
  rw [fcoeff, fcoeff, fhat_TOp v hv i f X, if_pos hX]
  ring

/-- If `v ∉ range X` and `rank X = d` then `𝒯_{d,v}` kills the coefficient at `X`. -/
lemma fcoeff_TOp_of_notMem_self {m n : ℕ} (v : Fin n → 𝔽₂) (hv : v ≠ 0) (i : ℕ)
    (hi : 1 ≤ i) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) (X : Matrix (Fin n) (Fin m) 𝔽₂)
    (hX : v ∉ LinearMap.range X.mulVecLin) (hr : X.rank = i) :
    fcoeff (TOp v i f) X = 0 := by
  rw [fcoeff, fhat_TOp v hv i f X, if_neg hX, hr, tau_bracket_self i hi, zero_mul, mul_zero]

/-- If `v ∉ range X` and `rank X = d - 1` then `𝒯_{d,v}` kills the coefficient at `X`. -/
lemma fcoeff_TOp_of_notMem_pred {m n : ℕ} (v : Fin n → 𝔽₂) (hv : v ≠ 0) (i : ℕ)
    (hi : 1 ≤ i) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) (X : Matrix (Fin n) (Fin m) 𝔽₂)
    (hX : v ∉ LinearMap.range X.mulVecLin) (hr : X.rank = i - 1) :
    fcoeff (TOp v i f) X = 0 := by
  rw [fcoeff, fhat_TOp v hv i f X, if_neg hX, hr, tau_bracket_pred i hi, zero_mul, mul_zero]

/-! ## The order-one hybrid Laplacian -/

/-- Under `ker Q = span v` and `range ι = ⊤`, the hybrid Laplacian is exactly the
"`v ∈ range X`" Fourier multiplier. -/
lemma hybridPred_iff {m n m' n' : ℕ} (Q : Matrix (Fin n') (Fin n) 𝔽₂)
    (ι : Matrix (Fin m) (Fin m') 𝔽₂) {v : Fin n → 𝔽₂}
    (hker : LinearMap.ker Q.mulVecLin = Submodule.span 𝔽₂ {v})
    (hιtop : LinearMap.range ι.mulVecLin = ⊤) (X : Matrix (Fin n) (Fin m) 𝔽₂) :
    hybridPred Q ι X ↔ v ∈ LinearMap.range X.mulVecLin := by
  rw [hybridPred]
  constructor
  · intro h
    exact h.1 (by rw [hker]; exact Submodule.subset_span rfl)
  · intro h
    refine ⟨?_, fun w _ => by rw [hιtop]; exact Submodule.mem_top⟩
    rw [hker]
    exact (Submodule.span_singleton_le_iff_mem v X.mulVecLin.range).mpr h

/-- If `v ≠ 0` lies in the range of `X` then `X` has rank at least `1`. -/
lemma one_le_rank_of_mem_range {m n : ℕ} {X : Matrix (Fin n) (Fin m) 𝔽₂} {v : Fin n → 𝔽₂}
    (hv : v ≠ 0) (hmem : v ∈ LinearMap.range X.mulVecLin) : 1 ≤ X.rank := by
  rcases Nat.eq_zero_or_pos X.rank with h | h
  · exfalso
    have hbot : X.mulVecLin.range = ⊥ := by
      rw [← Submodule.finrank_eq_zero, ← Matrix.rank]
      exact h
    rw [hbot, Submodule.mem_bot] at hmem
    exact hv hmem
  · exact h

/-! ## The main identity -/

/-- **`lem:lv` of arXiv:2209.04243.**  For an order-one restriction (`ker Q = span v`,
`range ι = ⊤`) the level-`(d-1)` part of the restriction of `𝒯_{d,v}[f]` is the order-one
derivative `D_{U,T}` of the pure level-`d` part of `f`. -/
theorem nprojPure_restr_shift_TOp {m n m' n' : ℕ}
    (Q : Matrix (Fin n') (Fin n) 𝔽₂) (ι : Matrix (Fin m) (Fin m') 𝔽₂)
    {v : Fin n → 𝔽₂} (hv : v ≠ 0)
    (hker : LinearMap.ker Q.mulVecLin = Submodule.span 𝔽₂ {v})
    (hιtop : LinearMap.range ι.mulVecLin = ⊤)
    (d : ℕ) (hd : 1 ≤ d) (T : Matrix (Fin m) (Fin n) 𝔽₂)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    nprojPure (d - 1) (restr Q ι (shift T (TOp v d f))) =
      restr Q ι (shift T (lapMulN (hybridPred Q ι) (nprojPure d f))) := by
  classical
  refine eq_of_fcoeff_eq fun Y => ?_
  have hYr : ∀ X : Matrix (Fin n) (Fin m) 𝔽₂, Q * X * ι = Y →
      Y.rank = X.rank - (if v ∈ LinearMap.range X.mulVecLin then 1 else 0) := by
    intro X hX
    rw [← hX, rank_mul_mul_eq_of_range_eq_top Q X ι hιtop, rank_mul_eq_of_ker_eq_span Q hv hker X]
  rw [fcoeff_nprojPure, fcoeff_restr_shift, fcoeff_restr_shift, Finset.mul_sum]
  refine Finset.sum_congr rfl fun X hX => ?_
  rw [Finset.mem_filter] at hX
  rw [fcoeff_lapMulN, fcoeff_nprojPure]
  have hr := hYr X hX.2
  have hiff := hybridPred_iff Q ι hker hιtop X
  by_cases hYd : Y.rank = d - 1
  · rw [if_pos hYd]
    by_cases hmem : v ∈ LinearMap.range X.mulVecLin
    · have hrd : X.rank = d := by
        have hh := hr; rw [if_pos hmem] at hh
        have hpos := one_le_rank_of_mem_range hv hmem
        omega
      rw [fcoeff_TOp_of_mem v hv d f X hmem, hrd,
        if_pos (hiff.mpr hmem), if_pos rfl]
      ring
    · have hrd : X.rank = d - 1 := by
        have hh := hr; rw [if_neg hmem] at hh
        omega
      rw [fcoeff_TOp_of_notMem_pred v hv d hd f X hmem hrd, hrd,
        if_neg (fun hh => hmem (hiff.mp hh))]
      ring
  · rw [if_neg hYd]
    by_cases hmem : v ∈ LinearMap.range X.mulVecLin
    · rw [if_pos (hiff.mpr hmem)]
      by_cases hrd : X.rank = d
      · have hh : Y.rank = d - 1 := by
          have h1 := hr; rw [if_pos hmem, hrd] at h1; omega
        exact absurd hh hYd
      · rw [if_neg hrd]; ring
    · rw [if_neg (fun hh => hmem (hiff.mp hh))]; ring

end

end Submission.Grassmann
