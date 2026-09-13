import Submission.Grassmann.LemLv
import Submission.Grassmann.DualLaplacian
import Submission.Grassmann.Duality

/-!
# The dual `lem:lv`: the order-one derivative in the `codim W₁ = 1` direction

arXiv:2209.04243, §3.6/§7.  The V-side `lem:lv` (`Submission.Grassmann.nprojPure_restr_shift_TOp`)
covers the order-one restriction with `V₁ = span v` and `W₁ = W`.  Here we prove the *dual*
statement, the one needed when Proposition 5.6 is applied to a pair with `dim V₁ = 0` and
`codim W₁ = 1`:

  `(𝒯_{d,W'}[f])^{=d-1}_{(V,W')→T} = D_{W',T}[f^{=d}]`

where `W' = (span w)^⊥` is the hyperplane orthogonal to `w` and
`𝒯_{d,W'}[f] = f - (2^d + 2^{d-1}) 𝓔_{W'}[f] + 2^{2d-1} 𝓔_{W'}²[f]`.

The proof is the same term-by-term Fourier comparison as the V-side, with two new inputs:

* the dual rank drop: for `ι` with `range ι = (span w)^⊥` and `ker Q = ⊥`,
  `(Q * X * ι).rank = X.rank - [w ∈ range Xᵀ]`;
* the dual identification of the hybrid Laplacian's Fourier multiplier:
  `hybridPred Q ι X ↔ w ∈ range Xᵀ`.
-/

open Finset BigOperators Matrix
open Classical

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission.Grassmann

noncomputable section

local notation "𝔽₂" => ZMod 2

/-! ## The dual pairing -/

/-- The transpose of the matrix of a linear map computes the adjoint for the standard
dot pairing. -/
lemma dotProduct_mulVec_transpose {m n : ℕ} (X : Matrix (Fin n) (Fin m) 𝔽₂)
    (a : Fin n → 𝔽₂) (b : Fin m → 𝔽₂) :
    (∑ i, (Xᵀ *ᵥ a) i * b i) = ∑ j, a j * (X *ᵥ b) j := by
  show (Xᵀ *ᵥ a) ⬝ᵥ b = a ⬝ᵥ (X *ᵥ b)
  rw [Matrix.mulVec_transpose, Matrix.dotProduct_mulVec]

/-! ## The range of the transpose is the orthocomplement of the kernel -/

/-- The range of the transposed matrix is the orthocomplement of the kernel. -/
lemma range_mulVecLin_transpose_eq_ortho_ker {m n : ℕ} (X : Matrix (Fin n) (Fin m) 𝔽₂) :
    LinearMap.range (Matrix.mulVecLin Xᵀ) = F2.ortho (LinearMap.ker X.mulVecLin) := by
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · intro y hy
    rw [F2.mem_ortho]
    intro u hu
    obtain ⟨a, ha⟩ := hy
    have hu' : X *ᵥ u = 0 := by
      have h := hu
      rwa [LinearMap.mem_ker, Matrix.mulVecLin_apply] at h
    rw [← ha, Matrix.mulVecLin_apply, dotProduct_mulVec_transpose, hu']
    simp
  · have h1 : Module.finrank 𝔽₂ ↥(LinearMap.range (Matrix.mulVecLin Xᵀ)) = X.rank :=
      Matrix.rank_transpose X
    rw [h1, F2.finrank_ortho]
    have h := LinearMap.finrank_range_add_finrank_ker X.mulVecLin
    rw [show Module.finrank 𝔽₂ ↥(LinearMap.range X.mulVecLin) = X.rank from rfl,
      Module.finrank_fin_fun] at h
    have hXm : (X.rank : ℕ) ≤ m := Matrix.rank_le_width X
    omega

/-- For any vector `w`, the condition `ker X ≤ (span w)^⊥` is equivalent to the condition
`w ∈ range Xᵀ`: in both forms this is the statement that `w` annihilates the kernel of `X`. -/
lemma ker_le_ortho_span_iff {m n : ℕ} (X : Matrix (Fin n) (Fin m) 𝔽₂)
    {w : Fin m → 𝔽₂} :
    LinearMap.ker X.mulVecLin ≤ F2.ortho (Submodule.span 𝔽₂ {w}) ↔
      w ∈ LinearMap.range (Matrix.mulVecLin Xᵀ) := by
  rw [← F2.le_ortho_iff (L := LinearMap.ker X.mulVecLin)
      (L' := F2.ortho (Submodule.span 𝔽₂ {w})),
    F2.ortho_ortho, Submodule.span_singleton_le_iff_mem,
    ← range_mulVecLin_transpose_eq_ortho_ker X]

/-! ## The hyperplane `(span w)^⊥` and its intersections -/

/-- A hyperplane of `𝔽₂ᵐ` cuts down any subspace by `0` or `1` dimensions: the intersection
`U ⊓ H` has the dimension of `U`, unless `U ⊄ H`, in which case it has codimension one in `U`.
(If `U ⊄ H` then `U + H` contains `H` strictly, hence is everything.) -/
lemma finrank_inf_ortho_span {m : ℕ} (U : Submodule 𝔽₂ (Fin m → 𝔽₂)) {w : Fin m → 𝔽₂}
    (hw : w ≠ 0) :
    Module.finrank 𝔽₂ ↥(U ⊓ F2.ortho (Submodule.span 𝔽₂ {w})) =
      Module.finrank 𝔽₂ ↥U - (if U ≤ F2.ortho (Submodule.span 𝔽₂ {w}) then 0 else 1) := by
  classical
  have hfinH : Module.finrank 𝔽₂ ↥(F2.ortho (Submodule.span 𝔽₂ {w})) = m - 1 := by
    rw [F2.finrank_ortho, finrank_span_singleton hw]
  have hm : 1 ≤ m := by
    have h2 := Submodule.finrank_le (Submodule.span 𝔽₂ {w} : Submodule 𝔽₂ (Fin m → 𝔽₂))
    rw [Module.finrank_fin_fun, finrank_span_singleton hw] at h2
    omega
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq U
    (F2.ortho (Submodule.span 𝔽₂ {w}))
  by_cases hle : U ≤ F2.ortho (Submodule.span 𝔽₂ {w})
  · rw [if_pos hle]
    have h1 : U ⊔ F2.ortho (Submodule.span 𝔽₂ {w}) = F2.ortho (Submodule.span 𝔽₂ {w}) :=
      sup_eq_right.mpr hle
    rw [h1] at hsup
    omega
  · rw [if_neg hle]
    have hlt : F2.ortho (Submodule.span 𝔽₂ {w}) <
        U ⊔ F2.ortho (Submodule.span 𝔽₂ {w}) :=
      lt_of_le_of_ne le_sup_right (fun h => hle (sup_eq_right.mp h.symm))
    have hgt : Module.finrank 𝔽₂ ↥(F2.ortho (Submodule.span 𝔽₂ {w})) <
        Module.finrank 𝔽₂ ↥(U ⊔ F2.ortho (Submodule.span 𝔽₂ {w})) :=
      Submodule.finrank_lt_finrank_of_lt hlt
    have hle' : Module.finrank 𝔽₂ ↥(U ⊔ F2.ortho (Submodule.span 𝔽₂ {w})) ≤ m := by
      have := Submodule.finrank_le (U ⊔ F2.ortho (Submodule.span 𝔽₂ {w}))
      rwa [Module.finrank_fin_fun] at this
    have hsupdim : Module.finrank 𝔽₂ ↥(U ⊔ F2.ortho (Submodule.span 𝔽₂ {w})) = m := by omega
    rw [hsupdim] at hsup
    have hpos : 1 ≤ Module.finrank 𝔽₂ ↥U := by
      have hne : U ≠ ⊥ := fun h => hle (by rw [h]; exact bot_le)
      have h0 : Module.finrank 𝔽₂ ↥U ≠ 0 := fun h => hne ((Submodule.finrank_eq_zero).mp h)
      omega
    omega

/-! ## The dual `hybridPred` -/

/-- In the dual case (`ker Q = ⊥`, `range ι = (span w)^⊥`), the hybrid Laplacian's Fourier
multiplier is exactly the condition `w ∈ range Xᵀ`. -/
lemma hybridPred_iff_dual {m n m' n' : ℕ} (Q : Matrix (Fin n') (Fin n) 𝔽₂)
    (ι : Matrix (Fin m) (Fin m') 𝔽₂) {w : Fin m → 𝔽₂} (_hw : w ≠ 0)
    (hQ : LinearMap.ker Q.mulVecLin = ⊥)
    (hι : LinearMap.range ι.mulVecLin = F2.ortho (Submodule.span 𝔽₂ {w}))
    (X : Matrix (Fin n) (Fin m) 𝔽₂) :
    hybridPred Q ι X ↔ w ∈ LinearMap.range (Matrix.mulVecLin Xᵀ) := by
  have h2 : (∀ u : Fin m → 𝔽₂, X.mulVec u ∈ LinearMap.ker Q.mulVecLin →
      u ∈ LinearMap.range ι.mulVecLin) ↔
      LinearMap.ker X.mulVecLin ≤ LinearMap.range ι.mulVecLin := by
    constructor
    · intro h u hu
      refine h u ?_
      have hu' : X.mulVecLin u = 0 := hu
      rw [hQ, Submodule.mem_bot, ← Matrix.mulVecLin_apply]
      exact hu'
    · intro h u hu
      refine h ?_
      have hu' : X.mulVec u = 0 := by
        rw [hQ, Submodule.mem_bot] at hu
        exact hu
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
      exact hu'
  rw [hybridPred, h2, hQ, hι, and_iff_right bot_le]
  exact ker_le_ortho_span_iff X

/-! ## The dual rank drop -/

/-- If `w ≠ 0` lies in the range of `Xᵀ` then `X` has rank at least one. -/
lemma one_le_rank_of_mem_range_transpose {m n : ℕ} {X : Matrix (Fin n) (Fin m) 𝔽₂}
    {w : Fin m → 𝔽₂} (hw : w ≠ 0) (hmem : w ∈ LinearMap.range (Matrix.mulVecLin Xᵀ)) :
    1 ≤ X.rank := by
  have h := one_le_rank_of_mem_range (X := Xᵀ) hw hmem
  rwa [Matrix.rank_transpose] at h

/-- **The exact rank drop of the dual order-one restriction.**  For `ker Q = ⊥` (so `Q` is
injective) and `ι` with `range ι = (span w)^⊥` (so `W₁ = range ι` is a hyperplane), the rank of
`Q * X * ι` drops by exactly one precisely when `w ∈ range Xᵀ`, i.e. when `ker X ⊆ range ι`. -/
lemma rank_mul_mul_eq_of_ker_eq_bot_ortho {m n m' n' : ℕ} (Q : Matrix (Fin n') (Fin n) 𝔽₂)
    (ι : Matrix (Fin m) (Fin m') 𝔽₂) {w : Fin m → 𝔽₂} (hw : w ≠ 0)
    (hQ : LinearMap.ker Q.mulVecLin = ⊥)
    (hι : LinearMap.range ι.mulVecLin = F2.ortho (Submodule.span 𝔽₂ {w}))
    (X : Matrix (Fin n) (Fin m) 𝔽₂) :
    (Q * X * ι).rank = X.rank - (if w ∈ LinearMap.range (Matrix.mulVecLin Xᵀ) then 1 else 0) := by
  classical
  -- Step 1: `Q` is injective, so it does not change the rank.
  have hA : (Q * X * ι).rank = (X * ι).rank := by
    rw [show (Q * X * ι).rank =
        Module.finrank 𝔽₂ ↥(LinearMap.range (Q * X * ι).mulVecLin) from rfl,
      show Q * X * ι = Q * (X * ι) from Matrix.mul_assoc Q X ι,
      Matrix.mulVecLin_mul, LinearMap.range_comp,
      Commons.LinearAlgebra.finrank_map_eq Q.mulVecLin (LinearMap.range (X * ι).mulVecLin),
      show (LinearMap.range (X * ι).mulVecLin ⊓ LinearMap.ker Q.mulVecLin) = ⊥ by
        rw [hQ, inf_bot_eq],
      finrank_bot, Nat.sub_zero]
    rfl
  rw [hA]
  have hB : (X * ι).rank = Module.finrank 𝔽₂ ↥(LinearMap.range ι.mulVecLin) -
      Module.finrank 𝔽₂ ↥(LinearMap.ker X.mulVecLin ⊓ LinearMap.range ι.mulVecLin) := by
    rw [show (X * ι).rank =
        Module.finrank 𝔽₂ ↥(LinearMap.range (X * ι).mulVecLin) from rfl,
      Matrix.mulVecLin_mul, LinearMap.range_comp,
      Commons.LinearAlgebra.finrank_map_eq X.mulVecLin (LinearMap.range ι.mulVecLin),
      inf_comm]
  rw [hB, hι]
  have hkey := finrank_inf_ortho_span (LinearMap.ker X.mulVecLin) hw
  have hiff : (w ∈ LinearMap.range (Matrix.mulVecLin Xᵀ)) ↔
      LinearMap.ker X.mulVecLin ≤ F2.ortho (Submodule.span 𝔽₂ {w}) :=
    (ker_le_ortho_span_iff X).symm
  have hrankX : X.rank = m - Module.finrank 𝔽₂ ↥(LinearMap.ker X.mulVecLin) := by
    have h := LinearMap.finrank_range_add_finrank_ker X.mulVecLin
    rw [show Module.finrank 𝔽₂ ↥(LinearMap.range X.mulVecLin) = X.rank from rfl,
      Module.finrank_fin_fun] at h
    have hXm : X.rank ≤ m := Matrix.rank_le_width X
    omega
  have hm : 1 ≤ m := by
    have h2 := Submodule.finrank_le (Submodule.span 𝔽₂ {w} : Submodule 𝔽₂ (Fin m → 𝔽₂))
    rw [Module.finrank_fin_fun, finrank_span_singleton hw] at h2
    omega
  have hfinH : Module.finrank 𝔽₂ ↥(F2.ortho (Submodule.span 𝔽₂ {w})) = m - 1 := by
    rw [F2.finrank_ortho, finrank_span_singleton hw]
  rw [hkey, hrankX, hfinH]
  by_cases hU : LinearMap.ker X.mulVecLin ≤ F2.ortho (Submodule.span 𝔽₂ {w})
  · rw [if_pos hU, if_pos (hiff.mpr hU)]
    have hle : Module.finrank 𝔽₂ ↥(LinearMap.ker X.mulVecLin) ≤ m - 1 := by
      have h := Submodule.finrank_mono hU
      rwa [hfinH] at h
    omega
  · rw [if_neg hU, if_neg (fun h => hU (hiff.mp h))]
    have hpos : 1 ≤ Module.finrank 𝔽₂ ↥(LinearMap.ker X.mulVecLin) := by
      have hne : LinearMap.ker X.mulVecLin ≠ ⊥ := fun h => hU (by rw [h]; exact bot_le)
      have h0 : Module.finrank 𝔽₂ ↥(LinearMap.ker X.mulVecLin) ≠ 0 :=
        fun h => hne ((Submodule.finrank_eq_zero).mp h)
      omega
    have hle : Module.finrank 𝔽₂ ↥(LinearMap.ker X.mulVecLin) ≤ m := by
      have h := Submodule.finrank_le (LinearMap.ker X.mulVecLin)
      rwa [Module.finrank_fin_fun] at h
    omega

/-! ## The operator `𝒯_{i,W'}` and its Fourier coefficients -/

/-- The dual operator `𝒯_{i,W'} = 1 - (q^i+q^{i-1})𝓔_{W'} + q^{2i-1}𝓔_{W'}²`. -/
def TOpW {m n : ℕ} (w : Fin m → 𝔽₂) (i : ℕ) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    Matrix (Fin m) (Fin n) 𝔽₂ → ℂ :=
  f - (((2 : ℂ) ^ i + (2 : ℂ) ^ (i - 1))) • eOpW w f +
    ((2 : ℂ) ^ (2 * i - 1)) • eOpW w (eOpW w f)

/-- The Fourier coefficients of `𝒯_{i,W'}`. -/
theorem fhat_TOpW {m n : ℕ} (w : Fin m → 𝔽₂) (hw : w ≠ 0) (i : ℕ)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) (X : Matrix (Fin n) (Fin m) 𝔽₂) :
    fhat (TOpW w i f) X =
      (1 - (((2 : ℂ) ^ i + (2 : ℂ) ^ (i - 1)) *
            (if w ∈ LinearMap.range (Matrix.mulVecLin Xᵀ) then 0
              else ((2 : ℂ) ^ X.rank)⁻¹))
          + ((2 : ℂ) ^ (2 * i - 1)) *
            ((if w ∈ LinearMap.range (Matrix.mulVecLin Xᵀ) then 0
                else ((2 : ℂ) ^ X.rank)⁻¹) *
             (if w ∈ LinearMap.range (Matrix.mulVecLin Xᵀ) then 0
                else ((2 : ℂ) ^ X.rank)⁻¹))) * fhat f X := by
  rw [TOpW, fhat_add, fhat_sub, fhat_smul, fhat_smul, fhat_eOpW w hw (eOpW w f) X,
    fhat_eOpW w hw f X]
  ring

/-- If `w ∈ range Xᵀ` then `𝒯_{i,W'}` does not change the coefficient at `X`. -/
lemma fcoeff_TOpW_of_mem {m n : ℕ} (w : Fin m → 𝔽₂) (hw : w ≠ 0) (i : ℕ)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) (X : Matrix (Fin n) (Fin m) 𝔽₂)
    (hX : w ∈ LinearMap.range (Matrix.mulVecLin Xᵀ)) :
    fcoeff (TOpW w i f) X = fcoeff f X := by
  rw [fcoeff, fcoeff, fhat_TOpW w hw i f X, if_pos hX]
  ring

/-- If `w ∉ range Xᵀ` and `rank X = i` then `𝒯_{i,W'}` kills the coefficient at `X`. -/
lemma fcoeff_TOpW_of_notMem_self {m n : ℕ} (w : Fin m → 𝔽₂) (hw : w ≠ 0) (i : ℕ)
    (hi : 1 ≤ i) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) (X : Matrix (Fin n) (Fin m) 𝔽₂)
    (hX : w ∉ LinearMap.range (Matrix.mulVecLin Xᵀ)) (hr : X.rank = i) :
    fcoeff (TOpW w i f) X = 0 := by
  rw [fcoeff, fhat_TOpW w hw i f X, if_neg hX, hr, tau_bracket_self i hi, zero_mul, mul_zero]

/-- If `w ∉ range Xᵀ` and `rank X = i - 1` then `𝒯_{i,W'}` kills the coefficient at `X`. -/
lemma fcoeff_TOpW_of_notMem_pred {m n : ℕ} (w : Fin m → 𝔽₂) (hw : w ≠ 0) (i : ℕ)
    (hi : 1 ≤ i) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) (X : Matrix (Fin n) (Fin m) 𝔽₂)
    (hX : w ∉ LinearMap.range (Matrix.mulVecLin Xᵀ)) (hr : X.rank = i - 1) :
    fcoeff (TOpW w i f) X = 0 := by
  rw [fcoeff, fhat_TOpW w hw i f X, if_neg hX, hr, tau_bracket_pred i hi, zero_mul, mul_zero]

/-! ## The main identity -/

/-- **The dual `lem:lv` of arXiv:2209.04243.**  For the dual order-one restriction
(`ker Q = ⊥`, `range ι = (span w)^⊥`) the level-`(d-1)` part of the restriction of
`𝒯_{d,W'}[f]` is the order-one derivative `D_{W',T}` of the pure level-`d` part of `f`. -/
theorem nprojPure_restr_shift_TOpW {m n m' n' : ℕ}
    (Q : Matrix (Fin n') (Fin n) 𝔽₂) (ι : Matrix (Fin m) (Fin m') 𝔽₂)
    {w : Fin m → 𝔽₂} (hw : w ≠ 0)
    (hQ : LinearMap.ker Q.mulVecLin = ⊥)
    (hι : LinearMap.range ι.mulVecLin = F2.ortho (Submodule.span 𝔽₂ {w}))
    (d : ℕ) (hd : 1 ≤ d) (T : Matrix (Fin m) (Fin n) 𝔽₂)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    nprojPure (d - 1) (restr Q ι (shift T (TOpW w d f))) =
      restr Q ι (shift T (lapMulN (hybridPred Q ι) (nprojPure d f))) := by
  classical
  refine eq_of_fcoeff_eq fun Y => ?_
  have hYr : ∀ X : Matrix (Fin n) (Fin m) 𝔽₂, Q * X * ι = Y →
      Y.rank = X.rank - (if w ∈ LinearMap.range (Matrix.mulVecLin Xᵀ) then 1 else 0) := by
    intro X hX
    rw [← hX, rank_mul_mul_eq_of_ker_eq_bot_ortho Q ι hw hQ hι X]
  rw [fcoeff_nprojPure, fcoeff_restr_shift, fcoeff_restr_shift, Finset.mul_sum]
  refine Finset.sum_congr rfl fun X hX => ?_
  rw [Finset.mem_filter] at hX
  rw [fcoeff_lapMulN, fcoeff_nprojPure]
  have hr := hYr X hX.2
  have hiff := hybridPred_iff_dual Q ι hw hQ hι X
  by_cases hYd : Y.rank = d - 1
  · rw [if_pos hYd]
    by_cases hmem : w ∈ LinearMap.range (Matrix.mulVecLin Xᵀ)
    · have hrd : X.rank = d := by
        have hh := hr; rw [if_pos hmem] at hh
        have hpos := one_le_rank_of_mem_range_transpose hw hmem
        omega
      rw [fcoeff_TOpW_of_mem w hw d f X hmem, hrd,
        if_pos (hiff.mpr hmem), if_pos rfl]
      ring
    · have hrd : X.rank = d - 1 := by
        have hh := hr; rw [if_neg hmem] at hh
        omega
      rw [fcoeff_TOpW_of_notMem_pred w hw d hd f X hmem hrd, hrd,
        if_neg (fun hh => hmem (hiff.mp hh))]
      ring
  · rw [if_neg hYd]
    by_cases hmem : w ∈ LinearMap.range (Matrix.mulVecLin Xᵀ)
    · rw [if_pos (hiff.mpr hmem)]
      by_cases hrd : X.rank = d
      · have hh : Y.rank = d - 1 := by
          have h1 := hr; rw [if_pos hmem, hrd] at h1; omega
        exact absurd hh hYd
      · rw [if_neg hrd]; ring
    · rw [if_neg (fun hh => hmem (hiff.mp hh))]; ring

end

end Submission.Grassmann