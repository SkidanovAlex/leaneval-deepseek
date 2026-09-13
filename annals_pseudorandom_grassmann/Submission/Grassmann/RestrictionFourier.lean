import Mathlib
import Submission.Grassmann.Restriction
import Submission.Grassmann.Fourier
import Submission.Grassmann.Laplacian
import Submission.Grassmann.BilinearDegree
import Submission.Grassmann.HybridLaplacian
import Submission.Commons.LinearAlgebra.Matrix.rank_mul_ge_add_sub
import Submission.Commons.LinearAlgebra.finrank_map_eq

/-!
# Fourier formulas for the restrictions (arXiv:2209.04243, §3.4)

For a "quotient" matrix `Q : Matrix (Fin n') (Fin n) 𝔽₂` (presenting a subspace `V₁ = ker Q ≤ V`)
and an "inclusion" matrix `ι : Matrix (Fin m) (Fin m') 𝔽₂` (presenting `W₁ = range ι ≤ W`), the
restriction operator of `Submission.Grassmann.Restriction` sends a function `f` on `L(V,W)` to
the function `A ↦ f(ι A Q)` on `L(V/V₁, W₁)`.

This file proves the two structural facts of §3.4 of arXiv:2209.04243:

* **`lem:restriction of characters`** — `restr Q ι (shift T (mchar X)) = mchar X T • mchar (Q*X*ι)`;
* **`lem:Fourier for restriction`** — the *normalised* Fourier coefficient of a restriction is
  the sum of the coefficients of the characters that map to a given character:
  `fcoeff (restr Q ι (shift T f)) Y = ∑_{X : Q*X*ι = Y} fcoeff f X * mchar X T`.

Both are stated for the *normalised* coefficient `fcoeff` (`= 2^{-mn} · fhat`), which is the
normalisation used throughout the paper.
-/

open Finset BigOperators Matrix
open Classical

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission.Grassmann

noncomputable section

local notation "𝔽₂" => ZMod 2

/-! ## The normalised Fourier coefficient -/

/-- The normalised Fourier coefficient `f̂(X) = 2^{-mn} ∑_A f A · mchar X A` (the normalisation
of arXiv:2209.04243). -/
def fcoeff {m n : ℕ} (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ)
    (X : Matrix (Fin n) (Fin m) 𝔽₂) : ℂ :=
  ((2 : ℂ) ^ (m * n))⁻¹ * fhat f X

lemma fcoeff_eq {m n : ℕ} (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ)
    (X : Matrix (Fin n) (Fin m) 𝔽₂) :
    fcoeff f X = ((2 : ℂ) ^ (m * n))⁻¹ * fhat f X := rfl

/-- `mchar X` evaluated at the zero matrix is `1`. -/
lemma mchar_zero {m n : ℕ} (X : Matrix (Fin n) (Fin m) 𝔽₂) :
    mchar X (0 : Matrix (Fin m) (Fin n) 𝔽₂) = 1 := by
  simp [mchar]

lemma fcoeff_add {m n : ℕ} (f g : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ)
    (X : Matrix (Fin n) (Fin m) 𝔽₂) : fcoeff (f + g) X = fcoeff f X + fcoeff g X := by
  simp only [fcoeff, fhat_add, mul_add]

lemma fcoeff_smul {m n : ℕ} (c : ℂ) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ)
    (X : Matrix (Fin n) (Fin m) 𝔽₂) : fcoeff (c • f) X = c * fcoeff f X := by
  simp only [fcoeff, fhat_smul]
  ring

lemma fcoeff_zero {m n : ℕ} (X : Matrix (Fin n) (Fin m) 𝔽₂) :
    fcoeff (0 : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) X = 0 := by
  simp [fcoeff, fhat]

/-- `fhat` is determined by the normalised coefficients. -/
theorem eq_of_fcoeff_eq {m n : ℕ} {f g : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ}
    (h : ∀ X : Matrix (Fin n) (Fin m) 𝔽₂, fcoeff f X = fcoeff g X) : f = g := by
  refine eq_of_fhat_eq fun X => ?_
  have h1 := h X
  rw [fcoeff_eq, fcoeff_eq] at h1
  exact mul_left_cancel₀ (inv_ne_zero (pow_ne_zero (m * n) (by norm_num : (2 : ℂ) ≠ 0))) h1

/-! ## The character identity (`lem:restriction of characters`) -/

/-- The value at `B` of the restricted character `mchar X`: `mchar X (ι B Q) = mchar (Q X ι) B`. -/
lemma mchar_restr_mul {m n m' n' : ℕ} (Q : Matrix (Fin n') (Fin n) 𝔽₂)
    (ι : Matrix (Fin m) (Fin m') 𝔽₂) (X : Matrix (Fin n) (Fin m) 𝔽₂)
    (B : Matrix (Fin m') (Fin n') 𝔽₂) :
    mchar X (ι * B * Q) = mchar (Q * X * ι) B :=
  congrFun (restr_mchar Q ι X) B

/-- **`lem:restriction of characters`**: the restriction of the character `mchar X` (after the
shift by `T`) is the scalar `mchar X T` times the character `mchar (Q * X * ι)` of the smaller
space. -/
theorem restr_shift_mchar {m n m' n' : ℕ} (Q : Matrix (Fin n') (Fin n) 𝔽₂)
    (ι : Matrix (Fin m) (Fin m') 𝔽₂) (T : Matrix (Fin m) (Fin n) 𝔽₂)
    (X : Matrix (Fin n) (Fin m) 𝔽₂) :
    restr Q ι (shift T (mchar X)) =
      (mchar X T) • (mchar (Q * X * ι) : Matrix (Fin m') (Fin n') 𝔽₂ → ℂ) := by
  funext B
  simp only [restr, shift, Pi.smul_apply, smul_eq_mul, mchar_restr_mul, mchar_add_right]
  ring

/-! ## The Fourier formula (`lem:Fourier for restriction`) -/

/-- **`lem:Fourier for restriction`** of arXiv:2209.04243: the normalised Fourier coefficient of
the restriction `f_{(V₁,W₁) → T}` at the character `Y` of the smaller space is the sum of
`f̂(X) · mchar X T` over all `X` with `Q * X * ι = Y`. -/
theorem fcoeff_restr_shift {m n m' n' : ℕ}
    (Q : Matrix (Fin n') (Fin n) 𝔽₂) (ι : Matrix (Fin m) (Fin m') 𝔽₂)
    (T : Matrix (Fin m) (Fin n) 𝔽₂) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ)
    (Y : Matrix (Fin n') (Fin m') 𝔽₂) :
    fcoeff (restr Q ι (shift T f)) Y =
      ∑ X ∈ Finset.univ.filter (fun X : Matrix (Fin n) (Fin m) 𝔽₂ => Q * X * ι = Y),
        fcoeff f X * mchar X T := by
  classical
  have h2pow : ((2 : ℂ) ^ (m' * n')) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h2pow' : ((2 : ℂ) ^ (m * n)) ≠ 0 := pow_ne_zero _ (by norm_num)
  -- The value of the restricted function at `B`, in terms of the coefficients of `f`.
  have hB : ∀ B : Matrix (Fin m') (Fin n') 𝔽₂,
      restr Q ι (shift T f) B =
        ((2 : ℂ) ^ (m * n))⁻¹ * ∑ X : Matrix (Fin n) (Fin m) 𝔽₂,
          fhat f X * mchar X T * mchar (Q * X * ι) B := by
    intro B
    have hinv := fhat_inversion f (ι * B * Q + T)
    have hgoal : ∑ X : Matrix (Fin n) (Fin m) 𝔽₂, fhat f X * mchar X (ι * B * Q + T) =
        ∑ X : Matrix (Fin n) (Fin m) 𝔽₂,
          fhat f X * mchar X T * mchar (Q * X * ι) B := by
      refine Finset.sum_congr rfl fun X _ => ?_
      rw [mchar_add_right, mchar_restr_mul]
      ring
    rw [restr, shift, ← hgoal, hinv]
    exact (inv_mul_cancel_left₀ h2pow' _).symm
  -- Read off the coefficient of `Y`.
  have houter : fhat (restr Q ι (shift T f)) Y =
      ((2 : ℂ) ^ (m * n))⁻¹ *
        ∑ X : Matrix (Fin n) (Fin m) 𝔽₂, fhat f X * mchar X T *
          (∑ B : Matrix (Fin m') (Fin n') 𝔽₂, mchar (Q * X * ι) B * mchar Y B) := by
    rw [fhat]
    calc ∑ B : Matrix (Fin m') (Fin n') 𝔽₂, restr Q ι (shift T f) B * mchar Y B
        = ∑ B, ((2 : ℂ) ^ (m * n))⁻¹ *
            (∑ X : Matrix (Fin n) (Fin m) 𝔽₂, fhat f X * mchar X T * mchar (Q * X * ι) B) *
              mchar Y B := Finset.sum_congr rfl fun B _ => by rw [hB B]
      _ = ((2 : ℂ) ^ (m * n))⁻¹ *
            ∑ B, (∑ X : Matrix (Fin n) (Fin m) 𝔽₂,
              fhat f X * mchar X T * mchar (Q * X * ι) B) * mchar Y B := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun B _ => by ring
      _ = ((2 : ℂ) ^ (m * n))⁻¹ *
            ∑ X : Matrix (Fin n) (Fin m) 𝔽₂, fhat f X * mchar X T *
              (∑ B : Matrix (Fin m') (Fin n') 𝔽₂, mchar (Q * X * ι) B * mchar Y B) := by
          congr 1
          rw [Finset.sum_congr rfl (fun B _ => Finset.sum_mul _ _ _), Finset.sum_comm]
          refine Finset.sum_congr rfl fun X _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun B _ => by ring
  rw [fcoeff, houter]
  have hkey : ∀ X : Matrix (Fin n) (Fin m) 𝔽₂,
      (∑ B : Matrix (Fin m') (Fin n') 𝔽₂, mchar (Q * X * ι) B * mchar Y B) =
        if Q * X * ι = Y then (2 : ℂ) ^ (m' * n') else 0 :=
    fun X => mchar_orthogonal (Q * X * ι) Y
  simp only [hkey]
  have hsum : ∑ X : Matrix (Fin n) (Fin m) 𝔽₂,
        fhat f X * mchar X T * (if Q * X * ι = Y then (2 : ℂ) ^ (m' * n') else 0) =
      (2 : ℂ) ^ (m' * n') *
        ∑ X ∈ Finset.univ.filter (fun X : Matrix (Fin n) (Fin m) 𝔽₂ => Q * X * ι = Y),
          fhat f X * mchar X T := by
    rw [Finset.mul_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun X _ => ?_
    by_cases h : Q * X * ι = Y
    · rw [if_pos h, if_pos h]; ring
    · rw [if_neg h, if_neg h]; ring
  rw [hsum]
  have hfix : ∑ X ∈ Finset.univ.filter (fun X : Matrix (Fin n) (Fin m) 𝔽₂ => Q * X * ι = Y),
        ((2 : ℂ) ^ (m * n))⁻¹ * fhat f X * mchar X T =
      ((2 : ℂ) ^ (m * n))⁻¹ *
        ∑ X ∈ Finset.univ.filter (fun X : Matrix (Fin n) (Fin m) 𝔽₂ => Q * X * ι = Y),
          fhat f X * mchar X T := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun X _ => by ring
  simp only [fcoeff]
  rw [hfix]
  field_simp

/-- **`lem:Fourier for restriction`**, unshifted form. -/
theorem fcoeff_restr {m n m' n' : ℕ}
    (Q : Matrix (Fin n') (Fin n) 𝔽₂) (ι : Matrix (Fin m) (Fin m') 𝔽₂)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) (Y : Matrix (Fin n') (Fin m') 𝔽₂) :
    fcoeff (restr Q ι f) Y =
      ∑ X ∈ Finset.univ.filter (fun X : Matrix (Fin n) (Fin m) 𝔽₂ => Q * X * ι = Y),
        fcoeff f X := by
  have h := fcoeff_restr_shift Q ι (0 : Matrix (Fin m) (Fin n) 𝔽₂) f Y
  have e1 : restr Q ι (shift (0 : Matrix (Fin m) (Fin n) 𝔽₂) f) = restr Q ι f := by
    congr 1
    funext A
    simp [shift]
  rw [e1] at h
  rw [Finset.sum_congr rfl (fun X _ => by rw [mchar_zero, mul_one])] at h
  exact h

/-- The normalised Fourier coefficients of a Fourier multiplier. -/
lemma fcoeff_lapMulN {m n : ℕ} (P : Matrix (Fin n) (Fin m) 𝔽₂ → Prop)
    (g : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) (X : Matrix (Fin n) (Fin m) 𝔽₂) :
    fcoeff (lapMulN P g) X = (if P X then 1 else 0) * fcoeff g X := by
  rw [fcoeff, fcoeff, fhat_lapMulN]
  ring


/-! ## The rank drop of a restriction, and the degree structure

A restriction can lower the *rank* (level) of a character by at most
`hybridOrder Q ι = dim V₁ + codim W₁`; this lets us control which levels can occur in the
restriction of a homogeneous function (`lem:lv`, §3.6 of arXiv:2209.04243). -/

/-- A first rank inequality: `rank X ≤ rank (Q * X) + (n - rank Q)`. -/
lemma rank_le_rank_mul_add {m n n' : ℕ} (Q : Matrix (Fin n') (Fin n) 𝔽₂)
    (X : Matrix (Fin n) (Fin m) 𝔽₂) :
    X.rank ≤ (Q * X).rank + (n - Q.rank) := by
  have h := Commons.LinearAlgebra.Matrix.rank_mul_ge_add_sub Q X
  have hQ : Q.rank ≤ n := Matrix.rank_le_width Q
  omega

/-- The rank drop of `Q * X * ι` is at most the order `hybridOrder Q ι`. -/
lemma rank_le_rank_mul_mul_add_hybridOrder {m n m' n' : ℕ}
    (Q : Matrix (Fin n') (Fin n) 𝔽₂) (X : Matrix (Fin n) (Fin m) 𝔽₂)
    (ι : Matrix (Fin m) (Fin m') 𝔽₂) :
    X.rank ≤ (Q * X * ι).rank + hybridOrder Q ι := by
  have h1 := rank_le_rank_mul_add Q X
  have h2 := Commons.LinearAlgebra.Matrix.rank_mul_ge_add_sub (Q * X) ι
  have hι : ι.rank ≤ m := Matrix.rank_le_height ι
  have hker : Module.finrank (ZMod 2) ↥(LinearMap.ker Q.mulVecLin) = n - Q.rank := by
    have h := LinearMap.finrank_range_add_finrank_ker Q.mulVecLin
    have hV : Module.finrank (ZMod 2) (Fin n → ZMod 2) = n := by
      rw [Module.finrank_pi, Fintype.card_fin]
    have hr : Module.finrank (ZMod 2) ↥(LinearMap.range Q.mulVecLin) = Q.rank := rfl
    omega
  have hιr : Module.finrank (ZMod 2) ↥(LinearMap.range ι.mulVecLin) = ι.rank := rfl
  rw [hybridOrder, hker, hιr]
  omega

/-! ## Minimum degree -/

/-- `f` has **minimum degree at least `d`**: all Fourier coefficients of rank `< d` vanish. -/
def DegGe {m n : ℕ} (d : ℕ) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) : Prop :=
  ∀ X : Matrix (Fin n) (Fin m) 𝔽₂, X.rank < d → fhat f X = 0

lemma degGe_projPure {m n : ℕ} (d : ℕ) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    DegGe d (projPure d f) := by
  intro X hX
  rw [fhat_projPure, if_neg (by omega), zero_mul]

lemma degLe_projPure {m n : ℕ} (d : ℕ) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    DegLe d (projPure d f) := by
  intro X hX
  rw [fhat_projPure, if_neg (by omega), zero_mul]

/-- **Restrictions raise the minimum degree by at most `hybridOrder Q ι`.** -/
theorem fcoeff_restr_shift_eq_zero_of_degGe {m n m' n' d : ℕ}
    (Q : Matrix (Fin n') (Fin n) 𝔽₂) (ι : Matrix (Fin m) (Fin m') 𝔽₂)
    (T : Matrix (Fin m) (Fin n) 𝔽₂) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ)
    (hf : DegGe d f) (Y : Matrix (Fin n') (Fin m') 𝔽₂)
    (hY : Y.rank + hybridOrder Q ι < d) :
    fcoeff (restr Q ι (shift T f)) Y = 0 := by
  rw [fcoeff_restr_shift]
  refine Finset.sum_eq_zero fun X hX => ?_
  rw [Finset.mem_filter] at hX
  have hXY : (Q * X * ι).rank = Y.rank := by rw [hX.2]
  have hXrank : X.rank ≤ Y.rank + hybridOrder Q ι := by
    have := rank_le_rank_mul_mul_add_hybridOrder Q X ι
    omega
  rw [fcoeff, hf X (by omega), mul_zero, zero_mul]

/-- **Restrictions lower the maximum degree**: a function of degree at most `d` restricts to
a function of degree at most `d`. -/
theorem fcoeff_restr_shift_eq_zero_of_degLe {m n m' n' d : ℕ}
    (Q : Matrix (Fin n') (Fin n) 𝔽₂) (ι : Matrix (Fin m) (Fin m') 𝔽₂)
    (T : Matrix (Fin m) (Fin n) 𝔽₂) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ)
    (hf : DegLe d f) (Y : Matrix (Fin n') (Fin m') 𝔽₂) (hY : d < Y.rank) :
    fcoeff (restr Q ι (shift T f)) Y = 0 := by
  rw [fcoeff_restr_shift]
  refine Finset.sum_eq_zero fun X hX => ?_
  rw [Finset.mem_filter] at hX
  have hXY : (Q * X * ι).rank = Y.rank := by rw [hX.2]
  have hle : (Q * X * ι).rank ≤ X.rank :=
    (Matrix.rank_mul_le_left (Q * X) ι).trans (Matrix.rank_mul_le_right Q X)
  rw [fcoeff, hf X (by omega), mul_zero, zero_mul]

/-- **The level structure of a restriction** (`lem:lv`'s linear-algebra input): the restriction
of a homogeneous function of degree `d` has nonzero Fourier coefficients only at levels in
`[d - hybridOrder Q ι, d]`. -/
theorem fcoeff_restr_shift_projPure_eq_zero_of_not_mem {m n m' n' d : ℕ}
    (Q : Matrix (Fin n') (Fin n) 𝔽₂) (ι : Matrix (Fin m) (Fin m') 𝔽₂)
    (T : Matrix (Fin m) (Fin n) 𝔽₂) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ)
    (Y : Matrix (Fin n') (Fin m') 𝔽₂)
    (hY : Y.rank + hybridOrder Q ι < d ∨ d < Y.rank) :
    fcoeff (restr Q ι (shift T (projPure d f))) Y = 0 := by
  rcases hY with h | h
  · exact fcoeff_restr_shift_eq_zero_of_degGe Q ι T _ (degGe_projPure d f) Y h
  · exact fcoeff_restr_shift_eq_zero_of_degLe Q ι T _ (degLe_projPure d f) Y h

/-! ## The exact rank drop

For the `(U,W) → 0` restriction (`V₁ = ker Q = span v`, `W₁ = W`, i.e. `range ι = ⊤`) the rank
of a restricted character drops by exactly `1` when `v` lies in the image of `X`, and not at
all otherwise.  This is the exact form of the level structure needed for `lem:lv`. -/

/-- Restricting along a surjection does not change the rank. -/
lemma rank_mul_mul_eq_of_range_eq_top {m n m' n' : ℕ} (Q : Matrix (Fin n') (Fin n) 𝔽₂)
    (X : Matrix (Fin n) (Fin m) 𝔽₂) (ι : Matrix (Fin m) (Fin m') 𝔽₂)
    (hι : LinearMap.range ι.mulVecLin = ⊤) : (Q * X * ι).rank = (Q * X).rank := by
  rw [Matrix.rank, Matrix.rank, Matrix.mulVecLin_mul (Q * X) ι, Matrix.mulVecLin_mul Q X,
    LinearMap.range_comp, hι, Submodule.map_top]

/-- **The exact rank drop of the `(span v, W) → 0` restriction**: for `ker Q = span v` with
`v ≠ 0`, the rank of `Q * X` is `X.rank - 1` when `v ∈ range X` and `X.rank` otherwise. -/
lemma rank_mul_eq_of_ker_eq_span {m n n' : ℕ} (Q : Matrix (Fin n') (Fin n) 𝔽₂)
    {v : Fin n → 𝔽₂} (hv : v ≠ 0)
    (hker : LinearMap.ker Q.mulVecLin = Submodule.span 𝔽₂ {v})
    (X : Matrix (Fin n) (Fin m) 𝔽₂) :
    (Q * X).rank = X.rank - (if v ∈ LinearMap.range X.mulVecLin then 1 else 0) := by
  classical
  have hedges : X.mulVecLin.range ⊓ LinearMap.ker Q.mulVecLin =
      if v ∈ LinearMap.range X.mulVecLin then Submodule.span 𝔽₂ {v} else ⊥ := by
    by_cases h : v ∈ LinearMap.range X.mulVecLin
    · rw [if_pos h, hker]
      exact le_antisymm inf_le_right (le_inf ((Submodule.span_singleton_le_iff_mem v X.mulVecLin.range).mpr h) le_rfl)
    · rw [if_neg h]
      refine le_antisymm ?_ bot_le
      intro w hw
      rw [Submodule.mem_bot]
      rw [hker, Submodule.mem_inf] at hw
      obtain ⟨hwX, hwv⟩ := hw
      rw [Submodule.mem_span_singleton] at hwv
      obtain ⟨c, hc⟩ := hwv
      have hc0 : c = 0 := by
        by_contra hcne
        apply h
        have hv_eq : v = c⁻¹ • w := by rw [← hc, smul_smul, inv_mul_cancel₀ hcne, one_smul]
        rw [hv_eq]
        exact Submodule.smul_mem _ _ hwX
      rw [hc0, zero_smul] at hc
      exact hc.symm
  have hmap : (Q * X).rank = Module.finrank (ZMod 2)
      ↥(Submodule.map Q.mulVecLin X.mulVecLin.range) := by
    rw [Matrix.rank, Matrix.mulVecLin_mul, LinearMap.range_comp]
  rw [hmap, Commons.LinearAlgebra.finrank_map_eq Q.mulVecLin X.mulVecLin.range, hedges]
  have hrank : Module.finrank (ZMod 2) ↥X.mulVecLin.range = X.rank := rfl
  rw [hrank]
  by_cases h : v ∈ LinearMap.range X.mulVecLin
  · rw [if_pos h, if_pos h, finrank_span_singleton hv]
  · rw [if_neg h, if_neg h, finrank_bot]

end

end Submission.Grassmann
