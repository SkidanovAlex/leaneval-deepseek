import Mathlib
import Submission.Grassmann.Shortcode
import Submission.Grassmann.Concentration
import Submission.Commons.Analysis.Inequalities.sum_Icc_pow_half_le
import Submission.Commons.Analysis.Inequalities.sum_Icc_pow_half_lt
import Submission.Commons.Analysis.Inequalities.le_mul_of_cube_le
import Submission.Commons.Analysis.Inequalities.le_rpow_third_mul

/-!
# Spectral expansion of the shortcode operator and small-set expansion (arXiv:2209.04243, §9)

This file contains the analytic endgame of route (B) of the Grassmann expansion project:

* the **spectral expansion** of the normalised shortcode adjacency operator
  `T f = ∑_X λ_{rank X} f̂(X) u_X`, equivalently
  `⟨T f, f⟩ = ∑_d λ_d ‖f^{=d}‖₂²` (paper §9, "Applications to small-set expansion");
* the **level-`d` concentration** in `ε^{1/3}` (cube-root) form;
* **Theorem 1.6** (`HypSSE`, small-set expansion in the shortcode graph) from the
  concentration corollary of the deep Theorem 1.5 (`HypCor4`).

The eigenvalue of `T` on the character `u_X` is

  `λ_{rank X} = (2^n (2^{m - rank X} - 1) - (2^m - 1)) / ((2^m - 1)(2^n - 1))`,

computed in `Submission.Grassmann.Shortcode` (`graphTOp_mchar`); note that this is the
honest Fourier multiplier of the average over rank-one shifts (the constant displayed in the
paper differs; see `ROADMAP.md`).  We record here the two properties that the small-set
expansion argument uses: `λ_d ≤ 2^{-d}` and `λ_d ≤ 1` for all `d`.
-/

open Finset BigOperators Matrix
open Classical

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission.Grassmann

noncomputable section

local notation "𝔽₂" => ZMod 2

variable {m n : ℕ}

/-! ## The shortcode eigenvalue, as a real number -/

/-- The normalised shortcode eigenvalue attached to a character of rank `d`. -/
def lamD (m n d : ℕ) : ℝ :=
  ((2 : ℝ) ^ n * ((2 : ℝ) ^ (m - d) - 1) - ((2 : ℝ) ^ m - 1)) /
    (((2 : ℝ) ^ m - 1) * ((2 : ℝ) ^ n - 1))

/-- `graphTOp_mchar`, with the eigenvalue written as a real number. -/
lemma graphTOp_mchar_lam {m n : ℕ} (X : Matrix (Fin n) (Fin m) 𝔽₂)
    (A : Matrix (Fin m) (Fin n) 𝔽₂) :
    graphTOp (mchar X) A = (lamD m n X.rank : ℂ) * mchar X A := by
  rw [graphTOp_mchar, lamD]
  push_cast
  rw [div_eq_mul_inv]

/-! ## Linearity of the shortcode operator -/

lemma graphTOp_add {m n : ℕ} (f g : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    graphTOp (f + g) = graphTOp f + graphTOp g := by
  funext A
  simp only [graphTOp, Pi.add_apply, Finset.sum_add_distrib, mul_add]

lemma graphTOp_smul {m n : ℕ} (c : ℂ) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    graphTOp (c • f) = c • graphTOp f := by
  funext A
  simp only [graphTOp, Pi.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum]
  ring

lemma graphTOp_sum {m n : ℕ} {ι : Type*} (s : Finset ι)
    (g : ι → Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    graphTOp (∑ i ∈ s, g i) = ∑ i ∈ s, graphTOp (g i) := by
  funext A
  simp only [graphTOp, Finset.sum_apply]
  rw [Finset.sum_comm, Finset.mul_sum]

/-! ## The spectral expansion -/

/-- Fourier inversion, in the normalised-coefficient form used throughout §9. -/
lemma eq_sum_fcoeff_mchar {m n : ℕ} (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    f = ∑ X : Matrix (Fin n) (Fin m) 𝔽₂, fcoeff f X • mchar X := by
  funext A
  have h := fhat_inversion f A
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, fcoeff]
  have h2 : (∑ X : Matrix (Fin n) (Fin m) 𝔽₂,
        ((2 : ℂ) ^ (m * n))⁻¹ * fhat f X * mchar X A) =
      ((2 : ℂ) ^ (m * n))⁻¹ *
        ∑ X : Matrix (Fin n) (Fin m) 𝔽₂, fhat f X * mchar X A := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun X _ => by ring
  rw [h2, h, inv_mul_cancel_left₀ (pow_ne_zero _ (by norm_num : (2 : ℂ) ≠ 0)) (f A)]

/-- **The spectral expansion**: `T f = ∑_X λ_{rank X} f̂(X) u_X`. -/
lemma graphTOp_eq_sum {m n : ℕ} (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    graphTOp f = ∑ X : Matrix (Fin n) (Fin m) 𝔽₂,
      (fcoeff f X * (lamD m n X.rank : ℂ)) • mchar X := by
  conv_lhs => rw [eq_sum_fcoeff_mchar f]
  rw [graphTOp_sum]
  refine Finset.sum_congr rfl fun X _ => ?_
  funext A
  rw [graphTOp_smul]
  simp only [Pi.smul_apply, smul_eq_mul, graphTOp_mchar_lam]
  ring

/-- **The Fourier multiplier form**: `T` multiplies the coefficient of `u_X` by
`λ_{rank X}`. -/
lemma fcoeff_graphTOp {m n : ℕ} (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ)
    (X : Matrix (Fin n) (Fin m) 𝔽₂) :
    fcoeff (graphTOp f) X = (lamD m n X.rank : ℂ) * fcoeff f X := by
  rw [fcoeff, graphTOp_eq_sum]
  rw [fhat_sum]
  have h : ∀ Y : Matrix (Fin n) (Fin m) 𝔽₂,
      fhat ((fcoeff f Y * (lamD m n Y.rank : ℂ)) • mchar Y) X =
        (fcoeff f Y * (lamD m n Y.rank : ℂ)) * (if Y = X then (2 : ℂ) ^ (m * n) else 0) := by
    intro Y
    rw [fhat_smul, fhat_mchar]
  rw [Finset.sum_congr rfl (fun Y _ => h Y)]
  rw [Finset.sum_eq_single X]
  · rw [if_pos rfl]
    rw [fcoeff]
    field_simp
  · intro Y _ hYX
    rw [if_neg hYX, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ X) h

/-- **Spectral expansion of the quadratic form**: `⟨T f, f⟩ = ∑_X λ_{rank X} ‖f̂(X)‖²`. -/
lemma inner2_graphTOp {m n : ℕ} (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    inner2 (graphTOp f) f =
      ∑ X : Matrix (Fin n) (Fin m) 𝔽₂,
        (lamD m n X.rank : ℂ) * ((‖fcoeff f X‖ ^ 2 : ℝ) : ℂ) := by
  rw [inner2_eq_fcoeff]
  refine Finset.sum_congr rfl fun X _ => ?_
  rw [fcoeff_graphTOp]
  simp [Complex.mul_conj', mul_assoc]

/-- The level decomposition of the quadratic form:
`⟨T f, f⟩ = ∑_d λ_d ‖f^{= d}‖₂²`. -/
lemma inner2_graphTOp_lvl {m n : ℕ} (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    inner2 (graphTOp f) f =
      ((∑ d ∈ Finset.range (min m n + 1), lamD m n d * l2sq (nprojPure d f) : ℝ) : ℂ) := by
  rw [inner2_graphTOp]
  have hcast : (∑ X : Matrix (Fin n) (Fin m) 𝔽₂,
        (lamD m n X.rank : ℂ) * ((‖fcoeff f X‖ ^ 2 : ℝ) : ℂ)) =
      ((∑ X : Matrix (Fin n) (Fin m) 𝔽₂, lamD m n X.rank * ‖fcoeff f X‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun X _ => by
      rw [Complex.ofReal_mul]
  rw [hcast]
  congr 1
  have hlv : ∀ d : ℕ, l2sq (nprojPure d f) =
      ∑ X : Matrix (Fin n) (Fin m) 𝔽₂, if X.rank = d then ‖fcoeff f X‖ ^ 2 else 0 := by
    intro d
    rw [← sum_normSq_fcoeff (nprojPure d f)]
    refine Finset.sum_congr rfl fun X _ => ?_
    rw [fcoeff_nprojPure]
    by_cases hX : X.rank = d <;> simp [hX]
  have hsum : (∑ d ∈ Finset.range (min m n + 1), lamD m n d * l2sq (nprojPure d f)) =
      ∑ d ∈ Finset.range (min m n + 1), ∑ X : Matrix (Fin n) (Fin m) 𝔽₂,
        if X.rank = d then lamD m n d * ‖fcoeff f X‖ ^ 2 else 0 := by
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [hlv d, Finset.mul_sum]
    refine Finset.sum_congr rfl fun X _ => ?_
    by_cases hX : X.rank = d <;> simp [hX]
  rw [hsum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun X _ => ?_
  rw [Finset.sum_eq_single X.rank]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg (fun h => hb h.symm)]
  · intro h
    exact absurd (Finset.mem_range.mpr (by have := rank_le_min X; omega)) h

/-- The real form of the level decomposition of the quadratic form. -/
lemma inner2_graphTOp_re {m n : ℕ} (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    (inner2 (graphTOp f) f).re =
      ∑ d ∈ Finset.range (min m n + 1), lamD m n d * l2sq (nprojPure d f) := by
  rw [inner2_graphTOp_lvl, Complex.ofReal_re]

/-! ## The indicator of a family of linear maps and the small-set-expansion count -/

/-- The indicator function of a family `S` of matrices, as a complex-valued function. -/
def ind {m n : ℕ} (S : Finset (Matrix (Fin m) (Fin n) 𝔽₂)) :
    Matrix (Fin m) (Fin n) 𝔽₂ → ℂ := fun A => if A ∈ S then 1 else 0

lemma ind_apply {m n : ℕ} (S : Finset (Matrix (Fin m) (Fin n) 𝔽₂))
    (A : Matrix (Fin m) (Fin n) 𝔽₂) : ind S A = if A ∈ S then 1 else 0 := rfl

lemma ind_isBool {m n : ℕ} (S : Finset (Matrix (Fin m) (Fin n) 𝔽₂)) : IsBoolBS (ind S) :=
  fun A => by by_cases h : A ∈ S <;> simp [ind, h]

lemma star_ind {m n : ℕ} (S : Finset (Matrix (Fin m) (Fin n) 𝔽₂))
    (A : Matrix (Fin m) (Fin n) 𝔽₂) : star (ind S A) = ind S A := by
  by_cases h : A ∈ S <;> simp [ind, h]

lemma ind_eq_ofReal {m n : ℕ} (S : Finset (Matrix (Fin m) (Fin n) 𝔽₂))
    (A : Matrix (Fin m) (Fin n) 𝔽₂) :
    ind S A = (((if A ∈ S then (1 : ℝ) else 0)) : ℂ) := by
  by_cases h : A ∈ S <;> simp [ind, h]

lemma l2sq_ind {m n : ℕ} (S : Finset (Matrix (Fin m) (Fin n) 𝔽₂)) :
    l2sq (ind S) = ((2 : ℝ) ^ (m * n))⁻¹ * (S.card : ℝ) := by
  rw [l2sq]
  congr 1
  rw [← Finset.sum_subset (Finset.subset_univ S)
      (fun A _ hA => by rw [ind, if_neg hA]; norm_num)]
  have h : ∀ A ∈ S, ‖ind S A‖ ^ 2 = (1 : ℝ) := by
    intro A hA
    rw [ind, if_pos hA]
    norm_num
  rw [Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- The set of matrices of rank one. -/
def rankOneSet (m n : ℕ) : Finset (Matrix (Fin m) (Fin n) 𝔽₂) :=
  Finset.univ.filter (fun B => B.rank = 1)

/-- The number of matrices of rank one. -/
def rankOneCount (m n : ℕ) : ℝ := ((rankOneSet m n).card : ℝ)

lemma rankOneCount_natCast {m n : ℕ} :
    ((rankOneCount m n : ℂ)) =
      ((Finset.univ.filter fun B : Matrix (Fin m) (Fin n) 𝔽₂ => B.rank = 1).card : ℂ) := by
  rw [rankOneCount, rankOneSet]
  push_cast
  ring

lemma rankOneCount_eq_sum {m n : ℕ} :
    rankOneCount m n =
      (∑ B : Matrix (Fin m) (Fin n) 𝔽₂, if B.rank = 1 then (1 : ℝ) else 0) := by
  rw [rankOneCount, rankOneSet, Finset.sum_boole]

lemma rankOneCount_eq_card {m n : ℕ} : rankOneCount m n = (((2 ^ m - 1) * (2 ^ n - 1) : ℕ) : ℝ) := by
  rw [rankOneCount, rankOneSet, card_rank_one_filter]

/-- The number of rank-one neighbours of `A` that lie in `S`. -/
def sseRow {m n : ℕ} (S : Finset (Matrix (Fin m) (Fin n) 𝔽₂))
    (A : Matrix (Fin m) (Fin n) 𝔽₂) : ℝ :=
  ∑ B ∈ rankOneSet m n, if A + B ∈ S then (1 : ℝ) else 0

lemma sseRow_eq_sum {m n : ℕ} (S : Finset (Matrix (Fin m) (Fin n) 𝔽₂))
    (A : Matrix (Fin m) (Fin n) 𝔽₂) :
    sseRow S A = ∑ B : Matrix (Fin m) (Fin n) 𝔽₂,
      if B.rank = 1 then (if A + B ∈ S then (1 : ℝ) else 0) else 0 := by
  rw [sseRow, rankOneSet, Finset.sum_filter]

/-- The numerator of the small-set-expansion probability `Pr_{A∼S, B of rank 1}[A + B ∈ S]`. -/
def sseNum {m n : ℕ} (S : Finset (Matrix (Fin m) (Fin n) 𝔽₂)) : ℝ :=
  ∑ A ∈ S, sseRow S A

lemma sseNum_eq_sum {m n : ℕ} (S : Finset (Matrix (Fin m) (Fin n) 𝔽₂)) :
    sseNum S = ∑ A ∈ S, ∑ B : Matrix (Fin m) (Fin n) 𝔽₂,
      if B.rank = 1 then (if A + B ∈ S then (1 : ℝ) else 0) else 0 := by
  rw [sseNum]
  exact Finset.sum_congr rfl fun A _ => sseRow_eq_sum S A

/-- The shortcode operator applied to the indicator of `S`, evaluated at `A`. -/
lemma graphTOp_ind_apply {m n : ℕ} (S : Finset (Matrix (Fin m) (Fin n) 𝔽₂))
    (A : Matrix (Fin m) (Fin n) 𝔽₂) :
    graphTOp (ind S) A = (rankOneCount m n : ℂ)⁻¹ * (sseRow S A : ℂ) := by
  rw [graphTOp, ← rankOneCount_natCast]
  have h : (∑ B ∈ (Finset.univ.filter fun B : Matrix (Fin m) (Fin n) 𝔽₂ => B.rank = 1),
        ind S (A + B)) = ((sseRow S A : ℝ) : ℂ) := by
    rw [show sseRow S A = ∑ B ∈ (Finset.univ.filter
        fun B : Matrix (Fin m) (Fin n) 𝔽₂ => B.rank = 1),
          (if A + B ∈ S then (1 : ℝ) else 0) from rfl]
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun B _ => ?_
    by_cases h : A + B ∈ S <;> simp [ind, h]
  rw [h]

/-- **The quadratic form of the shortcode operator against an indicator**: it counts the
rank-one steps `A → A + B` that stay inside `S`, suitably normalised. -/
lemma inner2_graphTOp_ind {m n : ℕ} (S : Finset (Matrix (Fin m) (Fin n) 𝔽₂)) :
    inner2 (graphTOp (ind S)) (ind S) =
      ((((2 : ℝ) ^ (m * n))⁻¹ * ((rankOneCount m n)⁻¹ * sseNum S) : ℝ) : ℂ) := by
  rw [inner2]
  have hsupp : (∑ A : Matrix (Fin m) (Fin n) 𝔽₂, graphTOp (ind S) A * ind S A) =
      ∑ A ∈ S, graphTOp (ind S) A := by
    have h1 : (∑ A : Matrix (Fin m) (Fin n) 𝔽₂, graphTOp (ind S) A * ind S A) =
        ∑ A ∈ S, graphTOp (ind S) A * ind S A :=
      (Finset.sum_subset (f := fun A => graphTOp (ind S) A * ind S A)
        (Finset.subset_univ S)
        (fun A _ hA => by rw [ind, if_neg hA, mul_zero])).symm
    rw [h1]
    exact Finset.sum_congr rfl fun A hA => by rw [ind, if_pos hA, mul_one]
  have hst : (∑ A : Matrix (Fin m) (Fin n) 𝔽₂, graphTOp (ind S) A * star (ind S A)) =
      ∑ A : Matrix (Fin m) (Fin n) 𝔽₂, graphTOp (ind S) A * ind S A :=
    Finset.sum_congr rfl fun A _ => by rw [star_ind]
  have hval : (∑ A ∈ S, graphTOp (ind S) A) = (rankOneCount m n : ℂ)⁻¹ * ↑(sseNum S) := by
    have h1 : (∑ A ∈ S, graphTOp (ind S) A) =
        ∑ A ∈ S, (rankOneCount m n : ℂ)⁻¹ * ↑(sseRow S A) :=
      Finset.sum_congr rfl fun A _ => graphTOp_ind_apply S A
    rw [h1, ← Finset.mul_sum]
    congr 1
    rw [sseNum, Complex.ofReal_sum]
  have hmain : (∑ A : Matrix (Fin m) (Fin n) 𝔽₂, graphTOp (ind S) A * star (ind S A)) =
      ((((rankOneCount m n)⁻¹ * sseNum S : ℝ)) : ℂ) := by
    rw [hst, hsupp, hval]
    push_cast
    ring
  rw [hmain]
  rw [show ((2 : ℂ) ^ (m * n))⁻¹ = ((((2 : ℝ) ^ (m * n))⁻¹ : ℝ) : ℂ) from by
    rw [Complex.ofReal_inv, Complex.ofReal_pow]
    norm_num]
  rw [← Complex.ofReal_mul]

/-- The real form of `inner2_graphTOp_ind`. -/
lemma inner2_graphTOp_ind_re {m n : ℕ} (S : Finset (Matrix (Fin m) (Fin n) 𝔽₂)) :
    (inner2 (graphTOp (ind S)) (ind S)).re =
      ((2 : ℝ) ^ (m * n))⁻¹ * ((rankOneCount m n)⁻¹ * sseNum S) := by
  rw [inner2_graphTOp_ind, Complex.ofReal_re]

/-- **The spectral expansion of the shortcode graph against an indicator**. -/
lemma spectral_expansion_ind {m n : ℕ} (S : Finset (Matrix (Fin m) (Fin n) 𝔽₂)) :
    (∑ d ∈ Finset.range (min m n + 1), lamD m n d * l2sq (nprojPure d (ind S))) =
      ((2 : ℝ) ^ (m * n))⁻¹ * ((rankOneCount m n)⁻¹ * sseNum S) := by
  rw [← inner2_graphTOp_re (ind S), inner2_graphTOp_ind_re]

/-! ## Monotonicity of globalness -/

lemma GlobalBS_mono {m n : ℕ} {d d' : ℕ} {ε : ℝ} {f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ}
    (h : d' ≤ d) (hf : GlobalBS d ε f) : GlobalBS d' ε f :=
  fun Q ι hQ T => hf Q ι (le_trans hQ h) T

/-! ## The shortcode eigenvalue is at most `2^{-d}` -/

lemma lamD_le_half {m n d : ℕ} (hm : d ≤ m) : lamD m n d ≤ ((1 / 2 : ℝ)) ^ d := by
  rw [one_div, inv_pow]
  set u : ℝ := ((2 : ℝ) ^ d)⁻¹ with hu
  have hu1 : u ≤ 1 := by
    rw [hu]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  have hpow : (2 : ℝ) ^ (m - d) = (2 : ℝ) ^ m * u := by
    rw [hu, pow_sub₀ (2 : ℝ) (by norm_num) hm]
  have hPm : (1 : ℝ) ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
  have hPn : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have hden : (0 : ℝ) ≤ ((2 : ℝ) ^ m - 1) * ((2 : ℝ) ^ n - 1) :=
    mul_nonneg (by linarith) (by linarith)
  rw [lamD, hpow]
  rcases lt_or_eq_of_le hden with hpos | hzero
  · rw [div_le_iff₀ hpos]
    have key : u * (((2 : ℝ) ^ m - 1) * ((2 : ℝ) ^ n - 1)) -
        ((2 : ℝ) ^ n * ((2 : ℝ) ^ m * u - 1) - ((2 : ℝ) ^ m - 1)) =
        (1 - u) * ((2 : ℝ) ^ m + (2 : ℝ) ^ n - 1) := by ring
    have hnn : 0 ≤ (1 - u) * ((2 : ℝ) ^ m + (2 : ℝ) ^ n - 1) :=
      mul_nonneg (by linarith) (by linarith)
    linarith
  · rw [← hzero, div_zero, hu]
    positivity

lemma lamD_le_one {m n d : ℕ} (hm : d ≤ m) : lamD m n d ≤ 1 := by
  have h1 := lamD_le_half (m := m) (n := n) hm
  have h2 : ((1 / 2 : ℝ)) ^ d ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  linarith
/-! ## Elementary arithmetic for the small-set expansion estimate -/

lemma arith_sse1 (K d r : ℕ) (hr : 1 ≤ r) (hd : d ≤ r + 1) :
    K * d^2 + 6 * (r+1) ≤ (4*K+30) * r^2 := by
  have h1 : d^2 ≤ 4 * r^2 := by
    have h2 : d ≤ 2 * r := by omega
    calc d^2 ≤ (2*r)^2 := Nat.pow_le_pow_left h2 2
      _ = 4 * r^2 := by ring
  have h3 : 6 * (r+1) ≤ 30 * r^2 := by
    have : 1 ≤ r := hr
    nlinarith
  have h4 : K * d^2 ≤ K * (4 * r^2) := Nat.mul_le_mul_left K h1
  calc K * d^2 + 6 * (r+1) ≤ K * (4*r^2) + 30*r^2 := add_le_add h4 h3
    _ = (4*K+30) * r^2 := by ring

lemma arith_sse2 (r : ℕ) (_hr : 1 ≤ r) : r + 2 ≤ 2^(r+1) := by
  have := Nat.lt_two_pow_self (n := r+1)
  omega

/-! ## The main estimate: the quadratic form is small -/

theorem sse_sum_lt (H : HypCor4) :
    ∃ C₀ : ℕ, 0 < C₀ ∧ ∀ (m n r : ℕ), 1 ≤ r →
      ∀ S : Finset (Matrix (Fin m) (Fin n) 𝔽₂),
      0 < l2sq (ind S) →
      GlobalBS (r + 1) (((2 : ℝ) ^ (C₀ * r ^ 2))⁻¹) (ind S) →
        (∑ d ∈ Finset.range (min m n + 1), lamD m n d * l2sq (nprojPure d (ind S)))
          < ((2 : ℝ) ^ r)⁻¹ * l2sq (ind S) := by
  obtain ⟨K, hK, hconc⟩ := concentration_of_HypCor4 H
  refine ⟨4 * K + 30, by omega, ?_⟩
  intro m n r hr S hB hglob
  set X : ℝ := (((2 : ℝ) ^ (r + 1) * ((r : ℝ) + 2))⁻¹) with hX
  have hXpos : 0 < X := by rw [hX]; positivity
  -- the level-`d` bound for `d ≤ r + 1`
  have hlev : ∀ d : ℕ, d ≤ r + 1 → l2sq (nprojPure d (ind S)) ≤ X * l2sq (ind S) := by
    intro d hd
    have hglob' : GlobalBS d (((2 : ℝ) ^ ((4 * K + 30) * r ^ 2))⁻¹) (ind S) :=
      GlobalBS_mono hd hglob
    have hε : 0 ≤ (((2 : ℝ) ^ ((4 * K + 30) * r ^ 2))⁻¹) := by positivity
    have hcube := hconc m n d (ind S) (((2 : ℝ) ^ ((4 * K + 30) * r ^ 2))⁻¹)
      hε (ind_isBool S) hglob'
    have harith : (2 : ℝ) ^ (K * d ^ 2) * ((2 : ℝ) ^ ((4 * K + 30) * r ^ 2))⁻¹ ≤ X^3 := by
      have hX3 : X^3 = ((2 : ℝ) ^ (3 * (r + 1)) * ((r : ℝ) + 2) ^ 3)⁻¹ := by
        rw [hX, inv_pow, mul_pow, ← pow_mul, show (r + 1) * 3 = 3 * (r + 1) from by ring]
      rw [hX3]
      have hnat : r + 2 ≤ 2 ^ (r+1) := arith_sse2 r hr
      have h2 : ((r : ℝ) + 2) ^ 3 ≤ (2 : ℝ) ^ (3 * (r + 1)) := by
        have hcast : ((r : ℝ) + 2) ≤ (2 : ℝ) ^ (r + 1) := by exact_mod_cast hnat
        calc ((r : ℝ) + 2) ^ 3 ≤ ((2 : ℝ) ^ (r + 1)) ^ 3 :=
              pow_le_pow_left₀ (by positivity) hcast 3
          _ = (2 : ℝ) ^ (3 * (r + 1)) := by
              rw [← pow_mul, show (r + 1) * 3 = 3 * (r + 1) from by ring]
      have h1 : (2 : ℝ) ^ (K * d ^ 2) * ((2 : ℝ) ^ (3 * (r + 1)) * ((r : ℝ) + 2) ^ 3)
          ≤ (2 : ℝ) ^ ((4 * K + 30) * r ^ 2) := by
        have hEE : (2 : ℝ) ^ (3 * (r + 1)) * (2 : ℝ) ^ (3 * (r + 1)) =
            (2 : ℝ) ^ (3 * (r + 1) + 3 * (r + 1)) := (pow_add _ _ _).symm
        have hexp : K * d ^ 2 + (3 * (r + 1) + 3 * (r + 1)) = K * d ^ 2 + 6 * (r + 1) := by
          ring
        calc (2 : ℝ) ^ (K * d ^ 2) * ((2 : ℝ) ^ (3 * (r + 1)) * ((r : ℝ) + 2) ^ 3)
            ≤ (2 : ℝ) ^ (K * d ^ 2) *
                ((2 : ℝ) ^ (3 * (r + 1)) * (2 : ℝ) ^ (3 * (r + 1))) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left h2 (by positivity)) (by positivity)
          _ = (2 : ℝ) ^ (K * d ^ 2) * (2 : ℝ) ^ (3 * (r + 1) + 3 * (r + 1)) := by rw [hEE]
          _ = (2 : ℝ) ^ (K * d ^ 2 + (3 * (r + 1) + 3 * (r + 1))) :=
              (pow_add (2 : ℝ) (K * d ^ 2) (3 * (r + 1) + 3 * (r + 1))).symm
          _ = (2 : ℝ) ^ (K * d ^ 2 + 6 * (r + 1)) := by rw [hexp]
          _ ≤ (2 : ℝ) ^ ((4 * K + 30) * r ^ 2) :=
              pow_le_pow_right₀ (by norm_num) (arith_sse1 K d r hr hd)
      have h3 : (2 : ℝ) ^ (K * d ^ 2) ≤
          (2 : ℝ) ^ ((4 * K + 30) * r ^ 2) *
            ((2 : ℝ) ^ (3 * (r + 1)) * ((r : ℝ) + 2) ^ 3)⁻¹ := by
        have hd1 : (2 : ℝ) ^ ((4 * K + 30) * r ^ 2) *
              ((2 : ℝ) ^ (3 * (r + 1)) * ((r : ℝ) + 2) ^ 3)⁻¹ =
            (2 : ℝ) ^ ((4 * K + 30) * r ^ 2) /
              ((2 : ℝ) ^ (3 * (r + 1)) * ((r : ℝ) + 2) ^ 3) := by
          rw [div_eq_mul_inv]
        rw [hd1, le_div_iff₀ (by positivity)]
        exact h1
      calc (2 : ℝ) ^ (K * d ^ 2) * ((2 : ℝ) ^ ((4 * K + 30) * r ^ 2))⁻¹
          ≤ ((2 : ℝ) ^ ((4 * K + 30) * r ^ 2) *
                ((2 : ℝ) ^ (3 * (r + 1)) * ((r : ℝ) + 2) ^ 3)⁻¹) *
              ((2 : ℝ) ^ ((4 * K + 30) * r ^ 2))⁻¹ :=
            mul_le_mul_of_nonneg_right h3 (by positivity)
        _ = ((2 : ℝ) ^ (3 * (r + 1)) * ((r : ℝ) + 2) ^ 3)⁻¹ := by
            rw [mul_assoc,
              mul_comm ((2 : ℝ) ^ (3 * (r + 1)) * ((r : ℝ) + 2) ^ 3)⁻¹
                ((2 : ℝ) ^ ((4 * K + 30) * r ^ 2))⁻¹,
              ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
    have hcube' : (l2sq (nprojPure d (ind S)))^3 ≤
        ((2 : ℝ) ^ (K * d ^ 2) * ((2 : ℝ) ^ ((4 * K + 30) * r ^ 2))⁻¹) *
          (l2sq (ind S))^3 := hcube
    exact Commons.Analysis.Inequalities.le_mul_of_cube_le (l2sq_nonneg _) (l2sq_nonneg _)
      (le_of_lt hXpos) hcube' harith
  -- splitting the level sum
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.range (min m n + 1))
    (fun d => d ≤ r + 1) (fun d => lamD m n d * l2sq (nprojPure d (ind S)))
  have hhead : (∑ d ∈ (Finset.range (min m n + 1)).filter (fun d => d ≤ r + 1),
      lamD m n d * l2sq (nprojPure d (ind S))) ≤ ((2 : ℝ) ^ (r + 1))⁻¹ * l2sq (ind S) := by
    have hterm : ∀ d ∈ (Finset.range (min m n + 1)).filter (fun d => d ≤ r + 1),
        lamD m n d * l2sq (nprojPure d (ind S)) ≤ X * l2sq (ind S) := by
      intro d hd
      rw [Finset.mem_filter, Finset.mem_range] at hd
      obtain ⟨hdm, hdr⟩ := hd
      have hdm' : d ≤ m := le_trans (Nat.lt_succ_iff.mp hdm) (min_le_left _ _)
      calc lamD m n d * l2sq (nprojPure d (ind S))
          ≤ 1 * l2sq (nprojPure d (ind S)) :=
            mul_le_mul_of_nonneg_right (lamD_le_one hdm') (l2sq_nonneg _)
        _ = l2sq (nprojPure d (ind S)) := one_mul _
        _ ≤ X * l2sq (ind S) := hlev d hdr
    have hcard : ((Finset.range (min m n + 1)).filter (fun d => d ≤ r + 1)).card ≤ r + 2 := by
      have hsub : (Finset.range (min m n + 1)).filter (fun d => d ≤ r + 1)
          ⊆ Finset.range (r + 2) := by
        intro d hd
        rw [Finset.mem_filter, Finset.mem_range] at hd
        rw [Finset.mem_range]
        omega
      simpa using Finset.card_le_card hsub
    calc (∑ d ∈ (Finset.range (min m n + 1)).filter (fun d => d ≤ r + 1),
          lamD m n d * l2sq (nprojPure d (ind S)))
        ≤ ∑ _d ∈ (Finset.range (min m n + 1)).filter (fun d => d ≤ r + 1),
            X * l2sq (ind S) := Finset.sum_le_sum hterm
      _ = (((Finset.range (min m n + 1)).filter (fun d => d ≤ r + 1)).card : ℝ) *
            (X * l2sq (ind S)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((r : ℝ) + 2) * (X * l2sq (ind S)) := by
          have hcast : (((Finset.range (min m n + 1)).filter (fun d => d ≤ r + 1)).card : ℝ) ≤
              ((r : ℝ) + 2) := by exact_mod_cast hcard
          exact mul_le_mul_of_nonneg_right hcast (by positivity)
      _ = ((2 : ℝ) ^ (r + 1))⁻¹ * l2sq (ind S) := by
          rw [hX]
          field_simp
  have htail : (∑ d ∈ (Finset.range (min m n + 1)).filter (fun d => ¬ d ≤ r + 1),
      lamD m n d * l2sq (nprojPure d (ind S))) < ((2 : ℝ) ^ (r + 1))⁻¹ * l2sq (ind S) := by
    have hset : (Finset.range (min m n + 1)).filter (fun d => ¬ d ≤ r + 1)
        = Finset.Icc (r + 2) (min m n) := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
      omega
    rw [hset]
    have hterm : ∀ d ∈ Finset.Icc (r + 2) (min m n),
        lamD m n d * l2sq (nprojPure d (ind S)) ≤ ((1 / 2 : ℝ) ^ d) * l2sq (ind S) := by
      intro d hd
      rw [Finset.mem_Icc] at hd
      have hdm : d ≤ m := le_trans hd.2 (min_le_left _ _)
      exact mul_le_mul (lamD_le_half hdm) (l2sq_nprojPure_le d (ind S))
        (l2sq_nonneg _) (by positivity)
    have hsum2 : (∑ d ∈ Finset.Icc (r + 2) (min m n), ((1 / 2 : ℝ) ^ d)) * l2sq (ind S)
        < ((2 : ℝ) ^ (r + 1))⁻¹ * l2sq (ind S) := by
      exact mul_lt_mul_of_pos_right
        (by simpa only [one_div, inv_pow] using
          Commons.Analysis.Inequalities.sum_Icc_pow_half_lt r (min m n)) hB
    exact lt_of_le_of_lt (by rw [Finset.sum_mul]; exact Finset.sum_le_sum hterm) hsum2
  have hdouble : ((2 : ℝ) ^ (r + 1))⁻¹ + ((2 : ℝ) ^ (r + 1))⁻¹ = ((2 : ℝ) ^ r)⁻¹ := by
    rw [pow_succ, mul_inv]
    field_simp
    norm_num
  have hfinal : (∑ d ∈ Finset.range (min m n + 1), lamD m n d * l2sq (nprojPure d (ind S)))
      < ((2 : ℝ) ^ (r + 1))⁻¹ * l2sq (ind S) + ((2 : ℝ) ^ (r + 1))⁻¹ * l2sq (ind S) := by
    linarith [hsplit, hhead, htail]
  calc (∑ d ∈ Finset.range (min m n + 1), lamD m n d * l2sq (nprojPure d (ind S)))
      < ((2 : ℝ) ^ (r + 1))⁻¹ * l2sq (ind S) + ((2 : ℝ) ^ (r + 1))⁻¹ * l2sq (ind S) := hfinal
    _ = ((2 : ℝ) ^ r)⁻¹ * l2sq (ind S) := by rw [← add_mul, hdouble]

/-! ## The concentration corollary in cube-root form -/

/-- **The concentration corollary in `ε^{1/3}` form**: a Boolean `(d,ε)`-restriction global
function has `‖f^{= d}‖₂² ≤ q^{C d²} ε^{1/3} ‖f‖₂²`. -/
theorem concentration_pow_third (H : HypCor4) :
    ∃ C' : ℕ, 0 < C' ∧ ∀ (m n d : ℕ) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) (ε : ℝ),
      0 ≤ ε → IsBoolBS f → GlobalBS d ε f →
        l2sq (nprojPure d f) ≤ (2 : ℝ) ^ (C' * d ^ 2) * ε ^ ((1 : ℝ) / 3) * l2sq f := by
  obtain ⟨K, hK, hconc⟩ := concentration_of_HypCor4 H
  refine ⟨K + 20, by omega, ?_⟩
  intro m n d f ε hε hbool hglob
  have hcube := hconc m n d f ε hε hbool hglob
  have h1 : l2sq (nprojPure d f) ≤ ((2 : ℝ) ^ (K * d ^ 2) * ε) ^ ((1 : ℝ) / 3) * l2sq f :=
    Commons.Analysis.Inequalities.le_rpow_third_mul (l2sq_nonneg _) (l2sq_nonneg _)
      (by positivity) hε hcube
  have h3 : ((2 : ℝ) ^ (K * d ^ 2)) ^ ((1 : ℝ) / 3) ≤ (2 : ℝ) ^ ((K + 20) * d ^ 2) := by
    rw [← Real.rpow_natCast (2 : ℝ) (K * d ^ 2),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_natCast (2 : ℝ) ((K + 20) * d ^ 2)]
    refine (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr ?_
    have hnat : (K + 20) * d ^ 2 = K * d ^ 2 + 20 * d ^ 2 := by ring
    rw [hnat]
    have hd2 : (0 : ℝ) ≤ (K : ℝ) * (d : ℝ) ^ 2 := by positivity
    push_cast
    nlinarith [hd2]
  calc l2sq (nprojPure d f)
      ≤ ((2 : ℝ) ^ (K * d ^ 2) * ε) ^ ((1 : ℝ) / 3) * l2sq f := h1
    _ = ((2 : ℝ) ^ (K * d ^ 2)) ^ ((1 : ℝ) / 3) * ε ^ ((1 : ℝ) / 3) * l2sq f := by
        rw [Real.mul_rpow (by positivity) hε]
    _ ≤ (2 : ℝ) ^ ((K + 20) * d ^ 2) * ε ^ ((1 : ℝ) / 3) * l2sq f := by
        refine mul_le_mul_of_nonneg_right ?_ (l2sq_nonneg f)
        exact mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg hε _)

/-! ## Theorem 1.6: small-set expansion in the shortcode graph -/

theorem sse_of_HypCor4 (H : HypCor4) :
    ∃ C₀ : ℕ, 0 < C₀ ∧ ∀ (m n r : ℕ), 1 ≤ r →
      ∀ S : Finset (Matrix (Fin m) (Fin n) 𝔽₂),
      GlobalBS (r + 1) (((2 : ℝ) ^ (C₀ * r ^ 2))⁻¹) (ind S) →
        sseNum S / ((S.card : ℝ) * rankOneCount m n) < ((2 : ℝ) ^ r)⁻¹ := by
  obtain ⟨C₀, hC₀, hsum⟩ := sse_sum_lt H
  refine ⟨C₀, hC₀, ?_⟩
  intro m n r hr S hglob
  by_cases hcard : S.card = 0
  · have h0 : (S.card : ℝ) = 0 := by exact_mod_cast hcard
    rw [h0, zero_mul, div_zero]
    positivity
  · have hpos : 0 < l2sq (ind S) := by
      rw [l2sq_ind]
      have hc : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hcard
      positivity
    have hlt := hsum m n r hr S hpos hglob
    by_cases hN : rankOneCount m n = 0
    · rw [hN, mul_zero, div_zero]
      positivity
    · have hratio : sseNum S / ((S.card : ℝ) * rankOneCount m n)
          = (∑ d ∈ Finset.range (min m n + 1),
              lamD m n d * l2sq (nprojPure d (ind S))) / l2sq (ind S) := by
        rw [spectral_expansion_ind S, l2sq_ind]
        field_simp
      rw [hratio, div_lt_iff₀ hpos]
      exact hlt

/-- **Theorem 1.6 of arXiv:2209.04243** (small-set expansion in the shortcode graph), derived
from the corollary of hypercontractivity `HypCor4`. -/
theorem hypSSE_of_HypCor4 (H : HypCor4) : HypSSE := by
  obtain ⟨C₀, hC₀, h⟩ := sse_of_HypCor4 H
  refine ⟨(C₀ : ℝ), by exact_mod_cast hC₀, ?_⟩
  intro m n r hr S hglob
  have hexp : (C₀ : ℝ) * (↑r : ℝ) ^ 2 = ↑(C₀ * r ^ 2) := by push_cast; ring
  have hpow : (2 : ℝ) ^ (-((C₀ : ℝ) * (↑r : ℝ) ^ 2)) = ((2 : ℝ) ^ (C₀ * r ^ 2))⁻¹ := by
    rw [show -((C₀ : ℝ) * (↑r : ℝ) ^ 2) = -(↑(C₀ * r ^ 2) : ℝ) from by rw [hexp],
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
  have hglob' : GlobalBS (r + 1) (((2 : ℝ) ^ (C₀ * r ^ 2))⁻¹) (ind S) := by
    rw [hpow] at hglob
    exact hglob
  have hmain := h m n r hr S hglob'
  rwa [sseNum_eq_sum, rankOneCount_eq_sum] at hmain

end

end Submission.Grassmann
