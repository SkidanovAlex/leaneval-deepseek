/-
# Uniform ellipticity of the *inverse* metric (`Work.Diff.STE.flat.elliptic_inv`)

The principal part of the flat DeTurck operator is
`secOpFlat A B |_{ij} = Σ_{cd} (reMat A)⁻¹_{cd} B_{cd,ij}`, and Clairaut's theorem
(`∂_c∂_d u = ∂_d∂_c u`) lets one replace the inverse metric by its symmetric part
`symInvR c a b x = (((reMat (seriesFunM c x))⁻¹) a b + ((reMat (seriesFunM c x))⁻¹) b a) / 2`
(see `Submission/Work/Diff/STE/flat/level_defs.lean`).  Gårding's inequality then requires a
**uniform lower bound** for the quadratic form of that symmetrised inverse: a single constant
`lam' > 0` working for *every* Galerkin truncation `N` and *every* box-supported coefficient family
`c` whose level-`s` energy is bounded by `Bs²` and whose real part is uniformly elliptic with
constant `lam > 0`.  That is the content of this file.

## Mathematics

Two elementary facts about a real `n × n` matrix `A` with `vᵀAv ≥ lam |v|²` for all `v` (`lam > 0`)
and `|A_{ij}| ≤ β`:

1. `A` is invertible (`det_ne_zero_of_elliptic`, from `level_aux.lean`), and for `u := A⁻¹ ξ` one has
   the **identity** `ξᵀA⁻¹ξ = uᵀAu`: indeed `A·u = ξ`, so
   `ξᵀA⁻¹ξ = (Au)ᵀA⁻¹(Au) = uᵀAᵀu = uᵀAu` (a transpose is invisible in a quadratic form).
   Hence `ξᵀ A⁻¹ ξ ≥ lam |u|²` by the ellipticity hypothesis applied to `u`.
2. The entry bound `|A_{ij}| ≤ β` gives, by Cauchy–Schwarz, `|ξ| = |Au| ≤ nβ|u|`, i.e.
   `|u| ≥ |ξ|/(nβ+1)`.

Combining, `ξᵀ sym(A⁻¹) ξ = ξᵀA⁻¹ξ ≥ (lam/(nβ+1)²) |ξ|²` — the symmetrisation is invisible on a
quadratic form, since `ξᵀ(A⁻¹)ᵀξ = ξᵀA⁻¹ξ`.

The entry bound `β` for `A = reMat (seriesFunM c x)` is supplied, uniformly in `N` and `c`, by the
elementary Sobolev/Agmon bound `seriesFunM_entry_sup_uniform` below (`ℓ¹ ≤ √(weighted ℓ²)` for a
Fourier series, `L²`-Parseval to compare the weighted `ℓ²` norm with the energy, and monotonicity of
`CSq` in the level): the level-`s` energy hypothesis `ENormSqFull s (seriesFunM c) ≤ Bs²` bounds the
entries by a constant times `1 + Bs`, where `s ≥ n + 5` ensures `sob n = n/2 + 1 ≤ s` (the Sobolev
level needed for the sup bound).
-/

import Mathlib
import Submission.Work.Diff.STE.FlatPDE
import Submission.Work.Diff.STE.flat.level_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1000000

open MeasureTheory BigOperators

namespace Work.Diff.STE.flat

open Work.Diff.STE.Flat

noncomputable section

variable {n : ℕ}

/-! ## Quadratic-form manipulations -/

/-- **Symmetrising a quadratic form.**  Averaging a matrix with its transpose does not change its
quadratic form, since `ξᵢξⱼ` is symmetric in `(i,j)`.  (The real-matrix version of `sum_swap_half`
of `level_defs.lean`, with the extra factor `ξᵢξⱼ`.) -/
lemma quadForm_symm {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) (ξ : Fin n → ℝ) :
    (∑ i, ∑ j, ((X i j + X j i) / 2) * ξ i * ξ j) = ∑ i, ∑ j, X i j * ξ i * ξ j := by
  have hswap : (∑ i, ∑ j, X j i * ξ i * ξ j) = ∑ i, ∑ j, X i j * ξ i * ξ j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hpoint : ∀ i j : Fin n, ((X i j + X j i) / 2) * ξ i * ξ j
      = (X i j * ξ i * ξ j) / 2 + (X j i * ξ i * ξ j) / 2 := fun i j => by ring
  have hsplit : (∑ i, ∑ j, ((X i j + X j i) / 2) * ξ i * ξ j)
      = (∑ i, ∑ j, X i j * ξ i * ξ j) / 2 + (∑ i, ∑ j, X j i * ξ i * ξ j) / 2 := by
    simp only [hpoint]
    simp only [Finset.sum_add_distrib, Finset.sum_div]
  rw [hsplit, hswap]
  ring

/-- **The quantitative inverse-ellipticity estimate.**  Let `A` be a real `n × n` matrix which is
invertible, elliptic with constant `lam > 0`, and whose entries are bounded by `β ≥ 0`.  Then the
quadratic form of the *symmetrised inverse* is bounded below by `lam / (nβ + 1)²`.

The constant `nβ + 1` is the (crude, but manifestly positive) bound for the operator norm of `A`
coming from the entry bound; `nβ + 1` rather than `nβ` so that it stays positive even when
`β = 0` (in which case `A = 0`, and the ellipticity hypothesis with `lam > 0` is inconsistent). -/
lemma inv_quadForm_lower {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {lam β : ℝ}
    (hlam : 0 < lam) (hβ : 0 ≤ β) (hdet : A.det ≠ 0)
    (hlo : ∀ v : Fin n → ℝ, lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j, A i j * v i * v j)
    (hab : ∀ i j, |A i j| ≤ β) :
    ∀ ξ : Fin n → ℝ,
      (lam / ((n : ℝ) * β + 1) ^ 2) * ∑ i, (ξ i) ^ 2
        ≤ ∑ i, ∑ j, ((A⁻¹) i j + (A⁻¹) j i) / 2 * ξ i * ξ j := by
  intro ξ
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hdet
  have hAA : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hunit
  set u : Fin n → ℝ := A⁻¹.mulVec ξ with hu
  have hu_apply : ∀ i, u i = ∑ j, (A⁻¹) i j * ξ j := by
    intro i; rw [hu]; simp [Matrix.mulVec, dotProduct]
  have hξu : A.mulVec u = ξ := by
    rw [hu, Matrix.mulVec_mulVec, hAA, Matrix.one_mulVec]
  have hrow : ∀ i, A.mulVec u i = ∑ j, A i j * u j := fun i => by
    simp [Matrix.mulVec, dotProduct]
  -- the identity `ξᵀA⁻¹ξ = uᵀAu`
  have key : (∑ i, ∑ j, (A⁻¹) i j * ξ i * ξ j) = ∑ i, ∑ j, A i j * u i * u j := by
    have h1 : (∑ i, ∑ j, (A⁻¹) i j * ξ i * ξ j) = ∑ i, ξ i * u i := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hu_apply i, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    have h2 : (∑ i, ξ i * u i) = ∑ i, ∑ j, A i j * u i * u j := by
      rw [← hξu]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hrow i, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    exact h1.trans h2
  -- the norm comparison `|ξ| ≤ (nβ+1)|u|`
  have hξsq : (∑ i, (ξ i) ^ 2) ≤ (((n : ℝ) * β + 1) ^ 2) * ∑ i, (u i) ^ 2 := by
    have hSnn : 0 ≤ ∑ i, (u i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hrow_bound : ∀ i, (∑ j, (A i j) ^ 2) ≤ (n : ℝ) * β ^ 2 := by
      intro i
      calc (∑ j, (A i j) ^ 2) ≤ ∑ _j : Fin n, β ^ 2 :=
            Finset.sum_le_sum fun j _ => by
              have h2 := pow_le_pow_left₀ (abs_nonneg (A i j)) (hab i j) 2
              rwa [sq_abs] at h2
        _ = (n : ℝ) * β ^ 2 := by simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hterm : ∀ i, (ξ i) ^ 2 ≤ ((n : ℝ) * β ^ 2) * ∑ j, (u j) ^ 2 := by
      intro i
      have hξi : ξ i = ∑ j, A i j * u j := by
        rw [← hrow i]; exact (congrFun hξu i).symm
      rw [hξi]
      calc (∑ j, A i j * u j) ^ 2
          ≤ (∑ j, (A i j) ^ 2) * ∑ j, (u j) ^ 2 := by
            have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n))
              (fun j => A i j) (fun j => u j)
            simpa using h
        _ ≤ ((n : ℝ) * β ^ 2) * ∑ j, (u j) ^ 2 :=
            mul_le_mul_of_nonneg_right (hrow_bound i) hSnn
    calc (∑ i, (ξ i) ^ 2) ≤ ∑ _i : Fin n, ((n : ℝ) * β ^ 2) * ∑ j, (u j) ^ 2 :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = (n : ℝ) * (((n : ℝ) * β ^ 2) * ∑ j, (u j) ^ 2) := by
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = (((n : ℝ) * β) ^ 2) * ∑ j, (u j) ^ 2 := by ring
      _ ≤ (((n : ℝ) * β + 1) ^ 2) * ∑ j, (u j) ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ hSnn
          nlinarith [sq_nonneg ((n : ℝ) * β), hβ, (by positivity : (0 : ℝ) ≤ (n : ℝ))]
  have hdiv : (∑ i, (ξ i) ^ 2) / ((n : ℝ) * β + 1) ^ 2 ≤ ∑ i, (u i) ^ 2 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < ((n : ℝ) * β + 1) ^ 2)]
    calc (∑ i, (ξ i) ^ 2) ≤ (((n : ℝ) * β + 1) ^ 2) * ∑ i, (u i) ^ 2 := hξsq
      _ = (∑ i, (u i) ^ 2) * (((n : ℝ) * β + 1) ^ 2) := by ring
  calc (lam / ((n : ℝ) * β + 1) ^ 2) * ∑ i, (ξ i) ^ 2
      = lam * ((∑ i, (ξ i) ^ 2) / ((n : ℝ) * β + 1) ^ 2) := by ring
    _ ≤ lam * ∑ i, (u i) ^ 2 := mul_le_mul_of_nonneg_left hdiv (le_of_lt hlam)
    _ ≤ ∑ i, ∑ j, A i j * u i * u j := hlo u
    _ = ∑ i, ∑ j, (A⁻¹) i j * ξ i * ξ j := key.symm
    _ = ∑ i, ∑ j, ((A⁻¹) i j + (A⁻¹) j i) / 2 * ξ i * ξ j := (quadForm_symm (A⁻¹) ξ).symm

/-! ## The uniform entry bound -/

/-- **Uniform sup bound for the entries of `seriesFunM c`.**  For a box-supported coefficient family
whose level-`s` energy is finite (`sob n ≤ s`), each entry of `seriesFunM c x` is bounded, uniformly
in the truncation `N`, in `c` and in `x`, by a constant times `1 + √(ENormSqFull s (seriesFunM c))`.

Route: `norm_seriesFun_le` (the `ℓ¹ ≤ √(weighted ℓ²)` Sobolev step for a single entry series),
`CSq ≤ C (ENormSq s + ENormSq 0)` (`CSq_le_ENormSq_seriesFun`) converting the weighted coefficient
norm into the physical energy, and the monotonicity of `CSq` in the level, `CSq (sob n) ≤ CSq s`. -/
lemma seriesFunM_entry_sup_uniform {n s : ℕ} (hσ : sob n ≤ s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (c : (Fin n → ℤ) → MatC n),
      (∀ k : Fin n → ℤ, k ∉ box n N → c k = 0) → ∀ (i j : Fin n) (x : Fin n → ℝ),
      ‖seriesFunM c x i j‖
        ≤ C * (1 + Real.sqrt (ENormSqFull s (seriesFunM c))) := by
  obtain ⟨C0, hC0, h0⟩ := norm_seriesFun_le (ι := Fin n) (sob n) (by simpa using n_lt_two_sob n)
  obtain ⟨C2, hC2, h2⟩ := CSq_le_ENormSq_seriesFun (ι := Fin n) s
  refine ⟨C0 * Real.sqrt C2, by positivity, fun N c hc i j x => ?_⟩
  have hmom : ∀ M : ℕ, Summable (fun k : Fin n → ℤ => (wt k) ^ M * ‖c k i j‖) :=
    fun M => summable_moment_box c hc i j M
  have hsumm : ∀ M : ℕ, Summable (fun k : Fin n → ℤ => (wt k) ^ M *
      ‖(fun k : Fin n → ℤ => c k i j) k‖) := hmom
  have hfun : (fun y : Fin n → ℝ => seriesFunM c y i j)
      = seriesFun (fun k : Fin n → ℤ => c k i j) := by funext y; rw [seriesFunM_apply]
  have hstep : ‖seriesFunM c x i j‖
      ≤ C0 * Real.sqrt (CSq (sob n) (fun k : Fin n → ℤ => c k i j)) := by
    rw [seriesFunM_apply]
    exact h0 (fun k => c k i j) (summable_wt_pow_mul_norm_sq _ hmom (sob n)) x
  have hmono : CSq (sob n) (fun k : Fin n → ℤ => c k i j)
      ≤ CSq s (fun k : Fin n → ℤ => c k i j) := by
    rw [CSq, CSq]
    refine Summable.tsum_le_tsum (fun k => ?_) (summable_wt_pow_mul_norm_sq _ hsumm (sob n))
      (summable_wt_pow_mul_norm_sq _ hsumm s)
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (wt_one_le k) hσ) (sq_nonneg _)
  have h4 : CSq s (fun k : Fin n → ℤ => c k i j) ≤ C2 * ENormSqFull s (seriesFunM c) := by
    have h := h2 (fun k => c k i j) hsumm
    have hEs : ENormSq s (seriesFun (fun k : Fin n → ℤ => c k i j))
        ≤ ENormSqM s (seriesFunM c) := by
      have hh := ENormSq_le_ENormSqM (j := s) (seriesFunM c) i j
      rwa [hfun] at hh
    have hE0 : ENormSq 0 (seriesFun (fun k : Fin n → ℤ => c k i j))
        ≤ ENormSqM 0 (seriesFunM c) := by
      have hh := ENormSq_le_ENormSqM (j := 0) (seriesFunM c) i j
      rwa [hfun] at hh
    refine h.trans ?_
    rw [ENormSqFull]
    exact mul_le_mul_of_nonneg_left (add_le_add hEs hE0) hC2
  calc ‖seriesFunM c x i j‖
      ≤ C0 * Real.sqrt (CSq (sob n) (fun k : Fin n → ℤ => c k i j)) := hstep
    _ ≤ C0 * Real.sqrt (CSq s (fun k : Fin n → ℤ => c k i j)) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmono) hC0
    _ ≤ C0 * Real.sqrt (C2 * ENormSqFull s (seriesFunM c)) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h4) hC0
    _ = C0 * Real.sqrt C2 * Real.sqrt (ENormSqFull s (seriesFunM c)) := by
        rw [Real.sqrt_mul hC2]; ring
    _ ≤ C0 * Real.sqrt C2 * (1 + Real.sqrt (ENormSqFull s (seriesFunM c))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith [Real.sqrt_nonneg (ENormSqFull s (seriesFunM c))]

/-! ## The target -/

theorem elliptic_inv {n s : ℕ} (hn : 1 ≤ n) (hs : n + 5 ≤ s)
    (lam : ℝ) (hlam : 0 < lam) (Bs : ℝ) (hBs : 0 ≤ Bs) :
    ∃ lam' : ℝ, 0 < lam' ∧ ∀ (N : ℕ) (c : (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n),
      (∀ k : Fin n → ℤ, k ∉ Work.Diff.STE.Flat.box n N → c k = 0) →
      Work.Diff.STE.Flat.ENormSqFull s (Work.Diff.STE.Flat.seriesFunM c) ≤ Bs ^ 2 →
      (∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
        lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
          Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM c x) i j * v i * v j) →
      ∀ (x : Fin n → ℝ) (ξ : Fin n → ℝ),
        lam' * ∑ i, (ξ i) ^ 2 ≤ ∑ i, ∑ j,
          ((((Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM c x))⁻¹) i j
            + ((Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM c x))⁻¹) j i) / 2)
            * ξ i * ξ j := by
  have hσ : sob n ≤ s := by
    simp only [sob]
    omega
  obtain ⟨Cs, hCs, hCs'⟩ := seriesFunM_entry_sup_uniform (n := n) (s := s) hσ
  refine ⟨lam / (((n : ℝ) * (Cs * (1 + Bs)) + 1) ^ 2), by positivity, ?_⟩
  intro N c hc hE hell x ξ
  have hsqrt : Real.sqrt (ENormSqFull s (seriesFunM c)) ≤ Bs := by
    rw [← Real.sqrt_sq hBs]
    exact Real.sqrt_le_sqrt hE
  have hab : ∀ i j : Fin n, |reMat (seriesFunM c x) i j| ≤ Cs * (1 + Bs) := by
    intro i j
    calc |reMat (seriesFunM c x) i j| = |(seriesFunM c x i j).re| := rfl
      _ ≤ ‖seriesFunM c x i j‖ := Complex.abs_re_le_norm _
      _ ≤ Cs * (1 + Real.sqrt (ENormSqFull s (seriesFunM c))) := hCs' N c hc i j x
      _ ≤ Cs * (1 + Bs) := by
          refine mul_le_mul_of_nonneg_left ?_ hCs
          linarith
  have hβ : 0 ≤ Cs * (1 + Bs) := by positivity
  have hdet : (reMat (seriesFunM c x)).det ≠ 0 :=
    det_ne_zero_of_elliptic (seriesFunM c x) hlam (hell x)
  exact inv_quadForm_lower (n := n) (A := reMat (seriesFunM c x)) (β := Cs * (1 + Bs))
    hlam hβ hdet (fun v => hell x v) hab ξ

end

end Work.Diff.STE.flat
