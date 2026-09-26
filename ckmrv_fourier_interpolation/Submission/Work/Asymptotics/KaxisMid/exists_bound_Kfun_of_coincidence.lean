/-
# Uniform bounds for the CKMRV kernel at the coincidences `j τ = j z`

The kernel `K^{(d)}` of CKMRV (Cohn--Kumar--Miller--Radchenko--Viazovska, Ann. of Math. 196
(2022), Theorem 4.9) is a meromorphic function of `(τ,z)` with simple poles exactly on the
coincidence set `j τ = j z`.  In the formalisation (`Work.Kernels.Kfun`) the values at the
poles are however *finite*: the convention `0⁻¹ = 0` of a field evaluates every occurring
reciprocal of a vanishing quantity to `0`.  This file bounds those values.

Concretely, if `j τ = j z`, then

* `UpsilonMinus d τ z = 0` for `d = 8` and `d = 24`, and `UpsilonPlus 8 τ z = 0`, because the
  outer factor of both coefficient matrices is `(… · (j τ - j z))⁻¹`;
* `UpsilonPlus 24 τ z` is the explicit matrix obtained from the formula of Section 4.4 by
  putting `(j τ - j z)⁻¹ = 0`, namely `Π_{14,12,10}(τ) · M · Π_{4,2,0}(z)` with the constant
  matrix `M` of `Mpos24` below,

so at a coincidence `K^{(8)} = 0` and `K^{(24)} = K^{(24)}_+/2` is an explicit polynomial
expression in `Δ, E₄, E₆, E₁₀, E₁₄, j, φ⃗, φ̃⃗` evaluated on the compact sets `S`, `T`.  All of
these are bounded there (`Δ` is bounded away from `0` because it has no zeros), whence the
uniform bound.

The metric statements are all about the `ℝ`-valued norm on `ℍ ⊆ ℂ`; no hyperbolic metric is
used.
-/
import Mathlib
import Submission.Work.Asymptotics.KaxisMid.Basic
import Submission.Work.Asymptotics.KaxisMid.exists_bound_fk
import Submission.Work.Asymptotics.KaxisMid.exists_bound_phiVec_phitVec

noncomputable section

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

namespace Work.Asymptotics.KaxisMid

open Work.Kernels

/-! ## The coefficient matrices at a coincidence -/

/-- The constant matrix `M` of `Υ_+^{(24)}` at a coincidence: the entries
`1728 (j τ - j z)⁻¹`, resp. `-2·1728 (j τ - j z)⁻¹`, of the third resp. second row are `0`
there. -/
def Mpos24 (jτ : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![6, 0, -6; -12 * jτ + 5 * c1728, 0, 12 * jτ - 7 * c1728; 6, 0, -6]

/-- Every entry of `Mpos24` is bounded by `12 ‖jτ‖ + 12096 = 12 ‖jτ‖ + 7·1728`. -/
lemma norm_Mpos24_le (jτ : ℂ) (i j : Fin 3) : ‖Mpos24 jτ i j‖ ≤ 12 * ‖jτ‖ + 12096 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [Mpos24, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val, c1728]
  · linarith [norm_nonneg jτ]
  · linarith [norm_nonneg jτ]
  · linarith [norm_nonneg jτ]
  · calc ‖-(12 * jτ) + (8640 : ℂ)‖ ≤ ‖-(12 * jτ)‖ + ‖(8640 : ℂ)‖ := norm_add_le _ _
      _ = 12 * ‖jτ‖ + 8640 := by rw [norm_neg, norm_mul]; norm_num
      _ ≤ 12 * ‖jτ‖ + 12096 := by linarith
  · linarith [norm_nonneg jτ]
  · calc ‖(12 : ℂ) * jτ - 12096‖ ≤ ‖(12 : ℂ) * jτ‖ + ‖(12096 : ℂ)‖ := norm_sub_le _ _
      _ = 12 * ‖jτ‖ + 12096 := by rw [norm_mul]; norm_num
  · linarith [norm_nonneg jτ]
  · linarith [norm_nonneg jτ]
  · linarith [norm_nonneg jτ]

/-- `Υ_-^{(d)}` vanishes at a coincidence `j τ = j z`, for both `d = 8` and `d = 24`: its
outer factor is `(c · (j τ - j z))⁻¹`. -/
lemma UpsilonMinus_eq_zero_of_coincidence {d : ℕ} (hd : d = 8 ∨ d = 24) {τ z : ℍ}
    (h : jInvariantFun τ = jInvariantFun z) : UpsilonMinus d τ z = 0 := by
  rcases hd with rfl | rfl
  · simp only [UpsilonMinus, h, sub_self, mul_zero, _root_.inv_zero, PiMat, if_true,
      zero_smul]
  · simp only [UpsilonMinus, h, sub_self, mul_zero, _root_.inv_zero, PiMat]
    split_ifs with h1
    · exact absurd h1 (by norm_num)
    · simp only [zero_smul]

/-- `Υ_+^{(8)}` vanishes at a coincidence `j τ = j z`. -/
lemma UpsilonPlus_eight_eq_zero {τ z : ℍ} (h : jInvariantFun τ = jInvariantFun z) :
    UpsilonPlus 8 τ z = 0 := by
  simp only [UpsilonPlus, h, sub_self, mul_zero, _root_.inv_zero, PiMat]
  split_ifs with h1
  · simp only [if_true, zero_smul]
  · exact absurd h1 (by norm_num)

/-- `K_-^{(d)}` vanishes at a coincidence, for both `d = 8` and `d = 24`. -/
lemma KMinus_eq_zero_of_coincidence (ℓ : LogLambdaData) {d : ℕ} (hd : d = 8 ∨ d = 24)
    {τ z : ℍ} (h : jInvariantFun τ = jInvariantFun z) : KMinus ℓ d τ z = 0 := by
  simp only [KMinus, UpsilonMinus_eq_zero_of_coincidence hd h, Matrix.zero_apply, mul_zero,
    zero_mul, Finset.sum_const_zero]

/-- `K_+^{(8)}` vanishes at a coincidence. -/
lemma KPlus_eight_eq_zero {τ z : ℍ} (h : jInvariantFun τ = jInvariantFun z) :
    KPlus 8 τ z = 0 := by
  simp only [KPlus, UpsilonPlus_eight_eq_zero h, Matrix.zero_apply, mul_zero, zero_mul,
    Finset.sum_const_zero]

/-- The `(i,j)` entry of `Υ_+^{(24)}` at a coincidence: the whole `(j τ - j z)⁻¹` dependence
is confined to the constant matrix `Mpos24`. -/
lemma UpsilonPlus24_entry_of_coincidence (τ z : ℍ) (h : jInvariantFun τ = jInvariantFun z)
    (i j : Fin 3) :
    UpsilonPlus 24 τ z i j =
      ((36 : ℂ) * c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I * DeltaFun z)⁻¹ *
        fk (![14, 12, 10] i) τ * Mpos24 (jInvariantFun τ) i j * fk (![4, 2, 0] j) z := by
  simp only [UpsilonPlus, h, sub_self, _root_.inv_zero, mul_zero, PiMat, Mpos24]
  split_ifs with h1
  · exact absurd h1 (by norm_num)
  · simp only [Matrix.smul_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.of_apply]
    ring_nf

/-! ## Bounds on the building blocks over compact sets -/

/-- A continuous complex-valued function is bounded by a positive constant on a compact set. -/
lemma exists_bound_of_compact {K : Set ℍ} (hK : IsCompact K) {f : ℍ → ℂ} (hf : Continuous f) :
    ∃ B : ℝ, 0 < B ∧ ∀ z ∈ K, ‖f z‖ ≤ B := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  exact ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
    fun z hz => le_trans (hC z hz) (le_max_left _ _)⟩

lemma continuous_jInvariantFun : Continuous (fun τ : ℍ => jInvariantFun τ) := by
  have h4 : Continuous (fun τ : ℍ => E4Fun τ) := ClassicalFacts.E4Fun_mem_InP.1.continuous
  have hΔ : Continuous (fun τ : ℍ => DeltaFun τ) := ClassicalFacts.DeltaFun_mem_InP.1.continuous
  have h : jInvariantFun = fun τ : ℍ => E4Fun τ ^ 3 / DeltaFun τ := by funext τ; rfl
  rw [h]
  exact (h4.pow 3).div hΔ (fun τ => ClassicalFacts.DeltaFun_ne_zero τ)

/-- `j` is bounded on compact subsets of `ℍ`. -/
lemma exists_bound_jInvariantFun {S : Set ℍ} (hS : IsCompact S) :
    ∃ J : ℝ, 0 < J ∧ ∀ τ ∈ S, ‖jInvariantFun τ‖ ≤ J :=
  exists_bound_of_compact hS continuous_jInvariantFun

/-- `‖Δ⁻¹‖` is bounded on compact subsets of `ℍ`, since `Δ` has no zeros. -/
lemma exists_bound_DeltaFun_inv {T : Set ℍ} (hT : IsCompact T) :
    ∃ D : ℝ, 0 < D ∧ ∀ z ∈ T, ‖(DeltaFun z)⁻¹‖ ≤ D := by
  obtain ⟨δ, hδpos, hδ⟩ := exists_lower_DeltaFun hT
  refine ⟨max (δ⁻¹) 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun z hz => ?_⟩
  have h1 : ‖(DeltaFun z)⁻¹‖ ≤ δ⁻¹ := by
    rw [norm_inv]
    exact inv_anti₀ hδpos (hδ z hz)
  exact le_trans h1 (le_max_left _ _)

/-- The reciprocal of the constant factor `c = 36 · 1728 · π^{-2} i Δ` of `Υ_+^{(24)}` is
bounded on compact subsets of `ℍ`. -/
lemma exists_bound_cinv {T : Set ℍ} (hT : IsCompact T) :
    ∃ D : ℝ, 0 < D ∧ ∀ z ∈ T,
      ‖((36 : ℂ) * c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I * DeltaFun z)⁻¹‖ ≤ D := by
  obtain ⟨D₀, hD₀pos, hD₀⟩ := exists_bound_DeltaFun_inv hT
  refine ⟨(‖((36 : ℂ) * c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)⁻¹‖ + 1) * (D₀ + 1),
    by positivity, fun z hz => ?_⟩
  rw [show ((36 : ℂ) * c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I * DeltaFun z)⁻¹
      = ((36 : ℂ) * c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)⁻¹ * (DeltaFun z)⁻¹ from by
    rw [_root_.mul_inv_rev, _root_.mul_inv_rev, _root_.mul_inv_rev, _root_.mul_inv_rev]
    ring]
  rw [norm_mul]
  refine mul_le_mul (by linarith) ?_ (norm_nonneg _) (by positivity)
  linarith [hD₀ z hz]

/-- The `τ`-blocks `f_{14}, f_{12}, f_{10} = E₁₄, Δ, E₁₀` of `Υ_+^{(24)}` are bounded on a
compact set. -/
lemma exists_bound_fk_S {S : Set ℍ} (hS : IsCompact S) :
    ∃ K : ℝ, 0 < K ∧ ∀ τ ∈ S, ∀ i : Fin 3, ‖fk (![14, 12, 10] i) τ‖ ≤ K := by
  obtain ⟨K₁, h₁pos, h₁⟩ := exists_bound_fk S hS (14 : ℤ)
  obtain ⟨K₂, h₂pos, h₂⟩ := exists_bound_fk S hS (12 : ℤ)
  obtain ⟨K₃, h₃pos, h₃⟩ := exists_bound_fk S hS (10 : ℤ)
  refine ⟨max (max K₁ K₂) K₃,
    lt_of_lt_of_le h₁pos (le_trans (le_max_left K₁ K₂) (le_max_left (max K₁ K₂) K₃)),
    fun τ hτ i => ?_⟩
  fin_cases i <;>
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val]
  · exact le_trans (h₁ τ hτ) (le_trans (le_max_left _ _) (le_max_left _ _))
  · exact le_trans (h₂ τ hτ) (le_trans (le_max_right _ _) (le_max_left _ _))
  · exact le_trans (h₃ τ hτ) (le_max_right _ _)

/-- The `z`-blocks `f_4, f_2, f_0 = E₄, E₁₄/Δ, 1` of `Υ_+^{(24)}` are bounded on a compact
set. -/
lemma exists_bound_fk_T {T : Set ℍ} (hT : IsCompact T) :
    ∃ K : ℝ, 0 < K ∧ ∀ z ∈ T, ∀ j : Fin 3, ‖fk (![4, 2, 0] j) z‖ ≤ K := by
  obtain ⟨K₁, h₁pos, h₁⟩ := exists_bound_fk T hT (4 : ℤ)
  obtain ⟨K₂, h₂pos, h₂⟩ := exists_bound_fk T hT (2 : ℤ)
  obtain ⟨K₃, h₃pos, h₃⟩ := exists_bound_fk T hT (0 : ℤ)
  refine ⟨max (max K₁ K₂) K₃,
    lt_of_lt_of_le h₁pos (le_trans (le_max_left K₁ K₂) (le_max_left (max K₁ K₂) K₃)),
    fun z hz j => ?_⟩
  fin_cases j <;>
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val]
  · exact le_trans (h₁ z hz) (le_trans (le_max_left _ _) (le_max_left _ _))
  · exact le_trans (h₂ z hz) (le_trans (le_max_right _ _) (le_max_left _ _))
  · exact le_trans (h₃ z hz) (le_max_right _ _)

/-! ## Elementary norm estimates -/

/-- The norm of the double sum over `Fin 3 × Fin 3` is at most `9 B` if every term is bounded
by `B`. -/
lemma norm_sum_Fin3_Fin3_le {f : Fin 3 → Fin 3 → ℂ} {B : ℝ} (h : ∀ i j, ‖f i j‖ ≤ B) :
    ‖∑ i : Fin 3, ∑ j : Fin 3, f i j‖ ≤ 9 * B := by
  calc ‖∑ i : Fin 3, ∑ j : Fin 3, f i j‖ ≤ ∑ i : Fin 3, ‖∑ j : Fin 3, f i j‖ :=
        norm_sum_le _ _
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, ‖f i j‖ :=
        Finset.sum_le_sum fun i _ => norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, B :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h i j
    _ = 9 * B := by simp only [Fin.sum_univ_three]; ring

/-- A four-factor product estimate. -/
lemma norm_mul_four_le {a b c d : ℂ} {A B C D : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B) (hc : ‖c‖ ≤ C) (hd : ‖d‖ ≤ D) :
    ‖a * b * c * d‖ ≤ A * B * C * D := by
  rw [norm_mul, norm_mul, norm_mul]
  exact mul_le_mul (mul_le_mul (mul_le_mul ha hb (norm_nonneg _) hA) hc (norm_nonneg _)
    (mul_nonneg hA hB)) hd (norm_nonneg _) (mul_nonneg (mul_nonneg hA hB) hC)

/-! ## The uniform bound at the coincidences -/

/-- **Uniform bound for the CKMRV kernel at the coincidences `j τ = j z`.**  `Kfun` is defined
with the convention `0⁻¹ = 0`, so at a coincidence the value is evaluated with `(j τ - j z)⁻¹ = 0`;
it is finite and bounded on compact parameter sets by an explicit constant (depending only on `ℓ`,
`d`, and bounds for `Δ`, `j`, the bases `φ, φ̃, ψ, ψ̃` and the `f_k` on `S × T`). -/
theorem exists_bound_Kfun_of_coincidence (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) {S T : Set UpperHalfPlane} (hS : IsCompact S) (hT : IsCompact T) :
    ∃ C : ℝ, 0 < C ∧ ∀ (τ z : UpperHalfPlane), τ ∈ S → z ∈ T →
      Work.Kernels.jInvariantFun τ = Work.Kernels.jInvariantFun z →
      ‖Work.Kernels.Kfun ℓ d τ z‖ ≤ C := by
  rcases hd with rfl | rfl
  · refine ⟨1, one_pos, fun τ z _ _ hc => ?_⟩
    rw [Kfun, KPlus_eight_eq_zero hc, KMinus_eq_zero_of_coincidence ℓ (Or.inl rfl) hc,
      add_zero, zero_div, norm_zero]
    exact zero_le_one
  · obtain ⟨P, hPpos, hP⟩ := exists_bound_phiVec_phitVec hS hT |>.1
    obtain ⟨Q, hQpos, hQ⟩ := exists_bound_phiVec_phitVec hS hT |>.2
    obtain ⟨Kτ, hKτpos, hKτ⟩ := exists_bound_fk_S hS
    obtain ⟨Kz, hKzpos, hKz⟩ := exists_bound_fk_T hT
    obtain ⟨Dinv, hDinvpos, hDinv⟩ := exists_bound_cinv hT
    obtain ⟨Jb, hJbpos, hJb⟩ := exists_bound_jInvariantFun hS
    have hBM : 0 ≤ 12 * Jb + 12096 := by positivity
    have hUpos : 0 < Dinv * Kτ * (12 * Jb + 12096) * Kz := by positivity
    refine ⟨max 1 (9 * (P * (Dinv * Kτ * (12 * Jb + 12096) * Kz) * Q)),
      lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun τ z hτ hz hc => ?_⟩
    have hUb : ∀ i j : Fin 3, ‖UpsilonPlus 24 τ z i j‖
        ≤ Dinv * Kτ * (12 * Jb + 12096) * Kz := by
      intro i j
      rw [UpsilonPlus24_entry_of_coincidence τ z hc i j]
      refine norm_mul_four_le hDinvpos.le hKτpos.le hBM (hDinv z hz)
        (hKτ τ hτ i) ?_ (hKz z hz j)
      exact le_trans (norm_Mpos24_le _ i j) (by linarith [hJb τ hτ])
    have hterm : ∀ i j : Fin 3,
        ‖phiVec τ i * UpsilonPlus 24 τ z i j * phitVec z j‖
          ≤ P * (Dinv * Kτ * (12 * Jb + 12096) * Kz) * Q := by
      intro i j
      rw [norm_mul, norm_mul]
      exact mul_le_mul (mul_le_mul (hP τ hτ i) (hUb i j) (norm_nonneg _) hPpos.le)
        (hQ z hz j) (norm_nonneg _) (mul_nonneg hPpos.le hUpos.le)
    have hKPlus : ‖KPlus 24 τ z‖
        ≤ 9 * (P * (Dinv * Kτ * (12 * Jb + 12096) * Kz) * Q) := by
      rw [KPlus]
      exact norm_sum_Fin3_Fin3_le hterm
    have hPUQ : 0 ≤ 9 * (P * (Dinv * Kτ * (12 * Jb + 12096) * Kz) * Q) := by positivity
    have hKMinus : KMinus ℓ 24 τ z = 0 := KMinus_eq_zero_of_coincidence ℓ (Or.inr rfl) hc
    have hKfun : Kfun ℓ 24 τ z = KPlus 24 τ z / 2 := by
      simp only [Kfun, hKMinus, add_zero]
    rw [hKfun, norm_div]
    simp only [Complex.norm_ofNat]
    calc ‖KPlus 24 τ z‖ / 2
        ≤ (9 * (P * (Dinv * Kτ * (12 * Jb + 12096) * Kz) * Q)) / 2 := by linarith
      _ ≤ 9 * (P * (Dinv * Kτ * (12 * Jb + 12096) * Kz) * Q) := by linarith
      _ ≤ max 1 (9 * (P * (Dinv * Kτ * (12 * Jb + 12096) * Kz) * Q)) := le_max_right _ _

end Work.Asymptotics.KaxisMid
