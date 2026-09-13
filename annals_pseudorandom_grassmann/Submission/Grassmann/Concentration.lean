import Submission.Grassmann.Prop56Main
import Submission.Commons.Analysis.Inequalities.sum_norm_mul_pow_four_le

/-!
# The level-`d` concentration corollary (arXiv:2209.04243, §9.1)

Combining Proposition 5.6 (`prop_5_6`) with the "corollary of hypercontractivity" (the
consequence of the deep Theorem 1.5 used by the paper, packaged here as the hypothesis
`HypCor4`), we obtain the *level-`d` concentration* of a restriction-global Boolean function:

  `‖f^{=d}‖₂² ≤ q^{O(d²)} ε^{1/3} ‖f‖₂²`,

stated in the equivalent root-free form `(‖f^{=d}‖₂²)³ ≤ q^{O(d²)} ε (‖f‖₂²)³`.

This is Corollary `cor:concentration on high degrees` of arXiv:2209.04243, the input to the
small-set expansion theorem for the shortcode graph (`thm:sses`).
-/

open Finset BigOperators Matrix
open Classical

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission.Grassmann

noncomputable section

local notation "𝔽₂" => ZMod 2

/-! ## Boolean functions -/

/-- Boolean functions on `L(V,W)`: the indicator of a set of linear maps. -/
def IsBoolBS {m n : ℕ} (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) : Prop := ∀ A, f A = 0 ∨ f A = 1

lemma isBool_norm_four {m n : ℕ} {f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ} (hf : IsBoolBS f)
    (A : Matrix (Fin m) (Fin n) 𝔽₂) : ‖f A‖ ^ 4 = ‖f A‖ ^ 2 := by
  rcases hf A with h | h <;> rw [h] <;> norm_num

lemma isBool_norm_rpow {m n : ℕ} {f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ} (hf : IsBoolBS f)
    (A : Matrix (Fin m) (Fin n) 𝔽₂) : ‖f A‖ ^ ((4 : ℝ) / 3) = ‖f A‖ ^ 2 := by
  rcases hf A with h | h
  · rw [h]; simp
  · rw [h]; norm_num

lemma l4q_eq_l2sq_of_isBool {m n : ℕ} {f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ}
    (hf : IsBoolBS f) : l4q f = l2sq f := by
  rw [l4q, l2sq]
  congr 1
  exact Finset.sum_congr rfl fun A _ => isBool_norm_four hf A

/-! ## The normalised inner product -/

/-- The normalised `L²` inner product `⟨g,h⟩ = 2^{-mn} ∑_A g A · conj (h A)`. -/
def inner2 {m n : ℕ} (g h : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) : ℂ :=
  ((2 : ℂ) ^ (m * n))⁻¹ * ∑ A, g A * star (h A)

/-- **Parseval in conjugated form.** -/
lemma sum_fhat_mul_star {m n : ℕ} (g h : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    (∑ X : Matrix (Fin n) (Fin m) 𝔽₂, fhat g X * star (fhat h X)) =
      ((2 : ℂ) ^ (m * n)) * ∑ A, g A * star (h A) := by
  have h1 := fhat_parseval g (fun A => star (h A))
  simpa only [fhat_star] using h1

/-- The inner product in terms of the *normalised* Fourier coefficients. -/
lemma inner2_eq_fcoeff {m n : ℕ} (g h : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    inner2 g h = ∑ X : Matrix (Fin n) (Fin m) 𝔽₂, fcoeff g X * star (fcoeff h X) := by
  have hc : ((2 : ℂ) ^ (m * n)) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hstar : star (((2 : ℂ) ^ (m * n))⁻¹) = ((2 : ℂ) ^ (m * n))⁻¹ := by
    rw [Complex.star_def, Complex.conj_inv, map_pow, Complex.conj_ofNat]
  have hsum : (∑ X : Matrix (Fin n) (Fin m) 𝔽₂, fcoeff g X * star (fcoeff h X)) =
      ((2 : ℂ) ^ (m * n))⁻¹ * ((2 : ℂ) ^ (m * n))⁻¹ *
        ∑ X, fhat g X * star (fhat h X) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun X _ => ?_
    simp only [fcoeff, star_mul, hstar]
    ring
  rw [hsum, sum_fhat_mul_star, inner2]
  field_simp

lemma inner2_self {m n : ℕ} (g : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    inner2 g g = (l2sq g : ℂ) := by
  rw [inner2, l2sq, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_pow,
    Complex.ofReal_ofNat, Complex.ofReal_sum]
  congr 1
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

lemma norm_inner2_self {m n : ℕ} (g : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    ‖inner2 g g‖ = l2sq g := by
  rw [inner2_self]
  exact Complex.norm_of_nonneg (l2sq_nonneg g)

/-- **The level-`d` projection is self-adjoint**: `⟨f^{=d}, f⟩ = ‖f^{=d}‖₂²`. -/
lemma inner2_nprojPure {m n d : ℕ} (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    inner2 (nprojPure d f) f = (l2sq (nprojPure d f) : ℂ) := by
  have h1 := inner2_eq_fcoeff (nprojPure d f) f
  have h2 := sum_normSq_fcoeff (nprojPure d f)
  rw [h1, ← h2, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun X _ => ?_
  rw [fcoeff_nprojPure]
  by_cases hX : X.rank = d
  · rw [if_pos hX, one_mul, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  · rw [if_neg hX, zero_mul]; simp

lemma norm_inner2_nprojPure {m n d : ℕ} (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    ‖inner2 (nprojPure d f) f‖ = l2sq (nprojPure d f) := by
  rw [inner2_nprojPure]
  exact Complex.norm_of_nonneg (l2sq_nonneg _)

/-! ## Hölder's inequality for the inner product -/

lemma norm_inner2_le_sum {m n : ℕ} (g h : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    ‖inner2 g h‖ ≤ ((2 : ℝ) ^ (m * n))⁻¹ * ∑ A, ‖g A‖ * ‖h A‖ := by
  have h1 : ‖inner2 g h‖ =
      ((2 : ℝ) ^ (m * n))⁻¹ * ‖∑ A, g A * star (h A)‖ := by
    rw [inner2, norm_mul, norm_inv, norm_pow, Complex.norm_ofNat]
  rw [h1]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (norm_sum_le Finset.univ _).trans (Finset.sum_le_sum fun A _ => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (le_of_eq (Complex.norm_conj (h A))) (norm_nonneg _)

/-- **Hölder for the normalised inner product**, in fourth-power form. -/
lemma norm_inner2_pow_four_le {m n : ℕ} (g h : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    ‖inner2 g h‖ ^ 4 ≤ l4q g *
      (((2 : ℝ) ^ (m * n))⁻¹ * ∑ A, ‖h A‖ ^ ((4 : ℝ) / 3)) ^ 3 := by
  set M : ℝ := (2 : ℝ) ^ (m * n) with hM
  have hholder : (∑ A, ‖g A‖ * ‖h A‖) ^ 4 ≤
      (∑ A, ‖g A‖ ^ 4) * (∑ A, ‖h A‖ ^ ((4 : ℝ) / 3)) ^ 3 :=
    Commons.Analysis.Inequalities.sum_norm_mul_pow_four_le Finset.univ g h
  have hb : ‖inner2 g h‖ ≤ M⁻¹ * ∑ A, ‖g A‖ * ‖h A‖ := by
    simpa only [hM] using norm_inner2_le_sum g h
  have hb4 : ‖inner2 g h‖ ^ 4 ≤ (M⁻¹ * ∑ A, ‖g A‖ * ‖h A‖) ^ 4 :=
    pow_le_pow_left₀ (norm_nonneg _) hb 4
  calc ‖inner2 g h‖ ^ 4
      ≤ (M⁻¹ * ∑ A, ‖g A‖ * ‖h A‖) ^ 4 := hb4
    _ = (M⁻¹) ^ 4 * (∑ A, ‖g A‖ * ‖h A‖) ^ 4 := by rw [mul_pow]
    _ ≤ (M⁻¹) ^ 4 * ((∑ A, ‖g A‖ ^ 4) * (∑ A, ‖h A‖ ^ ((4 : ℝ) / 3)) ^ 3) :=
        mul_le_mul_of_nonneg_left hholder (by positivity)
    _ = l4q g * ((M⁻¹) * ∑ A, ‖h A‖ ^ ((4 : ℝ) / 3)) ^ 3 := by
        rw [l4q, hM]; ring

/-! ## The level-`d` projection has bounded fourth norm -/

lemma l2sq_nprojPure_pow_four_le {m n d : ℕ} (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    (l2sq (nprojPure d f)) ^ 4 ≤ l4q (nprojPure d f) *
      (((2 : ℝ) ^ (m * n))⁻¹ * ∑ A, ‖f A‖ ^ ((4 : ℝ) / 3)) ^ 3 := by
  have h := norm_inner2_pow_four_le (nprojPure d f) f
  rwa [norm_inner2_nprojPure (d := d)] at h

/-! ## The corollary of hypercontractivity, and concentration -/

/-- **The corollary of hypercontractivity** of arXiv:2209.04243 §9.1 (a consequence of the
deep Theorem 1.5): a function of degree at most `d` whose generalised influences of order at
most `d` are all at most `ε` has `‖f‖₄⁴ ≤ q^{O(d²)} ε ‖f‖₂²`. -/
def HypCor4 : Prop :=
  ∃ C : ℕ, 0 < C ∧ ∀ (m n d : ℕ) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) (ε : ℝ),
    0 ≤ ε → DegLe d f → SmallInfl d ε f → l4q f ≤ (2 : ℝ) ^ (C * d ^ 2) * ε * l2sq f

lemma C_le (d : ℕ) : C d ≤ (2 : ℝ) ^ (2 * d ^ 2 + 9 * d) := by
  have h100 : (100 : ℝ) ^ d ≤ ((2 : ℝ) ^ 7) ^ d :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) d
  have h2 : (2 : ℝ) ^ (2 * d * (d + 1)) ≤ (2 : ℝ) ^ (2 * d ^ 2 + 2 * d) := by
    have h1 : 2 * d * (d + 1) = 2 * d ^ 2 + 2 * d := by ring
    rw [h1]
  calc C d = (100 : ℝ) ^ d * (2 : ℝ) ^ (2 * d * (d + 1)) := rfl
    _ ≤ ((2 : ℝ) ^ 7) ^ d * (2 : ℝ) ^ (2 * d ^ 2 + 2 * d) :=
        mul_le_mul h100 h2 (by positivity) (by positivity)
    _ = (2 : ℝ) ^ (2 * d ^ 2 + 9 * d) := by
        rw [← pow_mul, ← pow_add]
        congr 1
        ring

/-- **The level-`d` concentration corollary** (`cor:concentration on high degrees` of
arXiv:2209.04243), in root-free form: for a Boolean `(d,ε)`-restriction global function,
`(‖f^{=d}‖₂²)³ ≤ q^{O(d²)} ε (‖f‖₂²)³`, i.e. `‖f^{=d}‖₂² ≤ q^{O(d²)} ε^{1/3} ‖f‖₂²`. -/
theorem concentration_of_HypCor4 (H : HypCor4) :
    ∃ C' : ℕ, 0 < C' ∧ ∀ (m n d : ℕ) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) (ε : ℝ),
      0 ≤ ε → IsBoolBS f → GlobalBS d ε f →
        (l2sq (nprojPure d f)) ^ 3 ≤ (2 : ℝ) ^ (C' * d ^ 2) * ε * (l2sq f) ^ 3 := by
  obtain ⟨K, hK, hcor⟩ := H
  refine ⟨K + 20, by omega, ?_⟩
  intro m n d f ε hε hbool hglob
  have hSI : SmallInfl d (C d * ε) (nprojPure d f) := prop_5_6 d ε hε m n f hglob
  have hdeg : DegLe d (nprojPure d f) := by
    intro X hX
    rw [fhat_nprojPure, if_neg (by omega), zero_mul]
  have hε' : 0 ≤ C d * ε := mul_nonneg (le_trans zero_le_one (one_le_C d)) hε
  have h4 := hcor m n d (nprojPure d f) (C d * ε) hε' hdeg hSI
  have hholder := l2sq_nprojPure_pow_four_le (d := d) f
  have hY : (((2 : ℝ) ^ (m * n))⁻¹ * ∑ A, ‖f A‖ ^ ((4 : ℝ) / 3)) = l2sq f := by
    rw [l2sq]
    congr 1
    exact Finset.sum_congr rfl fun A _ => isBool_norm_rpow hbool A
  rw [hY] at hholder
  have hchain : (l2sq (nprojPure d f)) ^ 4 ≤
      ((2 : ℝ) ^ (K * d ^ 2) * (C d * ε)) * l2sq (nprojPure d f) * (l2sq f) ^ 3 :=
    hholder.trans (mul_le_mul_of_nonneg_right h4 (pow_nonneg (l2sq_nonneg f) 3))
  have hkey : (l2sq (nprojPure d f)) ^ 3 ≤
      (2 : ℝ) ^ (K * d ^ 2) * C d * ε * (l2sq f) ^ 3 := by
    by_cases hA0 : l2sq (nprojPure d f) = 0
    · rw [hA0, zero_pow (by norm_num : (3 : ℕ) ≠ 0)]
      exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
        (le_trans zero_le_one (one_le_C d))) hε) (pow_nonneg (l2sq_nonneg f) 3)
    · have hApos : 0 < l2sq (nprojPure d f) :=
        lt_of_le_of_ne (l2sq_nonneg _) (Ne.symm hA0)
      have h2 : l2sq (nprojPure d f) * (l2sq (nprojPure d f)) ^ 3 ≤
          l2sq (nprojPure d f) *
            ((2 : ℝ) ^ (K * d ^ 2) * C d * ε * (l2sq f) ^ 3) := by
        calc l2sq (nprojPure d f) * (l2sq (nprojPure d f)) ^ 3
            = (l2sq (nprojPure d f)) ^ 4 := by ring
          _ ≤ ((2 : ℝ) ^ (K * d ^ 2) * (C d * ε)) * l2sq (nprojPure d f) *
                (l2sq f) ^ 3 := hchain
          _ = l2sq (nprojPure d f) *
                ((2 : ℝ) ^ (K * d ^ 2) * C d * ε * (l2sq f) ^ 3) := by ring
      exact le_of_mul_le_mul_left h2 hApos
  calc (l2sq (nprojPure d f)) ^ 3
      ≤ (2 : ℝ) ^ (K * d ^ 2) * C d * ε * (l2sq f) ^ 3 := hkey
    _ ≤ (2 : ℝ) ^ ((K + 20) * d ^ 2) * ε * (l2sq f) ^ 3 := by
        have hconst : (2 : ℝ) ^ (K * d ^ 2) * C d ≤ (2 : ℝ) ^ ((K + 20) * d ^ 2) := by
          have hCd := C_le d
          calc (2 : ℝ) ^ (K * d ^ 2) * C d
              ≤ (2 : ℝ) ^ (K * d ^ 2) * (2 : ℝ) ^ (2 * d ^ 2 + 9 * d) :=
                mul_le_mul_of_nonneg_left hCd (by positivity)
            _ = (2 : ℝ) ^ (K * d ^ 2 + (2 * d ^ 2 + 9 * d)) := by rw [← pow_add]
            _ ≤ (2 : ℝ) ^ ((K + 20) * d ^ 2) := by
                refine pow_le_pow_right₀ (by norm_num) ?_
                have hkey2 : 2 * d ^ 2 + 9 * d ≤ 20 * d ^ 2 := by
                  rcases Nat.eq_zero_or_pos d with hd | hd
                  · subst hd; norm_num
                  · nlinarith [hd]
                rw [Nat.add_mul]
                omega
        have hεB : 0 ≤ ε * (l2sq f) ^ 3 := mul_nonneg hε (pow_nonneg (l2sq_nonneg f) 3)
        have hh := mul_le_mul_of_nonneg_right hconst hεB
        calc (2 : ℝ) ^ (K * d ^ 2) * C d * ε * (l2sq f) ^ 3
            = ((2 : ℝ) ^ (K * d ^ 2) * C d) * (ε * (l2sq f) ^ 3) := by ring
          _ ≤ (2 : ℝ) ^ ((K + 20) * d ^ 2) * (ε * (l2sq f) ^ 3) := hh
          _ = (2 : ℝ) ^ ((K + 20) * d ^ 2) * ε * (l2sq f) ^ 3 := by ring

/-! ## The level decomposition of `‖·‖₂²` -/

lemma rank_le_min {m n : ℕ} (X : Matrix (Fin n) (Fin m) 𝔽₂) : X.rank ≤ min m n :=
  le_min (Matrix.rank_le_width X) (Matrix.rank_le_height X)

/-- **The level decomposition of the normalised `L²` norm.** -/
lemma sum_l2sq_nprojPure {m n : ℕ} (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    (∑ d ∈ Finset.range (min m n + 1), l2sq (nprojPure d f)) = l2sq f := by
  have h : ∀ d, l2sq (nprojPure d f) =
      ∑ X : Matrix (Fin n) (Fin m) 𝔽₂, if X.rank = d then ‖fcoeff f X‖ ^ 2 else 0 := by
    intro d
    rw [← sum_normSq_fcoeff (nprojPure d f)]
    refine Finset.sum_congr rfl fun X _ => ?_
    rw [fcoeff_nprojPure]
    by_cases hX : X.rank = d <;> simp [hX]
  rw [Finset.sum_congr rfl (fun d _ => h d), ← sum_normSq_fcoeff f, Finset.sum_comm]
  refine Finset.sum_congr rfl fun X _ => ?_
  rw [Finset.sum_eq_single X.rank]
  · rw [if_pos rfl]
  · intro b _ hb
    exact if_neg (fun h => hb h.symm)
  · intro h
    exact absurd (Finset.mem_range.mpr (by have := rank_le_min X; omega)) h

end

end Submission.Grassmann
