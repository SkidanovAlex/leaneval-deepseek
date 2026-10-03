/-
# The Toeplitz matrices of a skew Laurent polynomial

This file collects the definitions and the two multiplicativity statements for the Toeplitz
matrices `toeplitz n p` used by the construction of the `∗`-regular envelope of the natural
extension.  It is a copy of the corresponding statements of
`Submission.Work.ORHughesFree.NaturalExtension.toeplitz_mul_of_nonneg` and
`.toeplitz_t_pow_const_mul`, renamed (`toeplitzMulNonneg`, `toeplitzTPowConstMul`) so that the
module does not depend on the main development file.
-/
import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.Defs
import Submission.Work.ORHughesFree.NaturalExtension
import Submission.Work.ORHughesFree.NaturalExtension.coeffMat_mul_bdd

set_option autoImplicit false
universe u

namespace Work.ORHughesFree.NaturalExtension

open Matrix

noncomputable def toeplitz {U : Type*} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
    (n : ℕ) (p : SkewL U) : Matrix (Fin n) (Fin n) U :=
  fun r s => (Multiplicative.ofAdd ((r : ℕ) : ℤ)) • (coeffElt p (((s : ℕ) : ℤ) - ((r : ℕ) : ℤ)))

/-- `toeplitz` is the block structure of the truncation `toep` of a matrix over `U[t^{±1};τ]`. -/
theorem toeplitz_toep {U : Type*} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
    (n k l : ℕ) (A : Matrix (Fin k) (Fin l) (SkewL U)) (i : Fin k) (r : Fin n) (j : Fin l)
    (s : Fin n) : toeplitz n (A i j) r s = toep n A (i, r) (j, s) := by
  simp [toeplitz, toep, coeffMat_apply, coeffElt]



/-- Reindexing a sum over `Fin n` along the translation `u ↦ u - R` of the integer line: the
values `(u : ℤ) - R` for `u ∈ Fin n` are exactly the integers in `[-R, n - 1 - R]`. -/
theorem sum_fin_sub_shift_skew {M : Type*} [AddCommMonoid M] (n : ℕ) (R : ℤ) (f : ℤ → M) :
    ∑ u : Fin n, f ((u : ℤ) - R) = ∑ v ∈ Finset.Icc (-R) ((n : ℤ) - 1 - R), f v := by
  have himg : (Finset.univ : Finset (Fin n)).image (fun u : Fin n => (u : ℤ) - R) =
      Finset.Icc (-R) ((n : ℤ) - 1 - R) := by
    ext v
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_Icc]
    constructor
    · rintro ⟨u, rfl⟩
      have := u.isLt
      omega
    · intro hv
      refine ⟨⟨(v + R).toNat, ?_⟩, ?_⟩
      · omega
      · simp only
        omega
  rw [← himg]
  rw [Finset.sum_image]
  intro a _ b _ h
  simp only at h
  omega

/-- Let `U` be a ring with a twist `τ` (`MulSemiringAction (Multiplicative ℤ) U`), `SkewL U :=
SkewMonoidAlgebra U (Multiplicative ℤ) = U[t^{±1};τ]`, and for `p ∈ SkewL U` let `toeplitz n p` be
the `n × n` matrix whose `(r,s)` entry is the coefficient of `t^s` in `t^r p`, i.e.
`τ^r (a_{s-r})` (defined in `Submission.Work.ORHughesFree.NaturalExtension.isStarRegularRank_naturalExtension`).

If `p` and `q` both have *nonnegative support* (`coeffElt _ k = 0` for `k < 0`, i.e. they lie in
the polynomial part `U[t;τ]`), then

`toeplitz n (p * q) = toeplitz n p * toeplitz n q`.

Useful ingredients already in the workspace: `Submission.Work.ORHughesFree.NaturalExtension.coeffElt_mul`
(`coeffElt (f * g) w = ∑_v coeffElt f v * (ofAdd v • coeffElt g (w - v))`) and
`NaturalExtensionPoly/coeffMat_mul_bdd_u.lean`'s `coeffElt_mul_support`.  (Without the support
hypotheses the statement is FALSE, e.g. `U = ℚ`, `n = 1`, `p = t`, `q = t⁻¹`.) -/
theorem toeplitzMulNonneg {U : Type} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
    (n : ℕ) {p q : SkewL U} (hp : ∀ k : ℤ, k < 0 → coeffElt p k = 0)
    (hq : ∀ k : ℤ, k < 0 → coeffElt q k = 0) :
    toeplitz n (p * q) = toeplitz n p * toeplitz n q := by
  classical
  -- Work entrywise: fix a row `r` and a column `s`, and write `R`, `S` for their images in `ℤ`.
  ext r s
  simp only [toeplitz, Matrix.mul_apply]
  set R : ℤ := (r : ℤ) with hRdef
  set S : ℤ := (s : ℤ) with hSdef
  have hR0 : 0 ≤ R := by rw [hRdef]; have := r.isLt; omega
  have hRn : R ≤ (n : ℤ) - 1 := by rw [hRdef]; have := r.isLt; omega
  have hSn : S ≤ (n : ℤ) - 1 := by rw [hSdef]; have := s.isLt; omega
  -- The common summand: the `v`-th summand of the coefficient formula for `t^R • (p * q)`.
  let T : ℤ → U := fun v =>
    (Multiplicative.ofAdd R • coeffElt p v) *
      (Multiplicative.ofAdd (R + v) • coeffElt q (S - R - v))
  -- Coefficients of `p` outside its support vanish.
  have hcoeff : ∀ x : ℤ, x ∉ p.support.image Multiplicative.toAdd → coeffElt p x = 0 := by
    intro x hx
    have hmem : Multiplicative.ofAdd x ∉ p.support := fun h =>
      hx (Finset.mem_image.mpr ⟨Multiplicative.ofAdd x, h, by simp⟩)
    simpa [coeffElt] using (Finsupp.notMem_support_iff.mp hmem)
  -- The left-hand side, expanded by the coefficient formula for a product.
  have hL : Multiplicative.ofAdd R • coeffElt (p * q) (S - R) =
      ∑ v ∈ p.support.image Multiplicative.toAdd, T v := by
    rw [coeffElt_mul_support, Finset.smul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only [T]
    rw [smul_mul', ← mul_smul, ← ofAdd_add]
  -- The summand of the matrix product at the intermediate index `u` is `T (u - R)`.
  have hterm : ∀ u : Fin n,
      (Multiplicative.ofAdd R • coeffElt p ((u : ℤ) - R)) *
        (Multiplicative.ofAdd (u : ℤ) • coeffElt q (S - (u : ℤ))) = T ((u : ℤ) - R) := by
    intro u
    simp only [T]
    rw [show R + ((u : ℤ) - R) = (u : ℤ) by ring,
        show S - R - ((u : ℤ) - R) = S - (u : ℤ) by ring]
  -- The right-hand side, reindexed over the intermediate degrees `v = u - R`.
  have hR : (∑ u : Fin n,
      (Multiplicative.ofAdd R • coeffElt p ((u : ℤ) - R)) *
        (Multiplicative.ofAdd (u : ℤ) • coeffElt q (S - (u : ℤ)))) =
      ∑ v ∈ Finset.Icc (-R) ((n : ℤ) - 1 - R), T v := by
    rw [show (∑ u : Fin n, (Multiplicative.ofAdd R • coeffElt p ((u : ℤ) - R)) *
            (Multiplicative.ofAdd (u : ℤ) • coeffElt q (S - (u : ℤ))))
          = ∑ u : Fin n, T ((u : ℤ) - R) from Finset.sum_congr rfl fun u _ => hterm u]
    exact sum_fin_sub_shift_skew n R T
  rw [hL, hR]
  -- Both sums are obtained by restricting the same sum over a large symmetric interval `[-N, N]`.
  set N : ℕ := max (lowDeg p) (max (upDeg p) n) with hNdef
  have h1 : lowDeg p ≤ N := by rw [hNdef]; exact le_max_left _ _
  have h2 : upDeg p ≤ N := by rw [hNdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have h3 : n ≤ N := by rw [hNdef]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hNd : (lowDeg p : ℤ) ≤ (N : ℤ) := by exact_mod_cast h1
  have hNu : (upDeg p : ℤ) ≤ (N : ℤ) := by exact_mod_cast h2
  have hNn : (n : ℤ) ≤ (N : ℤ) := by exact_mod_cast h3
  have hsub1 : p.support.image Multiplicative.toAdd ⊆ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    refine subset_trans (image_toAdd_support_subset_Icc p (le_refl _) (le_refl _)) ?_
    intro v hv
    rw [Finset.mem_Icc] at hv ⊢
    exact ⟨by omega, by omega⟩
  have hsub2 : Finset.Icc (-R) ((n : ℤ) - 1 - R) ⊆ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    intro v hv
    rw [Finset.mem_Icc] at hv ⊢
    exact ⟨by omega, by omega⟩
  -- On the complement of the support of `p` the summand vanishes.
  have hvan1 : ∀ x ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      x ∉ p.support.image Multiplicative.toAdd → T x = 0 := by
    intro x _ hx
    simp only [T]
    rw [hcoeff x hx, smul_zero, zero_mul]
  -- Outside `[-R, n - 1 - R]` one of the two factors of the summand vanishes: for `x < -R`
  -- because `p` has nonnegative support, for `x > n - 1 - R` because then `S - R - x < 0`
  -- and `q` has nonnegative support.
  have hvan2 : ∀ x ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      x ∉ Finset.Icc (-R) ((n : ℤ) - 1 - R) → T x = 0 := by
    intro x _ hx
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hx
    simp only [T]
    rcases hx with hlt | hgt
    · rw [hp x (by omega), smul_zero, zero_mul]
    · rw [hq (S - R - x) (by omega), smul_zero, mul_zero]
  rw [Finset.sum_subset hsub1 hvan1, Finset.sum_subset hsub2 hvan2]



/-- The coefficients of a monomial: `coeffElt (single m b) k` is `b` if `ofAdd k = m` and `0`
otherwise. -/
private lemma skewT_coeffElt_single_monomial {U : Type u} [AddMonoid U] (m : Multiplicative ℤ) (b : U)
    (k : ℤ) :
    coeffElt (SkewMonoidAlgebra.single m b) k
      = if m = Multiplicative.ofAdd k then b else 0 := by
  rw [coeffElt, SkewMonoidAlgebra.coeff_single, Finsupp.single_apply]

/-- A monomial `b t^j` of nonnegative degree `j` has no coefficient in a negative degree. -/
private lemma skewT_coeffElt_monomial_nonneg {U : Type u} [AddMonoid U] {j : ℕ} (b : U) {k : ℤ}
    (hk : k < 0) :
    coeffElt (SkewMonoidAlgebra.single (Multiplicative.ofAdd (j : ℤ)) b) k = 0 := by
  rw [skewT_coeffElt_single_monomial, if_neg]
  intro h
  have h' : (j : ℤ) = k := by simpa using congrArg Multiplicative.toAdd h
  omega

/-- Normal form for the powers of the variable `t`: `t ^ k = single (ofAdd k) 1`. -/
private lemma skewT_skewLaurentT_pow_eq_single {R : Type u} [Ring R]
    [MulSemiringAction (Multiplicative ℤ) R] (k : ℕ) :
    (skewLaurentT : SkewL R) ^ k = SkewMonoidAlgebra.single (Multiplicative.ofAdd (k : ℤ)) 1 := by
  rw [skewLaurentT]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, SkewMonoidAlgebra.single_mul_single, ← ofAdd_add]
    simp

/-- A constant `b t^0` has no coefficient in a negative degree. -/
private lemma skewT_coeffElt_single_one_neg {U : Type u} [AddMonoid U] (b : U) {k : ℤ} (hk : k < 0) :
    coeffElt (SkewMonoidAlgebra.single (1 : Multiplicative ℤ) b) k = 0 := by
  rw [show (1 : Multiplicative ℤ) = Multiplicative.ofAdd (0 : ℤ) from ofAdd_zero.symm]
  exact skewT_coeffElt_monomial_nonneg b hk

/-- Conjugating the Toeplitz matrix of a constant by the Toeplitz matrix of `t ^ y` applies the
twist `τ ^ y` to the constant:
`toeplitz N (t^y) * toeplitz N (a t^0) = toeplitz N ((τ^y a) t^0) * toeplitz N (t^y)`. -/
theorem toeplitzTPowConstMul {U : Type} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
    (N y : ℕ) (x : U) :
    toeplitz N ((skewLaurentT : SkewMonoidAlgebra U (Multiplicative ℤ)) ^ y) *
        toeplitz N (SkewMonoidAlgebra.single (1 : Multiplicative ℤ) x) =
      toeplitz N (SkewMonoidAlgebra.single (1 : Multiplicative ℤ)
          ((Multiplicative.ofAdd (y : ℤ)) • x)) *
        toeplitz N ((skewLaurentT : SkewMonoidAlgebra U (Multiplicative ℤ)) ^ y) := by
  have ht : (skewLaurentT : SkewL U) ^ y
      = SkewMonoidAlgebra.single (Multiplicative.ofAdd (y : ℤ)) (1 : U) :=
    skewT_skewLaurentT_pow_eq_single y
  -- Both `t ^ y` and the constants have nonnegative support.
  have hp : ∀ k : ℤ, k < 0 → coeffElt ((skewLaurentT : SkewL U) ^ y) k = 0 := by
    intro k hk
    rw [ht]
    exact skewT_coeffElt_monomial_nonneg (j := y) 1 hk
  have hq : ∀ k : ℤ, k < 0 →
      coeffElt (SkewMonoidAlgebra.single (1 : Multiplicative ℤ) x) k = 0 :=
    fun k hk => skewT_coeffElt_single_one_neg x hk
  have hq' : ∀ k : ℤ, k < 0 →
      coeffElt (SkewMonoidAlgebra.single (1 : Multiplicative ℤ)
        (Multiplicative.ofAdd (y : ℤ) • x)) k = 0 :=
    fun k hk => skewT_coeffElt_single_one_neg _ hk
  -- The two products of the underlying elements of `U[t^{±1};τ]` coincide.
  have hL : (skewLaurentT : SkewL U) ^ y * SkewMonoidAlgebra.single (1 : Multiplicative ℤ) x
      = SkewMonoidAlgebra.single (Multiplicative.ofAdd (y : ℤ))
          (Multiplicative.ofAdd (y : ℤ) • x) := by
    rw [ht, SkewMonoidAlgebra.single_mul_single]
    simp
  have hR : SkewMonoidAlgebra.single (1 : Multiplicative ℤ) (Multiplicative.ofAdd (y : ℤ) • x)
        * (skewLaurentT : SkewL U) ^ y
      = SkewMonoidAlgebra.single (Multiplicative.ofAdd (y : ℤ))
          (Multiplicative.ofAdd (y : ℤ) • x) := by
    rw [ht, SkewMonoidAlgebra.single_mul_single]
    simp
  -- Rewrite both sides as `toeplitz` of the corresponding product.
  rw [← toeplitzMulNonneg N hp hq, ← toeplitzMulNonneg N hq' hp, hL, hR]

end Work.ORHughesFree.NaturalExtension
