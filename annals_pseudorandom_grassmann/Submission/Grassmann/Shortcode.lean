import Mathlib
import Submission.Grassmann.CombinatorialLaplacian
import Submission.Commons.LinearAlgebra.Matrix.rank_le_one_iff
import Submission.Commons.LinearAlgebra.Matrix.rank_vecMulVec
import Submission.Commons.LinearAlgebra.Matrix.card_rank_one_zmod_two
import Submission.Hypercube.Resample
import Submission.Commons.LinearAlgebra.Matrix.vecMulVec_injective_zmod_two
import Submission.Commons.LinearAlgebra.LinearMap.natCard_fiber_mulVec

/-!
# The shortcode graph on `L(V,W)` (arXiv:2209.04243, §9)

The *shortcode graph* on `L(V,W) = Matrix (Fin m) (Fin n) 𝔽₂` joins two matrices when their
difference has rank one; its normalised adjacency operator is

  `graphTOp f A = 𝔼_{B : rank B = 1} f (A + B)`.

This file computes its Fourier multiplier: the character `mchar X` is an eigenvector with
eigenvalue

  `λ_{rank X} = (2^n (2^{m - rank X} - 1) - (2^m - 1)) / ((2^m - 1)(2^n - 1))`,

where `n = dim V`, `m = dim W`.  For `rank X = d` this is
`(2^{m+n-d} - 2^n - 2^m + 1)/((2^m-1)(2^n-1))`, asymptotically `2^{-d}` (the constant stated in
the paper differs, see `ROADMAP.md` §5 of session 9).
-/

open Finset BigOperators
open Classical

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission.Grassmann

noncomputable section

variable {m n : ℕ}

/-! ## The bilinear character -/

/-- `dotChar u φ = ω^{⟨φ, u⟩}`. -/
def dotChar (u φ : Fin n → ZMod 2) : ℂ := ∏ k : Fin n, ZMod.stdAddChar (φ k * u k)

lemma dotChar_add (u φ ψ : Fin n → ZMod 2) :
    dotChar u (φ + ψ) = dotChar u φ * dotChar u ψ := by
  rw [dotChar, dotChar, dotChar, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Pi.add_apply, add_mul]
  exact AddChar.map_add_eq_mul _ _ _

lemma dotChar_zero (u : Fin n → ZMod 2) : dotChar u 0 = 1 := by
  rw [dotChar]
  exact Finset.prod_eq_one fun k _ => by
    rw [Pi.zero_apply, zero_mul, AddChar.map_zero_eq_one]

lemma dotChar_single (u : Fin n → ZMod 2) (k : Fin n) :
    dotChar u (Pi.single k 1) = ZMod.stdAddChar (u k) := by
  rw [dotChar, Finset.prod_eq_single k]
  · rw [Pi.single_eq_same, one_mul]
  · intro j _ hjk
    rw [Pi.single_eq_of_ne hjk, zero_mul, AddChar.map_zero_eq_one]
  · intro h; exact absurd (Finset.mem_univ k) h

/-- Orthogonality of the bilinear characters. -/
lemma sum_dotChar (u : Fin n → ZMod 2) :
    (∑ φ : Fin n → ZMod 2, dotChar u φ) = if u = 0 then (2 : ℂ) ^ n else 0 := by
  by_cases hu : u = 0
  · subst hu
    rw [if_pos rfl]
    rw [show (∑ φ : Fin n → ZMod 2, dotChar (0 : Fin n → ZMod 2) φ) =
        ∑ _φ : Fin n → ZMod 2, (1 : ℂ) from
      Finset.sum_congr rfl fun φ _ => by
        rw [dotChar]; exact Finset.prod_eq_one fun k _ => by
          rw [Pi.zero_apply, mul_zero, AddChar.map_zero_eq_one]]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, ZMod.card,
      nsmul_eq_mul, mul_one, Nat.cast_pow, Nat.cast_ofNat]
  · rw [if_neg hu]
    obtain ⟨k₀, hk₀⟩ : ∃ k, u k ≠ 0 := by
      by_contra hc
      exact hu (funext fun k => by simpa using not_exists.mp hc k)
    have hsingle : dotChar u (Pi.single k₀ 1) = -1 := by
      rw [dotChar_single u k₀]
      rcases zmod2_eq_zero_or_one (u k₀) with h | h
      · exact absurd h hk₀
      · rw [h]; exact Submission.Hypercube.stdAddChar_one
    have hbij : (∑ φ : Fin n → ZMod 2, dotChar u (φ + Pi.single k₀ 1)) =
        ∑ φ : Fin n → ZMod 2, dotChar u φ :=
      Equiv.sum_comp (Equiv.addRight (Pi.single k₀ 1)) (dotChar u)
    have hneg : (∑ φ : Fin n → ZMod 2, dotChar u φ) =
        -(∑ φ : Fin n → ZMod 2, dotChar u φ) := by
      conv_lhs => rw [← hbij]
      simp only [dotChar_add, hsingle]
      rw [show (∑ φ : Fin n → ZMod 2, dotChar u φ * (-1)) = ∑ φ, -dotChar u φ from
        Finset.sum_congr rfl fun φ _ => by ring, Finset.sum_neg_distrib]
    have h2 : (∑ φ : Fin n → ZMod 2, dotChar u φ) + (∑ φ : Fin n → ZMod 2, dotChar u φ) = 0 := by
      nth_rewrite 2 [hneg]
      exact add_neg_cancel _
    have h3 : (2 : ℂ) * (∑ φ : Fin n → ZMod 2, dotChar u φ) = 0 := by
      rw [two_mul]; exact h2
    exact (mul_eq_zero.mp h3).resolve_left (by norm_num)

/-- The character summed over the nonzero elements: `2^n [u = 0] - 1`. -/
lemma sum_dotChar_ne_zero (u : Fin n → ZMod 2) :
    (∑ φ ∈ (Finset.univ : Finset (Fin n → ZMod 2)).filter (fun φ => φ ≠ 0), dotChar u φ) =
      (if u = 0 then (2 : ℂ) ^ n else 0) - 1 := by
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin n → ZMod 2))
    (fun φ => φ ≠ 0) (dotChar u)
  rw [sum_dotChar] at hsplit
  have hzero : (∑ φ ∈ (Finset.univ : Finset (Fin n → ZMod 2)).filter (fun φ => ¬ φ ≠ 0),
      dotChar u φ) = 1 := by
    rw [show (Finset.univ.filter (fun φ : Fin n → ZMod 2 => ¬ φ ≠ 0)) = {0} from by
      ext φ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro h; by_contra hc; exact h hc
      · intro h; rw [h]; exact fun hh => hh rfl]
    rw [Finset.sum_singleton]
    exact dotChar_zero u
  rw [hzero] at hsplit
  rw [eq_sub_iff_add_eq]
  exact hsplit

/-! ## The character of an outer product -/

lemma mchar_vecMulVec {m n : ℕ} (X : Matrix (Fin n) (Fin m) (ZMod 2))
    (b : Fin m → ZMod 2) (φ : Fin n → ZMod 2) :
    mchar X (Matrix.vecMulVec b φ) = dotChar (Matrix.mulVec X b) φ := by
  rw [mchar_eq_trace, dotChar, Matrix.trace]
  rw [stdAddChar_sum]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Matrix.diag_apply]
  congr 1
  rw [Matrix.mul_apply, Matrix.mulVec_apply_eq_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [Matrix.vecMulVec_apply]; ring

/-! ## The sum of the characters over the rank-one matrices -/

theorem sum_mchar_rank_one {m n : ℕ} (X : Matrix (Fin n) (Fin m) (ZMod 2)) :
    (∑ B ∈ (Finset.univ : Finset (Matrix (Fin m) (Fin n) (ZMod 2))).filter
        (fun B => B.rank = 1), mchar X B) =
      ∑ b ∈ (Finset.univ : Finset (Fin m → ZMod 2)).filter (fun b => b ≠ 0),
        ∑ φ ∈ (Finset.univ : Finset (Fin n → ZMod 2)).filter (fun φ => φ ≠ 0),
          dotChar (Matrix.mulVec X b) φ := by
  rw [← Finset.sum_product (Finset.univ.filter fun b : Fin m → ZMod 2 => b ≠ 0)
    (Finset.univ.filter fun φ : Fin n → ZMod 2 => φ ≠ 0)
    (fun p : (Fin m → ZMod 2) × (Fin n → ZMod 2) => dotChar (Matrix.mulVec X p.1) p.2)]
  refine (Finset.sum_bij (fun p _ => Matrix.vecMulVec p.1 p.2) ?_ ?_ ?_ ?_).symm
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hp ⊢
    exact Commons.LinearAlgebra.Matrix.rank_vecMulVec p.1 p.2 (by simp [hp.1, hp.2])
  · intro p hp q hq hpq
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hp hq
    obtain ⟨h1, h2⟩ := Commons.LinearAlgebra.Matrix.vecMulVec_injective_zmod_two hp.1 hp.2
      hq.1 hq.2 hpq
    exact Prod.ext h1 h2
  · intro B hB
    rw [Finset.mem_filter] at hB
    obtain ⟨-, hBrank⟩ := hB
    obtain ⟨b, φ, rfl⟩ :=
      (Commons.LinearAlgebra.Matrix.rank_le_one_iff B).mp (le_of_eq hBrank)
    have hb : b ≠ 0 := by
      intro hb0
      rw [hb0] at hBrank
      rw [show Matrix.vecMulVec (0 : Fin m → ZMod 2) φ = 0 from by
          ext i j; simp [Matrix.vecMulVec_apply],
        Matrix.rank_zero] at hBrank
      exact one_ne_zero hBrank.symm
    have hφ : φ ≠ 0 := by
      intro hφ0
      rw [hφ0] at hBrank
      rw [show Matrix.vecMulVec b (0 : Fin n → ZMod 2) = 0 from by
          ext i j; simp [Matrix.vecMulVec_apply],
        Matrix.rank_zero] at hBrank
      exact one_ne_zero hBrank.symm
    exact ⟨(b, φ), by simp [hb, hφ], rfl⟩
  · intro p _
    exact (mchar_vecMulVec X p.1 p.2).symm

/-- Removing one point decreases the cardinality by one. -/
lemma natCard_subtype_ne_of_finite {α : Type*} [Finite α] (a : α) :
    Nat.card {x : α // x ≠ a} = Nat.card α - 1 := by
  haveI : Fintype α := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_subtype_compl (fun x : α => x = a), Fintype.card_subtype_eq a]

/-- The number of nonzero vectors in the kernel of `X`. -/
lemma natCard_fiber_ne_zero {m n : ℕ} (X : Matrix (Fin n) (Fin m) (ZMod 2)) :
    Nat.card {b : Fin m → ZMod 2 // b ≠ 0 ∧ Matrix.mulVec X b = 0} =
      2 ^ (m - X.rank) - 1 := by
  have hker : Nat.card {b : Fin m → ZMod 2 // Matrix.mulVec X b = 0} = 2 ^ (m - X.rank) :=
    Commons.LinearAlgebra.LinearMap.natCard_fiber_mulVec X 0 (by simp)
  have hbij : {b : Fin m → ZMod 2 // b ≠ 0 ∧ Matrix.mulVec X b = 0} ≃
      {b : {b : Fin m → ZMod 2 // Matrix.mulVec X b = 0} // b ≠ ⟨0, by simp⟩} :=
    { toFun := fun b => ⟨⟨b.1, b.2.2⟩, fun h => b.2.1 (congrArg Subtype.val h)⟩
      invFun := fun b => ⟨b.1.1, fun h => b.2 (Subtype.ext h), b.1.2⟩
      left_inv := fun b => rfl
      right_inv := fun b => rfl }
  rw [Nat.card_congr hbij,
    natCard_subtype_ne_of_finite (⟨0, by simp⟩ : {b : Fin m → ZMod 2 // Matrix.mulVec X b = 0}),
    hker]

/-- The number of nonzero vectors in the kernel, as a `Finset` cardinality. -/
lemma card_filter_ne_zero_ker {m n : ℕ} (X : Matrix (Fin n) (Fin m) (ZMod 2)) :
    ((Finset.univ : Finset (Fin m → ZMod 2)).filter
      (fun b => b ≠ 0 ∧ Matrix.mulVec X b = 0)).card = 2 ^ (m - X.rank) - 1 := by
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact natCard_fiber_ne_zero X

/-- The sum of the characters over the rank-one matrices, evaluated. -/
theorem sum_mchar_rank_one_eq {m n : ℕ} (X : Matrix (Fin n) (Fin m) (ZMod 2)) :
    (∑ B ∈ (Finset.univ : Finset (Matrix (Fin m) (Fin n) (ZMod 2))).filter
        (fun B => B.rank = 1), mchar X B) =
      (2 : ℂ) ^ n * ((2 : ℂ) ^ (m - X.rank) - 1) - ((2 : ℂ) ^ m - 1) := by
  classical
  rw [sum_mchar_rank_one]
  rw [Finset.sum_congr rfl (fun b _ => sum_dotChar_ne_zero (Matrix.mulVec X b))]
  have h2 : (∑ b ∈ (Finset.univ : Finset (Fin m → ZMod 2)).filter (fun b => b ≠ 0),
        (if Matrix.mulVec X b = 0 then (2 : ℂ) ^ n else 0)) =
      (2 : ℂ) ^ n * ((2 : ℂ) ^ (m - X.rank) - 1) := by
    rw [show (∑ b ∈ (Finset.univ : Finset (Fin m → ZMod 2)).filter (fun b => b ≠ 0),
          (if Matrix.mulVec X b = 0 then (2 : ℂ) ^ n else 0)) =
        (2 : ℂ) ^ n * ∑ b ∈ (Finset.univ : Finset (Fin m → ZMod 2)).filter (fun b => b ≠ 0),
          (if Matrix.mulVec X b = 0 then (1 : ℂ) else 0) from by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      by_cases hb : Matrix.mulVec X b = 0 <;> simp [hb]]
    rw [Finset.sum_boole, Finset.filter_filter, card_filter_ne_zero_ker X,
      Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]
  have h3 : (∑ _b ∈ (Finset.univ : Finset (Fin m → ZMod 2)).filter (fun b => b ≠ 0),
      (1 : ℂ)) = ((2 : ℂ) ^ m - 1) := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    have hcard : Nat.card (Fin m → ZMod 2) = 2 ^ m := by
      rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, ZMod.card]
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card,
      natCard_subtype_ne_of_finite (0 : Fin m → ZMod 2), hcard,
      Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]
  rw [Finset.sum_sub_distrib, h2, h3]

/-! ## The shortcode graph averaging operator -/

/-- The shortcode graph on `L(V,W)`: its normalised adjacency operator averages over the
rank-one matrices. -/
def graphTOp {m n : ℕ} (f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) :
    Matrix (Fin m) (Fin n) (ZMod 2) → ℂ :=
  fun A => (((Finset.univ : Finset (Matrix (Fin m) (Fin n) (ZMod 2))).filter
      (fun B => B.rank = 1)).card : ℂ)⁻¹ *
    ∑ B ∈ (Finset.univ : Finset (Matrix (Fin m) (Fin n) (ZMod 2))).filter
      (fun B => B.rank = 1), f (A + B)

lemma card_rank_one_filter {m n : ℕ} :
    ((Finset.univ : Finset (Matrix (Fin m) (Fin n) (ZMod 2))).filter
      (fun B => B.rank = 1)).card = (2 ^ m - 1) * (2 ^ n - 1) := by
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact Commons.LinearAlgebra.Matrix.card_rank_one_zmod_two

/-- **The Fourier multiplier of the shortcode-graph operator**: the character `mchar X` is an
eigenvector with eigenvalue `λ_{rank X} = (2^n(2^{m-rank X}-1) - (2^m-1))/((2^m-1)(2^n-1))`. -/
theorem graphTOp_mchar {m n : ℕ} (X : Matrix (Fin n) (Fin m) (ZMod 2))
    (A : Matrix (Fin m) (Fin n) (ZMod 2)) :
    graphTOp (mchar X) A =
      ((2 : ℂ) ^ n * ((2 : ℂ) ^ (m - X.rank) - 1) - ((2 : ℂ) ^ m - 1)) *
        (((2 : ℂ) ^ m - 1) * ((2 : ℂ) ^ n - 1))⁻¹ * mchar X A := by
  rw [graphTOp]
  rw [show (∑ B ∈ (Finset.univ : Finset (Matrix (Fin m) (Fin n) (ZMod 2))).filter
        (fun B => B.rank = 1), mchar X (A + B)) =
      mchar X A * ∑ B ∈ (Finset.univ : Finset (Matrix (Fin m) (Fin n) (ZMod 2))).filter
        (fun B => B.rank = 1), mchar X B from by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun B _ => ?_
    rw [mchar_add_right]]
  rw [sum_mchar_rank_one_eq X, card_rank_one_filter]
  have hm : (1 : ℕ) ≤ 2 ^ m := Nat.one_le_two_pow
  have hn : (1 : ℕ) ≤ 2 ^ n := Nat.one_le_two_pow
  push_cast [Nat.cast_sub hm, Nat.cast_sub hn]
  ring

end

end Submission.Grassmann


