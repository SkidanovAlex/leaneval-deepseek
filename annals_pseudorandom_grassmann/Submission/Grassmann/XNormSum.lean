import Submission.Grassmann.XLaplacian
import Submission.Grassmann.ShiftAverage
import Submission.Grassmann.Concentration
import Submission.Commons.LinearAlgebra.Matrix.card_rank_poset_fiber_le_pow

/-!
# The `X`-Laplacian norms: the paper's `lem:getting rid of D_x 2-norms`

arXiv:2209.04243, §4, contains the following step of the induction proving the conditional
hypercontractive inequality: for a function `f` of degree at most `d`,

  `Σ_X q^{-4d·rank X} ‖D_X[f]‖₂² ≤ 2‖f‖₂²`,

where `D_X` is the `X`-Laplacian (`lapMulN (plLE X)`, keeping the characters `u_Y` with `Y ≥ X`
in the rank poset of `XLaplacian.lean`).  The proof is a double count in the Fourier basis:
expanding `‖D_X[f]‖₂² = Σ_{Y ≥ X} |f̂(Y)|²` and exchanging the two sums reduces the claim to
counting, for a fixed character `Y` of rank at most `d`, the number of `X ≤ Y` of a given rank
`k`: there are at most `q^{3kd}` of them (the commons lemma
`Commons.LinearAlgebra.Matrix.card_rank_poset_fiber_le_pow`).  Summing `q^{-4dk}·q^{3kd} = q^{-dk}`
over `k ≤ d` gives a geometric sum bounded by `2`.

The main results are `l2sq_lapMulN_eq` (Parseval for a general Fourier multiplier) and
`sum_inv_pow_l2sq_plLE_le` (the lemma).
-/

open Finset BigOperators Matrix
open Classical

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission.Grassmann

noncomputable section

local notation "𝔽₂" => ZMod 2

lemma geom_sum_le_two {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1/2) (n : ℕ) :
    (∑ k ∈ Finset.range n, r ^ k) ≤ 2 := by
  have key : (∑ k ∈ Finset.range n, r ^ k) * (1 - r) = 1 - r ^ n := by
    have h := geom_sum_mul r n
    linarith
  have hrn : r ^ n ≥ 0 := pow_nonneg hr0 n
  nlinarith [key, hrn]

lemma sum_range_pow_half_pow_le (d : ℕ) :
    (∑ k ∈ Finset.range (d+1), ((1/2:ℝ)^d)^k) ≤ 2 := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd; norm_num
  · refine geom_sum_le_two (by positivity) ?_ (d+1)
    rw [one_div]
    have h2d : (2:ℝ) ≤ 2 ^ d := by
      calc (2:ℝ) = 2^1 := by norm_num
        _ ≤ 2^d := pow_le_pow_right₀ (by norm_num) hd
    rw [inv_pow, inv_le_inv₀ (by norm_num) (by positivity)]
    exact h2d

lemma l2sq_lapMulN_eq {m n : ℕ} (P : Matrix (Fin n) (Fin m) 𝔽₂ → Prop)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    l2sq (lapMulN P f) = ∑ X : Matrix (Fin n) (Fin m) 𝔽₂,
      if P X then ‖fcoeff f X‖ ^ 2 else 0 := by
  rw [← sum_normSq_fcoeff (lapMulN P f)]
  refine Finset.sum_congr rfl fun X _ => ?_
  rw [fcoeff_lapMulN]
  by_cases hX : P X
  · rw [if_pos hX, if_pos hX, one_mul]
  · rw [if_neg hX, if_neg hX, zero_mul, norm_zero]
    norm_num

lemma sum_plLE_inv_pow_le {m n d : ℕ} (Y : Matrix (Fin n) (Fin m) 𝔽₂) (hY : Y.rank ≤ d) :
    (∑ X : Matrix (Fin n) (Fin m) 𝔽₂,
        if plLE X Y then ((2 : ℝ) ^ (4 * d * X.rank))⁻¹ else 0) ≤ 2 := by
  set c : ℕ → ℝ := fun r => ((2 : ℝ) ^ (4 * d * r))⁻¹ with hc
  have hcnn : ∀ r, 0 ≤ c r := by intro r; rw [hc]; positivity
  have hsplit : (∑ X : Matrix (Fin n) (Fin m) 𝔽₂, if plLE X Y then c X.rank else 0)
      = ∑ k ∈ Finset.range (d+1),
          ∑ X : Matrix (Fin n) (Fin m) 𝔽₂,
            if plLE X Y ∧ X.rank = k then c k else 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun X _ => ?_
    by_cases hX : plLE X Y
    · have hx : X.rank ∈ Finset.range (d+1) :=
        Finset.mem_range.mpr (Nat.lt_succ_of_le (le_trans (plLE_rank_le hX) hY))
      rw [if_pos hX]
      have hsingle : (∑ x ∈ Finset.range (d+1),
          (if plLE X Y ∧ X.rank = x then c x else 0))
          = (if plLE X Y ∧ X.rank = X.rank then c X.rank else 0) :=
        Finset.sum_eq_single X.rank
          (fun b _ hb => by rw [if_neg (fun hcon => hb hcon.2.symm)])
          (fun hmem => absurd hx hmem)
      rw [hsingle, if_pos (show plLE X Y ∧ X.rank = X.rank from ⟨hX, rfl⟩)]
    · rw [if_neg hX]
      refine (Finset.sum_eq_zero fun k _ => ?_).symm
      rw [if_neg]
      exact fun hcon => hX hcon.1
  rw [hsplit]
  have hterm : ∀ k ∈ Finset.range (d+1),
      (∑ X : Matrix (Fin n) (Fin m) 𝔽₂,
        if plLE X Y ∧ X.rank = k then c k else 0) ≤ c k * (2:ℝ) ^ (3 * k * d) := by
    intro k _
    have h1 : (∑ X : Matrix (Fin n) (Fin m) 𝔽₂,
          if plLE X Y ∧ X.rank = k then c k else 0)
        = c k * ↑(Nat.card {X : Matrix (Fin n) (Fin m) 𝔽₂ // plLE X Y ∧ X.rank = k}) := by
      have h2 : (∑ X : Matrix (Fin n) (Fin m) 𝔽₂,
            if plLE X Y ∧ X.rank = k then c k else 0)
          = c k * (∑ X : Matrix (Fin n) (Fin m) 𝔽₂,
            if plLE X Y ∧ X.rank = k then (1:ℝ) else 0) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun X _ => ?_
        by_cases h : plLE X Y ∧ X.rank = k <;> simp [h]
      rw [h2, Finset.sum_boole]
      congr 1
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [h1]
    refine mul_le_mul_of_nonneg_left ?_ (hcnn k)
    exact_mod_cast Commons.LinearAlgebra.Matrix.card_rank_poset_fiber_le_pow n m d k Y hY
  refine (Finset.sum_le_sum hterm).trans ?_
  have hpow : ∀ k : ℕ, c k * (2:ℝ) ^ (3 * k * d) = ((1/2:ℝ)^d)^k := by
    intro k
    have h1 : ((1/2:ℝ)^d)^k = ((2:ℝ)^(d*k))⁻¹ := by
      have h2 : ((1/2:ℝ)^d)^k * (2:ℝ)^(d*k) = 1 := by
        rw [← pow_mul, ← mul_pow]
        norm_num
      exact eq_inv_of_mul_eq_one_right (by rw [mul_comm]; exact h2)
    rw [h1, hc]
    change ((2:ℝ)^(4 * d * k))⁻¹ * (2:ℝ)^(3 * k * d) = ((2:ℝ)^(d * k))⁻¹
    have hexp : 4 * d * k = d * k + 3 * k * d := by ring
    rw [hexp, pow_add, mul_inv, mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero _ (by norm_num : (2:ℝ) ≠ 0)), mul_one]
  rw [Finset.sum_congr rfl (fun k _ => hpow k)]
  exact sum_range_pow_half_pow_le d

theorem sum_inv_pow_l2sq_plLE_le {m n d : ℕ} {f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ}
    (hf : DegLe d f) :
    (∑ X : Matrix (Fin n) (Fin m) 𝔽₂,
        ((2 : ℝ) ^ (4 * d * X.rank))⁻¹ * l2sq (lapMulN (plLE X) f)) ≤ 2 * l2sq f := by
  set c : ℕ → ℝ := fun r => ((2 : ℝ) ^ (4 * d * r))⁻¹ with hc
  set a : Matrix (Fin n) (Fin m) 𝔽₂ → ℝ := fun Y => ‖fcoeff f Y‖ ^ 2 with ha
  have step1 : (∑ X : Matrix (Fin n) (Fin m) 𝔽₂, c X.rank * l2sq (lapMulN (plLE X) f))
      = ∑ X : Matrix (Fin n) (Fin m) 𝔽₂, ∑ Y : Matrix (Fin n) (Fin m) 𝔽₂,
          c X.rank * (if plLE X Y then a Y else 0) := by
    refine Finset.sum_congr rfl fun X _ => ?_
    rw [l2sq_lapMulN_eq, Finset.mul_sum]
  have step2 : (∑ X : Matrix (Fin n) (Fin m) 𝔽₂, ∑ Y : Matrix (Fin n) (Fin m) 𝔽₂,
          c X.rank * (if plLE X Y then a Y else 0))
      = ∑ Y : Matrix (Fin n) (Fin m) 𝔽₂, a Y *
          (∑ X : Matrix (Fin n) (Fin m) 𝔽₂, if plLE X Y then c X.rank else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun Y _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun X _ => ?_
    by_cases h : plLE X Y <;> simp [h, mul_comm]
  have hb : ∀ Y : Matrix (Fin n) (Fin m) 𝔽₂,
      a Y * (∑ X : Matrix (Fin n) (Fin m) 𝔽₂, if plLE X Y then c X.rank else 0) ≤ a Y * 2 := by
    intro Y
    by_cases hY : Y.rank ≤ d
    · refine mul_le_mul_of_nonneg_left ?_ (by rw [ha]; positivity)
      rw [hc]
      exact sum_plLE_inv_pow_le Y hY
    · have hz : fcoeff f Y = 0 := by
        rw [fcoeff, hf Y (by omega), mul_zero]
      rw [ha]
      simp only [hz, norm_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0), zero_mul, le_refl]
  calc (∑ X : Matrix (Fin n) (Fin m) 𝔽₂, c X.rank * l2sq (lapMulN (plLE X) f))
      = ∑ Y : Matrix (Fin n) (Fin m) 𝔽₂, a Y *
          (∑ X : Matrix (Fin n) (Fin m) 𝔽₂, if plLE X Y then c X.rank else 0) := by
        exact step1.trans step2
    _ ≤ ∑ Y : Matrix (Fin n) (Fin m) 𝔽₂, a Y * 2 := Finset.sum_le_sum fun Y _ => hb Y
    _ = (∑ Y : Matrix (Fin n) (Fin m) 𝔽₂, a Y) * 2 := by rw [Finset.sum_mul]
    _ = l2sq f * 2 := by rw [ha, sum_normSq_fcoeff]
    _ = 2 * l2sq f := by ring

/-- **`cor:getting rid of D_X 4-norms`** of arXiv:2209.04243: for a function of degree at most
`d`, `Σ_X q^{-4d·rank X} (‖D_X[f]‖₂²)² ≤ 2‖f‖₂⁴`.

The proof is the paper's: `‖D_X[f]‖₂² ≤ ‖f‖₂²` (`l2sq (lapMulN (plLE X) f) ≤ l2sq f`), so
`Σ_X q^{-4d rank X}(‖D_Xf‖₂²)² ≤ ‖f‖₂² Σ_X q^{-4d rank X}‖D_Xf‖₂² ≤ 2‖f‖₂⁴` by
`sum_inv_pow_l2sq_plLE_le`.-/
theorem sum_inv_pow_sq_l2sq_plLE_le {m n d : ℕ} {f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ}
    (hf : DegLe d f) :
    (∑ X : Matrix (Fin n) (Fin m) 𝔽₂,
        ((2 : ℝ) ^ (4 * d * X.rank))⁻¹ * (l2sq (lapMulN (plLE X) f)) ^ 2) ≤
      2 * (l2sq f) ^ 2 := by
  have hle : ∀ X : Matrix (Fin n) (Fin m) 𝔽₂, l2sq (lapMulN (plLE X) f) ≤ l2sq f := by
    intro X
    rw [l2sq_lapMulN_eq]
    calc (∑ Y : Matrix (Fin n) (Fin m) 𝔽₂,
            (if plLE X Y then ‖fcoeff f Y‖ ^ 2 else 0)) ≤
          ∑ Y : Matrix (Fin n) (Fin m) 𝔽₂, ‖fcoeff f Y‖ ^ 2 :=
          Finset.sum_le_sum (fun Y _ => by
            by_cases h : plLE X Y
            · rw [if_pos h]
            · rw [if_neg h]; positivity)
      _ = l2sq f := sum_normSq_fcoeff f
  have hnn : ∀ X : Matrix (Fin n) (Fin m) 𝔽₂, 0 ≤ l2sq (lapMulN (plLE X) f) :=
    fun X => l2sq_nonneg _
  have hc : ∀ X : Matrix (Fin n) (Fin m) 𝔽₂, 0 ≤ ((2 : ℝ) ^ (4 * d * X.rank))⁻¹ :=
    fun X => by positivity
  calc (∑ X : Matrix (Fin n) (Fin m) 𝔽₂,
        ((2 : ℝ) ^ (4 * d * X.rank))⁻¹ * (l2sq (lapMulN (plLE X) f)) ^ 2)
      ≤ ∑ X : Matrix (Fin n) (Fin m) 𝔽₂,
          ((2 : ℝ) ^ (4 * d * X.rank))⁻¹ * (l2sq f * l2sq (lapMulN (plLE X) f)) := by
        refine Finset.sum_le_sum (fun X _ => mul_le_mul_of_nonneg_left ?_ (hc X))
        calc (l2sq (lapMulN (plLE X) f)) ^ 2
            = l2sq (lapMulN (plLE X) f) * l2sq (lapMulN (plLE X) f) := by ring
          _ ≤ l2sq f * l2sq (lapMulN (plLE X) f) :=
              mul_le_mul_of_nonneg_right (hle X) (hnn X)
    _ = l2sq f * ∑ X : Matrix (Fin n) (Fin m) 𝔽₂,
          ((2 : ℝ) ^ (4 * d * X.rank))⁻¹ * l2sq (lapMulN (plLE X) f) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun X _ => by ring)
    _ ≤ l2sq f * (2 * l2sq f) :=
        mul_le_mul_of_nonneg_left (sum_inv_pow_l2sq_plLE_le hf) (l2sq_nonneg f)
    _ = 2 * (l2sq f) ^ 2 := by ring



end

end Submission.Grassmann
