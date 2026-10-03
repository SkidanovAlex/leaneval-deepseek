import ChallengeDeps
import Mathlib.Tactic
import Submission.Telescope
import Submission.VarClamp

/-!
# The dyadic telescoping reduction for an arbitrary exponent `r ≥ 1`

`Submission.Telescope` proves the pointwise dyadic telescoping bound of Krause--Mirek--Tao,
Proposition 3.1 (iii), for the variational norm of exponent `r = 3` (the value needed by
Theorem 1.17 (i)--(iii)).  This file records the same argument for an arbitrary exponent
`r ≥ 1`.

Nothing in the argument depends on the value of `r`: the two estimates used for the
`2^{-k}`-pieces (`Submission.VarSums.variationalNorm_tsum_le`, homogeneity of the variational
norm) and for the error term (`Submission.VarCoeff.variationalNorm_mul_le`) all hold for every
`r ≥ 1` with the same constants, since the `ℓ^r` norm of a vector is bounded by its `ℓ¹` norm.
Hence the statement below is the exact `r`-general analogue of
`Submission.Telescope.variationalNorm_A_le`, and is available should the `r`-general form of the
integer-shift estimate be plugged into the reduction chain.
-/

set_option maxHeartbeats 3200000

namespace Submission

open _root_.PointwiseErgodicTheorems
set_option autoImplicit false

namespace PointwiseErgodicTheorems

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal PNat

variable {𝓧 : Type*} [MeasurableSpace 𝓧]

/-- **Pointwise dyadic telescoping, arbitrary exponent `r ≥ 1`.**  The variational norm of
exponent `r` of the averages `n ↦ A T (a n) X P f g x` is bounded by the weighted sum of the
variational norms of the halved averages at the rescaled dyadic scales `a n / 2^k`, plus the
weighted error term. -/
theorem variationalNorm_A_le_gen (r : ℝ≥0) (hr : 1 ≤ r) (T : 𝓧 ≃ᵐ 𝓧) (P : ℤ[X])
    (f g : 𝓧 → ℂ) (a : ℕ → ℝ≥0) (h1 : ∀ n, 1 ≤ a n) (x : 𝓧) :
    variationalNorm r (fun n => A T (a n) X P f g x) ≤
      (∑' k, ‖halfScalar k‖ₑ *
        variationalNorm r (fun n => AhalfR T (a n / 2 ^ k) X P f g x))
      + 3 * ∑' n, (Nat.floor (a n) : ℝ≥0∞)⁻¹ *
        (∑' k, ‖AhalfR T (a n / 2 ^ k) X P f g x‖ₑ) := by
  classical
  have hm1 : ∀ n, 1 ≤ Nat.floor (a n) := fun n => (Nat.one_le_floor_iff (a n)).mpr (h1 n)
  set c : ℕ → ℂ := fun k => halfScalar k with hc
  set F : ℕ → ℕ → ℂ := fun k n => AhalfR T (a n / 2 ^ k) X P f g x with hF
  have hc2 : ∀ k, (((((2 : ℝ≥0)⁻¹) ^ k : ℝ≥0)) : ℝ) = (((2 : ℝ)⁻¹) ^ k) := by
    intro k
    rw [NNReal.coe_pow, NNReal.coe_inv]
    norm_num
  have hc' : ∀ k, c k = ((((2 : ℝ)⁻¹) ^ k : ℝ) : ℂ) := by
    intro k
    rw [hc]
    exact congrArg (fun x : ℝ => (x : ℂ)) (hc2 k)
  have hFzero : ∀ n, ∀ k, Nat.floor (a n) < 2 ^ k → F k n = 0 := fun n k h => by
    rw [hF]
    exact AhalfR_eq_zero_of_two_pow_gt T h X P f g x
  have hlog : ∀ n k, k ≥ Nat.log2 (Nat.floor (a n)) + 1 → Nat.floor (a n) < 2 ^ k := by
    intro n k hk
    have h1 : Nat.floor (a n) < 2 ^ (Nat.log2 (Nat.floor (a n)) + 1) := by
      rw [Nat.log2_eq_log_two]
      simpa [Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self (by norm_num) (Nat.floor (a n))
    exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) hk)
  set XA : ℕ → ℂ := fun n => ∑' k, c k * F k n with hXA
  set YA : ℕ → ℂ := fun n => ∑' k, (((telCoeff (a n) k : ℝ) : ℂ) - c k) * F k n with hYA
  have hXY : (fun n => A T (a n) X P f g x) = XA + YA := by
    funext n
    have hA : A T (a n) X P f g x
        = ∑ k ∈ Finset.range (Nat.log2 (Nat.floor (a n)) + 1),
            (((telCoeff (a n) k : ℝ) : ℂ) * F k n) := by
      rw [A_eq_sum_AhalfR T (a n) P f g x (hm1 n)]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      simp only [telCoeff, hF]
      push_cast
      ring
    have hXs : XA n = ∑ k ∈ Finset.range (Nat.log2 (Nat.floor (a n)) + 1), c k * F k n :=
      tsum_eq_sum (f := fun k => c k * F k n)
        (s := Finset.range (Nat.log2 (Nat.floor (a n)) + 1))
        (fun k hk => by
          rw [hFzero n k (hlog n k (by simp only [Finset.mem_range, not_lt] at hk; omega)), mul_zero])
    have hYs : YA n = ∑ k ∈ Finset.range (Nat.log2 (Nat.floor (a n)) + 1),
        (((telCoeff (a n) k : ℝ) : ℂ) - c k) * F k n :=
      tsum_eq_sum (f := fun k => (((telCoeff (a n) k : ℝ) : ℂ) - c k) * F k n)
        (s := Finset.range (Nat.log2 (Nat.floor (a n)) + 1))
        (fun k hk => by
          rw [hFzero n k (hlog n k (by simp only [Finset.mem_range, not_lt] at hk; omega)), mul_zero])
    rw [hA, Pi.add_apply, hXs, hYs, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  have hsplit : variationalNorm r (fun n => A T (a n) X P f g x)
      ≤ variationalNorm r XA + variationalNorm r YA := by
    rw [hXY]
    exact variationalNorm_add_le (r := r) hr XA YA
  have hXbound : variationalNorm r XA
      ≤ ∑' k, ‖c k‖ₑ * variationalNorm r (fun n => F k n) := by
    have hb : ∀ n, ∃ K, ∀ k ≥ K, (fun k n => c k * F k n) k n = 0 :=
      fun n => ⟨Nat.log2 (Nat.floor (a n)) + 1, fun k hk => by
        show c k * F k n = 0
        rw [hFzero n k (hlog n k hk), mul_zero]⟩
    have := variationalNorm_tsum_le (r := r) hr (b := fun k n => c k * F k n) hb
    refine this.trans ?_
    refine ENNReal.tsum_le_tsum (fun k => ?_)
    have hs : (fun n => c k * F k n) = c k • (fun n => F k n) := by
      funext n; rw [Pi.smul_apply, smul_eq_mul]
    rw [hs, variationalNorm_smul (r := r) hr]
  have hYbound : variationalNorm r YA
      ≤ 3 * ∑' n, (Nat.floor (a n) : ℝ≥0∞)⁻¹ * (∑' k, ‖F k n‖ₑ) := by
    have hd : ∀ k n, ‖(((telCoeff (a n) k : ℝ) : ℂ) - c k)‖ ≤ (Nat.floor (a n) : ℝ)⁻¹ := by
      intro k n
      rw [hc' k, ← Complex.ofReal_sub, Complex.norm_real]
      exact telCoeff_sub_le (a n) k (hm1 n)
    have := variationalNorm_mul_le (r := r) hr (m := fun n => Nat.floor (a n))
      (d := fun k n => (((telCoeff (a n) k : ℝ) : ℂ) - c k)) (b := F)
      hd (fun n => ⟨Nat.log2 (Nat.floor (a n)) + 1, fun k hk => hFzero n k (hlog n k hk)⟩)
    exact this
  exact hsplit.trans (add_le_add hXbound hYbound)

/-- The pointwise dyadic telescoping bound for an arbitrary exponent `r ≥ 1`, written with the
bundled halved-average sequence `halfSeq`. -/
theorem variationalNorm_A_le_halfSeq_gen (r : ℝ≥0) (hr : 1 ≤ r) (T : 𝓧 ≃ᵐ 𝓧) (P : ℤ[X])
    (f g : 𝓧 → ℂ) (a : ℕ → ℝ≥0) (h1 : ∀ n, 1 ≤ a n) (x : 𝓧) :
    variationalNorm r (fun n => A T (a n) X P f g x) ≤
      (∑' k, ‖halfScalar k‖ₑ * variationalNorm r (fun n => halfSeq T a P f g k n x))
      + 3 * ∑' n, (Nat.floor (a n) : ℝ≥0∞)⁻¹ *
        (∑' k, ‖halfSeq T a P f g k n x‖ₑ) :=
  variationalNorm_A_le_gen r hr T P f g a h1 x

end PointwiseErgodicTheorems
end Submission
