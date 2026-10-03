import ChallengeDeps
import Mathlib.Tactic
import Submission.VarCoeff
import Submission.Half
import Submission.Commons.Analysis.Real.floor_div_pow_ratio_error

/-!
# The dyadic telescoping reduction (Krause--Mirek--Tao, Proposition 3.1 (iii))

We prove that a variational estimate for the *halved* averages `Ã_N` implies the corresponding
variational estimate for the full averages `A_N`.

The pointwise input is the telescoping identity `A_N = ∑_{k} (⌊N/2^k⌋/⌊N⌋) Ã_{N/2^k}` together
with the error estimate `⌊N/2^k⌋/⌊N⌋ = 2^{-k} + O(1/⌊N⌋)`:
writing `A_n = ∑_k 2^{-k} Ã_{a n/2^k} + ∑_k (⌊a n/2^k⌋/⌊a n⌋ - 2^{-k}) Ã_{a n/2^k}`,
the first sum is controlled by subadditivity and homogeneity of the variational norm, while the
second is controlled by `variationalNorm_mul_le`, whose `1/⌊a n⌋` weight makes the contribution
of the individual dyadic pieces summable.
-/

set_option maxHeartbeats 3200000

namespace Submission

open _root_.PointwiseErgodicTheorems
set_option autoImplicit false

namespace PointwiseErgodicTheorems

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal PNat

variable {𝓧 : Type*} [MeasurableSpace 𝓧]

/-- The telescoping coefficient `⌊N / 2^k⌋ / ⌊N⌋`. -/
noncomputable def telCoeff (N : ℝ≥0) (k : ℕ) : ℝ :=
  ((Nat.floor N / 2 ^ k : ℕ) : ℝ) / (Nat.floor N : ℝ)

/-- The telescoping coefficient differs from `2^{-k}` by at most `1/⌊N⌋`. -/
lemma telCoeff_sub_le (N : ℝ≥0) (k : ℕ) (hN : 1 ≤ Nat.floor N) :
    |telCoeff N k - ((2 : ℝ)⁻¹) ^ k| ≤ (Nat.floor N : ℝ)⁻¹ := by
  have h := Commons.Analysis.Real.floor_div_pow_ratio_error (Nat.floor N) k hN
  rw [← inv_pow] at h
  simpa only [telCoeff] using h

/-- The halved average vanishes once the dyadic scale exceeds the size of `⌊N⌋`. -/
lemma AhalfR_eq_zero_of_two_pow_gt (T : 𝓧 ≃ᵐ 𝓧) {N : ℝ≥0} {k : ℕ}
    (h : Nat.floor N < 2 ^ k) (P₁ P₂ : ℤ[X]) (f g : 𝓧 → ℂ) (x : 𝓧) :
    AhalfR T (N / 2 ^ k) P₁ P₂ f g x = 0 := by
  rw [AhalfR, nat_floor_div_pow_two, Nat.div_eq_of_lt h]
  exact Ahalf_zero T P₁ P₂ f g x

/-- The `enorm` of the real scalar `(1/2)^k` viewed as a complex number. -/
lemma enorm_half_pow (k : ℕ) :
    ‖(((((2 : ℝ≥0)⁻¹) ^ k : ℝ≥0)) : ℂ)‖ₑ = ((((2 : ℝ≥0)⁻¹) ^ k : ℝ≥0)) := by
  rw [← ofReal_norm, Complex.norm_of_nonneg (by positivity), ENNReal.ofReal_coe_nnreal]

/-- **Pointwise dyadic telescoping.**  The variational norm of the averages
`n ↦ A T (a n) X P f g x` is bounded by the sum of the variational norms of the halved averages at
the rescaled dyadic scales `a n / 2^k`, plus the weighted error term. -/
theorem variationalNorm_A_le (T : 𝓧 ≃ᵐ 𝓧) (P : ℤ[X]) (f g : 𝓧 → ℂ) (a : ℕ → ℝ≥0)
    (h1 : ∀ n, 1 ≤ a n) (x : 𝓧) :
    variationalNorm 3 (fun n => A T (a n) X P f g x) ≤
      (∑' k, ‖(((((2 : ℝ≥0)⁻¹) ^ k : ℝ≥0)) : ℂ)‖ₑ *
        variationalNorm 3 (fun n => AhalfR T (a n / 2 ^ k) X P f g x))
      + 3 * ∑' n, (Nat.floor (a n) : ℝ≥0∞)⁻¹ *
        (∑' k, ‖AhalfR T (a n / 2 ^ k) X P f g x‖ₑ) := by
  classical
  have hm1 : ∀ n, 1 ≤ Nat.floor (a n) := fun n => (Nat.one_le_floor_iff (a n)).mpr (h1 n)
  set c : ℕ → ℂ := fun k => (((((2 : ℝ≥0)⁻¹) ^ k : ℝ≥0)) : ℂ) with hc
  set F : ℕ → ℕ → ℂ := fun k n => AhalfR T (a n / 2 ^ k) X P f g x with hF
  have hc2 : ∀ k, (((((2 : ℝ≥0)⁻¹) ^ k : ℝ≥0)) : ℝ) = (((2 : ℝ)⁻¹) ^ k) := by
    intro k
    rw [NNReal.coe_pow, NNReal.coe_inv]
    norm_num
  have hc' : ∀ k, c k = ((((2 : ℝ)⁻¹) ^ k : ℝ) : ℂ) := by
    intro k
    rw [hc]
    exact congrArg (fun r : ℝ => (r : ℂ)) (hc2 k)
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
  have hsplit : variationalNorm 3 (fun n => A T (a n) X P f g x)
      ≤ variationalNorm 3 XA + variationalNorm 3 YA := by
    rw [hXY]
    exact variationalNorm_add_le (r := 3) (by norm_num) XA YA
  have hXbound : variationalNorm 3 XA
      ≤ ∑' k, ‖c k‖ₑ * variationalNorm 3 (fun n => F k n) := by
    have hb : ∀ n, ∃ K, ∀ k ≥ K, (fun k n => c k * F k n) k n = 0 :=
      fun n => ⟨Nat.log2 (Nat.floor (a n)) + 1, fun k hk => by
        show c k * F k n = 0
        rw [hFzero n k (hlog n k hk), mul_zero]⟩
    have := variationalNorm_tsum_le (r := 3) (by norm_num) (b := fun k n => c k * F k n) hb
    refine this.trans ?_
    refine ENNReal.tsum_le_tsum (fun k => ?_)
    have hs : (fun n => c k * F k n) = c k • (fun n => F k n) := by
      funext n; rw [Pi.smul_apply, smul_eq_mul]
    rw [hs, variationalNorm_smul (r := 3) (by norm_num)]
  have hYbound : variationalNorm 3 YA
      ≤ 3 * ∑' n, (Nat.floor (a n) : ℝ≥0∞)⁻¹ * (∑' k, ‖F k n‖ₑ) := by
    have hd : ∀ k n, ‖(((telCoeff (a n) k : ℝ) : ℂ) - c k)‖ ≤ (Nat.floor (a n) : ℝ)⁻¹ := by
      intro k n
      rw [hc' k, ← Complex.ofReal_sub, Complex.norm_real]
      exact telCoeff_sub_le (a n) k (hm1 n)
    have := variationalNorm_mul_le (r := 3) (by norm_num) (m := fun n => Nat.floor (a n))
      (d := fun k n => (((telCoeff (a n) k : ℝ) : ℂ) - c k)) (b := F)
      hd (fun n => ⟨Nat.log2 (Nat.floor (a n)) + 1, fun k hk => hFzero n k (hlog n k hk)⟩)
    exact this
  exact hsplit.trans (add_le_add hXbound hYbound)

end PointwiseErgodicTheorems
end Submission

namespace Submission

open _root_.PointwiseErgodicTheorems
set_option autoImplicit false

namespace PointwiseErgodicTheorems

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal PNat

variable {𝓧 : Type*} [MeasurableSpace 𝓧]

/-- The scalar `2^{-k}` of the dyadic telescoping identity, as a complex number. -/
noncomputable def halfScalar (k : ℕ) : ℂ := ((((2 : ℝ≥0)⁻¹) ^ k : ℝ≥0) : ℂ)

/-- The geometric series `∑ 2^{-k}` of the telescoping coefficients: the total weight of the
`2^{-k}` pieces is at most `2`. -/
lemma tsum_enorm_half_pow_le_two :
    ∑' k, ‖(((((2 : ℝ≥0)⁻¹) ^ k : ℝ≥0)) : ℂ)‖ₑ ≤ 2 := by
  have hfun : ∀ k, ‖(((((2 : ℝ≥0)⁻¹) ^ k : ℝ≥0)) : ℂ)‖ₑ = ENNReal.ofReal (((2 : ℝ)⁻¹) ^ k) := by
    intro k
    rw [enorm_half_pow, ← ENNReal.ofReal_coe_nnreal]
    congr 1
  have hgeo := hasSum_geometric_of_norm_lt_one (by norm_num : ‖(2:ℝ)⁻¹‖ < 1)
  have hsum : (∑' k, ((2 : ℝ)⁻¹) ^ k) = 2 := by
    rw [hgeo.tsum_eq]
    norm_num
  simp only [hfun]
  rw [← ENNReal.ofReal_tsum_of_nonneg (f := fun k => ((2 : ℝ)⁻¹) ^ k)
    (fun k => pow_nonneg (by norm_num) k) hgeo.summable, hsum]
  norm_num

/-- The scalar `2^{-k}` is bounded by `1`. -/
lemma enorm_halfScalar (k : ℕ) : ‖halfScalar k‖ₑ = ((((2 : ℝ≥0)⁻¹) ^ k : ℝ≥0)) :=
  enorm_half_pow k

/-- The total weight of the telescoping coefficients `∑ 2^{-k}` is at most `2`. -/
lemma tsum_enorm_halfScalar_le_two : ∑' k, ‖halfScalar k‖ₑ ≤ 2 := tsum_enorm_half_pow_le_two

/-- The scalar `2^{-k}` is finite. -/
lemma enorm_halfScalar_ne_top (k : ℕ) : ‖halfScalar k‖ₑ ≠ ⊤ := by
  rw [enorm_halfScalar]; exact ENNReal.coe_ne_top

/-- The halved averages of `f, g` at the rescaled dyadic scale `a n / 2^k`, as a function of
`(k, n, x)`.  Bundling this expression keeps the terms in the dyadic telescoping argument small. -/
noncomputable def halfSeq (T : 𝓧 ≃ᵐ 𝓧) (a : ℕ → ℝ≥0) (P : ℤ[X]) (f g : 𝓧 → ℂ)
    (k n : ℕ) (x : 𝓧) : ℂ :=
  AhalfR T (a n / 2 ^ k) X P f g x

/-- The pointwise dyadic telescoping bound, written with the bundled halved-average sequence. -/
theorem variationalNorm_A_le_halfSeq (T : 𝓧 ≃ᵐ 𝓧) (P : ℤ[X]) (f g : 𝓧 → ℂ)
    (a : ℕ → ℝ≥0) (h1 : ∀ n, 1 ≤ a n) (x : 𝓧) :
    variationalNorm 3 (fun n => A T (a n) X P f g x) ≤
      (∑' k, ‖(((((2 : ℝ≥0)⁻¹) ^ k : ℝ≥0)) : ℂ)‖ₑ *
        variationalNorm 3 (fun n => halfSeq T a P f g k n x))
      + 3 * ∑' n, (Nat.floor (a n) : ℝ≥0∞)⁻¹ *
        (∑' k, ‖halfSeq T a P f g k n x‖ₑ) :=
  variationalNorm_A_le T P f g a h1 x

end PointwiseErgodicTheorems
end Submission
