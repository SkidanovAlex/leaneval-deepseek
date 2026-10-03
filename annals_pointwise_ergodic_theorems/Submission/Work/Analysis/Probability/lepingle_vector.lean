import Mathlib
import Submission.Work.Analysis.Probability.lepingle_variation_lp_all

/-!
# Lépingle's inequality for vector-valued martingales

A finite family `i : ι` of real functions `f i` is turned into the martingale
`n ↦ (i ↦ 𝔼[f i | ℱ n])` with values in `ι → ℝ`, and the `s`-variation (`s > 2`) of that
vector-valued martingale is estimated in `L^s` by the `ℓ^s`-sum of the scalar `L^s` norms of
the `f i`.

The proof is three steps, all of them in this file:

* `VtrVec_le_sum_Vtr`: pointwise, the vector variation (taken in the sup norm on `ι → ℝ`) is at
  most the `ℓ^s`-sum of the scalar variations of the coordinates.  For a single increase
  `u j → u (j+1)` this is `‖v‖_∞ ≤ (∑ i, |v i|^s)^{1/s}`, i.e.
  `norm_rpow_le_sum_abs_rpow`, together with the fact that the sum over the increments of one
  coordinate is one of the terms in the defining supremum of the scalar variation.
* `eLpNorm_sum_rpow_eq`: for a family `W : ι → Ω → ℝ≥0∞`, the `L^s` norm of
  `ω ↦ (∑ i, (W i ω)^s)^{1/s}` is exactly the `ℓ^s`-sum of the `L^s` norms of the `W i`
  (a Tonelli/Fubini computation).
* `LepLp.eLpNorm_Vtr_le_decoup` (the scalar Lépingle inequality, from the probability area)
  applied to each coordinate.

The only place where the actual martingale structure enters is the last step.
-/

namespace Work.Analysis.Probability

open MeasureTheory
open scoped ENNReal BigOperators

/-- For `v : ι → ℝ`, the `s`-th power of the sup norm is at most the `ℓ^s`-sum of the absolute
values.  (For `s = 1` this is an equality; for `s > 0` it is the elementary
`ℓ^∞ ⊆ ℓ^s` inclusion.) -/
lemma norm_rpow_le_sum_abs_rpow {ι : Type*} [Fintype ι] (v : ι → ℝ) {s : ℝ} (hs : 0 < s) :
    ‖v‖ ^ s ≤ ∑ i, |v i| ^ s := by
  have hnn : ∀ i, 0 ≤ |v i| ^ s := fun i => Real.rpow_nonneg (abs_nonneg _) s
  have hsum_nn : 0 ≤ ∑ i, |v i| ^ s := Finset.sum_nonneg (fun i _ => hnn i)
  have hsup : ‖v‖ ≤ (∑ i, |v i| ^ s) ^ (1/s) := by
    rw [pi_norm_le_iff_of_nonneg (Real.rpow_nonneg hsum_nn _)]
    intro i
    calc |v i| = (|v i| ^ s) ^ (1/s) := by
          rw [← Real.rpow_mul (abs_nonneg (v i)), mul_one_div_cancel hs.ne', Real.rpow_one]
      _ ≤ (∑ j, |v j| ^ s) ^ (1/s) :=
          Real.rpow_le_rpow (hnn i) (Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i))
            (by positivity)
  calc ‖v‖ ^ s ≤ ((∑ i, |v i| ^ s) ^ (1/s)) ^ s := Real.rpow_le_rpow (norm_nonneg v) hsup hs.le
    _ = ∑ i, |v i| ^ s := by
        rw [← Real.rpow_mul hsum_nn, one_div_mul_cancel hs.ne', Real.rpow_one]

/-- `ℝ≥0∞`-valued version of `norm_rpow_le_sum_abs_rpow`. -/
lemma ofReal_norm_rpow_le_sum {ι : Type*} [Fintype ι] (v : ι → ℝ) {s : ℝ} (hs : 0 < s) :
    ENNReal.ofReal (‖v‖ ^ s) ≤ ∑ i, ENNReal.ofReal (|v i| ^ s) := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => Real.rpow_nonneg (abs_nonneg _) s)]
  exact ENNReal.ofReal_le_ofReal (norm_rpow_le_sum_abs_rpow v hs)

/-- One term of the defining supremum of the scalar variation, raised to the power `s`, dominates
the sum over the increments of that same chain. -/
lemma ofReal_sum_rpow_le_Vtr {Ω : Type*} [MeasurableSpace Ω] (g : ℕ → Ω → ℝ) {s : ℝ}
    (hs : 0 < s) (N : ℕ) (ω : Ω)
    (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ) (hg : u.1 J ≤ N) :
    ENNReal.ofReal (∑ j ∈ Finset.range J, |g (u.1 (j+1)) ω - g (u.1 j) ω| ^ s)
      ≤ (SFTest.Vtr g s N ω) ^ s := by
  have hX : 0 ≤ ∑ j ∈ Finset.range J, |g (u.1 (j+1)) ω - g (u.1 j) ω| ^ s :=
    Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (abs_nonneg _) s)
  have hB : 0 ≤ (∑ j ∈ Finset.range J, |g (u.1 (j+1)) ω - g (u.1 j) ω| ^ s) ^ (1/s) :=
    Real.rpow_nonneg hX _
  have hle : ENNReal.ofReal ((∑ j ∈ Finset.range J, |g (u.1 (j+1)) ω - g (u.1 j) ω| ^ s) ^ (1/s))
      ≤ SFTest.Vtr g s N ω := by
    have h := le_iSup₂ (f := fun (u' : {u : ℕ → ℕ // StrictMono u}) (J' : ℕ) =>
      if u'.1 J' ≤ N then
        ENNReal.ofReal ((∑ j ∈ Finset.range J', |g (u'.1 (j+1)) ω - g (u'.1 j) ω| ^ s) ^ (1/s))
      else 0) u J
    simpa only [SFTest.Vtr, if_pos hg] using h
  have hthis := ENNReal.rpow_le_rpow hle hs.le
  rwa [ENNReal.ofReal_rpow_of_nonneg hB hs.le, ← Real.rpow_mul hX, one_div_mul_cancel hs.ne',
    Real.rpow_one] at hthis

/-- For a family `W : ι → Ω → ℝ≥0∞` of a.e.-measurable functions, the `L^s` norm of
`ω ↦ (∑ i, (W i ω)^s)^{1/s}` is the `ℓ^s`-sum of the `L^s` norms of the `W i`. -/
lemma eLpNorm_sum_rpow_eq {ι : Type*} [Fintype ι] {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {s : ℝ} (hs : 0 < s) (W : ι → Ω → ℝ≥0∞)
    (hW : ∀ i, AEMeasurable (W i) μ) :
    eLpNorm (fun ω => (∑ i, (W i ω) ^ s) ^ (1/s)) (ENNReal.ofReal s) μ
      = (∑ i, (eLpNorm (W i) (ENNReal.ofReal s) μ) ^ s) ^ (1/s) := by
  rw [Commons.Analysis.Probability.eLpNorm_ennreal_eq (fun ω => (∑ i, (W i ω) ^ s) ^ (1/s)) hs]
  congr 1
  calc ∫⁻ ω, ((∑ i, (W i ω) ^ s) ^ (1/s)) ^ s ∂μ
      = ∫⁻ ω, (∑ i, (W i ω) ^ s) ∂μ := by
        refine lintegral_congr (fun ω => ?_)
        rw [← ENNReal.rpow_mul, one_div_mul_cancel hs.ne', ENNReal.rpow_one]
    _ = ∑ i, ∫⁻ ω, (W i ω) ^ s ∂μ := by
        rw [MeasureTheory.lintegral_finsetSum' Finset.univ (fun i _ => (hW i).pow_const s)]
    _ = ∑ i, (eLpNorm (W i) (ENNReal.ofReal s) μ) ^ s := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Commons.Analysis.Probability.eLpNorm_ennreal_eq (W i) hs, ← ENNReal.rpow_mul,
          one_div_mul_cancel hs.ne', ENNReal.rpow_one]

end Work.Analysis.Probability
