import Mathlib
import Submission.Work.BourgainPlan.Oscillation.lacunary_defs

/-!
# The block-oscillation functional is bounded by the `ℓ²` sizes of the increments

For an abstract family `A : ℕ → ℤ → ℂ` and a strictly increasing `k : ℕ → ℕ`, the block oscillation
`oscZ A J k = Σ_{j<J} ∫_ℤ (sup_{k_j ≤ i < k_{j+1}} |A_i − A_{k_j}|)²` is controlled by the
*increments* `A_{i+1} − A_i`:

if `‖A_{i+1} − A_i‖_{ℓ²} ≤ a_i · c` for every `i`, then

  `oscZ A J k ≤ ((Σ_{i < k_J} a_i) · c)²`.

The mechanism is the classical one for oscillation/variational bounds:

* *telescoping*: inside a block, `A_i − A_{k_j}` is the sum of the increments, so the pointwise
  sup over the block is at most the sum of the pointwise norms of the increments;
* *Minkowski in `ℓ²`*: the `ℓ²` norm of a finite sum is at most the sum of the `ℓ²` norms
  (`lintegral_sq_sum_le`, proved from Hölder with the conjugate pair `(2,2)`);
* the blocks `[k_j, k_{j+1})` are disjoint and contained in `[k_0, k_J) ⊆ [0, k_J)`, and the
  squares of the block budgets sum to at most the square of the total budget.

Everything is stated for `ℝ≥0∞`-valued functions in `lintegral` form, with respect to counting
measure on `ℤ`, i.e. exactly in the shape in which the circle-method/variation arguments of this
project produce their increment bounds.
-/

namespace Work.BourgainPlan.Oscillation

open Finset MeasureTheory
open scoped BigOperators ENNReal

/-- In `ℝ≥0∞`, the square root of a square is the original number. -/
theorem sq_rpow_half (x : ℝ≥0∞) : (x ^ 2) ^ ((1 : ℝ) / 2) = x := by
  rw [← ENNReal.rpow_natCast x 2, ← ENNReal.rpow_mul,
    show ((2 : ℕ) : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.rpow_one]

/-- **Minkowski's inequality** for a finite sum of `ℝ≥0∞`-valued functions: expanding the square
into a double sum and applying `ENNReal.lintegral_mul_le_Lp_mul_Lq` with the conjugate pair
`(2, 2)` bounds the `ℒ²` seminorm of `Σ_i b_i` by the sum of the `ℒ²` seminorms of the `b_i`. -/
theorem lintegral_sq_sum_le {ι α : Type*} [MeasurableSpace α] (μ : Measure α) (s : Finset ι)
    (b : ι → α → ℝ≥0∞) (hb : ∀ i ∈ s, Measurable (b i)) :
    ∫⁻ x, (∑ i ∈ s, b i x) ^ 2 ∂μ
      ≤ (∑ i ∈ s, (∫⁻ x, (b i x) ^ 2 ∂μ) ^ ((1 : ℝ) / 2)) ^ 2 := by
  classical
  have hpq : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hsum : ∫⁻ x, ∑ p ∈ s ×ˢ s, b p.1 x * b p.2 x ∂μ
      = ∑ p ∈ s ×ˢ s, ∫⁻ x, b p.1 x * b p.2 x ∂μ :=
    lintegral_finsetSum (s ×ˢ s) (f := fun p x => b p.1 x * b p.2 x)
      (fun p hp => (hb p.1 (Finset.mem_product.mp hp).1).mul
        (hb p.2 (Finset.mem_product.mp hp).2))
  have hexp : ∀ x, (∑ i ∈ s, b i x) ^ 2 = ∑ p ∈ s ×ˢ s, b p.1 x * b p.2 x := by
    intro x
    rw [sq, Finset.sum_mul_sum, Finset.sum_product]
  have hstep1 : ∫⁻ x, (∑ i ∈ s, b i x) ^ 2 ∂μ
      = ∑ p ∈ s ×ˢ s, ∫⁻ x, b p.1 x * b p.2 x ∂μ := (lintegral_congr hexp).trans hsum
  have hstep2 : ∑ p ∈ s ×ˢ s, ∫⁻ x, b p.1 x * b p.2 x ∂μ
      ≤ ∑ p ∈ s ×ˢ s, (∫⁻ x, (b p.1 x) ^ 2 ∂μ) ^ ((1 : ℝ) / 2)
          * (∫⁻ x, (b p.2 x) ^ 2 ∂μ) ^ ((1 : ℝ) / 2) := by
    refine Finset.sum_le_sum (fun p hp => ?_)
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq (hb p.1 hp1).aemeasurable
      (hb p.2 hp2).aemeasurable
    have h1 : (∫⁻ a, (b p.1 a) ^ (2 : ℝ) ∂μ) = (∫⁻ a, (b p.1 a) ^ 2 ∂μ) :=
      lintegral_congr (fun a => ENNReal.rpow_natCast (b p.1 a) 2)
    have h2 : (∫⁻ a, (b p.2 a) ^ (2 : ℝ) ∂μ) = (∫⁻ a, (b p.2 a) ^ 2 ∂μ) :=
      lintegral_congr (fun a => ENNReal.rpow_natCast (b p.2 a) 2)
    rw [h1, h2] at h
    exact h
  have hstep3 : ∑ p ∈ s ×ˢ s, (∫⁻ x, (b p.1 x) ^ 2 ∂μ) ^ ((1 : ℝ) / 2)
        * (∫⁻ x, (b p.2 x) ^ 2 ∂μ) ^ ((1 : ℝ) / 2)
      = (∑ i ∈ s, (∫⁻ x, (b i x) ^ 2 ∂μ) ^ ((1 : ℝ) / 2)) ^ 2 := by
    rw [sq, Finset.sum_mul_sum, Finset.sum_product]
  exact (hstep1.trans_le hstep2).trans (le_of_eq hstep3)

/-- The blocks `[k_j, k_{j+1})` of a strictly increasing sequence are disjoint and contained in
`[0, k_J)`, so for nonnegative `a` the sum of the block budgets is at most the total budget. -/
theorem sum_Ico_blocks_le (k : ℕ → ℕ) (hk : StrictMono k) (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i)
    (J : ℕ) :
    ∑ j ∈ Finset.range J, ∑ i ∈ Finset.Ico (k j) (k (j + 1)), a i
      ≤ ∑ i ∈ Finset.range (k J), a i := by
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range J) : Set ℕ)
      (fun j => Finset.Ico (k j) (k (j + 1))) := by
    intro j _ j' _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro i hi hi'
    rw [Finset.mem_Ico] at hi hi'
    rcases lt_or_gt_of_ne hne with h | h
    · have hmono : k (j + 1) ≤ k j' := hk.monotone (by omega)
      omega
    · have hmono : k (j' + 1) ≤ k j := hk.monotone (by omega)
      omega
  rw [← Finset.sum_biUnion hdisj]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => ha i)
  intro i hi
  rw [Finset.mem_biUnion] at hi
  obtain ⟨j, hj, hij⟩ := hi
  rw [Finset.mem_range] at hj ⊢
  exact lt_of_lt_of_le (Finset.mem_Ico.mp hij).2 (hk.monotone (Nat.succ_le_iff.mpr hj))

/-- **Telescoping inside a block**: the supremum over `[k_j, k_{j+1})` of `‖A_i − A_{k_j}‖ₑ` is at
most the sum of the norms of the increments over the block. -/
theorem sup_sub_le_sum_increments (A : ℕ → ℤ → ℂ) (k : ℕ → ℕ) (j : ℕ) (x : ℤ) :
    (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖A i x - A (k j) x‖ₑ)
      ≤ ∑ t ∈ Finset.Ico (k j) (k (j + 1)), ‖A (t + 1) x - A t x‖ₑ := by
  classical
  rw [← Finset.sup_eq_iSup]
  refine Finset.sup_le (fun i hi => ?_)
  have h1 : k j ≤ i := (Finset.mem_Ico.mp hi).1
  have h2 : i ≤ k (j + 1) := le_of_lt (Finset.mem_Ico.mp hi).2
  have htel : ∑ t ∈ Finset.Ico (k j) i, (A (t + 1) x - A t x) = A i x - A (k j) x :=
    Finset.sum_Ico_sub (fun t => A t x) h1
  have hnorm : ‖A i x - A (k j) x‖ₑ
      ≤ ∑ t ∈ Finset.Ico (k j) i, ‖A (t + 1) x - A t x‖ₑ := by
    rw [← htel]
    exact enorm_sum_le _ _
  exact hnorm.trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_right h2)
    (fun t _ _ => bot_le))

/-- **The per-block bound**: the squared oscillation of the block `[k_j, k_{j+1})` is at most the
square of the block's increment budget `Σ_{k_j ≤ i < k_{j+1}} a_i · c`. -/
theorem oscZ_block_le (A : ℕ → ℤ → ℂ) (c : ℝ) (hc : 0 ≤ c) (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hδ : ∀ i, ∑' x : ℤ, ‖A (i + 1) x - A i x‖ₑ ^ (2 : ℝ)
        ≤ ENNReal.ofReal ((a i * c) ^ 2)) (k : ℕ → ℕ) (j : ℕ) :
    ∫⁻ x : ℤ, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖A i x - A (k j) x‖ₑ) ^ 2
        ∂MeasureTheory.Measure.count
      ≤ ENNReal.ofReal ((∑ i ∈ Finset.Ico (k j) (k (j + 1)), a i * c) ^ 2) := by
  classical
  have hb : ∀ t : ℕ, ∫⁻ x : ℤ, ‖A (t + 1) x - A t x‖ₑ ^ 2 ∂MeasureTheory.Measure.count
      ≤ (ENNReal.ofReal (a t * c)) ^ 2 := by
    intro t
    rw [MeasureTheory.lintegral_count]
    calc ∑' x : ℤ, ‖A (t + 1) x - A t x‖ₑ ^ 2
        = ∑' x : ℤ, ‖A (t + 1) x - A t x‖ₑ ^ (2 : ℝ) :=
          tsum_congr (fun x => (ENNReal.rpow_natCast _ 2).symm)
      _ ≤ ENNReal.ofReal ((a t * c) ^ 2) := hδ t
      _ = (ENNReal.ofReal (a t * c)) ^ 2 := ENNReal.ofReal_pow (mul_nonneg (ha t) hc) 2
  have hmeas : ∀ t ∈ Finset.Ico (k j) (k (j + 1)),
      Measurable (fun x : ℤ => ‖A (t + 1) x - A t x‖ₑ) := fun t _ => measurable_of_countable _
  have step2 := lintegral_sq_sum_le (μ := MeasureTheory.Measure.count)
      (s := Finset.Ico (k j) (k (j + 1))) (b := fun t x => ‖A (t + 1) x - A t x‖ₑ) hmeas
  calc ∫⁻ x : ℤ, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖A i x - A (k j) x‖ₑ) ^ 2
          ∂MeasureTheory.Measure.count
      ≤ ∫⁻ x : ℤ, (∑ t ∈ Finset.Ico (k j) (k (j + 1)), ‖A (t + 1) x - A t x‖ₑ) ^ 2
          ∂MeasureTheory.Measure.count := by
        refine lintegral_mono (fun x => ?_)
        exact pow_le_pow_left₀ bot_le (sup_sub_le_sum_increments A k j x) 2
    _ ≤ (∑ t ∈ Finset.Ico (k j) (k (j + 1)),
          (∫⁻ x : ℤ, ‖A (t + 1) x - A t x‖ₑ ^ 2 ∂MeasureTheory.Measure.count)
            ^ ((1 : ℝ) / 2)) ^ 2 := step2
    _ ≤ (∑ t ∈ Finset.Ico (k j) (k (j + 1)), ENNReal.ofReal (a t * c)) ^ 2 := by
        refine pow_le_pow_left₀ bot_le (Finset.sum_le_sum (fun t _ => ?_)) 2
        exact (ENNReal.rpow_le_rpow (hb t) (by norm_num)).trans_eq (sq_rpow_half _)
    _ = ENNReal.ofReal ((∑ t ∈ Finset.Ico (k j) (k (j + 1)), a t * c) ^ 2) := by
        rw [← ENNReal.ofReal_sum_of_nonneg (s := Finset.Ico (k j) (k (j + 1)))
              (f := fun t => a t * c) (fun t _ => mul_nonneg (ha t) hc),
            ENNReal.ofReal_pow (Finset.sum_nonneg (fun t _ => mul_nonneg (ha t) hc)) 2]

/-- **The block-oscillation functional is bounded by the increments** (the requested lemma). -/
theorem oscZ_le_of_increment_enorm_bound (A : ℕ → ℤ → ℂ) (c : ℝ) (hc : 0 ≤ c)
    (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hδ : ∀ i, ∑' x : ℤ, ‖A (i + 1) x - A i x‖ₑ ^ (2:ℝ)
        ≤ ENNReal.ofReal ((a i * c) ^ 2)) :
    ∀ (J : ℕ) (k : ℕ → ℕ), StrictMono k →
      Work.BourgainPlan.Oscillation.oscZ A J k
        ≤ ENNReal.ofReal (((∑ i ∈ Finset.range (k J), a i) * c) ^ 2) := by
  intro J k hk
  calc oscZ A J k
      = ∑ j ∈ Finset.range J, ∫⁻ x : ℤ,
          (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖A i x - A (k j) x‖ₑ) ^ 2
            ∂MeasureTheory.Measure.count := by
        unfold oscZ
        refine Finset.sum_congr rfl (fun j _ => ?_)
        exact lintegral_congr (fun x => ENNReal.rpow_natCast _ 2)
    _ ≤ ∑ j ∈ Finset.range J, ENNReal.ofReal
          ((∑ i ∈ Finset.Ico (k j) (k (j + 1)), a i * c) ^ 2) :=
        Finset.sum_le_sum (fun j _ => oscZ_block_le A c hc a ha hδ k j)
    _ = ENNReal.ofReal (∑ j ∈ Finset.range J,
          (∑ i ∈ Finset.Ico (k j) (k (j + 1)), a i * c) ^ 2) :=
        (ENNReal.ofReal_sum_of_nonneg
          (s := Finset.range J)
          (f := fun j => (∑ i ∈ Finset.Ico (k j) (k (j + 1)), a i * c) ^ 2)
          (fun j _ => sq_nonneg _)).symm
    _ ≤ ENNReal.ofReal ((∑ j ∈ Finset.range J,
          ∑ i ∈ Finset.Ico (k j) (k (j + 1)), a i * c) ^ 2) :=
        ENNReal.ofReal_le_ofReal (Finset.sum_sq_le_sq_sum_of_nonneg
          (f := fun j => ∑ i ∈ Finset.Ico (k j) (k (j + 1)), a i * c)
          (fun j _ => Finset.sum_nonneg (fun i _ => mul_nonneg (ha i) hc)))
    _ ≤ ENNReal.ofReal ((∑ i ∈ Finset.range (k J), a i * c) ^ 2) :=
        ENNReal.ofReal_le_ofReal (pow_le_pow_left₀
          (Finset.sum_nonneg (fun j _ => Finset.sum_nonneg
            (fun i _ => mul_nonneg (ha i) hc)))
          (sum_Ico_blocks_le k hk (fun i => a i * c) (fun i => mul_nonneg (ha i) hc) J) 2)
    _ = ENNReal.ofReal (((∑ i ∈ Finset.range (k J), a i) * c) ^ 2) := by
        rw [Finset.sum_mul]

end Work.BourgainPlan.Oscillation
