import Mathlib
import Submission.Work.BourgainPlan.Maximal.l2_defs

namespace Work.BourgainPlan.Maximal

open _root_.MeasureTheory _root_.Filter _root_.Finset
open scoped BigOperators ENNReal Topology

/-- Any index below `N` lies below the next dyadic power of `N`. -/
private lemma mem_range_lt_pow_succ_log {N i : ℕ} (hi : i < N) : i < 2 ^ (Nat.log 2 N + 1) := by
  have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) N
  omega

/-- The norm of a sum of nonnegative *real* summands (viewed in `ℂ`). -/
private lemma norm_ofReal_sum_norm {ι : Type*} (s : Finset ι) (h : ι → ℂ) :
    ‖∑ i ∈ s, (((‖h i‖ : ℝ) : ℂ))‖ = ∑ i ∈ s, ‖h i‖ := by
  rw [← Complex.ofReal_sum, Complex.norm_real]
  exact Real.norm_of_nonneg (Finset.sum_nonneg (fun i _ => norm_nonneg _))

/-- **The dyadic `2^k` maximal estimate implies the full `sup_N` estimate, for the polynomial
averages on `ℤ`.**  Pure plumbing: no circle method.  Fix any `P : ℤ[X]` (no hypothesis on `P` is
needed).  Assume the `ℓ²` maximal inequality for the polynomial averages restricted to the dyadic
lengths `N = 2^k`.  Then it holds for all lengths `N` at once.

Proof route: copy `Commons.Analysis.ExponentialSums.pow_dyadic_reduction_z` in
`Submission/Commons/Analysis/ExponentialSums/pure_power_kernel_maximal_l2.lean` (about 130 lines)
and replace the shift `(i : ℤ) ^ d` by `P.eval (i : ℤ)` throughout.  That proof uses **only** the
following facts, all of which are insensitive to the shift sequence: `‖g‖ ≥ 0`, the inclusion
`range N ⊆ range (2 ^ (Nat.log 2 N + 1))`, `inv_le_inv₀`, `pow_succ`, and the elementary pointwise
bound `(1/N)·Σ_{i<N} h (m + a i) ≤ 2 · (1/2^{k+1})·Σ_{i<2^{k+1}} h (m + a i)` for `h ≥ 0` and
`k = Nat.log 2 N` (monotonicity of the sum in the upper limit for nonnegative summands).  Set
`G n = ((‖g n‖ : ℝ) : ℂ)` so that the dyadic hypothesis may be applied to `G`, and finish with
`le_iSup`. -/
theorem poly_dyadic_reduction_z (P : Polynomial ℤ)
    (h : ∃ C : ℝ, 0 < C ∧ ∀ (g : ℤ → ℂ), (∃ s : Finset ℤ, ∀ n, n ∉ s → g n = 0) →
      ∫⁻ m : ℤ, (⨆ k : ℕ, ‖((2 : ℝ) ^ k)⁻¹
            * ∑ i ∈ Finset.range (2 ^ k), g (m + P.eval (i : ℤ))‖ₑ) ^ (2 : ℝ)
          ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C ^ 2) *
            ∫⁻ m : ℤ, ‖g m‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count) :
    ∃ C : ℝ, 0 < C ∧ ∀ (g : ℤ → ℂ), (∃ s : Finset ℤ, ∀ n, n ∉ s → g n = 0) →
      ∫⁻ m : ℤ, (⨆ N : ℕ, ‖(N : ℝ)⁻¹
            * ∑ i ∈ Finset.range N, g (m + P.eval (i : ℤ))‖ₑ) ^ (2 : ℝ)
          ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C ^ 2) *
            ∫⁻ m : ℤ, ‖g m‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count := by
  obtain ⟨C₀, hC₀, hbound⟩ := h
  refine ⟨2 * C₀, by linarith, ?_⟩
  intro g hg
  set G : ℤ → ℂ := fun n => ((‖g n‖ : ℝ) : ℂ) with hGdef
  have hG : ∃ s : Finset ℤ, ∀ n, n ∉ s → G n = 0 := by
    obtain ⟨s, hs⟩ := hg
    exact ⟨s, fun n hn => by simp [hGdef, hs n hn]⟩
  have hGnorm : ∀ n : ℤ, ‖G n‖ = ‖g n‖ := by
    intro n
    rw [hGdef, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
  set D : ℤ → ℝ≥0∞ := fun m => ⨆ k : ℕ, ‖((2 : ℝ) ^ k)⁻¹ *
      ∑ i ∈ Finset.range (2 ^ k), G (m + P.eval (i : ℤ))‖ₑ with hDdef
  have hkey : ∀ m : ℤ, ∀ N : ℕ,
      ‖(N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, g (m + P.eval (i : ℤ))‖ₑ ≤ 2 * D m := by
    intro m N
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      simp only [Nat.cast_zero, Finset.range_zero, Finset.sum_empty, mul_zero, enorm_zero]
      positivity
    · have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
      have h1 : ‖(N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, g (m + P.eval (i : ℤ))‖ₑ
          = ENNReal.ofReal ((N : ℝ)⁻¹
              * ‖∑ i ∈ Finset.range N, g (m + P.eval (i : ℤ))‖) := by
        rw [← ofReal_norm, Complex.norm_mul, Complex.norm_real,
          Real.norm_of_nonneg (by positivity)]
      rw [h1]
      set k : ℕ := Nat.log 2 N with hk
      have hk1 : 2 ^ k ≤ N := Nat.pow_log_le_self 2 (by omega)
      have hcast : ((2 : ℝ) ^ k) ≤ (N : ℝ) := by exact_mod_cast hk1
      have hsum : ∑ i ∈ Finset.range N, ‖g (m + P.eval (i : ℤ))‖
          ≤ ∑ i ∈ Finset.range (2 ^ (k + 1)), ‖g (m + P.eval (i : ℤ))‖ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro i hi
          rw [Finset.mem_range] at hi ⊢
          have hk2 := mem_range_lt_pow_succ_log hi
          simpa [hk] using hk2
        · intro i _ _; positivity
      have hcoef : (N : ℝ)⁻¹ ≤ 2 * ((2 : ℝ) ^ (k + 1))⁻¹ := by
        have h2k : 0 < ((2 : ℝ) ^ k) := by positivity
        have hle : (N : ℝ)⁻¹ ≤ ((2 : ℝ) ^ k)⁻¹ := (inv_le_inv₀ hNpos h2k).2 hcast
        calc (N : ℝ)⁻¹ ≤ ((2 : ℝ) ^ k)⁻¹ := hle
          _ = 2 * ((2 : ℝ) ^ (k + 1))⁻¹ := by rw [pow_succ]; field_simp
      have hstep : (N : ℝ)⁻¹ * ‖∑ i ∈ Finset.range N, g (m + P.eval (i : ℤ))‖
          ≤ 2 * (((2 : ℝ) ^ (k + 1))⁻¹
              * ∑ i ∈ Finset.range (2 ^ (k + 1)), ‖g (m + P.eval (i : ℤ))‖) := by
        calc (N : ℝ)⁻¹ * ‖∑ i ∈ Finset.range N, g (m + P.eval (i : ℤ))‖
            ≤ (N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, ‖g (m + P.eval (i : ℤ))‖ :=
              mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
          _ ≤ (N : ℝ)⁻¹ * ∑ i ∈ Finset.range (2 ^ (k + 1)), ‖g (m + P.eval (i : ℤ))‖ :=
              mul_le_mul_of_nonneg_left hsum (by positivity)
          _ ≤ (2 * ((2 : ℝ) ^ (k + 1))⁻¹)
                * ∑ i ∈ Finset.range (2 ^ (k + 1)), ‖g (m + P.eval (i : ℤ))‖ :=
              mul_le_mul_of_nonneg_right hcoef (Finset.sum_nonneg (fun i _ => norm_nonneg _))
          _ = 2 * (((2 : ℝ) ^ (k + 1))⁻¹
                * ∑ i ∈ Finset.range (2 ^ (k + 1)), ‖g (m + P.eval (i : ℤ))‖) := by ring
      refine le_trans (ENNReal.ofReal_le_ofReal hstep) ?_
      have h4 : ENNReal.ofReal (2 * (((2 : ℝ) ^ (k + 1))⁻¹
            * ∑ i ∈ Finset.range (2 ^ (k + 1)), ‖g (m + P.eval (i : ℤ))‖))
          = 2 * ENNReal.ofReal (((2 : ℝ) ^ (k + 1))⁻¹
            * ∑ i ∈ Finset.range (2 ^ (k + 1)), ‖g (m + P.eval (i : ℤ))‖) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        exact ENNReal.ofReal_ofNat 2
      rw [h4]
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      have h5 : ENNReal.ofReal (((2 : ℝ) ^ (k + 1))⁻¹
            * ∑ i ∈ Finset.range (2 ^ (k + 1)), ‖g (m + P.eval (i : ℤ))‖)
          = ‖((2 : ℝ) ^ (k + 1))⁻¹
              * ∑ i ∈ Finset.range (2 ^ (k + 1)), G (m + P.eval (i : ℤ))‖ₑ := by
        rw [← ofReal_norm]
        congr 1
        rw [Complex.norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        congr 1
        have hsumG : ∑ i ∈ Finset.range (2 ^ (k + 1)), G (m + P.eval (i : ℤ))
            = ∑ i ∈ Finset.range (2 ^ (k + 1)),
                ((‖g (m + P.eval (i : ℤ))‖ : ℝ) : ℂ) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [hGdef]
        rw [hsumG, norm_ofReal_sum_norm]
      rw [h5, hDdef]
      exact le_iSup (fun k : ℕ => ‖((2 : ℝ) ^ k)⁻¹
        * ∑ i ∈ Finset.range (2 ^ k), G (m + P.eval (i : ℤ))‖ₑ) (k + 1)
  have hsup : ∀ m : ℤ, (⨆ N : ℕ,
      ‖(N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, g (m + P.eval (i : ℤ))‖ₑ) ≤ 2 * D m :=
    fun m => iSup_le (fun N => hkey m N)
  calc ∫⁻ m : ℤ, (⨆ N : ℕ, ‖(N : ℝ)⁻¹
        * ∑ i ∈ Finset.range N, g (m + P.eval (i : ℤ))‖ₑ) ^ (2 : ℝ)
        ∂MeasureTheory.Measure.count
      ≤ ∫⁻ m, (2 * D m) ^ (2 : ℝ) ∂Measure.count :=
        lintegral_mono (fun m => ENNReal.rpow_le_rpow (hsup m) (by norm_num))
    _ = ∫⁻ m, 4 * (D m) ^ (2 : ℝ) ∂Measure.count := by
        refine lintegral_congr (fun m => ?_)
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
    _ = 4 * ∫⁻ m, (D m) ^ (2 : ℝ) ∂Measure.count :=
        lintegral_const_mul' 4 _ (by simp)
    _ ≤ 4 * (ENNReal.ofReal (C₀ ^ 2)
          * ∫⁻ m, ‖G m‖ₑ ^ (2 : ℝ) ∂Measure.count) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        simpa only [hDdef] using hbound G hG
    _ = ENNReal.ofReal ((2 * C₀) ^ 2)
          * ∫⁻ m, ‖g m‖ₑ ^ (2 : ℝ) ∂Measure.count := by
        have hGint : ∫⁻ m, ‖G m‖ₑ ^ (2 : ℝ) ∂Measure.count
            = ∫⁻ m, ‖g m‖ₑ ^ (2 : ℝ) ∂Measure.count := by
          refine lintegral_congr (fun m => ?_)
          have h' : ‖G m‖ = ‖g m‖ := hGnorm m
          rw [← ofReal_norm, ← ofReal_norm, h']
        have h4 : ENNReal.ofReal ((2 * C₀) ^ 2) = 4 * ENNReal.ofReal (C₀ ^ 2) := by
          rw [show ((2 * C₀) ^ 2 : ℝ) = 4 * C₀ ^ 2 by ring,
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
          congr 1
          exact ENNReal.ofReal_ofNat 4
        rw [hGint, h4]
        ring

end Work.BourgainPlan.Maximal
