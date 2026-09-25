import Mathlib
import Submission.Work.BourgainPlan.Maximal.foundations
import Submission.Work.BourgainPlan.Maximal.z_defs
import Submission.Work.BourgainPlan.Maximal.z_transfer

namespace Work.BourgainPlan.Maximal

open MeasureTheory Set Finset
open scoped ENNReal BigOperators

set_option autoImplicit false

open Submission.BourgainPlan (discAvg NonnegOnNat)

/-! ## The three intermediate forms of the `1 < p < 2` inequality

We phrase the hypothesis of the reduction and the intermediate conclusions as `Prop`s so that the
chain of three transfers composes without any `simpa` gymnastics. -/

/-- The **dyadic `ℤ`-form** for complex-valued functions: the shape in which the circle method
delivers its estimates (this is the hypothesis `H` of `subtwo_of_dyadic_z`). -/
def DyadicZStatement (P : Polynomial ℤ) (p : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ g : ℤ → ℂ, (∃ s : Finset ℤ, ∀ n, n ∉ s → g n = 0) →
    MeasureTheory.lintegral MeasureTheory.Measure.count (fun m : ℤ =>
      (iSup fun k : ℕ => ‖((2 : ℝ) ^ k)⁻¹ *
        Finset.sum (Finset.range (2 ^ k)) (fun i => g (m + P.eval (i : ℤ)))‖ₑ) ^ p)
      ≤ ENNReal.ofReal (C ^ p) * MeasureTheory.lintegral MeasureTheory.Measure.count
          (fun m : ℤ => ‖g m‖ₑ ^ p)

/-- The **full `sup_N` form** for complex-valued functions on `ℤ`. -/
def AllZStatementC (P : Polynomial ℤ) (p : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ g : ℤ → ℂ, (∃ s : Finset ℤ, ∀ n, n ∉ s → g n = 0) →
    MeasureTheory.lintegral MeasureTheory.Measure.count (fun m : ℤ =>
      (iSup fun N : ℕ => ‖(N : ℝ)⁻¹ *
        Finset.sum (Finset.range N) (fun i => g (m + P.eval (i : ℤ)))‖ₑ) ^ p)
      ≤ ENNReal.ofReal (C ^ p) * MeasureTheory.lintegral MeasureTheory.Measure.count
          (fun m : ℤ => ‖g m‖ₑ ^ p)

/-- The **full `sup_N` form** for real-valued functions on `ℤ` (the `ℤ`-form of the target
inequality, matching `maxFZ` of `z_defs`). -/
def AllZStatementReal (P : Polynomial ℤ) (p : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ g : ℤ → ℝ, (∃ s : Finset ℤ, ∀ n, n ∉ s → g n = 0) →
    MeasureTheory.lintegral MeasureTheory.Measure.count (fun m : ℤ => (maxFZ P g m) ^ p)
      ≤ ENNReal.ofReal (C ^ p) * MeasureTheory.lintegral MeasureTheory.Measure.count
          (fun m : ℤ => ‖g m‖ₑ ^ p)

/-! ## Elementary helpers -/

private lemma mem_range_lt_pow_succ_log' {N i : ℕ} (hi : i < N) : i < 2 ^ (Nat.log 2 N + 1) := by
  have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) N
  omega

/-- The norm of a finite sum of nonnegative *real* summands, viewed in `ℂ`. -/
private lemma norm_ofReal_sum_norm_shift (s : Finset ℕ) (P : Polynomial ℤ) (g : ℤ → ℂ)
    (m : ℤ) :
    ‖∑ i ∈ s, ((‖g (m + P.eval (i : ℤ))‖ : ℝ) : ℂ)‖
      = ∑ i ∈ s, ‖g (m + P.eval (i : ℤ))‖ := by
  rw [← Complex.ofReal_sum, Complex.norm_real]
  exact Real.norm_of_nonneg (Finset.sum_nonneg (fun i _ => norm_nonneg _))

/-- The `enorm` of a real number seen in `ℂ`. -/
private lemma enorm_ofReal_complex (x : ℝ) : ‖(x : ℂ)‖ₑ = ‖x‖ₑ := by
  rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, ← Real.enorm_eq_ofReal_abs]

/-- **`discAvgZ` is the real part of the complex average**, under `NonnegOnNat P` (which makes
`((P.eval i).toNat : ℤ) = P.eval i` for `i : ℕ`). -/
private lemma discAvgZ_ofReal_eq (P : Polynomial ℤ) (hP : NonnegOnNat P) (N : ℕ)
    (g : ℤ → ℝ) (m : ℤ) :
    ((discAvgZ P N g m : ℝ) : ℂ)
      = (N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, ((g (m + P.eval (i : ℤ)) : ℝ) : ℂ) := by
  have hsum : (∑ i ∈ Finset.range N, g (m + ((P.eval (i : ℤ)).toNat : ℤ)))
      = ∑ i ∈ Finset.range N, g (m + P.eval (i : ℤ)) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Int.toNat_of_nonneg (hP i)]
  unfold discAvgZ
  rw [hsum]
  push_cast
  ring

/-! ## Step 1: dyadic `⟹` all `N` (complex-valued, on `ℤ`) -/

/-- **Dyadic reduction at an arbitrary exponent `p > 0`.**  If the dyadic polynomial averages on
`ℤ` satisfy the `ℓᵖ` maximal inequality, then so do the full averages: for `2 ^ k ≤ N < 2 ^ (k+1)`,
`|A_N g| ≤ 2 (A_{2^(k+1)} |g|)` pointwise.  Purely elementary: no circle method. -/
theorem dyadic_to_all_Z (P : Polynomial ℤ) (p : ℝ) (hp : 0 < p)
    (h : DyadicZStatement P p) : AllZStatementC P p := by
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
          have hk2 := mem_range_lt_pow_succ_log' hi
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
        rw [hGdef]
        exact (norm_ofReal_sum_norm_shift _ P g m).symm
      rw [h5, hDdef]
      exact le_iSup (fun k : ℕ => ‖((2 : ℝ) ^ k)⁻¹
        * ∑ i ∈ Finset.range (2 ^ k), G (m + P.eval (i : ℤ))‖ₑ) (k + 1)
  have hsup : ∀ m : ℤ, (⨆ N : ℕ,
      ‖(N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, g (m + P.eval (i : ℤ))‖ₑ) ≤ 2 * D m :=
    fun m => iSup_le (fun N => hkey m N)
  calc MeasureTheory.lintegral MeasureTheory.Measure.count (fun m : ℤ =>
        (iSup fun N : ℕ => ‖(N : ℝ)⁻¹ *
          Finset.sum (Finset.range N) (fun i => g (m + P.eval (i : ℤ)))‖ₑ) ^ p)
      ≤ ∫⁻ m, (2 * D m) ^ p ∂Measure.count :=
        lintegral_mono (fun m => ENNReal.rpow_le_rpow (hsup m) (le_of_lt hp))
    _ = ∫⁻ m, (2 : ℝ≥0∞) ^ p * (D m) ^ p ∂Measure.count := by
        refine lintegral_congr (fun m => ?_)
        rw [ENNReal.mul_rpow_of_nonneg _ _ (le_of_lt hp)]
    _ = (2 : ℝ≥0∞) ^ p * ∫⁻ m, (D m) ^ p ∂Measure.count :=
        lintegral_const_mul' _ _ (by simp)
    _ ≤ (2 : ℝ≥0∞) ^ p * (ENNReal.ofReal (C₀ ^ p)
          * ∫⁻ m, ‖G m‖ₑ ^ p ∂Measure.count) := by
        refine mul_le_mul_of_nonneg_left ?_ (by simp)
        simpa only [hDdef] using hbound G hG
    _ = ENNReal.ofReal ((2 * C₀) ^ p)
          * ∫⁻ m, ‖g m‖ₑ ^ p ∂Measure.count := by
        have hGint : ∫⁻ m, ‖G m‖ₑ ^ p ∂Measure.count
            = ∫⁻ m, ‖g m‖ₑ ^ p ∂Measure.count := by
          refine lintegral_congr (fun m => ?_)
          have h' : ‖G m‖ = ‖g m‖ := hGnorm m
          rw [← ofReal_norm, ← ofReal_norm, h']
        have h4 : ENNReal.ofReal ((2 * C₀) ^ p)
            = (2 : ℝ≥0∞) ^ p * ENNReal.ofReal (C₀ ^ p) := by
          rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hC₀,
            ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) p),
            (ENNReal.ofReal_rpow_of_nonneg (x := 2) (p := p)
              (by norm_num : (0:ℝ) ≤ 2) (le_of_lt hp)).symm,
            ENNReal.ofReal_ofNat]
        rw [hGint, h4]
        ring

/-! ## Step 2: complex-valued `⟹` real-valued on `ℤ` -/

/-- **Restriction to real-valued functions.**  The complex-valued maximal inequality on `ℤ`
implies the real-valued one (apply it to the complexification of the real function). -/
theorem Z_complex_to_real (P : Polynomial ℤ) (hP : NonnegOnNat P) (p : ℝ)
    (h : AllZStatementC P p) : AllZStatementReal P p := by
  obtain ⟨C, hC, hbound⟩ := h
  refine ⟨C, hC, ?_⟩
  intro g hg
  obtain ⟨s, hs⟩ := hg
  set G : ℤ → ℂ := fun n => ((g n : ℝ) : ℂ) with hGdef
  have hGsupp : ∃ s : Finset ℤ, ∀ n, n ∉ s → G n = 0 :=
    ⟨s, fun n hn => by simp [hGdef, hs n hn]⟩
  have hb := hbound G hGsupp
  have hpt : ∀ m : ℤ, (⨆ N : ℕ, ‖(N : ℝ)⁻¹ * ∑ i ∈ Finset.range N,
        G (m + P.eval (i : ℤ))‖ₑ) = maxFZ P g m := by
    intro m
    unfold maxFZ
    refine iSup_congr (fun N => ?_)
    have key : ((discAvgZ P N g m : ℝ) : ℂ)
        = (N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, G (m + P.eval (i : ℤ)) := by
      rw [hGdef]
      exact discAvgZ_ofReal_eq P hP N g m
    rw [← key, enorm_ofReal_complex]
  calc MeasureTheory.lintegral MeasureTheory.Measure.count (fun m : ℤ => (maxFZ P g m) ^ p)
      = MeasureTheory.lintegral MeasureTheory.Measure.count (fun m : ℤ =>
          (iSup fun N : ℕ => ‖(N : ℝ)⁻¹ *
            Finset.sum (Finset.range N) (fun i => G (m + P.eval (i : ℤ)))‖ₑ) ^ p) := by
        refine lintegral_congr (fun m => ?_)
        rw [← hpt m]
    _ ≤ ENNReal.ofReal (C ^ p) * MeasureTheory.lintegral MeasureTheory.Measure.count
          (fun m : ℤ => ‖G m‖ₑ ^ p) := hb
    _ = ENNReal.ofReal (C ^ p) * MeasureTheory.lintegral MeasureTheory.Measure.count
          (fun m : ℤ => ‖g m‖ₑ ^ p) := by
        congr 1
        refine lintegral_congr (fun m => ?_)
        rw [hGdef]
        exact congrArg (fun t : ℝ≥0∞ => t ^ p) (enorm_ofReal_complex (g m))

/-! ## Step 3: `ℤ ⟹ ℕ` at the restricted range `1 < p < 2` -/

/-- **The `ℤ`-form of the `1 < p < 2` maximal inequality implies `SubTwoStatement`.**  Verbatim
transfer `z_transfer`, but with the exponent restricted to `1 < p < 2` (which is all the
`subtwo`-half of the maximal inequality needs). -/
theorem z_transfer_subtwo
    (hZ : ∀ P : Polynomial ℤ, NonnegOnNat P → ∀ p : ℝ, 1 < p → p < 2 →
      AllZStatementReal P p) : SubTwoStatement := by
  intro P hP p hp hp2
  obtain ⟨C, hC, hbound⟩ := hZ P hP p hp hp2
  refine ⟨C, hC, ?_⟩
  intro g hg
  obtain ⟨s, hs⟩ := hg
  obtain ⟨s', hs'⟩ := liftZ_support g s hs
  have hp0 : (0 : ℝ) < p := by linarith
  have hG := hbound (liftZ g) ⟨s', hs'⟩
  have h1 : ∫⁻ n : ℕ, (⨆ N : ℕ, ‖discAvg P N g n‖ₑ) ^ p ∂Measure.count
      = ∫⁻ m : ℤ, (if 0 ≤ m then (⨆ N : ℕ, ‖discAvg P N g m.toNat‖ₑ) ^ p else 0)
          ∂Measure.count :=
    lintegral_count_nat_int (fun n => (⨆ N : ℕ, ‖discAvg P N g n‖ₑ) ^ p)
  have h2 : ∫⁻ m : ℤ, (if 0 ≤ m then (⨆ N : ℕ, ‖discAvg P N g m.toNat‖ₑ) ^ p else 0)
        ∂Measure.count
      ≤ ∫⁻ m : ℤ, (maxFZ P (liftZ g) m) ^ p ∂Measure.count := by
    apply MeasureTheory.lintegral_mono
    intro m
    dsimp only
    by_cases hm : 0 ≤ m
    · rw [if_pos hm]
      have heq : (⨆ N : ℕ, ‖discAvg P N g m.toNat‖ₑ) = maxFZ P (liftZ g) m := by
        rw [← maxFZ_liftZ P g m.toNat, Int.toNat_of_nonneg hm]
      rw [heq]
    · rw [if_neg hm]
      positivity
  rw [h1]
  refine le_trans h2 ?_
  refine le_trans hG ?_
  exact le_of_eq (by rw [liftZ_norm_lintegral g hp0])

/-! ## The target -/

/-- **Reduction of the target to the dyadic `ℤ`-form** (the shape in which the circle method
delivers its estimates: compare the conclusion of `Work.BourgainPlan.Maximal.poly_dyadic_of_model`,
which is exactly this inequality at `p = 2`).

If for every `P : ℤ[X]` nonnegative on `ℕ` and every `1 < p < 2` the *dyadic* polynomial averages
on `ℤ`, `T_k g (m) = (2^k)⁻¹ Σ_{i < 2^k} g (m + P(i))`, satisfy the `ℓᵖ(ℤ)` maximal inequality
`∫⁻_m (sup_k ‖T_k g m‖) ^ p ≤ C^p ∫⁻_m ‖g m‖ ^ p` for every finitely supported `g : ℤ → ℂ`, then
`Work.BourgainPlan.Maximal.SubTwoStatement` holds.

Proof route (three elementary steps, no analysis):
1. *Dyadic ⟹ all `N`*: for `2^k ≤ N < 2^{k+1}` and `G := (fun m => (‖g m‖ : ℂ))`,
   `|discAvgZ P N g m| ≤ 2 · ‖discAvgZ P (2^{k+1}) G m‖` (apply the hypothesis to the finitely
   supported `G`, whose `ℓᵖ` norm equals that of `g`); hence the full `sup_N` is dominated by twice
   the dyadic one, giving constant `2C`.
2. *`ℂ`-valued ⟹ `ℝ`-valued* on `ℤ` (restrict to real `g`).
3. *`ℤ ⟹ ℕ`*: mirror `z_transfer` (`liftZ`, `discAvgZ_liftZ`, `liftZ_support`,
   `liftZ_norm_lintegral`), which is stated for real `ℤ`-functions; note `z_transfer` itself is
   stated for the *full* `MaximalStatementZ` (all `p > 1`), so here one repeats its argument
   restricted to `1 < p < 2` rather than quoting it. -/
theorem subtwo_of_dyadic_z
    (H : ∀ (P : Polynomial ℤ), Submission.BourgainPlan.NonnegOnNat P → ∀ p : ℝ, 1 < p → p < 2 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : ℤ → ℂ), (∃ s : Finset ℤ, ∀ n, n ∉ s → g n = 0) →
        MeasureTheory.lintegral MeasureTheory.Measure.count
            (fun m : ℤ => ENNReal.rpow (iSup fun k : ℕ =>
              ‖((2 : ℝ) ^ k)⁻¹ * ∑ i ∈ Finset.range (2 ^ k), g (m + P.eval (i : ℤ))‖ₑ) p)
          ≤ ENNReal.ofReal (C ^ p) *
            MeasureTheory.lintegral MeasureTheory.Measure.count (fun m : ℤ => ENNReal.rpow (‖g m‖ₑ) p)) :
    Work.BourgainPlan.Maximal.SubTwoStatement := by
  refine z_transfer_subtwo (fun P hP p hp hp2 => ?_)
  have h0 : DyadicZStatement P p := H P hP p hp hp2
  exact Z_complex_to_real P hP p (dyadic_to_all_Z P p (by linarith) h0)

end Work.BourgainPlan.Maximal
