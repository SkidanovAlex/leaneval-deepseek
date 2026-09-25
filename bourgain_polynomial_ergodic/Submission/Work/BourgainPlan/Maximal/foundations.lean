import Mathlib
import Submission.BourgainPlan.Interfaces
import Submission.Commons.Analysis.Maximal.lintegral_rpow_iSup_le_of_l2_linf

/-!
# Foundations for the discrete `ℓᵖ` maximal inequality

This file sets up the *bookkeeping* half of `Submission.BourgainPlan.MaximalStatement`:

* the polynomial density average `discAvg` is the explicit average `N⁻¹ ∑_{i<N} g (n + P i)`;
* the elementary `ℓ^∞` bound for a single average (the density kernel is a sub-probability vector);
* the **dominating absolute-value maximal operator** `absMax P`, whose maximal function *is* the
  honest maximal function of `|g|`;
* the reduction `p > 2 ⟸ p = 2` (Marcinkiewicz interpolation between the trivial `ℓ^∞` bound and
  the `ℓ²` bound), using `Commons.Analysis.Maximal.lintegral_rpow_iSup_le_of_l2_linf`;
* the split of `MaximalStatement` into its `ℓ²` half and its `1 < p < 2` half, and the assembly.
-/

open Filter Finset Function MeasureTheory
open scoped BigOperators ENNReal Topology

set_option autoImplicit false

namespace Work.BourgainPlan.Maximal

open Submission.BourgainPlan (discAvg NonnegOnNat)

/-- `Nat.succ` iterated `j` times. -/
lemma succ_iterate (j n : ℕ) : (Nat.succ^[j]) n = n + j := by
  induction j with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', ih]; simp [Nat.add_assoc]

/-- **The density-kernel average is the explicit polynomial average.**  For every integer
polynomial `P`, `N : ℕ` and `g : ℕ → ℝ`,
`discAvg P N g n = N⁻¹ ∑_{i<N} g (n + P i)`, with `P i` read as a natural number. -/
theorem discAvg_eq_sum (P : Polynomial ℤ) (N : ℕ) (g : ℕ → ℝ) (n : ℕ) :
    discAvg P N g n = (N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, g (n + (P.eval (i : ℤ)).toNat) := by
  unfold discAvg
  rw [show (∑ j ∈ Finset.range (Submission.polySupport P N),
        Submission.polyKernel P N j * g (n + j))
      = ∑ j ∈ Finset.range (Submission.polySupport P N),
        Submission.polyKernel P N j * g ((Nat.succ^[j]) n)
      from Finset.sum_congr rfl (fun j _ => by rw [succ_iterate])]
  rw [Submission.sum_polyKernel_mul_orbit P N g Nat.succ n]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => by rw [succ_iterate])

/-- The density kernel is nonnegative. -/
lemma polyKernel_nonneg (P : Polynomial ℤ) (N j : ℕ) : 0 ≤ Submission.polyKernel P N j := by
  unfold Submission.polyKernel; positivity

/-- The density kernel is a sub-probability vector. -/
lemma sum_polyKernel_le_one (P : Polynomial ℤ) (N : ℕ) :
    ∑ j ∈ Finset.range (Submission.polySupport P N), Submission.polyKernel P N j ≤ 1 := by
  have h := Submission.sum_abs_polyKernel_le_one P N
  rwa [Finset.sum_congr rfl (fun j _ => abs_of_nonneg (polyKernel_nonneg P N j))] at h

/-- **The elementary `ℓ^∞` bound for a single polynomial average.** -/
lemma abs_discAvg_le_of_bound (P : Polynomial ℤ) (N : ℕ) (g : ℕ → ℝ) (n : ℕ) {M : ℝ}
    (hM : ∀ k, |g k| ≤ M) : |discAvg P N g n| ≤ M := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  have h1 : |discAvg P N g n|
      ≤ ∑ j ∈ Finset.range (Submission.polySupport P N),
          Submission.polyKernel P N j * |g (n + j)| := by
    unfold discAvg
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    apply Finset.sum_le_sum
    intro j _
    rw [abs_mul, abs_of_nonneg (polyKernel_nonneg P N j)]
  have h2 : ∑ j ∈ Finset.range (Submission.polySupport P N),
        Submission.polyKernel P N j * |g (n + j)| ≤ M := by
    calc ∑ j ∈ Finset.range (Submission.polySupport P N),
          Submission.polyKernel P N j * |g (n + j)|
        ≤ ∑ j ∈ Finset.range (Submission.polySupport P N),
            Submission.polyKernel P N j * M := by
          apply Finset.sum_le_sum; intro j _
          exact mul_le_mul_of_nonneg_left (hM (n + j)) (polyKernel_nonneg P N j)
      _ = (∑ j ∈ Finset.range (Submission.polySupport P N),
            Submission.polyKernel P N j) * M := by rw [Finset.sum_mul]
      _ ≤ 1 * M := mul_le_mul_of_nonneg_right (sum_polyKernel_le_one P N) hM0
      _ = M := one_mul M
  exact le_trans h1 h2

/-! ## The dominating absolute-value maximal operator -/

/-- The **absolute-value maximal operator** of the polynomial density averages: the sum of the
density kernel against `|g|`.  It dominates the honest maximal function `sup_N |discAvg P N g|`
and it *is* the honest maximal function of `|g|`. -/
noncomputable def absMaxSum (P : Polynomial ℤ) (g : ℕ → ℝ) (n N : ℕ) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range (Submission.polySupport P N),
    ENNReal.ofReal (Submission.polyKernel P N j) * ‖g (n + j)‖ₑ

noncomputable def absMax (P : Polynomial ℤ) (g : ℕ → ℝ) (n : ℕ) : ℝ≥0∞ :=
  ⨆ N : ℕ, absMaxSum P g n N

lemma absMax_def (P : Polynomial ℤ) (g : ℕ → ℝ) (n : ℕ) :
    absMax P g n = ⨆ N : ℕ, absMaxSum P g n N := rfl

lemma enorm_mul_ofReal (c : ℝ) (hc : 0 ≤ c) (x : ℝ) :
    ENNReal.ofReal c * ‖x‖ₑ = ‖c * x‖ₑ := by
  rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs, abs_mul, abs_of_nonneg hc,
    ENNReal.ofReal_mul hc]

lemma absMax_zero (P : Polynomial ℤ) : absMax P 0 = 0 := by
  funext n
  simp [absMax, absMaxSum]

lemma absMax_add_le (P : Polynomial ℤ) (f h : ℕ → ℝ) :
    absMax P (f + h) ≤ absMax P f + absMax P h := by
  intro n
  unfold absMax
  apply iSup_le; intro N
  calc ∑ j ∈ Finset.range (Submission.polySupport P N),
        ENNReal.ofReal (Submission.polyKernel P N j) * ‖(f + h) (n + j)‖ₑ
      = ∑ j ∈ Finset.range (Submission.polySupport P N),
          ENNReal.ofReal (Submission.polyKernel P N j) * ‖f (n + j) + h (n + j)‖ₑ := by
        apply Finset.sum_congr rfl; intro j _; rw [Pi.add_apply]
    _ ≤ ∑ j ∈ Finset.range (Submission.polySupport P N),
          ENNReal.ofReal (Submission.polyKernel P N j)
            * (‖f (n + j)‖ₑ + ‖h (n + j)‖ₑ) := by
        apply Finset.sum_le_sum; intro j _
        exact mul_le_mul_right (enorm_add_le (f (n + j)) (h (n + j))) _
    _ = (∑ j ∈ Finset.range (Submission.polySupport P N),
            ENNReal.ofReal (Submission.polyKernel P N j) * ‖f (n + j)‖ₑ)
          + ∑ j ∈ Finset.range (Submission.polySupport P N),
            ENNReal.ofReal (Submission.polyKernel P N j) * ‖h (n + j)‖ₑ := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib]
    _ ≤ (⨆ N : ℕ, absMaxSum P f n N) + (⨆ N : ℕ, absMaxSum P h n N) :=
        add_le_add (le_iSup (absMaxSum P f n) N) (le_iSup (absMaxSum P h n) N)

lemma absMax_mono (P : Polynomial ℤ) (f h : ℕ → ℝ) (hf : ∀ n, |f n| ≤ |h n|) :
    absMax P f ≤ absMax P h := by
  intro n
  unfold absMax
  apply iSup_le; intro N
  calc ∑ j ∈ Finset.range (Submission.polySupport P N),
        ENNReal.ofReal (Submission.polyKernel P N j) * ‖f (n + j)‖ₑ
      ≤ ∑ j ∈ Finset.range (Submission.polySupport P N),
          ENNReal.ofReal (Submission.polyKernel P N j) * ‖h (n + j)‖ₑ := by
        apply Finset.sum_le_sum; intro j _
        refine mul_le_mul_right ?_ _
        rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_ofReal (hf (n + j))
    _ ≤ ⨆ N : ℕ, absMaxSum P h n N := le_iSup (absMaxSum P h n) N

lemma absMax_le_iSup_enorm (P : Polynomial ℤ) (g : ℕ → ℝ) (n : ℕ) :
    absMax P g n ≤ ⨆ k, ‖g k‖ₑ := by
  unfold absMax
  apply iSup_le; intro N
  have hsum : ∑ j ∈ Finset.range (Submission.polySupport P N),
      ENNReal.ofReal (Submission.polyKernel P N j) ≤ 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => polyKernel_nonneg P N j)]
    simpa using ENNReal.ofReal_le_ofReal (sum_polyKernel_le_one P N)
  calc ∑ j ∈ Finset.range (Submission.polySupport P N),
        ENNReal.ofReal (Submission.polyKernel P N j) * ‖g (n + j)‖ₑ
      ≤ ∑ j ∈ Finset.range (Submission.polySupport P N),
          ENNReal.ofReal (Submission.polyKernel P N j) * (⨆ k, ‖g k‖ₑ) := by
        apply Finset.sum_le_sum; intro j _
        exact mul_le_mul_right (le_iSup (fun k => ‖g k‖ₑ) (n + j)) _
    _ = (∑ j ∈ Finset.range (Submission.polySupport P N),
          ENNReal.ofReal (Submission.polyKernel P N j)) * (⨆ k, ‖g k‖ₑ) := by
        rw [Finset.sum_mul]
    _ ≤ 1 * (⨆ k, ‖g k‖ₑ) := mul_le_mul_left hsum _
    _ = ⨆ k, ‖g k‖ₑ := one_mul _

/-- `absMax P g` is the honest maximal function of `|g|`. -/
lemma absMax_eq (P : Polynomial ℤ) (g : ℕ → ℝ) (n : ℕ) :
    absMax P g n = ⨆ N : ℕ, ‖discAvg P N (fun k => |g k|) n‖ₑ := by
  unfold absMax absMaxSum
  apply iSup_congr
  intro N
  unfold discAvg
  have hnn : ∀ j ∈ Finset.range (Submission.polySupport P N),
      0 ≤ Submission.polyKernel P N j * |g (n + j)| :=
    fun j _ => mul_nonneg (polyKernel_nonneg P N j) (abs_nonneg _)
  rw [Real.enorm_eq_ofReal_abs]
  rw [abs_of_nonneg (Finset.sum_nonneg hnn)]
  rw [ENNReal.ofReal_sum_of_nonneg hnn]
  apply Finset.sum_congr rfl
  intro j _
  rw [ENNReal.ofReal_mul (polyKernel_nonneg P N j)]
  simp only [Real.enorm_eq_ofReal_abs]

/-- The honest maximal function is dominated by `absMax`. -/
lemma iSup_discAvg_le_absMax (P : Polynomial ℤ) (g : ℕ → ℝ) (n : ℕ) :
    (⨆ N : ℕ, ‖discAvg P N g n‖ₑ) ≤ absMax P g n := by
  unfold absMax
  apply iSup_le; intro N
  calc ‖discAvg P N g n‖ₑ
      ≤ absMaxSum P g n N := by
        unfold absMaxSum discAvg
        calc ‖∑ j ∈ Finset.range (Submission.polySupport P N),
              Submission.polyKernel P N j * g (n + j)‖ₑ
            ≤ ∑ j ∈ Finset.range (Submission.polySupport P N),
                ‖Submission.polyKernel P N j * g (n + j)‖ₑ := enorm_sum_le _ _
          _ = ∑ j ∈ Finset.range (Submission.polySupport P N),
                ENNReal.ofReal (Submission.polyKernel P N j) * ‖g (n + j)‖ₑ := by
              apply Finset.sum_congr rfl; intro j _
              exact (enorm_mul_ofReal _ (polyKernel_nonneg P N j) (g (n + j))).symm
    _ ≤ ⨆ N : ℕ, absMaxSum P g n N := le_iSup (absMaxSum P g n) N

/-! ## Interpolation: `p > 2` follows from `p = 2` -/

/-- **The `p > 2` half of the maximal inequality follows from the `ℓ²` bound.**  Marcinkiewicz
interpolation between the trivial `ℓ^∞` bound and the `ℓ²` bound, in the absolute-value form that
makes the interpolation lemma applicable. -/
theorem lp_gt_two_of_l2 (P : Polynomial ℤ) {C : ℝ} (hC : 0 < C)
    (hl2 : ∀ g : ℕ → ℝ, (∃ s : Finset ℕ, ∀ n, n ∉ s → g n = 0) →
      ∫⁻ n, (⨆ N : ℕ, ‖discAvg P N g n‖ₑ) ^ (2 : ℝ) ∂Measure.count
        ≤ ENNReal.ofReal (C ^ 2) * ∫⁻ n, ‖g n‖ₑ ^ (2 : ℝ) ∂Measure.count)
    {p : ℝ} (hp : 2 < p) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ g : ℕ → ℝ, (∃ s : Finset ℕ, ∀ n, n ∉ s → g n = 0) →
      ∫⁻ n, (⨆ N : ℕ, ‖discAvg P N g n‖ₑ) ^ p ∂Measure.count
        ≤ ENNReal.ofReal (C' ^ p) * ∫⁻ n, ‖g n‖ₑ ^ p ∂Measure.count := by
  obtain ⟨C', hC'pos, hC'⟩ :=
    Commons.Analysis.Maximal.lintegral_rpow_iSup_le_of_l2_linf (T := absMax P) hC
      (absMax_zero P) (absMax_add_le P) (absMax_mono P) (absMax_le_iSup_enorm P)
      (fun g hg => by
        obtain ⟨s, hs⟩ := hg
        simp_rw [absMax_eq]
        simpa only [Real.enorm_eq_ofReal_abs, abs_abs] using
          hl2 (fun k => |g k|) ⟨s, fun n hn => by simp [hs n hn]⟩) hp
  refine ⟨C', hC'pos, fun g hg => ?_⟩
  calc ∫⁻ n, (⨆ N : ℕ, ‖discAvg P N g n‖ₑ) ^ p ∂Measure.count
      ≤ ∫⁻ n, (absMax P g n) ^ p ∂Measure.count :=
        lintegral_mono (fun n => ENNReal.rpow_le_rpow (iSup_discAvg_le_absMax P g n)
          (by linarith : (0:ℝ) ≤ p))
    _ ≤ ENNReal.ofReal (C' ^ p) * ∫⁻ n, ‖g n‖ₑ ^ p ∂Measure.count := hC' g hg

/-! ## Splitting `MaximalStatement` into its two halves -/

/-- The `ℓ²` maximal inequality for every nonneg polynomial (the `p = 2` case of
`MaximalStatement`, in the form in which the circle method produces it). -/
def L2Statement : Prop :=
  ∀ P : Polynomial ℤ, NonnegOnNat P → ∃ C : ℝ, 0 < C ∧
    ∀ g : ℕ → ℝ, (∃ s : Finset ℕ, ∀ n, n ∉ s → g n = 0) →
      ∫⁻ n, (⨆ N : ℕ, ‖discAvg P N g n‖ₑ) ^ (2 : ℝ) ∂Measure.count
        ≤ ENNReal.ofReal (C ^ 2) * ∫⁻ n, ‖g n‖ₑ ^ (2 : ℝ) ∂Measure.count

/-- The `1 < p < 2` case of `MaximalStatement` (Bourgain's §7). -/
def SubTwoStatement : Prop :=
  ∀ P : Polynomial ℤ, NonnegOnNat P → ∀ p : ℝ, 1 < p → p < 2 → ∃ C : ℝ, 0 ≤ C ∧
    ∀ g : ℕ → ℝ, (∃ s : Finset ℕ, ∀ n, n ∉ s → g n = 0) →
      ∫⁻ n, (⨆ N : ℕ, ‖discAvg P N g n‖ₑ) ^ p ∂Measure.count
        ≤ ENNReal.ofReal (C ^ p) * ∫⁻ n, ‖g n‖ₑ ^ p ∂Measure.count

/-- **Assembly of the maximal inequality from its `ℓ²` half and its `1 < p < 2` half.** -/
theorem maximal_statement_of_l2_and_subtwo (h2 : L2Statement) (hsub : SubTwoStatement) :
    Submission.BourgainPlan.MaximalStatement := by
  intro P hP p hp
  rcases lt_trichotomy p 2 with hlt | heq | hgt
  · obtain ⟨C, hC, hb⟩ := hsub P hP p hp hlt
    exact ⟨C, hC, hb⟩
  · subst heq
    obtain ⟨C, hCpos, hb⟩ := h2 P hP
    refine ⟨C, hCpos.le, fun g hg => ?_⟩
    rw [Real.rpow_ofNat]
    exact hb g hg
  · obtain ⟨C, hCpos, hb⟩ := h2 P hP
    obtain ⟨C', hC'pos, hb'⟩ := lp_gt_two_of_l2 P hCpos hb hgt
    exact ⟨C', hC'pos.le, hb'⟩

/-- **Assembly with the `ℓ²` statement in the shape in which the circle method produces it.**
`hk` is exactly `Work.BourgainPlan.Maximal.kernel_l2` quantified over all `P`; `hsub` is the
`1 < p < 2` half (Bourgain §7).  This is the final wiring of the maximal statement. -/
theorem maximal_statement_of_kernel_l2
    (hk : ∀ P : Polynomial ℤ, NonnegOnNat P → ∃ C : ℝ, 0 < C ∧
      ∀ g : ℕ → ℝ, (∃ s : Finset ℕ, ∀ n, n ∉ s → g n = 0) →
        ∫⁻ n, (⨆ N : ℕ, ‖discAvg P N g n‖ₑ) ^ (2 : ℝ) ∂Measure.count
          ≤ ENNReal.ofReal (C ^ 2) * ∫⁻ n, ‖g n‖ₑ ^ (2 : ℝ) ∂Measure.count)
    (hsub : SubTwoStatement) : Submission.BourgainPlan.MaximalStatement :=
  maximal_statement_of_l2_and_subtwo (fun P hP => hk P hP) hsub

end Work.BourgainPlan.Maximal
