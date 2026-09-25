import Mathlib
import Submission.Work.BourgainPlan.Maximal.kmsz_variation_defs
import Submission.Work.BourgainPlan.Maximal.rhoVarReductions
import Submission.Work.BourgainPlan.Maximal.varRho_geometric
import Submission.Work.BourgainPlan.Maximal.varRho_le_sum_increments

/-!
# The summation step (6.17) of the minor-arc half of the assembly

Kosz–Mirek–Słomian–Zhang (arXiv:2606.12663), (6.17): if a family `(a k)_{k ∈ ℕ}` of `ℤ`-indexed
functions has geometrically decaying `ℓᵖ` norms, `eLpNorm (a k) p ≤ C r^k` with `0 ≤ r < 1`, then
the `ℓᵖ(ℤ)` norm of the pointwise `ρ`-variation over the whole scale family is bounded by
`C (1 + r) / (1 - r)`.

The two ingredients are the landed comparison `varRho_le_sum_increments` (the `ρ`-variation is
dominated by the total variation of the consecutive increments) and the triangle inequality for
infinite sums in `ℓᵖ` (`eLpNorm_tsum_le_tsum_eLpNorm`, proved here for `ℝ≥0∞`-valued functions by
monotone convergence).
-/

open MeasureTheory
open scoped BigOperators ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.BourgainPlan.Maximal

noncomputable section

/-- **Every function out of `ℤ` is measurable** for the canonical (Borel/discrete) measurable
space on `ℤ`, because every subset of `ℤ` is countable, hence measurable. -/
lemma measurable_of_int {β : Type*} [MeasurableSpace β] (f : ℤ → β) : Measurable f :=
  fun s _ => (Set.to_countable (f ⁻¹' s)).measurableSet

/-- **The power of a supremum is the supremum of the powers** in `ℝ≥0∞` for a positive exponent.
`x ↦ x^q` is an order isomorphism for `q > 0`, hence preserves suprema. -/
lemma iSup_rpow_eq_of_pos {ι : Type*} (f : ι → ℝ≥0∞) {q : ℝ} (hq : 0 < q) :
    (⨆ i, f i) ^ q = ⨆ i, f i ^ q := by
  refine le_antisymm ?_ (iSup_le fun i => ENNReal.rpow_le_rpow (le_iSup f i) hq.le)
  rw [← ENNReal.le_rpow_inv_iff hq]
  refine iSup_le fun i => ?_
  rw [ENNReal.le_rpow_inv_iff hq]
  exact le_iSup (fun i => f i ^ q) i

/-- **The full `ρ`-variation is dominated by the total variation of the consecutive increments.**
This is `varRho_le_sum_increments` combined with the supremum over the index windows. -/
lemma varRhoAll_le_tsum_enorm {E : Type*} [SeminormedAddCommGroup E] {ρ : ℝ} (hρ : 1 ≤ ρ)
    (b : ℕ → E) :
    varRhoAll ρ b ≤ ∑' k : ℕ, ‖b (k + 1) - b k‖ₑ := by
  refine iSup_le fun K => ?_
  exact (varRho_le_sum_increments hρ b).trans (ENNReal.sum_le_tsum _)

/-- **The triangle inequality for infinite sums in `ℓᵖ`, `ℝ≥0∞`-valued.** If `1 ≤ p < ∞` then the
`eLpNorm` of the pointwise sum of a series is at most the sum of the `eLpNorm`s.  The proof passes
through the monotone convergence theorem: the series is the supremum of its partial sums and
`eLpNorm (⨆ n f n) p = ⨆ n eLpNorm (f n) p` for a monotone sequence of nonnegative functions. -/
lemma eLpNorm_tsum_le_tsum_eLpNorm {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {g : ℕ → α → ℝ≥0∞} {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hptop : p ≠ ∞)
    (hg : ∀ k, Measurable (g k)) :
    eLpNorm (fun x => ∑' k, g k x) p μ ≤ ∑' k, eLpNorm (g k) p μ := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp1).ne'
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hptop
  have hFmeas : ∀ n : ℕ, Measurable fun x => (∑ k ∈ Finset.range n, g k x) ^ p.toReal :=
    fun n => ENNReal.continuous_rpow_const.measurable.comp
      (Finset.measurable_sum _ fun k _ => hg k)
  have hFmono : Monotone fun n : ℕ => fun x => (∑ k ∈ Finset.range n, g k x) ^ p.toReal := by
    intro n m hnm x
    refine ENNReal.rpow_le_rpow (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) hq.le
    · exact Finset.range_subset_range.mpr hnm
    · intro k _ _; exact bot_le
  calc eLpNorm (fun x => ∑' k, g k x) p μ
      = (∫⁻ x, (∑' k, g k x) ^ p.toReal ∂μ) ^ (1 / p.toReal) := by
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop
          (Measurable.ennreal_tsum hg).aestronglyMeasurable]
        simp only [enorm_eq_self]
    _ = (∫⁻ x, ⨆ n, (∑ k ∈ Finset.range n, g k x) ^ p.toReal ∂μ) ^ (1 / p.toReal) := by
        refine congrArg (fun t : ℝ≥0∞ => t ^ (1 / p.toReal)) ?_
        refine lintegral_congr fun x => ?_
        rw [ENNReal.tsum_eq_iSup_nat]
        exact iSup_rpow_eq_of_pos _ hq
    _ = (⨆ n, ∫⁻ x, (∑ k ∈ Finset.range n, g k x) ^ p.toReal ∂μ) ^ (1 / p.toReal) :=
        congrArg (fun t : ℝ≥0∞ => t ^ (1 / p.toReal))
          (lintegral_iSup (f := fun n x => (∑ k ∈ Finset.range n, g k x) ^ p.toReal)
            hFmeas hFmono)
    _ = ⨆ n, (∫⁻ x, (∑ k ∈ Finset.range n, g k x) ^ p.toReal ∂μ) ^ (1 / p.toReal) :=
        iSup_rpow_eq_of_pos _ (one_div_pos.mpr hq)
    _ ≤ ∑' k, eLpNorm (g k) p μ := by
        refine iSup_le fun n => ?_
        calc (∫⁻ x, (∑ k ∈ Finset.range n, g k x) ^ p.toReal ∂μ) ^ (1 / p.toReal)
            = eLpNorm (∑ k ∈ Finset.range n, g k) p μ := by
              rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop
                (by rw [Finset.sum_fn]; exact (Finset.measurable_sum _ fun k _ => hg k).aestronglyMeasurable)]
              simp only [enorm_eq_self, Finset.sum_apply]
          _ ≤ ∑ k ∈ Finset.range n, eLpNorm (g k) p μ :=
              eLpNorm_sum_le hp1
          _ ≤ ∑' k, eLpNorm (g k) p μ := ENNReal.sum_le_tsum _

/-- KMSZ (6.17), the summation step of the minor-arc half of the assembly, in reusable form: if the scales of a family `(a k)_{k ∈ ℕ}` of `ℤ`-indexed functions have geometrically decaying `ℓᵖ` norms, `eLpNorm (a k) p ≤ C r^k` with `0 ≤ r < 1`, then the `ℓᵖ(ℤ)` norm of the pointwise `ρ`-variation over the whole scale family is bounded by `C(1+r)/(1-r)`.

Proof: pointwise, `varRhoAll ρ (fun k => a k m) ≤ Σ_k ‖a (k+1) m − a k m‖` (the landed `varRho_le_sum_increments` plus the supremum over windows), so it suffices to bound `eLpNorm (Σ_k ‖a (k+1) − a k‖) p` by the sum of the `eLpNorm`s (triangle inequality for infinite sums, e.g. via finite truncations and monotone convergence), and to sum the geometric series `Σ_k C(r^{k+1} + r^k) = C(1+r)/(1-r)`. -/
theorem eLpNorm_varRhoAll_le_geometric {p ρ C r : ℝ} (hp : 1 ≤ p) (hρ : 1 ≤ ρ)
    (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1) (a : ℕ → ℤ → ℂ)
    (ha : ∀ k : ℕ, MeasureTheory.eLpNorm (a k) (ENNReal.ofReal p) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (C * r ^ k)) :
    MeasureTheory.eLpNorm (fun m : ℤ => Work.BourgainPlan.Maximal.varRhoAll ρ
        (fun k : ℕ => a k m)) (ENNReal.ofReal p) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (C * (1 + r) * (1 - r)⁻¹) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr hp
  have hptop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hrnorm : ‖r‖ < 1 := by rw [Real.norm_of_nonneg hr0]; exact hr1
  have hsumm : Summable fun k : ℕ => C * (1 + r) * r ^ k :=
    (summable_geometric_of_norm_lt_one hrnorm).mul_left _
  -- the per-scale `ℓᵖ` bound for the consecutive increments
  have hge : ∀ k : ℕ,
      eLpNorm (fun m : ℤ => ‖a (k + 1) m - a k m‖ₑ) (ENNReal.ofReal p) Measure.count
        ≤ ENNReal.ofReal (C * (1 + r) * r ^ k) := by
    intro k
    calc eLpNorm (fun m : ℤ => ‖a (k + 1) m - a k m‖ₑ) (ENNReal.ofReal p) Measure.count
        = eLpNorm (fun m : ℤ => a (k + 1) m - a k m) (ENNReal.ofReal p) Measure.count := by
          rw [eLpNorm_enorm _ AEStronglyMeasurable.of_discrete]
      _ ≤ eLpNorm (a (k + 1)) (ENNReal.ofReal p) Measure.count
            + eLpNorm (a k) (ENNReal.ofReal p) Measure.count :=
          eLpNorm_sub_le hp1
      _ ≤ ENNReal.ofReal (C * r ^ (k + 1)) + ENNReal.ofReal (C * r ^ k) :=
          add_le_add (ha (k + 1)) (ha k)
      _ = ENNReal.ofReal (C * (1 + r) * r ^ k) := by
          rw [← ENNReal.ofReal_add (mul_nonneg hC (pow_nonneg hr0 _))
            (mul_nonneg hC (pow_nonneg hr0 _))]
          congr 1
          rw [pow_succ]
          ring
  -- the geometric series of `ℓᵖ` norms
  have hsum : (∑' k : ℕ, eLpNorm (fun m : ℤ => ‖a (k + 1) m - a k m‖ₑ) (ENNReal.ofReal p)
        Measure.count) ≤ ENNReal.ofReal (C * (1 + r) * (1 - r)⁻¹) := by
    calc ∑' k, eLpNorm (fun m : ℤ => ‖a (k + 1) m - a k m‖ₑ) (ENNReal.ofReal p) Measure.count
        ≤ ∑' k, ENNReal.ofReal (C * (1 + r) * r ^ k) := ENNReal.tsum_le_tsum hge
      _ = ENNReal.ofReal (∑' k : ℕ, C * (1 + r) * r ^ k) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hsumm).symm
      _ = ENNReal.ofReal (C * (1 + r) * (1 - r)⁻¹) := by
          congr 1
          rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hrnorm]
  calc eLpNorm (fun m : ℤ => Work.BourgainPlan.Maximal.varRhoAll ρ (fun k : ℕ => a k m))
        (ENNReal.ofReal p) Measure.count
      ≤ eLpNorm (fun m : ℤ => ∑' k : ℕ, ‖a (k + 1) m - a k m‖ₑ) (ENNReal.ofReal p)
          Measure.count := by
        refine eLpNorm_mono_enorm AEStronglyMeasurable.of_discrete fun m => ?_
        simp only [enorm_eq_self]
        exact varRhoAll_le_tsum_enorm hρ (fun k => a k m)
    _ ≤ ∑' k : ℕ, eLpNorm (fun m : ℤ => ‖a (k + 1) m - a k m‖ₑ) (ENNReal.ofReal p)
          Measure.count :=
        eLpNorm_tsum_le_tsum_eLpNorm hp1 hptop (fun k => measurable_of_int _)
    _ ≤ ENNReal.ofReal (C * (1 + r) * (1 - r)⁻¹) := hsum

end

end Work.BourgainPlan.Maximal
