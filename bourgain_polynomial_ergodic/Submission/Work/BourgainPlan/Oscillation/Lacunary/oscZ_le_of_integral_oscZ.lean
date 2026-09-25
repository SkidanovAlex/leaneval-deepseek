import Mathlib
import Submission.Work.BourgainPlan.Oscillation.lacunary_defs
import Submission.Work.BourgainPlan.Oscillation.oscZ_lacunary_defs
import Submission.Work.BourgainPlan.Oscillation.Lacunary.dilProfDefs
import Submission.Work.BourgainPlan.Maximal.lintegral_rpow_pred_le

/-!
# The oscillation of a `t`-integral is bounded by the `t`-integral of the oscillations

If a family `A : ℕ → ℤ → ℂ` is, block-wise, the `mu01`-integral of a family `G t` against a
uniformly bounded kernel `Hd`,

`A_i x - A_{k_j} x = -∫_t Hd t · (G_t i x - G_t k_j x) ∂mu01`   (all `i`, `j`, `x`),

with `‖Hd t‖ ≤ M` a.e., then the block oscillation of `A` is dominated by `M²` times the
`mu01`-average of the block oscillations of the families `G t`:

`oscZ A J k ≤ M² · ∫⁻ t, oscZ (G t) J k ∂mu01`.

The point is that Cauchy–Schwarz is applied *inside* the supremum over the block, so that the
`t`-integral of the square can be taken before the (finite) supremum is evaluated.
-/

namespace Work.BourgainPlan.Oscillation.Lacunary

open MeasureTheory Finset
open scoped BigOperators ENNReal

noncomputable section

/-- **Cauchy–Schwarz for the square on a probability space**: `(∫⁻ A)² ≤ ∫⁻ A²`.  This is
`Work.BourgainPlan.Maximal.lintegral_rpow_pred_le` at `q = 2`, squared. -/
private lemma sq_lintegral_le_lintegral_sq {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (A : α → ℝ≥0∞) (hA : AEMeasurable A μ) :
    (∫⁻ x, A x ∂μ) ^ (2 : ℝ) ≤ ∫⁻ x, (A x) ^ (2 : ℝ) ∂μ := by
  have h := Work.BourgainPlan.Maximal.lintegral_rpow_pred_le μ A hA (q := 2) (by norm_num)
  rw [show (2 : ℝ) - 1 = 1 by norm_num] at h
  simp only [ENNReal.rpow_one] at h
  have h2 : (∫⁻ x, A x ∂μ) ^ (2 : ℝ)
      ≤ ((∫⁻ x, (A x) ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) :=
    ENNReal.rpow_le_rpow h (by norm_num)
  refine h2.trans ?_
  rw [← ENNReal.rpow_mul]
  norm_num

/-- Fubini for a finite sum of a.e. measurable `ℝ≥0∞`-valued functions. -/
private lemma lintegral_finsetSum' {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    (s : Finset ι) {f : ι → α → ℝ≥0∞} (hf : ∀ i ∈ s, AEMeasurable (f i) μ) :
    ∫⁻ a, ∑ i ∈ s, f i a ∂μ = ∑ i ∈ s, ∫⁻ a, f i a ∂μ := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      have h1 : ∀ x, ∑ i ∈ insert a s, f i x = f a x + ∑ i ∈ s, f i x := by
        intro x; rw [Finset.sum_insert ha]
      rw [lintegral_congr (fun x => h1 x), lintegral_add_left' (hf a (Finset.mem_insert_self a s)),
        ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)), Finset.sum_insert ha]

theorem oscZ_le_of_integral_oscZ (J : ℕ) (k : ℕ → ℕ) (hk : StrictMono k)
    (M : ℝ) (hM : 0 ≤ M) (Hd : ℝ → ℂ)
    (hHdb : ∀ᵐ t ∂Work.BourgainPlan.Oscillation.Lacunary.mu01, ‖Hd t‖ ≤ M)
    (A : ℕ → ℤ → ℂ) (G : ℝ → ℕ → ℤ → ℂ)
    (hA : ∀ (j i : ℕ) (x : ℤ), A i x - A (k j) x
        = -∫ t, Hd t * (G t i x - G t (k j) x) ∂Work.BourgainPlan.Oscillation.Lacunary.mu01)
    (hGm : ∀ i : ℕ, AEMeasurable (fun p : ℝ × ℤ => G p.1 i p.2)
        (Work.BourgainPlan.Oscillation.Lacunary.mu01.prod MeasureTheory.Measure.count))
    (hGx : ∀ (i : ℕ) (x : ℤ),
        AEMeasurable (fun t : ℝ => G t i x) Work.BourgainPlan.Oscillation.Lacunary.mu01) :
    Work.BourgainPlan.Oscillation.oscZ A J k
      ≤ ENNReal.ofReal (M ^ 2) *
        ∫⁻ t, Work.BourgainPlan.Oscillation.oscZ (G t) J k
          ∂Work.BourgainPlan.Oscillation.Lacunary.mu01 := by
  -- the a.e. bound, in `ℝ≥0∞`
  have hb : ∀ᵐ t ∂mu01, ‖Hd t‖ₑ ≤ ENNReal.ofReal M :=
    hHdb.mono (fun t ht => by rw [← ofReal_norm]; exact ENNReal.ofReal_mono ht)
  -- the pointwise bound for one block and one `x`
  have hpoint : ∀ (j : ℕ) (x : ℤ),
      (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖A i x - A (k j) x‖ₑ) ^ (2 : ℝ)
        ≤ ENNReal.ofReal (M ^ 2) * ∫⁻ t, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
            ‖G t i x - G t (k j) x‖ₑ) ^ (2 : ℝ) ∂mu01 := by
    intro j x
    have key : ∀ i ∈ Finset.Ico (k j) (k (j + 1)),
        ‖A i x - A (k j) x‖ₑ ^ (2 : ℝ)
          ≤ ENNReal.ofReal (M ^ 2) * ∫⁻ t, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
              ‖G t i x - G t (k j) x‖ₑ) ^ (2 : ℝ) ∂mu01 := by
      intro i hi
      have hgi : AEMeasurable (fun t : ℝ => ‖G t i x - G t (k j) x‖ₑ) mu01 :=
        ((hGx i x).sub (hGx (k j) x)).enorm
      have h1 : ‖A i x - A (k j) x‖ₑ
          ≤ ENNReal.ofReal M * ∫⁻ t, ‖G t i x - G t (k j) x‖ₑ ∂mu01 := by
        rw [hA j i x, enorm_neg]
        calc ‖∫ t, Hd t * (G t i x - G t (k j) x) ∂mu01‖ₑ
            ≤ ∫⁻ t, ‖Hd t * (G t i x - G t (k j) x)‖ₑ ∂mu01 :=
              enorm_integral_le_lintegral_enorm _
          _ = ∫⁻ t, ‖Hd t‖ₑ * ‖G t i x - G t (k j) x‖ₑ ∂mu01 := by
              simp only [enorm_mul]
          _ ≤ ∫⁻ t, ENNReal.ofReal M * ‖G t i x - G t (k j) x‖ₑ ∂mu01 :=
              lintegral_mono_ae (hb.mono (fun t ht => by gcongr))
          _ = ENNReal.ofReal M * ∫⁻ t, ‖G t i x - G t (k j) x‖ₑ ∂mu01 :=
              lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      calc ‖A i x - A (k j) x‖ₑ ^ (2 : ℝ)
          ≤ (ENNReal.ofReal M * ∫⁻ t, ‖G t i x - G t (k j) x‖ₑ ∂mu01) ^ (2 : ℝ) :=
            ENNReal.rpow_le_rpow h1 (by norm_num)
        _ = ENNReal.ofReal (M ^ 2) * (∫⁻ t, ‖G t i x - G t (k j) x‖ₑ ∂mu01) ^ (2 : ℝ) := by
            rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
            congr 1
            rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow hM]
        _ ≤ ENNReal.ofReal (M ^ 2) * ∫⁻ t, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
              ‖G t i x - G t (k j) x‖ₑ) ^ (2 : ℝ) ∂mu01 := by
            refine mul_le_mul' le_rfl ?_
            refine (sq_lintegral_le_lintegral_sq mu01 _ hgi).trans ?_
            refine lintegral_mono (fun t => ?_)
            exact ENNReal.rpow_le_rpow (le_iSup₂_of_le i hi le_rfl) (by norm_num)
    calc (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖A i x - A (k j) x‖ₑ) ^ (2 : ℝ)
        = ⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖A i x - A (k j) x‖ₑ ^ (2 : ℝ) :=
          Work.BourgainPlan.Oscillation.iSup_finset_rpow_two _
      _ ≤ ENNReal.ofReal (M ^ 2) * ∫⁻ t, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
            ‖G t i x - G t (k j) x‖ₑ) ^ (2 : ℝ) ∂mu01 := iSup₂_le key
  -- a.e. measurability in `t` of the block integrands
  have hΦae : ∀ (j : ℕ) (x : ℤ), AEMeasurable (fun t : ℝ =>
      (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖G t i x - G t (k j) x‖ₑ) ^ (2 : ℝ)) mu01 := by
    intro j x
    have h1 : AEMeasurable (fun t : ℝ => ⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
        ‖G t i x - G t (k j) x‖ₑ) mu01 := by
      refine AEMeasurable.biSup (s := ((Finset.Ico (k j) (k (j + 1)) : Finset ℕ) : Set ℕ))
        (f := fun i (t : ℝ) => ‖G t i x - G t (k j) x‖ₑ) (Set.to_countable _) ?_
      intro i _
      exact ((hGx i x).sub (hGx (k j) x)).enorm
    exact h1.pow_const 2
  -- joint measurability of the integrand of the Fubini step
  have hGmad : ∀ j : ℕ, AEMeasurable (fun p : ℝ × ℤ => ⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
      ‖G p.1 i p.2 - G p.1 (k j) p.2‖ₑ) (mu01.prod MeasureTheory.Measure.count) := by
    intro j
    refine AEMeasurable.biSup (s := ((Finset.Ico (k j) (k (j + 1)) : Finset ℕ) : Set ℕ))
      (f := fun i (p : ℝ × ℤ) => ‖G p.1 i p.2 - G p.1 (k j) p.2‖ₑ) (Set.to_countable _) ?_
    intro i _
    exact ((hGm i).sub (hGm (k j))).enorm
  have hmeas : AEMeasurable (fun p : ℝ × ℤ => ∑ j ∈ Finset.range J,
      (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖G p.1 i p.2 - G p.1 (k j) p.2‖ₑ) ^ (2 : ℝ))
      (mu01.prod MeasureTheory.Measure.count) := by
    have h := Finset.aemeasurable_sum (Finset.range J)
      (f := fun j (p : ℝ × ℤ) => (⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
        ‖G p.1 i p.2 - G p.1 (k j) p.2‖ₑ) ^ (2 : ℝ))
      (fun j _ => (hGmad j).pow_const 2)
    exact h.congr (by filter_upwards with p; simp [Finset.sum_apply])
  calc Work.BourgainPlan.Oscillation.oscZ A J k
      = ∑ j ∈ Finset.range J, ∫⁻ x : ℤ, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
          ‖A i x - A (k j) x‖ₑ) ^ (2 : ℝ) ∂MeasureTheory.Measure.count := rfl
    _ ≤ ∑ j ∈ Finset.range J, ∫⁻ x : ℤ, ENNReal.ofReal (M ^ 2) * (∫⁻ t,
          (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖G t i x - G t (k j) x‖ₑ) ^ (2 : ℝ)
            ∂mu01) ∂MeasureTheory.Measure.count :=
        Finset.sum_le_sum (fun j _ => lintegral_mono (fun x => hpoint j x))
    _ = ∑ j ∈ Finset.range J, ENNReal.ofReal (M ^ 2) * ∫⁻ x : ℤ, (∫⁻ t,
          (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖G t i x - G t (k j) x‖ₑ) ^ (2 : ℝ)
            ∂mu01) ∂MeasureTheory.Measure.count :=
        Finset.sum_congr rfl (fun j _ => lintegral_const_mul' _ _ ENNReal.ofReal_ne_top)
    _ = ENNReal.ofReal (M ^ 2) * ∑ j ∈ Finset.range J, ∫⁻ x : ℤ, (∫⁻ t,
          (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖G t i x - G t (k j) x‖ₑ) ^ (2 : ℝ)
            ∂mu01) ∂MeasureTheory.Measure.count := by
        rw [Finset.mul_sum]
    _ = ENNReal.ofReal (M ^ 2) * ∫⁻ x : ℤ, ∑ j ∈ Finset.range J, (∫⁻ t,
          (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖G t i x - G t (k j) x‖ₑ) ^ (2 : ℝ)
            ∂mu01) ∂MeasureTheory.Measure.count := by
        rw [lintegral_finsetSum _ (fun j _ => measurable_of_countable _)]
    _ = ENNReal.ofReal (M ^ 2) * ∫⁻ x : ℤ, (∫⁻ t, ∑ j ∈ Finset.range J,
          (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖G t i x - G t (k j) x‖ₑ) ^ (2 : ℝ)
            ∂mu01) ∂MeasureTheory.Measure.count := by
        have h : (fun x : ℤ => ∑ j ∈ Finset.range J, (∫⁻ t,
              (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖G t i x - G t (k j) x‖ₑ) ^ (2 : ℝ)
                ∂mu01))
            = fun x : ℤ => ∫⁻ t, ∑ j ∈ Finset.range J,
              (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖G t i x - G t (k j) x‖ₑ) ^ (2 : ℝ)
                ∂mu01 := by
          funext x
          rw [← lintegral_finsetSum' (μ := mu01) (s := Finset.range J)
            (f := fun j (t : ℝ) => (⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
              ‖G t i x - G t (k j) x‖ₑ) ^ (2 : ℝ))
            (fun j _ => hΦae j x)]
        rw [h]
    _ = ENNReal.ofReal (M ^ 2) * ∫⁻ t, (∫⁻ x : ℤ, ∑ j ∈ Finset.range J,
          (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖G t i x - G t (k j) x‖ₑ) ^ (2 : ℝ)
            ∂MeasureTheory.Measure.count) ∂mu01 := by
        have hswap : (∫⁻ x : ℤ, ∫⁻ t : ℝ, (fun t x => ∑ j ∈ Finset.range J,
              (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖G t i x - G t (k j) x‖ₑ) ^ (2 : ℝ)) t x
                ∂mu01 ∂MeasureTheory.Measure.count)
            = ∫⁻ t : ℝ, ∫⁻ x : ℤ, (fun t x => ∑ j ∈ Finset.range J,
              (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖G t i x - G t (k j) x‖ₑ) ^ (2 : ℝ)) t x
                ∂MeasureTheory.Measure.count ∂mu01 :=
          (lintegral_lintegral_swap (μ := mu01) (ν := MeasureTheory.Measure.count)
            (f := fun t x => ∑ j ∈ Finset.range J,
              (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖G t i x - G t (k j) x‖ₑ) ^ (2 : ℝ))
            hmeas).symm
        rw [hswap]
    _ = ENNReal.ofReal (M ^ 2) * ∫⁻ t, Work.BourgainPlan.Oscillation.oscZ (G t) J k ∂mu01 := by
        have h : (fun t : ℝ => ∫⁻ x : ℤ, ∑ j ∈ Finset.range J,
              (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖G t i x - G t (k j) x‖ₑ) ^ (2 : ℝ)
                ∂MeasureTheory.Measure.count)
            = fun t : ℝ => Work.BourgainPlan.Oscillation.oscZ (G t) J k := by
          funext t
          rw [lintegral_finsetSum _ (fun j _ => measurable_of_countable _)]
          rfl
        rw [h]

end

end Work.BourgainPlan.Oscillation.Lacunary
