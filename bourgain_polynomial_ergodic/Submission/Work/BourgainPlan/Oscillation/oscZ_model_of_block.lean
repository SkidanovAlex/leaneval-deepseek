import Mathlib
import Submission.Work.BourgainPlan.Oscillation.lacunary_defs
import Submission.Work.BourgainPlan.Maximal.poly_block_defs
import Submission.Work.BourgainPlan.Maximal.poly_block_cap

/-!
# Assembling the `m`-denominator-blocks of the major-arc model on the oscillation functional

`oscZ_model_of_block` is the oscillation analogue of
`Work.BourgainPlan.Maximal.poly_model_maximal_of_block`: a per-denominator-block bound for the
block-oscillation functional `oscZ` of the model blocks `polyModelBlockOp P g s m (N i)`, with the
weight `C · 2^{-mσ} · (m+2)²` decaying geometrically in `m`, implies the corresponding bound for
the full major-arc model `polyModelOp P g s (N i)`.

The mechanism is exactly the one of the maximal case: the model is the (locally finite) sum over
`m` of its denominator blocks, the oscillation functional is subadditive in the family index
(`‖Σ_m a_m‖ₑ ≤ Σ_m ‖a_m‖ₑ` and `sup_i Σ_m ≤ Σ_m sup_i`), and a weighted Cauchy--Schwarz in `m`
(`Commons.Analysis.ExponentialSums.block_cauchy_sig`) with the splitting exponent `τ = σ/2`
converts the geometric weight into a square-summable one.
-/

namespace Work.BourgainPlan.Oscillation

open Finset MeasureTheory
open scoped BigOperators ENNReal
open Work.BourgainPlan.Maximal
open Commons.Analysis.ExponentialSums

noncomputable section

/-! ## Vanishing of the denominator blocks past the cutoff -/

/-- The `m`-th denominator block of the model is empty once the dyadic index `m` exceeds the
denominator cutoff `⌊N^{1/4}⌋` (every `q` of the block satisfies `Nat.log 2 q = m ≤ q ≤ ⌊N^{1/4}⌋`). -/
lemma polyModelQBlock_eq_zero_of_floor_lt (P : Polynomial ℤ) {m N : ℕ}
    (h : Nat.floor ((N : ℝ) ^ ((1:ℝ)/4)) < m) (θ : ℝ) :
    polyModelQBlock P m N θ = 0 := by
  unfold polyModelQBlock
  have hempty : (Finset.Icc 1 (Nat.floor ((N : ℝ) ^ ((1:ℝ)/4)))).filter
      (fun q => Nat.log 2 q = m) = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro q hq
    rw [Finset.mem_filter] at hq
    obtain ⟨hqIcc, hlog⟩ := hq
    have hqle : q ≤ Nat.floor ((N : ℝ) ^ ((1:ℝ)/4)) := (Finset.mem_Icc.mp hqIcc).2
    have : m ≤ Nat.floor ((N : ℝ) ^ ((1:ℝ)/4)) := by
      rw [← hlog]
      exact le_trans (Nat.log_le_self 2 q) hqle
    omega
  rw [hempty]
  simp

/-- The corresponding block model operator vanishes. -/
lemma polyModelBlockOp_eq_zero_of_floor_lt (P : Polynomial ℤ) (g : ℤ → ℂ) (s : Finset ℤ)
    {m N : ℕ} (h : Nat.floor ((N : ℝ) ^ ((1:ℝ)/4)) < m) (x : ℤ) :
    polyModelBlockOp P g s m N x = 0 := by
  have hzero : (∫ θ in (0:ℝ)..1, (starRingEnd ℂ (polyModelQBlock P m N θ)) *
      (∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (θ : ℂ)))) *
      Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℂ) * (θ : ℂ)))))
      = ∫ θ in (0:ℝ)..1, (0 : ℂ) :=
    intervalIntegral.integral_congr (fun θ _ => by
      rw [polyModelQBlock_eq_zero_of_floor_lt P h, map_zero, zero_mul, zero_mul])
  unfold polyModelBlockOp
  rw [hzero]
  simp

/-! ## Integrability of a single block summand at an arbitrary scale -/

lemma intervalIntegrable_polyModelBlock (P : Polynomial ℤ) (g : ℤ → ℂ) (s : Finset ℤ)
    (m N : ℕ) (x : ℤ) :
    IntervalIntegrable (fun θ : ℝ => (starRingEnd ℂ (polyModelQBlock P m N θ)) *
      (∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (θ : ℂ)))) *
      Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℂ) * (θ : ℂ))))) volume 0 1 := by
  rw [intervalIntegrable_iff]
  have hfin : IsFiniteMeasure (volume.restrict (Set.uIoc (0:ℝ) 1)) :=
    ⟨by rw [Measure.restrict_apply_univ, Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1),
        Real.volume_Ioc]; norm_num⟩
  refine MeasureTheory.Integrable.of_bound ?_
    (((((Nat.floor (((N : ℕ) : ℝ) ^ ((1:ℝ)/4))) : ℝ)^2
        * (((P.leadingCoeff + 2).toNat) : ℝ)) * (∑ j ∈ s, ‖g j‖)) + 1) ?_
  · exact (((Complex.continuous_conj.measurable.comp
      (measurable_polyModelQBlock P m N)).mul (by fun_prop)).mul (by fun_prop)).aestronglyMeasurable
  · filter_upwards with θ
    rw [norm_mul, norm_mul, norm_exp_neg_pure_imag' x θ, mul_one]
    have hP := norm_polyModelP_le g s θ
    have hb := norm_polyModelQBlock_le P m N θ
    have h1 : ‖(starRingEnd ℂ (polyModelQBlock P m N θ))‖ *
            ‖∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (θ : ℂ)))‖
        ≤ (((Nat.floor (((N : ℕ) : ℝ) ^ ((1:ℝ)/4))) : ℝ)^2
            * (((P.leadingCoeff + 2).toNat) : ℝ)) * (∑ j ∈ s, ‖g j‖) := by
      rw [Complex.norm_conj]
      exact mul_le_mul hb hP (by positivity) (by positivity)
    linarith

/-! ## The model operator as the sum of its denominator blocks -/

lemma polyModelOp_eq_sum_block (P : Polynomial ℤ) (g : ℤ → ℂ) (s : Finset ℤ) (N : ℕ) (x : ℤ) :
    polyModelOp P g s N x
      = ∑ m ∈ Finset.range (Nat.floor (((N : ℕ) : ℝ) ^ ((1:ℝ)/4)) + 1),
          polyModelBlockOp P g s m N x := by
  have hmain : (∫ θ in (0:ℝ)..1, (starRingEnd ℂ (polyMajorArcModelPre P ((1:ℝ)/4) N θ)) *
        (∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (θ : ℂ)))) *
        Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℂ) * (θ : ℂ)))))
      = ∫ θ in (0:ℝ)..1,
          ∑ m ∈ Finset.range (Nat.floor (((N : ℕ) : ℝ) ^ ((1:ℝ)/4)) + 1),
            (starRingEnd ℂ (polyModelQBlock P m N θ)) *
            (∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (θ : ℂ)))) *
            Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℂ) * (θ : ℂ)))) := by
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    rw [polyMajorArcModelPre_eq_sum_modelQBlock, map_sum, Finset.sum_mul, Finset.sum_mul]
  have hsum : (∫ θ in (0:ℝ)..1,
          ∑ m ∈ Finset.range (Nat.floor (((N : ℕ) : ℝ) ^ ((1:ℝ)/4)) + 1),
            (starRingEnd ℂ (polyModelQBlock P m N θ)) *
            (∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (θ : ℂ)))) *
            Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℂ) * (θ : ℂ)))))
      = ∑ m ∈ Finset.range (Nat.floor (((N : ℕ) : ℝ) ^ ((1:ℝ)/4)) + 1),
          polyModelBlockOp P g s m N x := by
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl (fun m _ => ?_)
      unfold polyModelBlockOp
      rfl
    · intro m _
      exact intervalIntegrable_polyModelBlock P g s m N x
  unfold polyModelOp
  exact hmain.trans hsum

/-- The model operator as the `tsum` of its denominator blocks (the blocks past the cutoff
vanish, so the locally finite sum converges). -/
lemma polyModelOp_eq_tsum_block (P : Polynomial ℤ) (g : ℤ → ℂ) (s : Finset ℤ) (N : ℕ) (x : ℤ) :
    polyModelOp P g s N x = ∑' m : ℕ, polyModelBlockOp P g s m N x := by
  rw [polyModelOp_eq_sum_block]
  refine (tsum_eq_sum (s := Finset.range (Nat.floor (((N : ℕ) : ℝ) ^ ((1:ℝ)/4)) + 1)) ?_).symm
  intro m hm
  rw [Finset.mem_range, not_lt] at hm
  exact polyModelBlockOp_eq_zero_of_floor_lt P g s (m := m) (N := N) (by omega) x

/-! ## The pointwise sup is bounded by the sum of the blockwise sups -/

lemma modelOp_sup_le_tsum_blockSup (P : Polynomial ℤ) (g : ℤ → ℂ) (s : Finset ℤ)
    (N : ℕ → ℕ) (k : ℕ → ℕ) (j : ℕ) (x : ℤ) :
    (⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
        ‖polyModelOp P g s (N i) x - polyModelOp P g s (N (k j)) x‖ₑ)
      ≤ ∑' m : ℕ, ⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
          ‖polyModelBlockOp P g s m (N i) x - polyModelBlockOp P g s m (N (k j)) x‖ₑ := by
  refine iSup₂_le fun i hi => ?_
  have hs1 : Summable (fun m : ℕ => polyModelBlockOp P g s m (N i) x) :=
    summable_of_ne_finset_zero
      (s := Finset.range (Nat.floor (((N i : ℕ) : ℝ) ^ ((1:ℝ)/4)) + 1))
      (fun m hm => by
        rw [Finset.mem_range, not_lt] at hm
        exact polyModelBlockOp_eq_zero_of_floor_lt P g s (m := m) (N := N i) (by omega) x)
  have hs2 : Summable (fun m : ℕ => polyModelBlockOp P g s m (N (k j)) x) :=
    summable_of_ne_finset_zero
      (s := Finset.range (Nat.floor (((N (k j) : ℕ) : ℝ) ^ ((1:ℝ)/4)) + 1))
      (fun m hm => by
        rw [Finset.mem_range, not_lt] at hm
        exact polyModelBlockOp_eq_zero_of_floor_lt P g s (m := m) (N := N (k j)) (by omega) x)
  calc ‖polyModelOp P g s (N i) x - polyModelOp P g s (N (k j)) x‖ₑ
      = ‖∑' m : ℕ, (polyModelBlockOp P g s m (N i) x
          - polyModelBlockOp P g s m (N (k j)) x)‖ₑ := by
        rw [hs1.tsum_sub hs2, ← polyModelOp_eq_tsum_block P g s (N i) x,
          ← polyModelOp_eq_tsum_block P g s (N (k j)) x]
    _ ≤ ∑' m : ℕ,
          ‖polyModelBlockOp P g s m (N i) x - polyModelBlockOp P g s m (N (k j)) x‖ₑ :=
        enorm_tsum_le_tsum_enorm
    _ ≤ ∑' m : ℕ, ⨆ i' ∈ Finset.Ico (k j) (k (j + 1)),
          ‖polyModelBlockOp P g s m (N i') x - polyModelBlockOp P g s m (N (k j)) x‖ₑ :=
        ENNReal.tsum_le_tsum (fun m => le_iSup₂_of_le i hi le_rfl)

/-! ## Interchange of a finite sum with an `ℝ≥0∞`-valued `tsum` -/

lemma sum_tsum_ennreal {ι : Type*} (s : Finset ι) (f : ι → ℕ → ℝ≥0∞) :
    ∑ i ∈ s, ∑' m, f i m = ∑' m, ∑ i ∈ s, f i m := by
  calc ∑ i ∈ s, ∑' m, f i m
      = ∑' i : ↥s, ∑' m, f (i : ι) m :=
          (Finset.tsum_subtype s (fun i => ∑' m, f i m)).symm
    _ = ∑' m, ∑' i : ↥s, f (i : ι) m := ENNReal.tsum_comm
    _ = ∑' m, ∑ i ∈ s, f i m := by
        refine tsum_congr (fun m => ?_)
        exact Finset.tsum_subtype s (fun i => f i m)

/-- `(a * b) ^ (2 : ℝ) = a ^ 2 * b ^ 2` in `ℝ≥0∞`. -/
lemma mul_rpow_two (a b : ℝ≥0∞) : (a * b) ^ (2:ℝ) = a^(2:ℝ) * b^(2:ℝ) := by
  rw [ENNReal.mul_rpow_of_nonneg a b (by norm_num : (0:ℝ) ≤ 2)]

/-! ## The per-block Cauchy--Schwarz step -/

lemma oscZ_model_term_le (P : Polynomial ℤ) (g : ℤ → ℂ) (s : Finset ℤ) (N : ℕ → ℕ)
    (k : ℕ → ℕ) {τ : ℝ} (hτ : 0 < τ) (j : ℕ) :
    (∫⁻ x : ℤ, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
        ‖polyModelOp P g s (N i) x - polyModelOp P g s (N (k j)) x‖ₑ) ^ (2:ℝ)
      ∂MeasureTheory.Measure.count)
    ≤ (∑' m : ℕ, ((2:ℝ≥0∞) ^ (-(m:ℝ) * τ)) ^ (2:ℝ)) *
      (∑' m : ℕ, ((2:ℝ≥0∞) ^ ((m:ℝ) * τ)) ^ (2:ℝ) *
        (∫⁻ x : ℤ, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
          ‖polyModelBlockOp P g s m (N i) x - polyModelBlockOp P g s m (N (k j)) x‖ₑ) ^ (2:ℝ)
        ∂MeasureTheory.Measure.count)) := by
  calc (∫⁻ x : ℤ, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
        ‖polyModelOp P g s (N i) x - polyModelOp P g s (N (k j)) x‖ₑ) ^ (2:ℝ)
      ∂MeasureTheory.Measure.count)
      ≤ ∫⁻ x : ℤ, (∑' m : ℕ, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
          ‖polyModelBlockOp P g s m (N i) x - polyModelBlockOp P g s m (N (k j)) x‖ₑ)) ^ (2:ℝ)
          ∂MeasureTheory.Measure.count := by
        refine lintegral_mono (fun x => ?_)
        exact ENNReal.rpow_le_rpow (modelOp_sup_le_tsum_blockSup P g s N k j x) (by norm_num)
    _ ≤ ∫⁻ x : ℤ, (∑' m : ℕ, ((2:ℝ≥0∞) ^ (-(m:ℝ) * τ)) ^ (2:ℝ)) *
          (∑' m : ℕ, ((2:ℝ≥0∞) ^ ((m:ℝ) * τ) * (⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
            ‖polyModelBlockOp P g s m (N i) x - polyModelBlockOp P g s m (N (k j)) x‖ₑ)) ^ (2:ℝ))
          ∂MeasureTheory.Measure.count := by
        refine lintegral_mono (fun x => ?_)
        exact block_cauchy_sig hτ (fun m => ⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
          ‖polyModelBlockOp P g s m (N i) x - polyModelBlockOp P g s m (N (k j)) x‖ₑ)
    _ = (∑' m : ℕ, ((2:ℝ≥0∞) ^ (-(m:ℝ) * τ)) ^ (2:ℝ)) *
          ∫⁻ x : ℤ, (∑' m : ℕ, ((2:ℝ≥0∞) ^ ((m:ℝ) * τ) * (⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
            ‖polyModelBlockOp P g s m (N i) x - polyModelBlockOp P g s m (N (k j)) x‖ₑ)) ^ (2:ℝ))
            ∂MeasureTheory.Measure.count :=
        lintegral_const_mul _ (measurable_of_countable _)
    _ = (∑' m : ℕ, ((2:ℝ≥0∞) ^ (-(m:ℝ) * τ)) ^ (2:ℝ)) *
          (∑' m : ℕ, ∫⁻ x : ℤ, ((2:ℝ≥0∞) ^ ((m:ℝ) * τ) * (⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
            ‖polyModelBlockOp P g s m (N i) x - polyModelBlockOp P g s m (N (k j)) x‖ₑ)) ^ (2:ℝ)
            ∂MeasureTheory.Measure.count) := by
        rw [lintegral_tsum (fun m => Measurable.aemeasurable (measurable_of_countable _))]
    _ = (∑' m : ℕ, ((2:ℝ≥0∞) ^ (-(m:ℝ) * τ)) ^ (2:ℝ)) *
          (∑' m : ℕ, ((2:ℝ≥0∞) ^ ((m:ℝ) * τ)) ^ (2:ℝ) *
            (∫⁻ x : ℤ, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
              ‖polyModelBlockOp P g s m (N i) x - polyModelBlockOp P g s m (N (k j)) x‖ₑ) ^ (2:ℝ)
              ∂MeasureTheory.Measure.count)) := by
        congr 1
        refine tsum_congr (fun m => ?_)
        rw [lintegral_congr (fun x => mul_rpow_two _ _)]
        rw [lintegral_const_mul _ (measurable_of_countable _)]

/-! ## The assembly -/

theorem oscZ_model_of_block (P : Polynomial ℤ) (σ : ℝ) (hσ : 0 < σ) (N : ℕ → ℕ)
    (hm : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (g : ℤ → ℂ) (s : Finset ℤ),
      (∀ n, n ∉ s → g n = 0) →
        ∀ (J : ℕ) (k : ℕ → ℕ),
          Work.BourgainPlan.Oscillation.oscZ
              (fun i x => Work.BourgainPlan.Oscillation.polyModelBlockOp P g s m (N i) x) J k
            ≤ ENNReal.ofReal (C * (2:ℝ)^(-(m:ℝ)*σ) * ((m:ℝ)+2)^2) ^ 2 *
                ∫⁻ x : ℤ, ‖g x‖ₑ^(2:ℝ) ∂MeasureTheory.Measure.count) :
    ∃ A : ℝ, 0 < A ∧ ∀ (g : ℤ → ℂ) (s : Finset ℤ), (∀ n, n ∉ s → g n = 0) →
      ∀ (J : ℕ) (k : ℕ → ℕ),
        Work.BourgainPlan.Oscillation.oscZ
            (fun i x => Work.BourgainPlan.Oscillation.polyModelOp P g s (N i) x) J k
          ≤ ENNReal.ofReal (A^2) *
              ∫⁻ x : ℤ, ‖g x‖ₑ^(2:ℝ) ∂MeasureTheory.Measure.count := by
  obtain ⟨C, hCpos, hblk⟩ := hm
  set τ : ℝ := σ / 2 with hτdef
  have hτpos : 0 < τ := by rw [hτdef]; linarith
  have hτσ : τ < σ := by rw [hτdef]; linarith
  set W : ℝ≥0∞ := ∑' m : ℕ, ((2:ℝ≥0∞)^(-(m:ℝ)*τ))^(2:ℝ) with hW
  set D : ℝ≥0∞ := ∑' m : ℕ, (((2:ℝ≥0∞)^((m:ℝ)*τ))^(2:ℝ) *
    ENNReal.ofReal (C * (2:ℝ)^(-(m:ℝ)*σ) * ((m:ℝ)+2)^2)^2) with hD
  have hWfin : W < ∞ := by rw [hW]; exact tsum_block_weight_sig_lt_top hτpos
  have hDfin : D < ∞ := by rw [hD]; exact tsum_scaled_K_sig_lt_top hCpos.le hτσ hτpos
  have hWD : W * D ≠ ∞ := ne_top_of_lt (ENNReal.mul_lt_top hWfin hDfin)
  refine ⟨Real.sqrt ((W * D).toReal) + 1, by positivity, ?_⟩
  have hA : W * D ≤ ENNReal.ofReal ((Real.sqrt ((W * D).toReal) + 1)^2) := by
    have h5 : (W * D).toReal ≤ (Real.sqrt ((W * D).toReal) + 1)^2 := by
      rw [add_sq, Real.sq_sqrt (by positivity : (0:ℝ) ≤ (W * D).toReal)]
      linarith [Real.sqrt_nonneg ((W * D).toReal)]
    calc W * D = ENNReal.ofReal ((W * D).toReal) := (ENNReal.ofReal_toReal hWD).symm
      _ ≤ ENNReal.ofReal ((Real.sqrt ((W * D).toReal) + 1)^2) := ENNReal.ofReal_le_ofReal h5
  intro g s hgs J k
  have key : oscZ (fun i x => polyModelOp P g s (N i) x) J k
      ≤ W * D * (∫⁻ x : ℤ, ‖g x‖ₑ^(2:ℝ) ∂MeasureTheory.Measure.count) := by
    rw [oscZ]
    calc ∑ j ∈ Finset.range J, (∫⁻ x : ℤ, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
          ‖polyModelOp P g s (N i) x - polyModelOp P g s (N (k j)) x‖ₑ) ^ (2:ℝ)
        ∂MeasureTheory.Measure.count)
        ≤ ∑ j ∈ Finset.range J, W * (∑' m : ℕ, ((2:ℝ≥0∞)^((m:ℝ)*τ))^(2:ℝ) *
            (∫⁻ x : ℤ, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
              ‖polyModelBlockOp P g s m (N i) x - polyModelBlockOp P g s m (N (k j)) x‖ₑ) ^ (2:ℝ)
              ∂MeasureTheory.Measure.count)) := by
          refine Finset.sum_le_sum (fun j _ => ?_)
          have h := oscZ_model_term_le P g s N k hτpos j
          rwa [← hW] at h
      _ = W * (∑' m : ℕ, ((2:ℝ≥0∞)^((m:ℝ)*τ))^(2:ℝ) *
            (∑ j ∈ Finset.range J, ∫⁻ x : ℤ, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
              ‖polyModelBlockOp P g s m (N i) x - polyModelBlockOp P g s m (N (k j)) x‖ₑ) ^ (2:ℝ)
              ∂MeasureTheory.Measure.count)) := by
          rw [← Finset.mul_sum, sum_tsum_ennreal]
          congr 1
          refine tsum_congr (fun m => ?_)
          rw [Finset.mul_sum]
      _ ≤ W * (D * (∫⁻ x : ℤ, ‖g x‖ₑ^(2:ℝ) ∂MeasureTheory.Measure.count)) := by
          gcongr
          have h1 : (∑' m : ℕ, ((2:ℝ≥0∞)^((m:ℝ)*τ))^(2:ℝ) *
              (∑ j ∈ Finset.range J, ∫⁻ x : ℤ, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
                ‖polyModelBlockOp P g s m (N i) x - polyModelBlockOp P g s m (N (k j)) x‖ₑ) ^ (2:ℝ)
                ∂MeasureTheory.Measure.count))
              ≤ ∑' m : ℕ, (((2:ℝ≥0∞)^((m:ℝ)*τ))^(2:ℝ) *
                  (ENNReal.ofReal (C * (2:ℝ)^(-(m:ℝ)*σ) * ((m:ℝ)+2)^2)^2 *
                    (∫⁻ x : ℤ, ‖g x‖ₑ^(2:ℝ) ∂MeasureTheory.Measure.count))) := by
            refine ENNReal.tsum_le_tsum (fun m => ?_)
            gcongr
            have hZ : (∑ j ∈ Finset.range J, ∫⁻ x : ℤ, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
                  ‖polyModelBlockOp P g s m (N i) x - polyModelBlockOp P g s m (N (k j)) x‖ₑ) ^ (2:ℝ)
                  ∂MeasureTheory.Measure.count)
                = oscZ (fun i x => polyModelBlockOp P g s m (N i) x) J k := rfl
            rw [hZ]
            exact hblk m g s hgs J k
          have h2 : (∑' m : ℕ, (((2:ℝ≥0∞)^((m:ℝ)*τ))^(2:ℝ) *
                (ENNReal.ofReal (C * (2:ℝ)^(-(m:ℝ)*σ) * ((m:ℝ)+2)^2)^2 *
                  (∫⁻ x : ℤ, ‖g x‖ₑ^(2:ℝ) ∂MeasureTheory.Measure.count))))
              = D * (∫⁻ x : ℤ, ‖g x‖ₑ^(2:ℝ) ∂MeasureTheory.Measure.count) := by
            rw [hD]
            rw [show (∑' m : ℕ, (((2:ℝ≥0∞)^((m:ℝ)*τ))^(2:ℝ) *
                  (ENNReal.ofReal (C * (2:ℝ)^(-(m:ℝ)*σ) * ((m:ℝ)+2)^2)^2 *
                    (∫⁻ x : ℤ, ‖g x‖ₑ^(2:ℝ) ∂MeasureTheory.Measure.count))))
                = ∑' m : ℕ, ((((2:ℝ≥0∞)^((m:ℝ)*τ))^(2:ℝ) *
                  ENNReal.ofReal (C * (2:ℝ)^(-(m:ℝ)*σ) * ((m:ℝ)+2)^2)^2) *
                    (∫⁻ x : ℤ, ‖g x‖ₑ^(2:ℝ) ∂MeasureTheory.Measure.count)) from
              tsum_congr (fun m => (mul_assoc _ _ _).symm)]
            rw [ENNReal.tsum_mul_right]
          exact le_trans h1 (le_of_eq h2)
      _ = W * D * (∫⁻ x : ℤ, ‖g x‖ₑ^(2:ℝ) ∂MeasureTheory.Measure.count) := by rw [mul_assoc]
  refine le_trans key ?_
  exact mul_le_mul_of_nonneg_right hA (by positivity)

end

end Work.BourgainPlan.Oscillation
