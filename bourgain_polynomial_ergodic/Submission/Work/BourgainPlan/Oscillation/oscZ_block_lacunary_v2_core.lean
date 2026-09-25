import Mathlib
import Submission.Work.BourgainPlan.Oscillation.oscZ_lacunary_defs
import Submission.Work.BourgainPlan.Oscillation.oscZ_err_lacunary
import Submission.Work.BourgainPlan.Oscillation.polyBlockCoreN_eq_weighted
import Submission.Work.BourgainPlan.Oscillation.polyErrMultCutN_tsum_sq_le
import Submission.Work.BourgainPlan.Oscillation.norm_polyModelQBlock_le_capN
import Submission.Work.BourgainPlan.Maximal.polyBlockT_sep
import Submission.Work.BourgainPlan.Maximal.poly_block_cap
import Submission.Work.BourgainPlan.Maximal.poly_block_maximal

/-!
# The per-block oscillation inequality at the lacunary scales, assembled from the three inputs

`oscZ_block_lacunary_v2_core` is the *assembly* step of the per-denominator-block oscillation
bound: assuming

* `Hcore : OscZCoreLacunary` — the block oscillation estimate for the weighted sharp core,
* `Herr : OscZErrLacunary P ρ` — the block oscillation estimate for the profile-replacement error,
* `Hwin`, `hcut₁`, `Hcutidx` — the elementary scale/cutoff data,

it proves the oscillation of the `m`-th denominator block of the major-arc model at the lacunary
scales `⌊ρ^i⌋`.

The proof splits the model multiplier into the weighted neighbourhood core
`coreW T δ · unNbhd T (polyDilN P N)⁻¹` and the profile-replacement error, applies `Hcore` to the
core (using the private head-cut lemma `oscZ_le_head_p`, which handles the scale blocks starting
below the cutoff index) and `Herr` plus a square-function bound to the error, and collects the
constants.

The supporting material is

* `errOp_congr_Ioo`, `errOp_add_of_bound`, `lintegral_errOp_le`, `polyModelBlockOp_eq_errOp` —
  elementary properties of the multiplier operator `errOp` of `oscZ_err_lacunary`;
* `oscZ_le_head_p` — the head-cut lemma for `oscZ`;
* `logTerm_le_KM`, `hX_arith`, `sqrt_const_arith` — the (isolated) real arithmetic of the constant.
-/

namespace Work.BourgainPlan.Oscillation

open Finset MeasureTheory
open scoped BigOperators ENNReal
open Work.BourgainPlan.Maximal
open Commons.Analysis.ExponentialSums

set_option maxHeartbeats 1000000

noncomputable section

/-! ## Generic tools for the multiplier operator `errOp` -/

/-- The multiplier operator depends only on the values of the multiplier on `(0,1)`. -/
private lemma errOp_congr_Ioo {m m' : ℝ → ℂ} (h : ∀ θ ∈ Set.Ioo (0:ℝ) 1, m θ = m' θ)
    (g : ℤ → ℂ) (s : Finset ℤ) (x : ℤ) :
    errOp m g s x = errOp m' g s x := by
  unfold errOp
  refine intervalIntegral.integral_congr_ae ?_
  rw [MeasureTheory.ae_iff]
  refine measure_mono_null (fun y hy => ?_) (measure_singleton 1)
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff] at hy ⊢
  push_neg at hy
  rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hy
  by_contra hne
  exact hy.2 (by rw [h y ⟨hy.1.1, lt_of_le_of_ne hy.1.2 hne⟩])

/-- The operator is additive in the multiplier, on `(0,1)`. -/
private lemma errOp_add_of_bound (m m' : ℝ → ℂ) (hm : Measurable m) (hm' : Measurable m')
    {A B : ℝ} (hA : ∀ θ ∈ Set.Ioc (0:ℝ) 1, ‖m θ‖ ≤ A)
    (hB : ∀ θ ∈ Set.Ioc (0:ℝ) 1, ‖m' θ‖ ≤ B) (g : ℤ → ℂ) (s : Finset ℤ) (x : ℤ) :
    errOp (fun θ => m θ + m' θ) g s x = errOp m g s x + errOp m' g s x := by
  have hb1 : ∀ θ ∈ Set.Ioc (0:ℝ) 1,
      ‖(fun θ => m θ * Lacunary.trigP s g θ * Lacunary.Echar x θ) θ‖
        ≤ A * (∑ j ∈ s, ‖g j‖) := by
    intro θ hθ
    rw [norm_mul, norm_mul, Lacunary.norm_Echar x θ, mul_one]
    exact mul_le_mul (hA θ hθ) (Lacunary.norm_trigP_le s g θ) (norm_nonneg _)
      (le_trans (norm_nonneg _) (hA (1/2) (by norm_num)))
  have hb2 : ∀ θ ∈ Set.Ioc (0:ℝ) 1,
      ‖(fun θ => m' θ * Lacunary.trigP s g θ * Lacunary.Echar x θ) θ‖
        ≤ B * (∑ j ∈ s, ‖g j‖) := by
    intro θ hθ
    rw [norm_mul, norm_mul, Lacunary.norm_Echar x θ, mul_one]
    exact mul_le_mul (hB θ hθ) (Lacunary.norm_trigP_le s g θ) (norm_nonneg _)
      (le_trans (norm_nonneg _) (hB (1/2) (by norm_num)))
  have hint1 : IntervalIntegrable (fun θ => m θ * Lacunary.trigP s g θ * Lacunary.Echar x θ)
      volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    refine IntegrableOn.of_bound ?_ ?_ (A * (∑ j ∈ s, ‖g j‖)) ?_
    · rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
    · exact ((hm.mul (Lacunary.measurable_trigP s g)).mul
        (Lacunary.continuous_Echar x).measurable).aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem (μ := volume) measurableSet_Ioc] with θ hθ
      exact hb1 θ hθ
  have hint2 : IntervalIntegrable (fun θ => m' θ * Lacunary.trigP s g θ * Lacunary.Echar x θ)
      volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    refine IntegrableOn.of_bound ?_ ?_ (B * (∑ j ∈ s, ‖g j‖)) ?_
    · rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
    · exact ((hm'.mul (Lacunary.measurable_trigP s g)).mul
        (Lacunary.continuous_Echar x).measurable).aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem (μ := volume) measurableSet_Ioc] with θ hθ
      exact hb2 θ hθ
  unfold errOp
  rw [← intervalIntegral.integral_add hint1 hint2]
  refine intervalIntegral.integral_congr (fun θ _ => ?_)
  ring_nf

/-- **Plancherel bound for a single bounded multiplier.** -/
private lemma lintegral_errOp_le (m : ℝ → ℂ) (hm : Measurable m) {A : ℝ} (hA : 0 ≤ A)
    (hbd : ∀ θ, ‖m θ‖ ≤ A) (g : ℤ → ℂ) (s : Finset ℤ) (hs : ∀ n, n ∉ s → g n = 0) :
    ∫⁻ x : ℤ, ‖errOp m g s x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (A ^ 2) * ∫⁻ x : ℤ, ‖g x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count := by
  rw [lintegral_errOp_eq m hm hA (fun θ _ => hbd θ) g s]
  calc ∫⁻ θ, ‖m θ‖ₑ ^ (2 : ℝ) * ‖Lacunary.trigP s g θ‖ₑ ^ (2 : ℝ) ∂Lacunary.mu01
      ≤ ∫⁻ θ, ENNReal.ofReal (A ^ 2) * ‖Lacunary.trigP s g θ‖ₑ ^ (2 : ℝ) ∂Lacunary.mu01 := by
        refine lintegral_mono (fun θ => ?_)
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [Commons.Analysis.Fourier.enorm_complex_pow_two]
        exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (hbd θ) 2)
    _ = ENNReal.ofReal (A ^ 2) * ∫⁻ θ, ‖Lacunary.trigP s g θ‖ₑ ^ (2 : ℝ) ∂Lacunary.mu01 :=
        lintegral_const_mul _ ((Lacunary.measurable_trigP s g).enorm.pow_const 2)
    _ = ENNReal.ofReal (A ^ 2) * ∫⁻ x : ℤ, ‖g x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count := by
        rw [Lacunary.trig_lintegral, Lacunary.f_lintegral s g hs]

private lemma norm_unNbhd_le_one' (T : Finset (ℝ × ℂ)) (r θ : ℝ) : ‖unNbhd T r θ‖ ≤ 1 := by
  rw [unNbhd]
  split <;> norm_num

/-- The model block operator is the multiplier operator of the block multiplier. -/
private lemma polyModelBlockOp_eq_errOp (P : Polynomial ℤ) (g : ℤ → ℂ) (s : Finset ℤ)
    (m N : ℕ) (x : ℤ) :
    polyModelBlockOp P g s m N x
      = errOp (fun θ => starRingEnd ℂ (polyModelQBlock P m N θ)) g s x := by
  unfold polyModelBlockOp errOp
  refine intervalIntegral.integral_congr (fun θ _ => ?_)
  have h1 : (∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (θ : ℂ))))
      = Lacunary.trigP s g θ := by
    unfold Lacunary.trigP
    refine Finset.sum_congr rfl (fun j _ => ?_)
    congr 1
    ring
  have h2 : Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℂ) * (θ : ℂ))))
      = Lacunary.Echar x θ := by
    unfold Lacunary.Echar
    congr 1
    ring
  rw [h1, h2]


/-- The head-cut lemma for `oscZ`: a family vanishing below `c` has its block oscillation
controlled by the functional at any increasing sequence starting above `c` plus the `ℓ²` norm of
the member `A c`. -/
private lemma oscZ_le_head_p (A : ℕ → ℤ → ℂ) (J : ℕ) (k : ℕ → ℕ)
    (hk : StrictMono k) (c : ℕ) (hvan : ∀ i, i < c → A i = 0)
    {B : ENNReal} (hB : ∀ (J' : ℕ) (k' : ℕ → ℕ), StrictMono k' → c ≤ k' 0 → oscZ A J' k' ≤ B)
    {C₀ : ENNReal} (hC₀ : ∀ i, ∫⁻ x : ℤ, ‖A i x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count ≤ C₀) :
    oscZ A J k ≤ 5 * B + 4 * C₀ := by
  by_cases hkc : c ≤ k 0
  · refine le_trans (hB J k hk hkc) ?_
    calc B ≤ 5 * B := le_mul_of_one_le_left' (by norm_num : (1:ENNReal) ≤ 5)
      _ ≤ 5 * B + 4 * C₀ := le_add_of_nonneg_right (by positivity)
  · have hk0lt : k 0 < c := not_le.mp hkc
    have hgrowth : ∀ n, k 0 + n ≤ k n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have h1 : k n + 1 ≤ k (n + 1) := hk (Nat.lt_succ_self n)
        omega
    have hex : ∃ j : ℕ, c ≤ k j := ⟨c, le_trans (by omega) (hgrowth c)⟩
    set J₀ : ℕ := Nat.find hex with hJ₀def
    have hJ₀spec : c ≤ k J₀ := by rw [hJ₀def]; exact Nat.find_spec hex
    have hJ₀min : ∀ j, j < J₀ → ¬ (c ≤ k j) := by
      intro j hj; rw [hJ₀def] at hj; exact Nat.find_min hex hj
    have hJ₀pos : 1 ≤ J₀ := by
      rcases Nat.eq_zero_or_pos J₀ with h | h
      · rw [h] at hJ₀spec
        exact absurd hJ₀spec (not_le.mpr hk0lt)
      · exact h
    have hJ₀lt : k (J₀ - 1) < c :=
      not_le.mp (hJ₀min (J₀ - 1) (by omega))
    set fam : ℕ → ENNReal := fun j => ∫⁻ x : ℤ,
      (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖A i x - A (k j) x‖ₑ) ^ (2 : ℝ)
        ∂MeasureTheory.Measure.count with hfam
    -- the tail
    have htail : (∑ j ∈ Finset.Ico J₀ J, fam j) ≤ B := by
      have hk' : StrictMono (fun j => k (j + J₀)) :=
        fun a b hab => hk (Nat.add_lt_add_right hab J₀)
      have hk'0 : c ≤ (fun j => k (j + J₀)) 0 := by simpa using hJ₀spec
      have h := hB (J - J₀) (fun j => k (j + J₀)) hk' hk'0
      have heq : (∑ j ∈ Finset.Ico J₀ J, fam j) = oscZ A (J - J₀) (fun j => k (j + J₀)) := by
        rw [Finset.sum_Ico_eq_sum_range]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        simp only [hfam, Nat.add_comm J₀ j, Nat.add_right_comm j J₀ 1]
      rw [heq]; exact h
    -- the head
    have hhead : (∑ j ∈ (Finset.range J).filter (fun j => k j < c), fam j) ≤ 4 * B + 4 * C₀ := by
      -- a block whose right end is below `c` contributes nothing
      have hzero : ∀ j, j < J₀ → j + 1 < J₀ → fam j = 0 := by
        intro j _ hj1
        have hkjc : k (j + 1) < c := not_le.mp (hJ₀min (j + 1) hj1)
        have hkjlt : k j < c := lt_of_lt_of_le (hk (Nat.lt_succ_self j)) hkjc.le
        rw [hfam]
        have hpt : ∀ x : ℤ, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
            ‖A i x - A (k j) x‖ₑ) = 0 := by
          intro x
          refine iSup_eq_bot.mpr (fun i => iSup_eq_bot.mpr (fun hi => ?_))
          rw [Finset.mem_Ico] at hi
          have hic : i < c := lt_of_lt_of_le hi.2 hkjc.le
          rw [hvan i hic, hvan (k j) hkjlt]
          simp
        simp only [hpt]
        simp
      have hle : (∑ j ∈ (Finset.range J).filter (fun j => k j < c), fam j) ≤ fam (J₀ - 1) := by
        set S := (Finset.range J).filter (fun j => k j < c) with hS
        have hSsub : S ⊆ Finset.range J₀ := by
          intro j hj
          rw [hS, Finset.mem_filter, Finset.mem_range] at hj
          rw [Finset.mem_range]
          by_contra hcon
          exact absurd (le_trans hJ₀spec (hk.monotone (Nat.le_of_not_lt hcon))) (not_le.mpr hj.2)
        have hstep : ∀ j ∈ S, fam j ≤ (if j = J₀ - 1 then fam (J₀ - 1) else 0) := by
          intro j hj
          by_cases h : j = J₀ - 1
          · rw [if_pos h, h]
          · rw [if_neg h]
            have hj₀ : j < J₀ := Finset.mem_range.mp (hSsub hj)
            have hj1 : j + 1 < J₀ := by omega
            rw [hzero j hj₀ hj1]
        calc (∑ j ∈ S, fam j) ≤ ∑ j ∈ S, (if j = J₀ - 1 then fam (J₀ - 1) else 0) :=
              Finset.sum_le_sum hstep
          _ = (if J₀ - 1 ∈ S then fam (J₀ - 1) else 0) := Finset.sum_ite_eq' S (J₀ - 1) _
          _ ≤ fam (J₀ - 1) := by split_ifs <;> simp
      refine le_trans hle ?_
      have hk₂mono : StrictMono (fun j : ℕ => if j = 0 then c else k J₀ + c + j) := by
        intro a b hab
        show (if a = 0 then c else k J₀ + c + a) < (if b = 0 then c else k J₀ + c + b)
        rcases eq_or_ne a 0 with rfl | ha0
        · rw [if_pos rfl, if_neg (show b ≠ 0 by omega)]
          omega
        · rw [if_neg ha0, if_neg (show b ≠ 0 by omega)]
          omega
      have hk₂0 : c ≤ (fun j : ℕ => if j = 0 then c else k J₀ + c + j) 0 := by simp
      have hB₂ := hB 1 (fun j : ℕ => if j = 0 then c else k J₀ + c + j) hk₂mono hk₂0
      have hB₂' : (∫⁻ x : ℤ, (⨆ i ∈ Finset.Ico c (k J₀ + c + 1), ‖A i x - A c x‖ₑ) ^ (2 : ℝ)
          ∂MeasureTheory.Measure.count) ≤ B := by
        rw [oscZ] at hB₂
        simpa using hB₂
      have hpt : ∀ x : ℤ, (⨆ i ∈ Finset.Ico (k (J₀ - 1)) (k ((J₀ - 1) + 1)),
            ‖A i x - A (k (J₀ - 1)) x‖ₑ) ^ (2 : ℝ)
          ≤ 4 * ((⨆ i ∈ Finset.Ico c (k J₀ + c + 1), ‖A i x - A c x‖ₑ) ^ (2 : ℝ)
              + ‖A c x‖ₑ ^ (2 : ℝ)) := by
        intro x
        have hsup : (⨆ i ∈ Finset.Ico (k (J₀ - 1)) (k ((J₀ - 1) + 1)),
              ‖A i x - A (k (J₀ - 1)) x‖ₑ)
            ≤ (⨆ i ∈ Finset.Ico c (k J₀ + c + 1), ‖A i x - A c x‖ₑ) + ‖A c x‖ₑ := by
          refine iSup_le (fun i => iSup_le (fun hi => ?_))
          have hi' : i ∈ Finset.Ico (k (J₀ - 1)) (k J₀) := by
            simpa [Nat.sub_add_cancel hJ₀pos] using hi
          rw [Finset.mem_Ico] at hi'
          have hbase : A (k (J₀ - 1)) x = 0 := congrFun (hvan _ hJ₀lt) x
          rw [hbase, sub_zero]
          by_cases hic : i < c
          · rw [hvan i hic]; simp
          · have hic' : c ≤ i := Nat.le_of_not_lt hic
            have hi2 : i ∈ Finset.Ico c (k J₀ + c + 1) := by
              rw [Finset.mem_Ico]
              exact ⟨hic', by omega⟩
            calc ‖A i x‖ₑ = ‖A i x - A c x + A c x‖ₑ := by rw [sub_add_cancel]
              _ ≤ ‖A i x - A c x‖ₑ + ‖A c x‖ₑ := enorm_add_le _ _
              _ ≤ _ := add_le_add (le_iSup₂_of_le i hi2 le_rfl) le_rfl
        calc (⨆ i ∈ Finset.Ico (k (J₀ - 1)) (k (J₀ - 1 + 1)),
              ‖A i x - A (k (J₀ - 1)) x‖ₑ) ^ (2 : ℝ)
            ≤ ((⨆ i ∈ Finset.Ico c (k J₀ + c + 1), ‖A i x - A c x‖ₑ) + ‖A c x‖ₑ) ^ (2:ℝ) :=
              ENNReal.rpow_le_rpow hsup (by norm_num)
          _ ≤ 4 * ((⨆ i ∈ Finset.Ico c (k J₀ + c + 1), ‖A i x - A c x‖ₑ) ^ (2:ℝ)
              + ‖A c x‖ₑ ^ (2:ℝ)) := Lacunary.add_sq_le _ _
      calc fam (J₀ - 1)
          = ∫⁻ x : ℤ, (⨆ i ∈ Finset.Ico (k (J₀ - 1)) (k ((J₀ - 1) + 1)),
              ‖A i x - A (k (J₀ - 1)) x‖ₑ) ^ (2 : ℝ) ∂MeasureTheory.Measure.count := by
            rw [hfam]
        _ ≤ ∫⁻ x : ℤ, 4 * ((⨆ i ∈ Finset.Ico c (k J₀ + c + 1), ‖A i x - A c x‖ₑ) ^ (2:ℝ)
              + ‖A c x‖ₑ ^ (2:ℝ)) ∂MeasureTheory.Measure.count := lintegral_mono hpt
        _ = 4 * ((∫⁻ x : ℤ, (⨆ i ∈ Finset.Ico c (k J₀ + c + 1), ‖A i x - A c x‖ₑ) ^ (2:ℝ)
              ∂MeasureTheory.Measure.count)
              + ∫⁻ x : ℤ, ‖A c x‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count) := by
            rw [lintegral_const_mul' _ _ (by norm_num),
              lintegral_add_left (measurable_of_countable _)]
        _ ≤ 4 * (B + C₀) :=
            mul_le_mul_of_nonneg_left (add_le_add hB₂' (hC₀ c)) (by norm_num)
        _ = 4 * B + 4 * C₀ := by ring
    have hsplit : (∑ j ∈ Finset.range J, fam j)
        = (∑ j ∈ Finset.Ico J₀ J, fam j)
          + (∑ j ∈ (Finset.range J).filter (fun j => k j < c), fam j) := by
      have h1 : (Finset.range J).filter (fun j => c ≤ k j) = Finset.Ico J₀ J := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
        constructor
        · rintro ⟨hjJ, hj⟩
          exact ⟨Nat.le_of_not_lt (fun h => hJ₀min j h hj), hjJ⟩
        · rintro ⟨h1, h2⟩
          exact ⟨h2, le_trans hJ₀spec (hk.monotone h1)⟩
      have h2 : (Finset.range J).filter (fun j => ¬ c ≤ k j)
          = (Finset.range J).filter (fun j => k j < c) := by
        congr 1
        ext j
        simp only [not_le]
      rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.range J)
        (p := fun j => c ≤ k j) (f := fam), h1, h2]
    have hgoal : oscZ A J k = ∑ j ∈ Finset.range J, fam j := rfl
    rw [hgoal, hsplit]
    calc (∑ j ∈ Finset.Ico J₀ J, fam j) + (∑ j ∈ (Finset.range J).filter (fun j => k j < c), fam j)
        ≤ B + (4 * B + 4 * C₀) := add_le_add htail hhead
      _ = 5 * B + 4 * C₀ := by ring


/-! ## Bookkeeping lemmas for the final constant -/

private lemma ofReal_nat_mul (n : ℕ) (b : ℝ) :
    ENNReal.ofReal ((n : ℝ) * b) = (n : ENNReal) * ENNReal.ofReal b := by
  rw [← ENNReal.ofReal_natCast n, ENNReal.ofReal_mul (by positivity)]

private lemma ofReal_mul_add_ofReal_mul (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (I : ENNReal) :
    ENNReal.ofReal a * I + ENNReal.ofReal b * I = ENNReal.ofReal (a + b) * I := by
  rw [← add_mul, ENNReal.ofReal_add ha hb]

private lemma ofReal_sum_four_mul (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (I : ENNReal) :
    (ENNReal.ofReal a + ENNReal.ofReal b) * I + (ENNReal.ofReal c + ENNReal.ofReal d) * I
      = ENNReal.ofReal (a + b + c + d) * I := by
  rw [add_mul, add_mul,
    ofReal_mul_add_ofReal_mul a b ha hb I,
    ofReal_mul_add_ofReal_mul c d hc hd I,
    ofReal_mul_add_ofReal_mul (a + b) (c + d) (by linarith) (by linarith) I,
    show a + b + (c + d) = a + b + c + d from by ring]

/-! ## Elementary real arithmetic, isolated for speed -/

private lemma one_le_add_two_sq (m : ℕ) : (1:ℝ) ≤ ((m:ℝ)+2)^2 := by
  have h : (1:ℝ) ≤ (m:ℝ)+2 := by
    have h0 : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
    linarith
  calc (1:ℝ) = 1^2 := by norm_num
    _ ≤ ((m:ℝ)+2)^2 := pow_le_pow_left₀ (by norm_num) h 2

private lemma one_le_add_two_pow4 (m : ℕ) : (1:ℝ) ≤ ((m:ℝ)+2)^4 := by
  have h : (1:ℝ) ≤ (m:ℝ)+2 := by
    have h0 : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
    linarith
  calc (1:ℝ) = 1^4 := by norm_num
    _ ≤ ((m:ℝ)+2)^4 := pow_le_pow_left₀ (by norm_num) h 4

private lemma sixteen_le_thousand_pow4 (m : ℕ) : (16:ℝ) ≤ 1000 * ((m:ℝ)+2)^4 := by
  have h := one_le_add_two_pow4 m
  linarith

private lemma mul_pow2_le_thousand_pow4 (m : ℕ) :
    (128:ℝ) * ((m:ℝ)+2)^2 ≤ 1000 * ((m:ℝ)+2)^4 := by
  have h2 := one_le_add_two_sq m
  have h4 := one_le_add_two_pow4 m
  nlinarith [h2, h4]

private lemma logTerm_le_KM (P : Polynomial ℤ) (hc0 : 0 ≤ P.leadingCoeff) (m Mw : ℕ) :
    (Real.log (((polyBlockT P m).card : ℝ) + 2)) ^ 2 + (Mw : ℝ) + 1
      ≤ (((P.leadingCoeff.toNat : ℝ) + 5) ^ 2 + (Mw : ℝ) + 1) * ((m:ℝ)+2)^2 := by
  have hlog := log_polyBlockT_le P hc0 m
  have hlog0 : 0 ≤ Real.log (((polyBlockT P m).card : ℝ) + 2) := by
    refine Real.log_nonneg ?_
    have hc : (0:ℝ) ≤ ((polyBlockT P m).card : ℝ) := Nat.cast_nonneg _
    linarith
  have hsq : (Real.log (((polyBlockT P m).card : ℝ) + 2)) ^ 2
      ≤ (((P.leadingCoeff.toNat : ℝ) + 5) * ((m:ℝ)+2)) ^ 2 :=
    pow_le_pow_left₀ hlog0 hlog 2
  have hsq' : (((P.leadingCoeff.toNat : ℝ) + 5) * ((m:ℝ)+2)) ^ 2
      = ((P.leadingCoeff.toNat : ℝ) + 5) ^ 2 * ((m:ℝ)+2)^2 := by ring
  have hm2 := one_le_add_two_sq m
  have hMw0 : (0:ℝ) ≤ (Mw : ℝ) := Nat.cast_nonneg _
  have hq0 : (0:ℝ) ≤ ((P.leadingCoeff.toNat : ℝ) + 5) := by positivity
  have e1 : (Mw:ℝ) ≤ (Mw:ℝ) * ((m:ℝ)+2)^2 := by nlinarith [hm2, hMw0]
  have e2 : (1:ℝ) ≤ 1 * ((m:ℝ)+2)^2 := by linarith [hm2]
  nlinarith [hsq, hsq', e1, e2, hm2, hMw0, hq0]

private lemma hX_arith (C₁ A KM Cε Cj Bm dec L : ℝ) (m : ℕ)
    (hL0 : 0 ≤ L) (hL : L ≤ KM * ((m:ℝ)+2)^2) (hdec0 : 0 ≤ dec) :
    20 * (C₁ * (A * dec) * L) ^ 2 + 16 * (A * dec) ^ 2 + 16 * (Cε * dec) ^ 2
      + 16 * (8 * (((Cj + 2) * ((m:ℝ)+2) * (Bm + A)) * dec) ^ 2)
      ≤ (1000 * ((C₁ * A * KM) ^ 2 + A ^ 2 + Cε ^ 2 + ((Cj + 2) * (Bm + A)) ^ 2) + 1000)
        * dec ^ 2 * ((m:ℝ)+2)^4 := by
  have h16 := sixteen_le_thousand_pow4 m
  have h128 := mul_pow2_le_thousand_pow4 m
  have e1 : 20 * (C₁ * (A * dec) * L) ^ 2
      ≤ 1000 * (C₁ * A * KM) ^ 2 * (dec ^ 2 * ((m:ℝ)+2)^4) := by
    have h1 : L ^ 2 ≤ (KM * ((m:ℝ)+2)^2) ^ 2 := pow_le_pow_left₀ hL0 hL 2
    calc 20 * (C₁ * (A * dec) * L) ^ 2
        = 20 * ((C₁ * (A * dec)) ^ 2 * L ^ 2) := by ring
      _ ≤ 20 * ((C₁ * (A * dec)) ^ 2 * (KM * ((m:ℝ)+2)^2) ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (sq_nonneg _)) (by norm_num)
      _ = 20 * ((C₁ * A * KM) ^ 2 * (dec ^ 2 * ((m:ℝ)+2)^4)) := by ring
      _ ≤ 1000 * ((C₁ * A * KM) ^ 2 * (dec ^ 2 * ((m:ℝ)+2)^4)) :=
          mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ = 1000 * (C₁ * A * KM) ^ 2 * (dec ^ 2 * ((m:ℝ)+2)^4) := by ring
  have e2 : 16 * (A * dec) ^ 2 ≤ 1000 * A ^ 2 * (dec ^ 2 * ((m:ℝ)+2)^4) := by
    have hAd : 0 ≤ A ^ 2 * dec ^ 2 := by positivity
    calc 16 * (A * dec) ^ 2 = 16 * (A ^ 2 * dec ^ 2) := by ring
      _ ≤ (1000 * ((m:ℝ)+2)^4) * (A ^ 2 * dec ^ 2) :=
          mul_le_mul_of_nonneg_right h16 hAd
      _ = 1000 * A ^ 2 * (dec ^ 2 * ((m:ℝ)+2)^4) := by ring
  have e3 : 16 * (Cε * dec) ^ 2 ≤ 1000 * Cε ^ 2 * (dec ^ 2 * ((m:ℝ)+2)^4) := by
    have hAd : 0 ≤ Cε ^ 2 * dec ^ 2 := by positivity
    calc 16 * (Cε * dec) ^ 2 = 16 * (Cε ^ 2 * dec ^ 2) := by ring
      _ ≤ (1000 * ((m:ℝ)+2)^4) * (Cε ^ 2 * dec ^ 2) :=
          mul_le_mul_of_nonneg_right h16 hAd
      _ = 1000 * Cε ^ 2 * (dec ^ 2 * ((m:ℝ)+2)^4) := by ring
  have e4 : 16 * (8 * (((Cj + 2) * ((m:ℝ)+2) * (Bm + A)) * dec) ^ 2)
      ≤ 1000 * ((Cj + 2) * (Bm + A)) ^ 2 * (dec ^ 2 * ((m:ℝ)+2)^4) := by
    have hAd : 0 ≤ ((Cj + 2) * (Bm + A)) ^ 2 * dec ^ 2 := by positivity
    calc 16 * (8 * (((Cj + 2) * ((m:ℝ)+2) * (Bm + A)) * dec) ^ 2)
        = (128 * ((m:ℝ)+2)^2) * (((Cj + 2) * (Bm + A)) ^ 2 * dec ^ 2) := by ring
      _ ≤ (1000 * ((m:ℝ)+2)^4) * (((Cj + 2) * (Bm + A)) ^ 2 * dec ^ 2) :=
          mul_le_mul_of_nonneg_right h128 hAd
      _ = 1000 * ((Cj + 2) * (Bm + A)) ^ 2 * (dec ^ 2 * ((m:ℝ)+2)^4) := by ring
  have hS : 0 ≤ dec ^ 2 * ((m:ℝ)+2)^4 := by positivity
  nlinarith [e1, e2, e3, e4, hS, sq_nonneg (C₁ * A * KM), sq_nonneg A, sq_nonneg Cε,
    sq_nonneg ((Cj + 2) * (Bm + A))]

private lemma sqrt_const_arith (BIG dec : ℝ) (m : ℕ) (hBIG : 0 < BIG) (hdec0 : 0 ≤ dec) :
    BIG * dec ^ 2 * ((m:ℝ)+2)^4 ≤ ((Real.sqrt BIG + 1) * dec * ((m:ℝ)+2)^2)^2 := by
  have h1 : (0:ℝ) ≤ Real.sqrt BIG := Real.sqrt_nonneg BIG
  have h2 : BIG ≤ (Real.sqrt BIG + 1) ^ 2 := by
    have h3 := Real.sq_sqrt (le_of_lt hBIG)
    nlinarith [h3, h1]
  have hS : 0 ≤ dec ^ 2 * ((m:ℝ)+2)^4 := by positivity
  nlinarith [h2, hS]


lemma oscZ_block_lacunary_v2_core (P : Polynomial ℤ) (hc : 0 < P.leadingCoeff) (hd : 2 ≤ P.natDegree)
    (ρ : ℝ) (hρ : 1 < ρ) (K₁ : ℕ)
    (hcut₁ : ∀ (m N : ℕ), K₁ ≤ N → 4 ^ m ≤ N →
      (P.leadingCoeff : ℝ) * (Work.BourgainPlan.Oscillation.polyDilN P N)⁻¹ ≤ Work.BourgainPlan.Oscillation.polyArcRadN P N ∧
      (Work.BourgainPlan.Oscillation.polyDilN P N)⁻¹ < 1 / (2 * (P.leadingCoeff : ℝ)) ∧
      (Work.BourgainPlan.Oscillation.polyDilN P N)⁻¹ ≤ (1 / ((P.leadingCoeff : ℝ)^2 * (4:ℝ)^(m+1))) / 3)
    (Hcutidx : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ), ∃ j₀ : ℕ,
      max K₁ (2 ^ (4*m+4)) ≤ Work.BourgainPlan.Oscillation.lacScale ρ j₀ ∧ (j₀ : ℝ) ≤ C * ((m:ℝ)+2))
    (Hcore : Work.BourgainPlan.Oscillation.OscZCoreLacunary)
    (Herr : Work.BourgainPlan.Oscillation.OscZErrLacunary P ρ)
    (Hwin : ∃ M : ℕ, ∀ (j t : ℕ),
      (Work.BourgainPlan.Oscillation.polyDilN P (Work.BourgainPlan.Oscillation.lacScale ρ t))⁻¹ ≤ (2:ℝ)^(-(j:ℝ)-1) →
      (Work.BourgainPlan.Oscillation.polyDilN P (Work.BourgainPlan.Oscillation.lacScale ρ (t+M)))⁻¹ ≤ (2:ℝ)^(-(j:ℝ)-2)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (g : ℤ → ℂ) (s : Finset ℤ), (∀ n, n ∉ s → g n = 0) →
      ∀ (J : ℕ) (k : ℕ → ℕ), StrictMono k →
        Work.BourgainPlan.Oscillation.oscZ
            (fun i x => Work.BourgainPlan.Oscillation.polyModelBlockOp P g s m (Work.BourgainPlan.Oscillation.lacScale ρ i) x) J k
          ≤ ENNReal.ofReal (C * (2:ℝ)^(-(m:ℝ) * Work.BourgainPlan.Maximal.polySig P) * ((m:ℝ)+2)^2) ^ 2 *
              ∫⁻ x : ℤ, ‖g x‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Hcore
  obtain ⟨Cε, hCεpos, hCε⟩ := Herr
  obtain ⟨Cj, hCjpos, hCj⟩ := Hcutidx
  obtain ⟨Mw, hMw⟩ := Hwin
  obtain ⟨A, hApos, hAcap⟩ := polyWeight_cap_Icc P hc hd
  obtain ⟨Bm, hBmpos, hBm⟩ := norm_polyModelQBlock_le_capN P hc hd
  have hlc1 : (1:ℝ) ≤ (P.leadingCoeff : ℝ) := by
    have h1 : (1:ℤ) ≤ P.leadingCoeff := by omega
    exact_mod_cast h1
  have hσpos : 0 < polySig P := by rw [polySig, powSig]; positivity
  set KM : ℝ := ((P.leadingCoeff.toNat : ℝ) + 5) ^ 2 + (Mw : ℝ) + 1 with hKM
  set BIG : ℝ := 1000 * ((C₁ * A * KM) ^ 2 + A ^ 2 + Cε ^ 2 + ((Cj + 2) * (Bm + A)) ^ 2) + 1000
    with hBIG
  have hBIGpos : 0 < BIG := by rw [hBIG]; positivity
  refine ⟨Real.sqrt BIG + 1, by positivity, ?_⟩
  intro m g s hs J k hk
  -- ===================== setup =====================
  set dec : ℝ := (2:ℝ) ^ (-(m:ℝ) * polySig P) with hdec
  have hdecpos : 0 < dec := by rw [hdec]; exact Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) _
  have hdec0 : 0 ≤ dec := hdecpos.le
  have hdec1 : dec ≤ 1 := by
    rw [hdec]
    have h : -(m:ℝ) * polySig P ≤ 0 := by
      have hm : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
      nlinarith
    calc (2:ℝ) ^ (-(m:ℝ) * polySig P) ≤ (2:ℝ) ^ (0:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) h
      _ = 1 := Real.rpow_zero 2
  set T : Finset (ℝ × ℂ) := polyBlockT P m with hT
  set δ : ℝ := 1 / ((P.leadingCoeff : ℝ)^2 * (4:ℝ)^(m+1)) with hδ
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hδle : δ ≤ 1/2 := by
    rw [hδ, div_le_iff₀ (by positivity)]
    have h4 : (4:ℝ) ≤ (4:ℝ)^(m+1) := by
      calc (4:ℝ) = (4:ℝ)^1 := (pow_one 4).symm
        _ ≤ (4:ℝ)^(m+1) := pow_le_pow_right₀ (by norm_num) (by omega)
    nlinarith [hlc1, h4, sq_nonneg ((P.leadingCoeff:ℝ) - 1)]
  set cap : ℝ := A * dec with hcap
  have hcappos : 0 < cap := by rw [hcap]; positivity
  have hcap0 : 0 ≤ cap := hcappos.le
  set L : ℝ := (Real.log ((T.card : ℝ) + 2)) ^ 2 + (Mw : ℝ) + 1 with hLdef
  have hL0 : 0 ≤ L := by
    rw [hLdef]
    have h1 : (0:ℝ) ≤ Real.log ((T.card : ℝ) + 2) := by
      refine Real.log_nonneg ?_
      have : (0:ℝ) ≤ (T.card : ℝ) := Nat.cast_nonneg _
      linarith
    have h2 : (0:ℝ) ≤ (Mw : ℝ) := Nat.cast_nonneg _
    positivity
  -- the cutoff index
  obtain ⟨j₀, hj₀max, hj₀card⟩ := hCj m
  set N₀ : ℕ := lacScale ρ j₀ with hN₀
  have hN₀spec : max K₁ (2 ^ (4*m+4)) ≤ N₀ := by rw [hN₀]; exact hj₀max
  have hK₁N₀ : K₁ ≤ N₀ := le_trans (le_max_left _ _) hN₀spec
  have h4mN₀ : 2 ^ (4*m+4) ≤ N₀ := le_trans (le_max_right _ _) hN₀spec
  have hN₀pos : 1 ≤ N₀ := le_trans Nat.one_le_two_pow h4mN₀
  have hex : ∃ i : ℕ, N₀ ≤ lacScale ρ i := ⟨j₀, le_of_eq hN₀⟩
  set c : ℕ := Nat.find hex with hcdef
  have hcspec : N₀ ≤ lacScale ρ c := by rw [hcdef]; exact Nat.find_spec hex
  have hcmin : ∀ i, i < c → ¬ (N₀ ≤ lacScale ρ i) := by
    intro i hi; rw [hcdef] at hi; exact Nat.find_min hex hi
  have hcj₀ : c ≤ j₀ := by rw [hcdef]; exact Nat.find_le (le_of_eq hN₀)
  have hccard : (c : ℝ) ≤ Cj * ((m:ℝ)+2) := le_trans (by exact_mod_cast hcj₀) hj₀card
  -- elementary scale facts
  have hlac1 : ∀ i, 1 ≤ lacScale ρ i := by
    intro i; rw [lacScale]; exact Nat.le_floor (by simpa using one_le_pow₀ hρ.le)
  have hlacpos : ∀ i, (0:ℝ) < (lacScale ρ i : ℝ) := fun i =>
    Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one (hlac1 i))
  have hcutc : K₁ ≤ lacScale ρ c ∧ 4 ^ m ≤ lacScale ρ c := by
    refine ⟨le_trans hK₁N₀ hcspec, ?_⟩
    have h1 : (4:ℕ)^m ≤ 2^(4*m+4) := by
      have h : (4:ℕ)^m = 2^(2*m) := by rw [show (4:ℕ) = 2^2 by norm_num, ← pow_mul]
      rw [h]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    exact le_trans h1 (le_trans h4mN₀ hcspec)
  have hcutsc : ∀ t, c ≤ t → K₁ ≤ lacScale ρ t ∧ 4 ^ m ≤ lacScale ρ t := fun t ht =>
    ⟨le_trans hcutc.1 (lacScale_mono ρ hρ.le ht), le_trans hcutc.2 (lacScale_mono ρ hρ.le ht)⟩
  set rf : ℕ → ℝ := fun i => (polyDilN P (lacScale ρ i))⁻¹ with hrf
  have hrfpos : ∀ i, 0 < rf i := fun i => inv_pos.mpr (pow_pos (hlacpos i) _)
  have hrfanti : Antitone rf := by
    intro a b hab
    rw [hrf]
    refine inv_anti₀ (pow_pos (hlacpos a) _) ?_
    exact pow_le_pow_left₀ (hlacpos a).le (by exact_mod_cast lacScale_mono ρ hρ.le hab) _
  have hrfc : rf c ≤ δ/3 := by
    rw [hrf, hδ]
    exact (hcut₁ m (lacScale ρ c) hcutc.1 hcutc.2).2.2
  have hrf_le : ∀ t, c ≤ t → rf t ≤ δ/3 := fun t ht => le_trans (hrfanti ht) hrfc
  have hsmall : ∀ t, c ≤ t → (polyDilN P (lacScale ρ t))⁻¹ < 1 / (2 * (P.leadingCoeff : ℝ)) :=
    fun t ht => (hcut₁ m (lacScale ρ t) (hcutsc t ht).1 (hcutsc t ht).2).2.1
  have h1le : ∀ t, c ≤ t → 1 ≤ lacScale ρ t :=
    fun t ht => le_trans hN₀pos (le_trans hcspec (lacScale_mono ρ hρ.le ht))
  have hsepT : ∀ p ∈ T, ∀ q ∈ T, p ≠ q → ∀ l : ℤ, δ ≤ |p.1 - q.1 + (l : ℝ)| := by
    intro p hp q hq hpq l
    rw [hδ]
    exact polyBlockT_sep P hc m p (by rwa [hT] at hp) q (by rwa [hT] at hq) hpq l
  have hcapT : ∀ p ∈ T, ‖p.2‖ ≤ cap := by
    intro p hp
    rw [hT, polyBlockT, Finset.mem_image] at hp
    obtain ⟨⟨⟨q, a⟩, s'⟩, hmem, rfl⟩ := hp
    obtain ⟨hb, hs'⟩ := Finset.mem_product.mp hmem
    rw [Finset.mem_range] at hs'
    obtain ⟨h1, h2, h3, h4⟩ := mem_blockPair.mp hb
    have hsI : ((s' : ℤ)) ∈ Finset.Icc (-1 : ℤ) P.leadingCoeff := by
      simp only [Finset.mem_Icc]
      have hcn : ((P.leadingCoeff.toNat : ℕ) : ℤ) = P.leadingCoeff :=
        Int.toNat_of_nonneg (le_of_lt hc)
      constructor <;> omega
    have hbnd := hAcap m q a ((s' : ℤ)) h1 h2 h4 hsI
    rw [hcap, hdec]
    simpa [Complex.norm_conj] using hbnd
  -- the sharp-core identification
  have hId : ∀ t, c ≤ t → ∀ θ ∈ Set.Ioo (0:ℝ) 1,
      polyBlockCoreN P m (lacScale ρ t) θ = coreW T δ θ * unNbhd T (rf t) θ := by
    intro t ht θ hθ
    rw [polyBlockCoreN_eq_weighted P hc hd (h1le t ht) (hsmall t ht) θ hθ.1 hθ.2]
    exact (coreW_mul_unNbhd T δ hδpos hsepT (hrf_le t ht) θ).symm
  -- ===================== the two multipliers =====================
  set mC : ℕ → ℝ → ℂ := fun i θ => if c ≤ i then coreW T δ θ * unNbhd T (rf i) θ else 0
    with hmC
  set mE : ℕ → ℝ → ℂ := fun i θ =>
    starRingEnd ℂ (polyModelQBlock P m (lacScale ρ i) θ) - mC i θ with hmE
  have hmC_meas : ∀ i, Measurable (mC i) := by
    intro i
    by_cases h : c ≤ i
    · have hh : mC i = fun θ => coreW T δ θ * unNbhd T (rf i) θ := by
        funext θ; rw [hmC]; simp [h]
      rw [hh]
      exact (measurable_coreW T δ).mul (measurable_unNbhd T (rf i))
    · have hh : mC i = fun _ => (0:ℂ) := by funext θ; rw [hmC]; simp [h]
      rw [hh]; exact measurable_const
  have hmE_meas : ∀ i, Measurable (mE i) := by
    intro i
    rw [hmE]
    exact Measurable.sub
      (Complex.continuous_conj.measurable.comp (measurable_polyModelQBlock P m _)) (hmC_meas i)
  have hmC_bound : ∀ i θ, ‖mC i θ‖ ≤ cap := by
    intro i θ
    by_cases h : c ≤ i
    · have hh : mC i θ = coreW T δ θ * unNbhd T (rf i) θ := by rw [hmC]; simp [h]
      rw [hh]
      calc ‖coreW T δ θ * unNbhd T (rf i) θ‖ = ‖coreW T δ θ‖ * ‖unNbhd T (rf i) θ‖ := norm_mul _ _
        _ ≤ cap * 1 := mul_le_mul (norm_coreW_le T δ hδpos hsepT hcap0 hcapT θ)
            (norm_unNbhd_le_one' T (rf i) θ) (norm_nonneg _) hcap0
        _ = cap := mul_one cap
    · have hh : mC i θ = 0 := by rw [hmC]; simp [h]
      rw [hh, norm_zero]; exact hcap0
  have hmE_bound : ∀ i θ, ‖mE i θ‖ ≤ (Bm + A) * dec := by
    intro i θ
    have hh : mE i θ = starRingEnd ℂ (polyModelQBlock P m (lacScale ρ i) θ) - mC i θ := by
      rw [hmE]
    rw [hh]
    refine le_trans (norm_sub_le _ _) ?_
    have h1 : ‖starRingEnd ℂ (polyModelQBlock P m (lacScale ρ i) θ)‖ ≤ Bm * dec := by
      rw [Complex.norm_conj]
      simpa [hdec] using hBm m (lacScale ρ i) θ
    have h2 : ‖mC i θ‖ ≤ A * dec := by
      simpa [hcap] using hmC_bound i θ
    nlinarith [hdecpos, h1, h2]
  -- ===================== the split of the model =====================
  have hKE : ∀ i x, polyModelBlockOp P g s m (lacScale ρ i) x
      = errOp (mC i) g s x + errOp (mE i) g s x := by
    intro i x
    rw [polyModelBlockOp_eq_errOp]
    have hsum : (fun θ => starRingEnd ℂ (polyModelQBlock P m (lacScale ρ i) θ))
        = (fun θ => mC i θ + mE i θ) := by
      funext θ
      rw [hmE]
      ring
    rw [hsum]
    exact errOp_add_of_bound (mC i) (mE i) (hmC_meas i) (hmE_meas i)
      (fun θ _ => hmC_bound i θ) (fun θ _ => hmE_bound i θ) g s x
  set I : ENNReal := ∫⁻ x : ℤ, ‖g x‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count with hI
  have hstep_split : oscZ (fun i x => polyModelBlockOp P g s m (lacScale ρ i) x) J k
      ≤ 4 * oscZ (fun i x => errOp (mC i) g s x) J k
        + 4 * oscZ (fun i x => errOp (mE i) g s x) J k :=
    oscZ_add_le _ _ _ hKE J k
  -- ===================== the core =====================
  have hcorefam : ∀ (J' : ℕ) (k' : ℕ → ℕ), StrictMono k' → c ≤ k' 0 →
      oscZ (fun i x => errOp (mC i) g s x) J' k'
        ≤ ENNReal.ofReal ((C₁ * cap * L) ^ 2) * I := by
    intro J' k' hk' hk'0
    have hwin : ∀ (j t : ℕ), rf t ≤ (2:ℝ) ^ (-(j:ℝ)-1) →
        rf (t + Mw) ≤ (2:ℝ) ^ (-(j:ℝ)-2) := fun j t ht => hMw j t ht
    have h := hC₁ T cap δ hδpos hδle hcap0 hcapT hsepT rf Mw hrfpos hrfanti hwin c
      (fun t ht => hrf_le t ht) J' k' hk' hk'0 g s hs
    have hfam : (fun i x => errOp (mC i) g s x) = (fun i x => ∫ θ in (0 : ℝ)..1,
        (if c ≤ i then ∑ p ∈ T, p.2 * perNbhd p.1 (rf i) θ else 0) *
        (∑ n ∈ s, g n * Complex.exp (2 * Real.pi * Complex.I * ((n : ℤ) : ℂ) * (θ : ℂ))) *
        Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (θ : ℂ)))) := by
      funext i x
      by_cases hci : c ≤ i
      · have hmult : ∀ θ, mC i θ = ∑ p ∈ T, p.2 * perNbhd p.1 (rf i) θ := by
          intro θ
          rw [hmC]
          simp only [hci, ↓reduceIte]
          exact coreW_mul_unNbhd T δ hδpos hsepT (hrf_le i hci) θ
        rw [show errOp (mC i) g s x = ∫ θ in (0:ℝ)..1,
            (∑ p ∈ T, p.2 * perNbhd p.1 (rf i) θ) * Lacunary.trigP s g θ
              * Lacunary.Echar x θ from by
          unfold errOp
          refine intervalIntegral.integral_congr (fun θ _ => ?_)
          rw [hmult θ]]
        simp only [hci, ↓reduceIte, Lacunary.trigP, Lacunary.Echar]
      · have hmult : ∀ θ, mC i θ = 0 := by
          intro θ; rw [hmC]; simp only [hci, ↓reduceIte]
        have hz : (fun θ => mC i θ * Lacunary.trigP s g θ * Lacunary.Echar x θ) = fun _ => (0:ℂ) := by
          funext θ; rw [hmult θ]; ring
        rw [show errOp (mC i) g s x = 0 from by
          unfold errOp; rw [hz]; simp]
        simp [hci]
    rw [hfam]
    exact h
  have hcore_osc : oscZ (fun i x => errOp (mC i) g s x) J k
      ≤ 5 * (ENNReal.ofReal ((C₁ * cap * L) ^ 2) * I)
        + 4 * (ENNReal.ofReal (cap ^ 2) * I) := by
    by_cases hkc : c ≤ k 0
    · refine le_trans (hcorefam J k hk hkc) ?_
      calc ENNReal.ofReal ((C₁ * cap * L) ^ 2) * I
          ≤ 5 * (ENNReal.ofReal ((C₁ * cap * L) ^ 2) * I) :=
            le_mul_of_one_le_left' (by norm_num : (1:ENNReal) ≤ 5)
        _ ≤ 5 * (ENNReal.ofReal ((C₁ * cap * L) ^ 2) * I)
              + 4 * (ENNReal.ofReal (cap ^ 2) * I) := le_add_of_nonneg_right (by positivity)
    · have hC₀ : ∀ i, ∫⁻ x : ℤ, ‖errOp (mC i) g s x‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (cap ^ 2) * I := fun i =>
        lintegral_errOp_le (mC i) (hmC_meas i) (A := cap) hcap0
          (fun θ => hmC_bound i θ) g s hs
      have hvanC : ∀ i, i < c → (fun i x => errOp (mC i) g s x) i = 0 := by
        intro i hi
        funext x
        have hmult : ∀ θ, mC i θ = 0 := by
          intro θ
          rw [hmC]; simp only [not_le.mpr hi, ↓reduceIte]
        have hz : (fun θ => mC i θ * Lacunary.trigP s g θ * Lacunary.Echar x θ)
            = fun _ => (0:ℂ) := by
          funext θ; rw [hmult θ]; ring
        show errOp (mC i) g s x = 0
        unfold errOp
        rw [hz]
        simp
      have h := oscZ_le_head_p (fun i x => errOp (mC i) g s x) J k hk c hvanC
        (fun J' k' hk' hk'0 => hcorefam J' k' hk' hk'0) hC₀
      exact h
  -- ===================== the error =====================
  have herr_split : oscZ (fun i x => errOp (mE i) g s x) J k
      ≤ 4 * oscZ (fun i x => if c ≤ i then errOp (mE i) g s x else 0) J k
        + 4 * oscZ (fun i x => if i < c then errOp (mE i) g s x else 0) J k := by
    refine oscZ_add_le _ _ _ ?_ J k
    intro i x
    by_cases h : c ≤ i
    · rw [if_pos h, if_neg (not_lt.mpr h)]; ring
    · have h' : i < c := not_le.mp h
      rw [if_neg h, if_pos h']; ring
  -- the fine part: the profile-replacement error above the cutoff
  set FineFam : ℕ → ℤ → ℂ := fun i x => if c ≤ i then ∫ θ in (0 : ℝ)..1,
      polyErrMultCutN P m N₀ (lacScale ρ i) θ *
      (∑ n ∈ s, g n * Complex.exp (2 * Real.pi * Complex.I * ((n : ℤ) : ℂ) * (θ : ℂ))) *
      Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (θ : ℂ))) else 0 with hFineFam
  have hFineEq : (fun i x => if c ≤ i then errOp (mE i) g s x else 0) = FineFam := by
    funext i x
    by_cases hci : c ≤ i
    · simp only [hci, ↓reduceIte, hFineFam]
      rw [errOp_congr_Ioo (m' := polyErrMultCutN P m N₀ (lacScale ρ i)) (fun θ hθ => ?_) g s x]
      · unfold errOp
        simp only [Lacunary.trigP, Lacunary.Echar]
      · have hN : N₀ ≤ lacScale ρ i := le_trans hcspec (lacScale_mono ρ hρ.le hci)
        rw [hmE, hmC]
        simp only [hci, ↓reduceIte, polyErrMultCutN, polyErrMultN, polyBlockErrN]
        rw [if_pos hN, if_pos ⟨hθ.1, hθ.2⟩, if_pos hN, hId i hci θ hθ]
    · simp only [hci, ↓reduceIte, hFineFam]
  have hfine : oscZ (fun i x => if c ≤ i then errOp (mE i) g s x else 0) J k
      ≤ ENNReal.ofReal ((Cε * dec) ^ 2) * I := by
    rw [hFineEq]
    have h := hCε m N₀ h4mN₀ c J k hk g s hs
    refine le_trans h ?_
    rw [← ENNReal.ofReal_pow (by positivity : (0:ℝ) ≤ Cε * dec) 2, hI]
  -- the crude part: the model below the cutoff, via the square function
  set A₀ : ℝ := (Cj + 2) * ((m:ℝ)+2) * (Bm + A) * dec with hA₀
  have hA₀0 : 0 ≤ A₀ := by rw [hA₀]; positivity
  have hcrude_id : (fun i x => if i < c then errOp (mE i) g s x else 0)
      = (fun i x => errOp (fun θ => if i < c then mE i θ else 0) g s x) := by
    funext i x
    by_cases h : i < c
    · have hm : (fun θ => if i < c then mE i θ else 0) = mE i := by funext θ; simp [h]
      rw [if_pos h, hm]
    · have hm : (fun θ => if i < c then mE i θ else 0) = fun _ => (0:ℂ) := by
        funext θ; simp [h]
      rw [if_neg h, hm]
      unfold errOp
      simp
  have hcrude : oscZ (fun i x => if i < c then errOp (mE i) g s x else 0) J k
      ≤ ENNReal.ofReal (8 * A₀ ^ 2) * I := by
    rw [hcrude_id]
    set mF : ℕ → ℝ → ℂ := fun j θ => if j < c then mE j θ else 0 with hmF
    have hmF_meas : ∀ j, Measurable (mF j) := by
      intro j
      by_cases h : j < c
      · have hh : mF j = mE j := by funext θ; rw [hmF]; simp [h]
        rw [hh]; exact hmE_meas j
      · have hh : mF j = fun _ => (0:ℂ) := by funext θ; rw [hmF]; simp [h]
        rw [hh]; exact measurable_const
    have hsumF : ∀ (t : Finset ℕ) (θ : ℝ),
        ∑ j ∈ t, ‖mF j θ‖ₑ ^ (2:ℝ) ≤ ENNReal.ofReal (A₀ ^ 2) := by
      intro t θ
      have hsplit : ∑ j ∈ t, ‖mF j θ‖ₑ ^ (2:ℝ)
          = ∑ j ∈ t.filter (fun j => j < c), ‖mE j θ‖ₑ ^ (2:ℝ) := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl (fun j hj => ?_)
        by_cases h : j < c <;> simp [hmF, h]
      rw [hsplit]
      have hcard : (t.filter (fun j => j < c)).card ≤ c := by
        refine le_trans (Finset.card_le_card (fun j hj => ?_)) (le_of_eq (Finset.card_range c))
        rw [Finset.mem_range]; exact (Finset.mem_filter.mp hj).2
      calc ∑ j ∈ t.filter (fun j => j < c), ‖mE j θ‖ₑ ^ (2:ℝ)
          ≤ ∑ _j ∈ t.filter (fun j => j < c),
              ENNReal.ofReal (((Bm + A) * dec) ^ 2) := by
            refine Finset.sum_le_sum (fun j hj => ?_)
            rw [Commons.Analysis.Fourier.enorm_complex_pow_two]
            exact ENNReal.ofReal_le_ofReal
              (pow_le_pow_left₀ (norm_nonneg _) (hmE_bound j θ) 2)
        _ = ((t.filter (fun j => j < c)).card : ENNReal)
              * ENNReal.ofReal (((Bm + A) * dec) ^ 2) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ = ENNReal.ofReal (((t.filter (fun j => j < c)).card : ℝ) * ((Bm + A) * dec) ^ 2) := by
            rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        _ ≤ ENNReal.ofReal (((Cj + 2) * ((m:ℝ)+2)) * ((Bm + A) * dec) ^ 2) := by
            refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (by positivity))
            calc ((t.filter (fun j => j < c)).card : ℝ) ≤ (c : ℝ) := by exact_mod_cast hcard
              _ ≤ Cj * ((m:ℝ)+2) := hccard
              _ ≤ (Cj + 2) * ((m:ℝ)+2) := by
                  nlinarith [hCjpos, (show (0:ℝ) ≤ (m:ℝ) from Nat.cast_nonneg m)]
        _ ≤ ENNReal.ofReal (A₀ ^ 2) := by
            refine ENNReal.ofReal_le_ofReal ?_
            rw [hA₀]
            have hge1 : (1:ℝ) ≤ (Cj + 2) * ((m:ℝ)+2) := by
              nlinarith [hCjpos, (show (0:ℝ) ≤ (m:ℝ) from Nat.cast_nonneg m)]
            have H : ((Bm + A) * dec) ^ 2
                ≤ ((Cj + 2) * ((m:ℝ)+2)) * ((Bm + A) * dec) ^ 2 := by
              have hX0 : (0:ℝ) ≤ ((Bm + A) * dec) ^ 2 := by positivity
              simpa using mul_le_mul_of_nonneg_right hge1 hX0
            calc ((Cj + 2) * ((m:ℝ)+2)) * ((Bm + A) * dec) ^ 2
                ≤ ((Cj + 2) * ((m:ℝ)+2))
                    * (((Cj + 2) * ((m:ℝ)+2)) * ((Bm + A) * dec) ^ 2) :=
                  mul_le_mul_of_nonneg_left H (by positivity)
              _ = (((Cj + 2) * ((m:ℝ)+2)) * (Bm + A) * dec) ^ 2 := by ring
    have hsqF := errOp_sqFn mF A₀ hA₀0 hmF_meas hsumF g s hs
    have hstep1 : oscZ (fun i x => errOp (mF i) g s x) J k
        ≤ 8 * ∑' i : ℕ, ∫⁻ x : ℤ, ‖errOp (mF i) g s x‖ₑ ^ (2:ℝ)
            ∂MeasureTheory.Measure.count :=
      oscZ_le_eight_tsum _ J k hk
    have hstep2 : (∑' i : ℕ, ∫⁻ x : ℤ, ‖errOp (mF i) g s x‖ₑ ^ (2:ℝ)
          ∂MeasureTheory.Measure.count)
        = ∫⁻ x : ℤ, (∑' i : ℕ, ‖errOp (mF i) g s x‖ₑ ^ (2:ℝ))
            ∂MeasureTheory.Measure.count := by
      simp_rw [MeasureTheory.lintegral_count]
      exact ENNReal.tsum_comm
    calc oscZ (fun i x => errOp (mF i) g s x) J k
        ≤ 8 * ∑' i : ℕ, ∫⁻ x : ℤ, ‖errOp (mF i) g s x‖ₑ ^ (2:ℝ)
            ∂MeasureTheory.Measure.count := hstep1
      _ = 8 * ∫⁻ x : ℤ, (∑' i : ℕ, ‖errOp (mF i) g s x‖ₑ ^ (2:ℝ))
            ∂MeasureTheory.Measure.count := by rw [hstep2]
      _ ≤ 8 * (ENNReal.ofReal (A₀ ^ 2) * I) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          rw [hI]; exact hsqF
      _ = ENNReal.ofReal (8 * A₀ ^ 2) * I := by
          rw [show ENNReal.ofReal (8 * A₀ ^ 2)
                = (8:ENNReal) * ENNReal.ofReal (A₀ ^ 2) from ofReal_nat_mul 8 (A₀ ^ 2)]
          ring
  have herr_osc : oscZ (fun i x => errOp (mE i) g s x) J k
      ≤ 4 * (ENNReal.ofReal ((Cε * dec) ^ 2) * I)
        + 4 * (ENNReal.ofReal (8 * A₀ ^ 2) * I) := by
    refine le_trans herr_split ?_
    exact add_le_add (mul_le_mul_of_nonneg_left hfine (by norm_num))
      (mul_le_mul_of_nonneg_left hcrude (by norm_num))
  -- ===================== the final bookkeeping =====================
  have hLbound : L ≤ KM * ((m:ℝ)+2)^2 := by
    have h := logTerm_le_KM P (le_of_lt hc) m Mw
    simpa [hLdef, hKM, hT] using h
  have hX : 20 * (C₁ * cap * L) ^ 2 + 16 * cap ^ 2 + 16 * (Cε * dec) ^ 2
      + 16 * (8 * A₀ ^ 2) ≤ BIG * dec ^ 2 * ((m:ℝ)+2)^4 := by
    have h := hX_arith C₁ A KM Cε Cj Bm dec L m hL0 hLbound hdec0
    simpa [hcap, hA₀, hBIG] using h
  have hcombine : oscZ (fun i x => polyModelBlockOp P g s m (lacScale ρ i) x) J k
      ≤ ENNReal.ofReal (20 * (C₁ * cap * L) ^ 2 + 16 * cap ^ 2 + 16 * (Cε * dec) ^ 2
          + 16 * (8 * A₀ ^ 2)) * I := by
    refine le_trans hstep_split ?_
    have ha : (4:ENNReal) * oscZ (fun i x => errOp (mC i) g s x) J k
        ≤ 4 * (5 * (ENNReal.ofReal ((C₁ * cap * L) ^ 2) * I)
            + 4 * (ENNReal.ofReal (cap ^ 2) * I)) :=
      mul_le_mul_of_nonneg_left hcore_osc (by norm_num : (0:ENNReal) ≤ 4)
    have hb : (4:ENNReal) * oscZ (fun i x => errOp (mE i) g s x) J k
        ≤ 4 * (4 * (ENNReal.ofReal ((Cε * dec) ^ 2) * I)
            + 4 * (ENNReal.ofReal (8 * A₀ ^ 2) * I)) :=
      mul_le_mul_of_nonneg_left herr_osc (by norm_num : (0:ENNReal) ≤ 4)
    refine le_trans (add_le_add ha hb) ?_
    have e1 : (4:ENNReal) * (5 * (ENNReal.ofReal ((C₁ * cap * L) ^ 2) * I)
          + 4 * (ENNReal.ofReal (cap ^ 2) * I))
        = (ENNReal.ofReal (20 * (C₁ * cap * L) ^ 2) + ENNReal.ofReal (16 * cap ^ 2)) * I := by
      rw [show ENNReal.ofReal (20 * (C₁ * cap * L) ^ 2)
            = (20:ENNReal) * ENNReal.ofReal ((C₁ * cap * L) ^ 2) from
          ofReal_nat_mul 20 ((C₁ * cap * L) ^ 2),
        show ENNReal.ofReal (16 * cap ^ 2)
            = (16:ENNReal) * ENNReal.ofReal (cap ^ 2) from ofReal_nat_mul 16 (cap ^ 2)]
      ring
    have e2 : (4:ENNReal) * (4 * (ENNReal.ofReal ((Cε * dec) ^ 2) * I)
          + 4 * (ENNReal.ofReal (8 * A₀ ^ 2) * I))
        = (ENNReal.ofReal (16 * (Cε * dec) ^ 2) + ENNReal.ofReal (16 * (8 * A₀ ^ 2))) * I := by
      rw [show ENNReal.ofReal (16 * (Cε * dec) ^ 2)
            = (16:ENNReal) * ENNReal.ofReal ((Cε * dec) ^ 2) from
          ofReal_nat_mul 16 ((Cε * dec) ^ 2),
        show ENNReal.ofReal (16 * (8 * A₀ ^ 2))
            = (16:ENNReal) * ENNReal.ofReal (8 * A₀ ^ 2) from ofReal_nat_mul 16 (8 * A₀ ^ 2)]
      ring
    rw [e1, e2]
    exact le_of_eq (ofReal_sum_four_mul (20 * (C₁ * cap * L) ^ 2) (16 * cap ^ 2)
      (16 * (Cε * dec) ^ 2) (16 * (8 * A₀ ^ 2)) (by positivity) (by positivity)
      (by positivity) (by positivity) I)
  refine le_trans hcombine ?_
  refine le_trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hX) bot_le) ?_
  refine mul_le_mul_of_nonneg_right ?_ bot_le
  rw [← ENNReal.ofReal_pow (by positivity : (0:ℝ) ≤ (Real.sqrt BIG + 1) * dec * ((m:ℝ)+2)^2) 2]
  exact ENNReal.ofReal_le_ofReal (sqrt_const_arith BIG dec m hBIGpos hdec0)
