import Mathlib
import Submission.Work.BourgainPlan.Maximal.l2_defs
import Submission.Commons.Analysis.ExponentialSums.quadratic_kernel_model_maximal_l2
import Submission.Commons.Analysis.ExponentialSums.pure_power_kernel_maximal_l2
import Submission.Commons.Analysis.Fourier.maximal_l2_of_fixed_multiplier

/-!
# Dyadic-block decomposition of the general-polynomial major-arc model

This file sets up the *bookkeeping* half of the `ℓ²` maximal inequality for the major-arc model
`polyMajorArcModelPre P (1/4) N` of the non-monic polynomial `P` (see `l2_defs`):

* the `q`-block decomposition of the model by the dyadic range `2^m ≤ q < 2^(m+1)`;
* the block model operator `polyTkBlockMax` and the exact splitting
  `polyTkMax = Σ_m polyTkBlockMax`;
* the assembly `poly_model_maximal_of_block`: a per-block `ℓ²` bound with the correct
  `2^{-mσ}(m+2)²` shape implies the model maximal inequality.

The analytic core (the per-block bound) lives in the companion file.
-/

open Filter Finset Function MeasureTheory
open scoped BigOperators ENNReal Topology

set_option autoImplicit false

namespace Work.BourgainPlan.Maximal

open Commons.Analysis.ExponentialSums

/-! ## Elementary norms -/

lemma norm_exp_pure_imag' (j : ℤ) (θ : ℝ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (θ : ℂ)))‖ = 1 := by
  have h : 2 * Real.pi * Complex.I * ((j : ℂ) * (θ : ℂ))
      = (((2 * Real.pi * (j : ℝ) * θ : ℝ)) : ℂ) * Complex.I := by push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

lemma norm_exp_neg_pure_imag' (x : ℤ) (θ : ℝ) :
    ‖Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℂ) * (θ : ℂ))))‖ = 1 := by
  have h : -(2 * Real.pi * Complex.I * ((x : ℂ) * (θ : ℂ)))
      = (((-(2 * Real.pi * (x : ℝ) * θ) : ℝ)) : ℂ) * Complex.I := by push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

lemma norm_polyModelP_le (g : ℤ → ℂ) (s : Finset ℤ) (θ : ℝ) :
    ‖∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (θ : ℂ)))‖
      ≤ ∑ j ∈ s, ‖g j‖ := by
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun j _ => ?_))
  rw [norm_mul, norm_exp_pure_imag' j θ, mul_one]

/-! ## The dyadic `q`-block decomposition of the polynomial model -/

/-- The `q`-layer of the `m`-th dyadic block of the model `polyMajorArcModelPre P (1/4) N`. -/
noncomputable def polyModelQBlock (P : Polynomial ℤ) (m N : ℕ) (θ : ℝ) : ℂ :=
  ∑ q ∈ (Finset.Icc 1 (Nat.floor ((N : ℝ) ^ ((1:ℝ)/4)))).filter (fun q => Nat.log 2 q = m),
    polyMajorArcBlockPre P ((1:ℝ)/4) N θ q

/-- **Dyadic-block decomposition of the general-polynomial major-arc model.** -/
theorem polyMajorArcModelPre_eq_sum_modelQBlock (P : Polynomial ℤ) (N : ℕ) (θ : ℝ) :
    polyMajorArcModelPre P ((1:ℝ)/4) N θ
      = ∑ m ∈ Finset.range (Nat.floor ((N : ℝ) ^ ((1:ℝ)/4)) + 1),
          polyModelQBlock P m N θ := by
  unfold polyMajorArcModelPre polyModelQBlock
  symm
  calc ∑ m ∈ Finset.range (Nat.floor ((N : ℝ) ^ ((1:ℝ)/4)) + 1),
        ∑ q ∈ (Finset.Icc 1 (Nat.floor ((N : ℝ) ^ ((1:ℝ)/4)))).filter
            (fun q => Nat.log 2 q = m),
          polyMajorArcBlockPre P ((1:ℝ)/4) N θ q
      = ∑ m ∈ Finset.range (Nat.floor ((N : ℝ) ^ ((1:ℝ)/4)) + 1),
          ∑ q ∈ Finset.Icc 1 (Nat.floor ((N : ℝ) ^ ((1:ℝ)/4))),
            (if Nat.log 2 q = m then polyMajorArcBlockPre P ((1:ℝ)/4) N θ q else 0) := by
        refine Finset.sum_congr rfl (fun m _ => ?_)
        rw [Finset.sum_filter]
    _ = ∑ q ∈ Finset.Icc 1 (Nat.floor ((N : ℝ) ^ ((1:ℝ)/4))),
          ∑ m ∈ Finset.range (Nat.floor ((N : ℝ) ^ ((1:ℝ)/4)) + 1),
            (if Nat.log 2 q = m then polyMajorArcBlockPre P ((1:ℝ)/4) N θ q else 0) :=
        Finset.sum_comm
    _ = ∑ q ∈ Finset.Icc 1 (Nat.floor ((N : ℝ) ^ ((1:ℝ)/4))),
          polyMajorArcBlockPre P ((1:ℝ)/4) N θ q := by
        refine Finset.sum_congr rfl (fun q hq => ?_)
        obtain ⟨hq1, hq2⟩ := Finset.mem_Icc.mp hq
        have h := Finset.sum_eq_single (f := fun m => if Nat.log 2 q = m then
            polyMajorArcBlockPre P ((1:ℝ)/4) N θ q else 0) (Nat.log 2 q)
          (fun m _ hmne => by rw [if_neg (fun hh => hmne hh.symm)])
          (fun hnot => absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le
            (log2_le_floor_pow_quarter hq1 hq2))) hnot)
        simpa using h

/-- For `k < 4m` the `m`-th dyadic block of the model at scale `2^k` is empty. -/
lemma polyModelQBlock_eq_zero_of_lt (P : Polynomial ℤ) {m k : ℕ} (hk : k < 4*m) (θ : ℝ) :
    polyModelQBlock P m (2^k) θ = 0 := by
  have hempty : (Finset.Icc 1 (Nat.floor (((2^k : ℕ) : ℝ) ^ ((1:ℝ)/4)))).filter
      (fun q => Nat.log 2 q = m) = ∅ := by
    rw [filter_log_eq_filter_pow, Finset.eq_empty_iff_forall_notMem]
    intro q hq
    rw [Finset.mem_filter, Finset.mem_Icc] at hq
    obtain ⟨⟨hq1, hqQ⟩, h2m, _⟩ := hq
    have hQ : Nat.floor (((2^k : ℕ) : ℝ) ^ ((1:ℝ)/4)) < 2^m := by
      rw [Nat.floor_lt (by positivity)]
      push_cast
      rw [← Real.rpow_natCast (2:ℝ) k, ← Real.rpow_natCast (2:ℝ) m,
        ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      refine Real.rpow_lt_rpow_of_exponent_lt (by norm_num) ?_
      have hk' : (k:ℝ) < 4 * (m:ℝ) := by exact_mod_cast hk
      linarith
    omega
  unfold polyModelQBlock
  rw [hempty, Finset.sum_empty]

/-- Crude bound for a dyadic block of the model. -/
lemma norm_polyModelQBlock_le (P : Polynomial ℤ) (m N : ℕ) (θ : ℝ) :
    ‖polyModelQBlock P m N θ‖
      ≤ ((Nat.floor ((N : ℝ) ^ ((1:ℝ)/4))) : ℝ)^2 * (((P.leadingCoeff + 2).toNat) : ℝ) := by
  unfold polyModelQBlock
  refine le_trans (norm_sum_le _ _) ?_
  set Q : ℕ := Nat.floor ((N : ℝ) ^ ((1:ℝ)/4)) with hQ
  have hcard : ((Finset.Icc 1 Q).card : ℝ) = (Q : ℝ) := by
    rw [Nat.card_Icc]; push_cast; ring
  calc ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => Nat.log 2 q = m),
        ‖polyMajorArcBlockPre P ((1:ℝ)/4) N θ q‖
      ≤ ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => Nat.log 2 q = m),
          (q : ℝ) * (((P.leadingCoeff + 2).toNat) : ℝ) :=
        Finset.sum_le_sum (fun q _ => norm_polyMajorArcBlockPre_le P _ N q θ)
    _ ≤ ∑ q ∈ Finset.Icc 1 Q, (q : ℝ) * (((P.leadingCoeff + 2).toNat) : ℝ) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun q hq hnot => ?_)
        positivity
    _ = (∑ q ∈ Finset.Icc 1 Q, (q : ℝ)) * (((P.leadingCoeff + 2).toNat) : ℝ) := by
        rw [Finset.sum_mul]
    _ ≤ (Q : ℝ)^2 * (((P.leadingCoeff + 2).toNat) : ℝ) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        calc ∑ q ∈ Finset.Icc 1 Q, (q : ℝ)
            ≤ ∑ _q ∈ Finset.Icc 1 Q, (Q : ℝ) := by
              refine Finset.sum_le_sum (fun q hq => ?_)
              exact_mod_cast (Finset.mem_Icc.mp hq).2
          _ = ((Finset.Icc 1 Q).card : ℝ) * (Q : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
          _ = (Q : ℝ) * (Q : ℝ) := by rw [hcard]
          _ = (Q : ℝ)^2 := by ring

/-! ## Measurability -/

/-- The profile is continuous in its frequency variable. -/
lemma continuous_polyProfile (P : Polynomial ℤ) (N : ℕ) :
    Continuous (fun β : ℝ => polyProfile P N β) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun (β : ℝ) (s : ℝ) => Complex.exp (2 * Real.pi * Complex.I *
      ((β * (Polynomial.eval (((N : ℝ) * s)) (toRealPoly P)) : ℝ) : ℂ)))
    (by fun_prop) 0 1

lemma measurable_polyModelTermPre (P : Polynomial ℤ) (N q : ℕ) (a : ℕ) (l : ℤ) :
    Measurable (fun θ : ℝ => polyModelTermPre P N q a l θ) := by
  unfold polyModelTermPre
  refine Measurable.mul measurable_const ?_
  refine (continuous_polyProfile P N).comp ?_ |>.measurable
  fun_prop

lemma measurable_polyMajorArcBlockPre (P : Polynomial ℤ) (δ : ℝ) (N q : ℕ) :
    Measurable (fun θ : ℝ => polyMajorArcBlockPre P δ N θ q) := by
  unfold polyMajorArcBlockPre
  refine Finset.measurable_sum _ (fun a _ => ?_)
  refine Measurable.ite (by measurability) ?_ measurable_const
  refine Finset.measurable_sum _ (fun l _ => ?_)
  exact Measurable.ite (by measurability) (measurable_polyModelTermPre P N q a l) measurable_const

lemma measurable_polyModelQBlock (P : Polynomial ℤ) (m N : ℕ) :
    Measurable (fun θ : ℝ => polyModelQBlock P m N θ) := by
  unfold polyModelQBlock
  exact Finset.measurable_sum _ (fun q _ => measurable_polyMajorArcBlockPre P ((1:ℝ)/4) N q)

/-! ## The block model operators -/

/-- The block model operator at scale `2^k`. -/
noncomputable def polyTkBlockMax (P : Polynomial ℤ) (g : ℤ → ℂ) (s : Finset ℤ) (m k : ℕ)
    (x : ℤ) : ℂ :=
  ∫ θ in (0:ℝ)..1, (starRingEnd ℂ (polyModelQBlock P m (2^k) θ)) *
    (∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (θ : ℂ)))) *
    Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℂ) * (θ : ℂ))))

lemma poly_intervalIntegrable_block (P : Polynomial ℤ) (g : ℤ → ℂ) (s : Finset ℤ)
    (m k : ℕ) (x : ℤ) :
    IntervalIntegrable (fun θ : ℝ => (starRingEnd ℂ (polyModelQBlock P m (2^k) θ)) *
      (∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (θ : ℂ)))) *
      Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℂ) * (θ : ℂ))))) volume 0 1 := by
  rw [intervalIntegrable_iff]
  haveI hfin : IsFiniteMeasure (volume.restrict (Set.uIoc (0:ℝ) 1)) :=
    ⟨by rw [Measure.restrict_apply_univ, Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1),
        Real.volume_Ioc]; norm_num⟩
  refine MeasureTheory.Integrable.of_bound ?_
    ((((Nat.floor ((((2^k : ℕ) : ℝ)) ^ ((1:ℝ)/4))) : ℝ)^2
        * (((P.leadingCoeff + 2).toNat) : ℝ)) * (∑ j ∈ s, ‖g j‖) + 1) ?_
  · exact (((Complex.continuous_conj.measurable.comp
      (measurable_polyModelQBlock P m (2^k))).mul (by fun_prop)).mul (by fun_prop)).aestronglyMeasurable
  · filter_upwards with θ
    rw [norm_mul, norm_mul, norm_exp_neg_pure_imag' x θ, mul_one]
    have hP := norm_polyModelP_le g s θ
    have hb := norm_polyModelQBlock_le P m (2^k) θ
    have h1 : ‖(starRingEnd ℂ (polyModelQBlock P m (2^k) θ))‖ *
            ‖∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (θ : ℂ)))‖
        ≤ (((Nat.floor ((((2^k : ℕ) : ℝ)) ^ ((1:ℝ)/4))) : ℝ)^2
            * (((P.leadingCoeff + 2).toNat) : ℝ)) * (∑ j ∈ s, ‖g j‖) := by
      rw [Complex.norm_conj]
      exact mul_le_mul hb hP (by positivity) (by positivity)
    linarith

/-- **The model operator splits over dyadic `q`-blocks.** -/
lemma poly_TkMax_eq_sum_block (P : Polynomial ℤ) (g : ℤ → ℂ) (s : Finset ℤ) (k : ℕ) (x : ℤ) :
    polyTkMax P g s k x
      = ∑ m ∈ Finset.range (Nat.floor ((((2^k : ℕ) : ℝ)) ^ ((1:ℝ)/4)) + 1),
          polyTkBlockMax P g s m k x := by
  have hmain : (∫ θ in (0:ℝ)..1, (starRingEnd ℂ (polyMajorArcModelPre P ((1:ℝ)/4) (2^k) θ)) *
        (∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (θ : ℂ)))) *
        Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℂ) * (θ : ℂ)))))
      = ∫ θ in (0:ℝ)..1,
          ∑ m ∈ Finset.range (Nat.floor ((((2^k : ℕ) : ℝ)) ^ ((1:ℝ)/4)) + 1),
            (starRingEnd ℂ (polyModelQBlock P m (2^k) θ)) *
            (∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (θ : ℂ)))) *
            Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℂ) * (θ : ℂ)))) := by
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    rw [polyMajorArcModelPre_eq_sum_modelQBlock, map_sum, Finset.sum_mul, Finset.sum_mul]
  have hsum : (∫ θ in (0:ℝ)..1,
          ∑ m ∈ Finset.range (Nat.floor ((((2^k : ℕ) : ℝ)) ^ ((1:ℝ)/4)) + 1),
            (starRingEnd ℂ (polyModelQBlock P m (2^k) θ)) *
            (∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (θ : ℂ)))) *
            Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℂ) * (θ : ℂ)))))
      = ∑ m ∈ Finset.range (Nat.floor ((((2^k : ℕ) : ℝ)) ^ ((1:ℝ)/4)) + 1),
          polyTkBlockMax P g s m k x := by
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl (fun m _ => ?_)
      unfold polyTkBlockMax
      rfl
    · intro m _
      exact poly_intervalIntegrable_block P g s m k x
  unfold polyTkMax
  exact hmain.trans hsum

lemma poly_Tsup_le_tsum (P : Polynomial ℤ) (g : ℤ → ℂ) (s : Finset ℤ) (x : ℤ) :
    (⨆ k : ℕ, ‖polyTkMax P g s k x‖ₑ)
      ≤ ∑' m : ℕ, ⨆ k : ℕ, ‖polyTkBlockMax P g s m k x‖ₑ := by
  refine iSup_le (fun k => ?_)
  calc ‖polyTkMax P g s k x‖ₑ
      = ‖∑ m ∈ Finset.range (Nat.floor ((((2^k : ℕ) : ℝ)) ^ ((1:ℝ)/4)) + 1),
            polyTkBlockMax P g s m k x‖ₑ := by rw [poly_TkMax_eq_sum_block]
    _ ≤ ∑ m ∈ Finset.range (Nat.floor ((((2^k : ℕ) : ℝ)) ^ ((1:ℝ)/4)) + 1),
            ‖polyTkBlockMax P g s m k x‖ₑ := enorm_sum_le _ _
    _ ≤ ∑' m : ℕ, ⨆ k : ℕ, ‖polyTkBlockMax P g s m k x‖ₑ := by
        calc ∑ m ∈ Finset.range (Nat.floor ((((2^k : ℕ) : ℝ)) ^ ((1:ℝ)/4)) + 1),
              ‖polyTkBlockMax P g s m k x‖ₑ
            ≤ ∑ m ∈ Finset.range (Nat.floor ((((2^k : ℕ) : ℝ)) ^ ((1:ℝ)/4)) + 1),
              ⨆ k : ℕ, ‖polyTkBlockMax P g s m k x‖ₑ :=
              Finset.sum_le_sum (fun m _ => le_iSup (fun k => ‖polyTkBlockMax P g s m k x‖ₑ) k)
          _ ≤ ∑' m : ℕ, ⨆ k : ℕ, ‖polyTkBlockMax P g s m k x‖ₑ := ENNReal.sum_le_tsum _

/-- The block maximal bound implies the model maximal bound, with block exponent `τ`. -/
lemma poly_lintegral_Tsup_sq_le (P : Polynomial ℤ) (g : ℤ → ℂ) (s : Finset ℤ) {τ : ℝ}
    (hτ : 0 < τ) (K : ℕ → ℝ≥0∞) (G : ℝ≥0∞)
    (hblk : ∀ m : ℕ,
      ∫⁻ x : ℤ, (⨆ k : ℕ, ‖polyTkBlockMax P g s m k x‖ₑ)^(2:ℝ)
          ∂MeasureTheory.Measure.count ≤ K m * G) :
    ∫⁻ x : ℤ, (⨆ k : ℕ, ‖polyTkMax P g s k x‖ₑ)^(2:ℝ) ∂MeasureTheory.Measure.count
      ≤ (∑' m : ℕ, ((2:ℝ≥0∞)^(-(m:ℝ)*τ))^(2:ℝ)) *
        (∑' m : ℕ, (((2:ℝ≥0∞)^((m:ℝ)*τ))^(2:ℝ) * K m)) * G := by
  have h1 : ∫⁻ x : ℤ, (⨆ k : ℕ, ‖polyTkMax P g s k x‖ₑ)^(2:ℝ) ∂MeasureTheory.Measure.count
      ≤ ∫⁻ x : ℤ, (∑' m : ℕ, (⨆ k : ℕ, ‖polyTkBlockMax P g s m k x‖ₑ))^(2:ℝ)
          ∂MeasureTheory.Measure.count := by
    apply lintegral_mono; intro x
    exact ENNReal.rpow_le_rpow (poly_Tsup_le_tsum P g s x) (by norm_num)
  have hinner : ∫⁻ x : ℤ, (∑' m : ℕ, ((2:ℝ≥0∞)^((m:ℝ)*τ) *
        (⨆ k : ℕ, ‖polyTkBlockMax P g s m k x‖ₑ))^(2:ℝ)) ∂MeasureTheory.Measure.count
      ≤ (∑' m : ℕ, (((2:ℝ≥0∞)^((m:ℝ)*τ))^(2:ℝ) * K m)) * G := by
    calc ∫⁻ x : ℤ, (∑' m : ℕ, ((2:ℝ≥0∞)^((m:ℝ)*τ) *
          (⨆ k : ℕ, ‖polyTkBlockMax P g s m k x‖ₑ))^(2:ℝ)) ∂MeasureTheory.Measure.count
        = ∑' m : ℕ, ∫⁻ x : ℤ, ((2:ℝ≥0∞)^((m:ℝ)*τ) *
            (⨆ k : ℕ, ‖polyTkBlockMax P g s m k x‖ₑ))^(2:ℝ) ∂MeasureTheory.Measure.count :=
          lintegral_tsum (fun m => AEMeasurable.pow_const
            (Measurable.aemeasurable (measurable_of_countable _)) 2)
      _ ≤ ∑' m : ℕ, (((2:ℝ≥0∞)^((m:ℝ)*τ))^(2:ℝ) * K m) * G :=
          ENNReal.tsum_le_tsum (fun m => ?_)
      _ = (∑' m : ℕ, (((2:ℝ≥0∞)^((m:ℝ)*τ))^(2:ℝ) * K m)) * G := by
          rw [ENNReal.tsum_mul_right]
    calc ∫⁻ x : ℤ, ((2:ℝ≥0∞)^((m:ℝ)*τ) *
          (⨆ k : ℕ, ‖polyTkBlockMax P g s m k x‖ₑ))^(2:ℝ) ∂MeasureTheory.Measure.count
        = ∫⁻ x : ℤ, ((2:ℝ≥0∞)^((m:ℝ)*τ))^(2:ℝ) *
            (⨆ k : ℕ, ‖polyTkBlockMax P g s m k x‖ₑ)^(2:ℝ) ∂MeasureTheory.Measure.count :=
          lintegral_congr (fun x => by rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)])
      _ = ((2:ℝ≥0∞)^((m:ℝ)*τ))^(2:ℝ) *
            ∫⁻ x : ℤ, (⨆ k : ℕ, ‖polyTkBlockMax P g s m k x‖ₑ)^(2:ℝ)
              ∂MeasureTheory.Measure.count :=
          lintegral_const_mul _ (Measurable.pow_const (measurable_of_countable _) 2)
      _ ≤ ((2:ℝ≥0∞)^((m:ℝ)*τ))^(2:ℝ) * (K m * G) := by
          gcongr
          exact hblk m
      _ = (((2:ℝ≥0∞)^((m:ℝ)*τ))^(2:ℝ) * K m) * G := by rw [mul_assoc]
  refine le_trans h1 ?_
  calc ∫⁻ x : ℤ, (∑' m : ℕ, (⨆ k : ℕ, ‖polyTkBlockMax P g s m k x‖ₑ))^(2:ℝ)
        ∂MeasureTheory.Measure.count
      ≤ ∫⁻ x : ℤ, (∑' m : ℕ, ((2:ℝ≥0∞)^(-(m:ℝ)*τ))^(2:ℝ)) *
          (∑' m : ℕ, ((2:ℝ≥0∞)^((m:ℝ)*τ) *
            (⨆ k : ℕ, ‖polyTkBlockMax P g s m k x‖ₑ))^(2:ℝ)) ∂MeasureTheory.Measure.count :=
        lintegral_mono (fun x => block_cauchy_sig hτ
          (fun m => ⨆ k : ℕ, ‖polyTkBlockMax P g s m k x‖ₑ))
    _ = (∑' m : ℕ, ((2:ℝ≥0∞)^(-(m:ℝ)*τ))^(2:ℝ)) *
          ∫⁻ x : ℤ, (∑' m : ℕ, ((2:ℝ≥0∞)^((m:ℝ)*τ) *
            (⨆ k : ℕ, ‖polyTkBlockMax P g s m k x‖ₑ))^(2:ℝ)) ∂MeasureTheory.Measure.count :=
        lintegral_const_mul _ (measurable_of_countable _)
    _ ≤ (∑' m : ℕ, ((2:ℝ≥0∞)^(-(m:ℝ)*τ))^(2:ℝ)) *
          ((∑' m : ℕ, (((2:ℝ≥0∞)^((m:ℝ)*τ))^(2:ℝ) * K m)) * G) := by
        gcongr
    _ = (∑' m : ℕ, ((2:ℝ≥0∞)^(-(m:ℝ)*τ))^(2:ℝ)) *
          (∑' m : ℕ, (((2:ℝ≥0∞)^((m:ℝ)*τ))^(2:ℝ) * K m)) * G := by rw [mul_assoc]

/-- **Assembly of the model maximal estimate from the per-`q`-block maximal estimate.** -/
theorem poly_model_maximal_of_block (P : Polynomial ℤ) (σ : ℝ) (hσ : 0 < σ)
    (hm : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (g : ℤ → ℂ) (s : Finset ℤ),
      (∀ n, n ∉ s → g n = 0) →
      ∫⁻ x : ℤ, (⨆ k : ℕ, ‖polyTkBlockMax P g s m k x‖ₑ)^(2:ℝ)
          ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * (2:ℝ)^(-(m:ℝ)*σ) * ((m:ℝ)+2)^2)^2 *
          ∫⁻ x : ℤ, ‖g x‖ₑ^(2:ℝ) ∂MeasureTheory.Measure.count) :
    ∃ A : ℝ, 0 < A ∧ ∀ (g : ℤ → ℂ) (s : Finset ℤ), (∀ n, n ∉ s → g n = 0) →
      ∫⁻ m : ℤ, (⨆ k : ℕ, ‖polyTkMax P g s k m‖ₑ) ^ (2:ℝ)
          ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (A ^ 2) * ∫⁻ m : ℤ, ‖g m‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count := by
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
  intro g s hgs
  have hA : W * D ≤ ENNReal.ofReal ((Real.sqrt ((W * D).toReal) + 1)^2) := by
    have h5 : (W * D).toReal ≤ (Real.sqrt ((W * D).toReal) + 1)^2 := by
      rw [add_sq, Real.sq_sqrt (by positivity : (0:ℝ) ≤ (W * D).toReal)]
      linarith [Real.sqrt_nonneg ((W * D).toReal)]
    calc W * D = ENNReal.ofReal ((W * D).toReal) := (ENNReal.ofReal_toReal hWD).symm
      _ ≤ ENNReal.ofReal ((Real.sqrt ((W * D).toReal) + 1)^2) := ENNReal.ofReal_le_ofReal h5
  have key : ∫⁻ m : ℤ, (⨆ k : ℕ, ‖polyTkMax P g s k m‖ₑ)^(2:ℝ)
      ∂MeasureTheory.Measure.count
      ≤ W * D * (∫⁻ m : ℤ, ‖g m‖ₑ^(2:ℝ) ∂MeasureTheory.Measure.count) := by
    have hK : ∀ m : ℕ,
        ∫⁻ x : ℤ, (⨆ k : ℕ, ‖polyTkBlockMax P g s m k x‖ₑ)^(2:ℝ)
            ∂MeasureTheory.Measure.count
          ≤ (ENNReal.ofReal (C * (2:ℝ)^(-(m:ℝ)*σ) * ((m:ℝ)+2)^2)^2)
              * (∫⁻ x : ℤ, ‖g x‖ₑ^(2:ℝ) ∂MeasureTheory.Measure.count) := by
      intro m
      exact hblk m g s hgs
    simpa only [hW, hD] using poly_lintegral_Tsup_sq_le P g s hτpos
      (fun m => ENNReal.ofReal (C * (2:ℝ)^(-(m:ℝ)*σ) * ((m:ℝ)+2)^2)^2)
      (∫⁻ x : ℤ, ‖g x‖ₑ^(2:ℝ) ∂MeasureTheory.Measure.count) hK
  refine le_trans key ?_
  exact mul_le_mul_of_nonneg_right hA (by positivity)

end Work.BourgainPlan.Maximal
