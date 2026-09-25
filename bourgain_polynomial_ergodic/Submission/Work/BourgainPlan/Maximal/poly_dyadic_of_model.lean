import Mathlib
import Submission.Work.BourgainPlan.Maximal.l2_defs
import Submission.Work.BourgainPlan.Maximal.shift_fourier_coeff_conj
import Submission.Commons.Analysis.Fourier.maximal_l2_of_summable_multiplier_family

/-!
# From the model maximal estimate to the dyadic kernel maximal estimate (general `P`)

Fix `P : ℤ[X]` of degree `d ≥ 2` with `c = P.leadingCoeff > 0`.  Assuming

* `hmaj` : the Weyl kernel is uniformly approximated by the major-arc model, and
* `hmodel` : the marginals of the dyadic model multipliers form an `ℓ²` maximal family,

this file proves the `ℓ²` maximal inequality for the **dyadic** polynomial averages
`((2^k))⁻¹ ∑_{i<2^k} g (m + P i)` on `ℤ`.  It is the general-`P` analogue of
`Commons.Analysis.ExponentialSums.pow_dyadic_of_model`.
-/

open Filter Finset Function MeasureTheory
open scoped BigOperators ENNReal Topology

set_option autoImplicit false

namespace Work.BourgainPlan.Maximal

/-- Continuity of the oscillatory profile in the offset. -/
lemma continuous_polyProfile (P : Polynomial ℤ) (N : ℕ) :
    Continuous (fun β : ℝ => polyProfile P N β) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun (β : ℝ) (s : ℝ) => Complex.exp (2 * Real.pi * Complex.I *
      ((β * (Polynomial.eval (((N : ℝ) * s)) (toRealPoly P)) : ℝ) : ℂ))) (by fun_prop) 0 1

/-- Measurability of a single model term in the frequency. -/
lemma measurable_polyModelTermPre (P : Polynomial ℤ) (N q : ℕ) (a : ℕ) (l : ℤ) :
    Measurable (fun θ : ℝ => polyModelTermPre P N q a l θ) := by
  unfold polyModelTermPre
  refine Measurable.const_mul ?_ _
  refine (continuous_polyProfile P N).comp ?_ |>.measurable
  fun_prop

/-- Measurability of a major-arc block in the frequency. -/
lemma measurable_polyMajorArcBlockPre (P : Polynomial ℤ) (δ : ℝ) (N q : ℕ) :
    Measurable (fun θ : ℝ => polyMajorArcBlockPre P δ N θ q) := by
  unfold polyMajorArcBlockPre
  refine Finset.measurable_sum _ (fun a _ => ?_)
  refine Measurable.ite (by measurability) ?_ measurable_const
  refine Finset.measurable_sum _ (fun l _ => ?_)
  exact Measurable.ite (by measurability) (measurable_polyModelTermPre P N q a l) measurable_const

/-- Measurability of the major-arc model in the frequency. -/
lemma measurable_polyMajorArcModelPre (P : Polynomial ℤ) (δ : ℝ) (N : ℕ) :
    Measurable (fun θ : ℝ => polyMajorArcModelPre P δ N θ) := by
  unfold polyMajorArcModelPre
  exact Finset.measurable_sum _ (fun q _ => measurable_polyMajorArcBlockPre P δ N q)

/-- Crude bound for the major-arc model: at most `q ≤ ⌊N^δ⌋` blocks of at most `q·(c+2)` terms. -/
lemma norm_polyMajorArcModelPre_le (P : Polynomial ℤ) (δ : ℝ) (N : ℕ) (θ : ℝ) :
    ‖polyMajorArcModelPre P δ N θ‖
      ≤ ((Nat.floor ((N : ℝ) ^ δ) : ℝ))^2 * (((P.leadingCoeff + 2).toNat) : ℝ) := by
  set Q := Nat.floor ((N : ℝ) ^ δ) with hQ
  have hQnn : (0 : ℝ) ≤ (Q : ℝ) := by positivity
  calc ‖∑ q ∈ Finset.Icc 1 Q, polyMajorArcBlockPre P δ N θ q‖
      ≤ ∑ q ∈ Finset.Icc 1 Q, ‖polyMajorArcBlockPre P δ N θ q‖ := norm_sum_le _ _
    _ ≤ ∑ q ∈ Finset.Icc 1 Q, (q : ℝ) * (((P.leadingCoeff + 2).toNat) : ℝ) :=
        Finset.sum_le_sum (fun q _ => norm_polyMajorArcBlockPre_le P δ N q θ)
    _ = (∑ q ∈ Finset.Icc 1 Q, (q : ℝ)) * (((P.leadingCoeff + 2).toNat) : ℝ) := by
        rw [Finset.sum_mul]
    _ ≤ (Q : ℝ) * (Q : ℝ) * (((P.leadingCoeff + 2).toNat) : ℝ) := by
        have hc2 : (0 : ℝ) ≤ (((P.leadingCoeff + 2).toNat) : ℝ) := by positivity
        refine mul_le_mul_of_nonneg_right ?_ hc2
        calc ∑ q ∈ Finset.Icc 1 Q, (q : ℝ) ≤ ∑ _q ∈ Finset.Icc 1 Q, (Q : ℝ) := by
              refine Finset.sum_le_sum (fun q hq => ?_)
              exact_mod_cast (Finset.mem_Icc.mp hq).2
          _ = ((Finset.Icc 1 Q).card : ℝ) * (Q : ℝ) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (Q : ℝ) * (Q : ℝ) := by
              refine mul_le_mul_of_nonneg_right ?_ hQnn
              have hcard : (Finset.Icc 1 Q).card ≤ Q := by
                rw [Nat.card_Icc]; simp
              exact_mod_cast hcard
    _ = ((Q : ℝ))^2 * (((P.leadingCoeff + 2).toNat) : ℝ) := by ring

/-- The major-arc model at a fixed scale is bounded, hence interval integrable against a continuous
function. -/
lemma intervalIntegrable_polyMajorArcModelPre_mul (P : Polynomial ℤ) (δ : ℝ) (N : ℕ)
    {f : ℝ → ℂ} (hf : Continuous f) :
    IntervalIntegrable (fun θ : ℝ => (starRingEnd ℂ (polyMajorArcModelPre P δ N θ)) * f θ)
      volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn hf.continuousOn
  set Q := Nat.floor ((N : ℝ) ^ δ) with hQ
  set B : ℝ := ((Q : ℝ))^2 * (((P.leadingCoeff + 2).toNat) : ℝ) with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  refine IntegrableOn.of_bound ?_ ?_ (B * D + 1) ?_
  · rw [Real.volume_Ioc]; simp
  · exact ((Complex.continuous_conj.measurable.comp
      (measurable_polyMajorArcModelPre P δ N)).mul hf.measurable).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall (fun θ hθ => ?_))
    have hθI : θ ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hθ.1, hθ.2⟩
    have hb := norm_polyMajorArcModelPre_le P δ N θ
    have hbD := hD θ hθI
    rw [norm_mul, Complex.norm_conj]
    calc ‖polyMajorArcModelPre P δ N θ‖ * ‖f θ‖ ≤ B * D := by
          refine mul_le_mul hb hbD (norm_nonneg _) hB0
      _ ≤ B * D + 1 := by linarith

/-- Conjugate form of the Weyl kernel. -/
lemma conj_polyWeylKernel (P : Polynomial ℤ) (N : ℕ) (θ : ℝ) :
    starRingEnd ℂ (polyWeylKernel P N θ)
      = ((N : ℂ))⁻¹ * ∑ i ∈ Finset.range N,
          Complex.exp (-(2 * Real.pi * Complex.I * (((P.eval (i : ℤ) : ℤ) : ℝ) * θ))) := by
  rw [polyWeylKernel, map_mul, map_sum]
  congr 1
  · rw [map_inv₀, Complex.conj_ofReal]
    push_cast
    rfl
  · apply Finset.sum_congr rfl
    intro i _
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    push_cast
    ring

/-- Continuity of the Weyl kernel in the frequency. -/
lemma continuous_polyWeylKernel (P : Polynomial ℤ) (N : ℕ) :
    Continuous (fun θ : ℝ => polyWeylKernel P N θ) := by
  rw [show (fun θ : ℝ => polyWeylKernel P N θ) = fun θ : ℝ => ((N : ℝ)⁻¹ : ℂ) *
      ∑ n ∈ Finset.range N, Complex.exp (2 * Real.pi * Complex.I *
        (((θ * ((P.eval (n : ℤ) : ℤ) : ℝ) : ℝ)) : ℂ)) from rfl]
  fun_prop


/-- `polyTkMax` written with the multiplication associated as in
`Commons.Analysis.Fourier.maximal_l2_of_summable_multiplier_family` (the two differ only by the
association of the product in the phase, which is not definitional). -/
lemma polyTkMax_eq_explicit (P : Polynomial ℤ) (g : ℤ → ℂ) (s : Finset ℤ) (k : ℕ) (x : ℤ) :
    polyTkMax P g s k x
      = ∫ θ in (0:ℝ)..1, (starRingEnd ℂ (polyMajorArcModelPre P ((1:ℝ)/4) (2^k) θ)) *
          (∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * (j:ℂ) * (θ:ℂ))) *
          Complex.exp (-(2 * Real.pi * Complex.I * (x:ℂ) * (θ:ℂ))) := by
  rw [polyTkMax]
  apply intervalIntegral.integral_congr
  intro θ _
  simp only
  have hsum : (∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * ((j:ℂ) * (θ:ℂ))))
      = (∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * (j:ℂ) * (θ:ℂ))) := by
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    ring
  have hexp : Complex.exp (-(2 * Real.pi * Complex.I * ((x:ℂ) * (θ:ℂ))))
      = Complex.exp (-(2 * Real.pi * Complex.I * (x:ℂ) * (θ:ℂ))) := by
    congr 1
    ring
  rw [hsum, hexp]

/-- Translation invariance of the counting measure on `ℤ`, in the form used below. -/
lemma lintegral_count_shift_add (F : ℤ → ℝ≥0∞) (c : ℤ) :
    ∫⁻ m : ℤ, F (m + c) ∂MeasureTheory.Measure.count
      = ∫⁻ m : ℤ, F m ∂MeasureTheory.Measure.count := by
  rw [MeasureTheory.lintegral_count, MeasureTheory.lintegral_count]
  exact Equiv.tsum_eq (Equiv.addRight c) F

/-- **From the model maximal estimate to the dyadic kernel maximal estimate.**  Fix `P : ℤ[X]` of
degree `d ≥ 2` with `c = P.leadingCoeff > 0`.  Given that the Weyl kernel is uniformly approximated
by the major-arc model (`hmaj`) and that the dyadic model multipliers form an `ℓ²` maximal family
(`hmodel`), the dyadic polynomial averages on `ℤ` satisfy the `ℓ²` maximal inequality.

This is the general-`P` analogue of `Commons.Analysis.ExponentialSums.pow_dyadic_of_model`: the
kernel average is written as the Fourier coefficient of `conj (kernel)` times the Fourier series of
`g` (`shift_fourier_coeff_conj`), the model part is estimated by `hmodel` and the error symbol
`conj (kernel) - conj (model)` by `maximal_l2_of_summable_multiplier_family`. -/
theorem poly_dyadic_of_model (P : Polynomial ℤ) (hc : 0 < P.leadingCoeff) (hd : 2 ≤ P.natDegree)
    (hmaj : ∃ c₀ C : ℝ, 0 < c₀ ∧ 0 < C ∧ ∀ (N : ℕ) (θ : ℝ), 3 ≤ N → 0 ≤ θ → θ ≤ 1 →
      ‖polyWeylKernel P N θ - polyMajorArcModelPre P ((1 : ℝ) / 4) N θ‖ ≤ C * (N : ℝ) ^ (-c₀))
    (hmodel : ∃ A : ℝ, 0 < A ∧ ∀ (g : ℤ → ℂ) (s : Finset ℤ), (∀ n, n ∉ s → g n = 0) →
      ∫⁻ x : ℤ, (⨆ k : ℕ, ‖polyTkMax P g s k x‖ₑ) ^ (2 : ℝ)
          ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (A ^ 2) *
            ∫⁻ x : ℤ, ‖g x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count) :
    ∃ C : ℝ, 0 < C ∧ ∀ (g : ℤ → ℂ), (∃ s : Finset ℤ, ∀ n, n ∉ s → g n = 0) →
      ∫⁻ m : ℤ, (⨆ k : ℕ, ‖((2 : ℝ) ^ k)⁻¹
            * ∑ i ∈ Finset.range (2 ^ k), g (m + P.eval (i : ℤ))‖ₑ) ^ (2 : ℝ)
          ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C ^ 2) *
            ∫⁻ m : ℤ, ‖g m‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count := by
  classical
  obtain ⟨A, hApos, hAbound⟩ := hmodel
  obtain ⟨cm, Cm, hcmpos, hCmpos, hmaj'⟩ := hmaj
  -- the geometric ratio of the error family
  set r : ℝ := (2 : ℝ) ^ (-cm) with hr
  have hrpos : 0 < r := by rw [hr]; exact Real.rpow_pos_of_pos (by norm_num) _
  have hrlt : r < 1 := by
    rw [hr]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  -- the error symbol
  set psi : ℕ → ℝ → ℂ := fun k θ =>
      if k < 2 then 0
      else if θ ∈ Set.Icc (0 : ℝ) 1 then
        (starRingEnd ℂ (polyWeylKernel P (2 ^ k) θ) -
         starRingEnd ℂ (polyMajorArcModelPre P ((1 : ℝ) / 4) (2 ^ k) θ))
      else 0 with hpsi
  set Ab : ℕ → ℝ := fun k => if k < 2 then 0 else Cm * r ^ k with hAb
  have hAbnn : ∀ k, 0 ≤ Ab k := by
    intro k
    simp only [hAb]
    by_cases hk : k < 2
    · simp [hk]
    · simp only [hk, ↓reduceIte]
      exact mul_nonneg (le_of_lt hCmpos) (pow_nonneg (le_of_lt hrpos) k)
  have hAb_summable : Summable Ab := by
    refine Summable.of_nonneg_of_le (f := fun k : ℕ => Cm * r ^ k) hAbnn (fun k => ?_) ?_
    · simp only [hAb]
      by_cases hk : k < 2
      · simp only [hk, ↓reduceIte]
        positivity
      · simp only [hk, ↓reduceIte]
        exact le_rfl
    · refine (summable_geometric_iff_norm_lt_one.mpr ?_).mul_left Cm
      rw [Real.norm_eq_abs, abs_of_pos hrpos]
      exact hrlt
  have hpsi_meas : ∀ k, Measurable (psi k) := by
    intro k
    simp only [hpsi]
    by_cases hk : k < 2
    · simp only [hk, ↓reduceIte]
      exact measurable_const
    · simp only [hk, ↓reduceIte]
      refine Measurable.ite measurableSet_Icc ?_ measurable_const
      exact ((Complex.continuous_conj.measurable).comp (continuous_polyWeylKernel P (2 ^ k)).measurable).sub
        ((Complex.continuous_conj.measurable).comp (measurable_polyMajorArcModelPre P ((1 : ℝ) / 4) (2 ^ k)))
  have hpow : ∀ k : ℕ, (((2 : ℝ) ^ k) ^ cm)⁻¹ = r ^ k := by
    intro k
    rw [hr]
    calc (((2 : ℝ) ^ k) ^ cm)⁻¹
        = ((2 : ℝ) ^ ((k : ℝ) * cm))⁻¹ := by
          rw [← Real.rpow_natCast (2 : ℝ) k, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      _ = (2 : ℝ) ^ (-((k : ℝ) * cm)) := by
          rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      _ = ((2 : ℝ) ^ (-cm)) ^ k := by
          rw [← Real.rpow_natCast ((2 : ℝ) ^ (-cm)) k, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
          congr 1
          ring
  have hpsi_bd : ∀ k θ, ‖psi k θ‖ ≤ Ab k := by
    intro k θ
    simp only [hpsi, hAb]
    by_cases hk : k < 2
    · simp only [hk, ↓reduceIte]
      simp
    · simp only [hk, ↓reduceIte]
      by_cases hθ : θ ∈ Set.Icc (0 : ℝ) 1
      · rw [if_pos hθ, ← map_sub, Complex.norm_conj]
        have h3 : 3 ≤ 2 ^ k := by
          have h4 : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
          norm_num at h4 ⊢
          omega
        have hm := hmaj' (2 ^ k) θ h3 hθ.1 hθ.2
        have hbase : (((2 ^ k : ℕ)) : ℝ) = (2 : ℝ) ^ k := by push_cast; ring
        rw [hbase] at hm
        have hCoefk : Cm * (((2 : ℝ) ^ k) ^ cm)⁻¹ = Cm * r ^ k := by rw [hpow k]
        rw [← hCoefk, ← Real.rpow_neg (show (0 : ℝ) ≤ (2 : ℝ) ^ k by positivity) cm]
        exact hm
      · rw [if_neg hθ]
        simp only [norm_zero]
        positivity
  set S : ℝ := ∑' k, Ab k with hS
  have hSnn : 0 ≤ S := by rw [hS]; exact tsum_nonneg hAbnn
  set D : ℝ := 16 * A ^ 2 + 16 * S ^ 2 + 32 with hD
  have hDnn : 0 ≤ D := by rw [hD]; positivity
  set C : ℝ := Real.sqrt D + 1 with hC
  have hCpos : 0 < C := by rw [hC]; positivity
  have hCsq : D ≤ C ^ 2 := by
    rw [hC]
    nlinarith [Real.sq_sqrt hDnn, Real.sqrt_nonneg D]
  refine ⟨C, hCpos, ?_⟩
  intro g hg
  obtain ⟨s, hgs⟩ := hg
  set G : ℝ≥0∞ := ∫⁻ m : ℤ, ‖g m‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count with hG
  set Pg : ℝ → ℂ := fun θ => ∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * (j : ℂ) * (θ : ℂ)) with hPg
  set W : ℤ → ℝ → ℂ := fun m θ => Complex.exp (-(2 * Real.pi * Complex.I * (m : ℂ) * (θ : ℂ))) with hW
  set Mfun : ℕ → ℤ → ℂ := fun k m => ∫ θ in (0 : ℝ)..1,
      (starRingEnd ℂ (polyMajorArcModelPre P ((1 : ℝ) / 4) (2 ^ k) θ)) * Pg θ * W m θ with hMfun
  set Efun : ℕ → ℤ → ℂ := fun k m => ∫ θ in (0 : ℝ)..1,
      psi k θ * Pg θ * W m θ with hEfun
  have htk_eq : ∀ k m, Mfun k m = polyTkMax P g s k m := by
    intro k m
    rw [hMfun, hPg, hW, polyTkMax_eq_explicit P g s k m]
  -- the Fourier identity for the actual shift operator
  have hQfourier : ∀ k m, ((2 : ℝ) ^ k)⁻¹ * ∑ i ∈ Finset.range (2 ^ k), g (m + P.eval (i : ℤ))
      = ∫ θ in (0 : ℝ)..1, (starRingEnd ℂ (polyWeylKernel P (2 ^ k) θ)) * Pg θ * W m θ := by
    intro k m
    have h := shift_fourier_coeff_conj P g s hgs (2 ^ k) m
    have hcoef : (↑(((2 : ℝ) ^ k)⁻¹) : ℂ) = (((2 ^ k : ℕ) : ℂ))⁻¹ := by push_cast; rfl
    have hconv : (∫ θ in (0 : ℝ)..1, (starRingEnd ℂ (polyWeylKernel P (2 ^ k) θ)) * Pg θ * W m θ)
        = (∫ θ in (0 : ℝ)..1, (((2 ^ k : ℕ) : ℂ))⁻¹ *
              (∑ i ∈ Finset.range (2 ^ k),
                Complex.exp (-(2 * Real.pi * Complex.I * ((((P.eval (i : ℤ) : ℤ)) : ℝ) * θ))))
            * (∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℝ) * θ)))
            * Complex.exp (-(2 * Real.pi * Complex.I * ((m : ℝ) * θ)))) := by
      apply intervalIntegral.integral_congr
      intro θ _
      dsimp only
      simp only [conj_polyWeylKernel P, hPg, hW]
      have hpoly : (∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * (j : ℂ) * (θ : ℂ)))
          = (∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℝ) * θ))) := by
        apply Finset.sum_congr rfl
        intro j _
        congr 1
        push_cast
        ring
      have hexp : Complex.exp (-(2 * Real.pi * Complex.I * (m : ℂ) * (θ : ℂ)))
          = Complex.exp (-(2 * Real.pi * Complex.I * ((m : ℝ) * θ))) := by
        congr 1
        push_cast
        ring
      rw [hpoly, hexp]
    rw [hconv, h, hcoef]
  -- the error symbol on the range of integration
  have hpsi_pt : ∀ k, 2 ≤ k → ∀ θ ∈ Set.uIcc (0 : ℝ) 1,
      psi k θ = (starRingEnd ℂ (polyWeylKernel P (2 ^ k) θ) -
                 starRingEnd ℂ (polyMajorArcModelPre P ((1 : ℝ) / 4) (2 ^ k) θ)) := by
    intro k hk θ hθ
    have hθI : θ ∈ Set.Icc (0 : ℝ) 1 := by
      rwa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hθ
    simp only [hpsi]
    rw [if_neg (by omega : ¬ (k < 2)), if_pos hθI]
  have hME : ∀ k, 2 ≤ k → ∀ m,
      (∫ θ in (0 : ℝ)..1, (starRingEnd ℂ (polyWeylKernel P (2 ^ k) θ)) * Pg θ * W m θ)
        = Mfun k m + Efun k m := by
    intro k hk m
    rw [hMfun, hEfun]
    dsimp only
    have hPW : Continuous (fun θ : ℝ => Pg θ * W m θ) := by rw [hPg, hW]; fun_prop
    have hIntM : IntervalIntegrable
        (fun θ : ℝ => (starRingEnd ℂ (polyMajorArcModelPre P ((1 : ℝ) / 4) (2 ^ k) θ)) * Pg θ * W m θ)
        volume 0 1 :=
      IntervalIntegrable.congr (fun θ _ => by ring)
        (intervalIntegrable_polyMajorArcModelPre_mul P ((1 : ℝ) / 4) (2 ^ k) hPW)
    have hE_eq : (∫ θ in (0 : ℝ)..1, psi k θ * Pg θ * W m θ)
        = (∫ θ in (0 : ℝ)..1, (starRingEnd ℂ (polyWeylKernel P (2 ^ k) θ)) * Pg θ * W m θ)
          - (∫ θ in (0 : ℝ)..1, (starRingEnd ℂ (polyMajorArcModelPre P ((1 : ℝ) / 4) (2 ^ k) θ)) * Pg θ * W m θ) := by
      rw [show (∫ θ in (0 : ℝ)..1, psi k θ * Pg θ * W m θ)
            = ∫ θ in (0 : ℝ)..1,
              ((starRingEnd ℂ (polyWeylKernel P (2 ^ k) θ) -
                starRingEnd ℂ (polyMajorArcModelPre P ((1 : ℝ) / 4) (2 ^ k) θ)) * Pg θ * W m θ) from
          intervalIntegral.integral_congr (fun θ hθ => by rw [hpsi_pt k hk θ hθ])]
      rw [show (∫ θ in (0 : ℝ)..1,
              ((starRingEnd ℂ (polyWeylKernel P (2 ^ k) θ) -
                starRingEnd ℂ (polyMajorArcModelPre P ((1 : ℝ) / 4) (2 ^ k) θ)) * Pg θ * W m θ))
            = ∫ θ in (0 : ℝ)..1,
              ((starRingEnd ℂ (polyWeylKernel P (2 ^ k) θ) * Pg θ * W m θ) -
               (starRingEnd ℂ (polyMajorArcModelPre P ((1 : ℝ) / 4) (2 ^ k) θ) * Pg θ * W m θ)) from
          intervalIntegral.integral_congr (fun θ _ => by ring)]
      rw [intervalIntegral.integral_sub]
      · refine Continuous.intervalIntegrable ?_ 0 1
        have hPg' : Continuous Pg := by rw [hPg]; fun_prop
        have hWc : Continuous (fun θ : ℝ => W m θ) := by rw [hW]; fun_prop
        exact ((Complex.continuous_conj.comp (continuous_polyWeylKernel P (2 ^ k))).mul hPg').mul hWc
      · exact hIntM
    rw [hE_eq]
    ring
  -- the pointwise maximal decomposition
  have hpoint : ∀ m : ℤ, (⨆ k : ℕ, ‖((2 : ℝ) ^ k)⁻¹ * ∑ i ∈ Finset.range (2 ^ k),
        g (m + P.eval (i : ℤ))‖ₑ) ^ (2 : ℝ)
      ≤ (16 * (⨆ k : ℕ, ‖Mfun k m‖ₑ) ^ (2 : ℝ) + 16 * (⨆ k : ℕ, ‖Efun k m‖ₑ) ^ (2 : ℝ))
        + 16 * ((‖g (m + P.eval (0 : ℤ))‖ₑ) ^ (2 : ℝ)
            + (‖g (m + P.eval (1 : ℤ))‖ₑ) ^ (2 : ℝ)) := by
    intro m
    have hsplit : (⨆ k : ℕ, ‖((2 : ℝ) ^ k)⁻¹ * ∑ i ∈ Finset.range (2 ^ k),
          g (m + P.eval (i : ℤ))‖ₑ)
        ≤ (⨆ k : ℕ, ‖Mfun k m‖ₑ) + (⨆ k : ℕ, ‖Efun k m‖ₑ)
          + (‖g (m + P.eval (0 : ℤ))‖ₑ + ‖g (m + P.eval (1 : ℤ))‖ₑ) := by
      refine iSup_le (fun k => ?_)
      by_cases hk : k < 2
      · have hcoef : ‖(↑(((2 : ℝ) ^ k)⁻¹) : ℂ)‖ₑ ≤ 1 := by
          have h : ‖(↑(((2 : ℝ) ^ k)⁻¹) : ℂ)‖ₑ = ‖(((2 : ℝ) ^ k)⁻¹ : ℝ)‖ₑ := by
            rw [enorm_eq_nnnorm, enorm_eq_nnnorm, Complex.nnnorm_real]
          rw [h, Real.enorm_eq_ofReal_abs,
              abs_of_pos (by positivity : (0 : ℝ) < ((2 : ℝ) ^ k)⁻¹), ENNReal.ofReal_le_one,
              inv_le_one₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ k)]
          exact one_le_pow₀ (by norm_num)
        have hsum : ‖∑ i ∈ Finset.range (2 ^ k), g (m + P.eval (i : ℤ))‖ₑ
            ≤ ‖g (m + P.eval (0 : ℤ))‖ₑ + ‖g (m + P.eval (1 : ℤ))‖ₑ := by
          refine le_trans (enorm_sum_le _ _) ?_
          have h2 : 2 ^ k = 1 ∨ 2 ^ k = 2 := by interval_cases k <;> norm_num
          rcases h2 with h2 | h2
          · rw [h2, Finset.sum_range_one]
            have h0 : (↑(0 : ℕ) : ℤ) = (0 : ℤ) := by norm_num
            rw [h0]
            exact le_add_of_nonneg_right (by positivity)
          · rw [h2, Finset.sum_range_succ, Finset.sum_range_one]
            have h0 : (↑(0 : ℕ) : ℤ) = (0 : ℤ) := by norm_num
            have h1 : (↑(1 : ℕ) : ℤ) = (1 : ℤ) := by norm_num
            rw [h0, h1]
        calc ‖((2 : ℝ) ^ k)⁻¹ * ∑ i ∈ Finset.range (2 ^ k), g (m + P.eval (i : ℤ))‖ₑ
            = ‖(↑(((2 : ℝ) ^ k)⁻¹) : ℂ)‖ₑ
              * ‖∑ i ∈ Finset.range (2 ^ k), g (m + P.eval (i : ℤ))‖ₑ := enorm_mul _ _
          _ ≤ 1 * (‖g (m + P.eval (0 : ℤ))‖ₑ + ‖g (m + P.eval (1 : ℤ))‖ₑ) :=
              mul_le_mul' hcoef hsum
          _ = ‖g (m + P.eval (0 : ℤ))‖ₑ + ‖g (m + P.eval (1 : ℤ))‖ₑ := one_mul _
          _ ≤ (⨆ k : ℕ, ‖Mfun k m‖ₑ) + (⨆ k : ℕ, ‖Efun k m‖ₑ)
              + (‖g (m + P.eval (0 : ℤ))‖ₑ + ‖g (m + P.eval (1 : ℤ))‖ₑ) :=
              le_add_of_nonneg_left (by positivity)
      · have hk2 : 2 ≤ k := by omega
        rw [hQfourier k m, hME k hk2 m]
        calc ‖Mfun k m + Efun k m‖ₑ ≤ ‖Mfun k m‖ₑ + ‖Efun k m‖ₑ := enorm_add_le _ _
          _ ≤ (⨆ k : ℕ, ‖Mfun k m‖ₑ) + (⨆ k : ℕ, ‖Efun k m‖ₑ) :=
              add_le_add (le_iSup (fun j : ℕ => ‖Mfun j m‖ₑ) k) (le_iSup (fun j : ℕ => ‖Efun j m‖ₑ) k)
          _ ≤ (⨆ k : ℕ, ‖Mfun k m‖ₑ) + (⨆ k : ℕ, ‖Efun k m‖ₑ)
              + (‖g (m + P.eval (0 : ℤ))‖ₑ + ‖g (m + P.eval (1 : ℤ))‖ₑ) :=
              le_self_add
    have h1 := ENNReal.add_rpow_le_two_rpow_mul_rpow_add_rpow
      ((⨆ k : ℕ, ‖Mfun k m‖ₑ) + (⨆ k : ℕ, ‖Efun k m‖ₑ))
      (‖g (m + P.eval (0 : ℤ))‖ₑ + ‖g (m + P.eval (1 : ℤ))‖ₑ) (p := 2) (by norm_num)
    have h2 := ENNReal.add_rpow_le_two_rpow_mul_rpow_add_rpow
      (⨆ k : ℕ, ‖Mfun k m‖ₑ) (⨆ k : ℕ, ‖Efun k m‖ₑ) (p := 2) (by norm_num)
    have h3 := ENNReal.add_rpow_le_two_rpow_mul_rpow_add_rpow
      (‖g (m + P.eval (0 : ℤ))‖ₑ) (‖g (m + P.eval (1 : ℤ))‖ₑ) (p := 2) (by norm_num)
    have h4 : ((2 : ℝ≥0∞) ^ (2 : ℝ)) = 4 := by norm_num [ENNReal.rpow_natCast]
    rw [h4] at h1 h2 h3
    calc (⨆ k : ℕ, ‖((2 : ℝ) ^ k)⁻¹ * ∑ i ∈ Finset.range (2 ^ k),
          g (m + P.eval (i : ℤ))‖ₑ) ^ (2 : ℝ)
        ≤ ((⨆ k : ℕ, ‖Mfun k m‖ₑ) + (⨆ k : ℕ, ‖Efun k m‖ₑ)
            + (‖g (m + P.eval (0 : ℤ))‖ₑ + ‖g (m + P.eval (1 : ℤ))‖ₑ)) ^ (2 : ℝ) :=
          ENNReal.rpow_le_rpow hsplit (by norm_num)
      _ ≤ 4 * (((⨆ k : ℕ, ‖Mfun k m‖ₑ) + (⨆ k : ℕ, ‖Efun k m‖ₑ)) ^ (2 : ℝ)
            + (‖g (m + P.eval (0 : ℤ))‖ₑ + ‖g (m + P.eval (1 : ℤ))‖ₑ) ^ (2 : ℝ)) := h1
      _ ≤ 4 * (4 * ((⨆ k : ℕ, ‖Mfun k m‖ₑ) ^ (2 : ℝ) + (⨆ k : ℕ, ‖Efun k m‖ₑ) ^ (2 : ℝ))
            + (‖g (m + P.eval (0 : ℤ))‖ₑ + ‖g (m + P.eval (1 : ℤ))‖ₑ) ^ (2 : ℝ)) := by
          refine mul_le_mul_right ?_ 4
          exact add_le_add h2 le_rfl
      _ ≤ 4 * (4 * ((⨆ k : ℕ, ‖Mfun k m‖ₑ) ^ (2 : ℝ) + (⨆ k : ℕ, ‖Efun k m‖ₑ) ^ (2 : ℝ))
            + 4 * ((‖g (m + P.eval (0 : ℤ))‖ₑ) ^ (2 : ℝ)
              + (‖g (m + P.eval (1 : ℤ))‖ₑ) ^ (2 : ℝ))) := by
          refine mul_le_mul_right ?_ 4
          exact add_le_add le_rfl h3
      _ = 16 * (⨆ k : ℕ, ‖Mfun k m‖ₑ) ^ (2 : ℝ) + 16 * (⨆ k : ℕ, ‖Efun k m‖ₑ) ^ (2 : ℝ)
            + 16 * ((‖g (m + P.eval (0 : ℤ))‖ₑ) ^ (2 : ℝ)
              + (‖g (m + P.eval (1 : ℤ))‖ₑ) ^ (2 : ℝ)) := by ring
  -- measurability of the pieces
  have hMmeas : Measurable (fun m : ℤ => 16 * (⨆ k : ℕ, ‖Mfun k m‖ₑ) ^ (2 : ℝ)) := by
    refine Measurable.const_mul ?_ 16
    exact (Measurable.iSup (fun k => (measurable_of_countable (fun m : ℤ => Mfun k m)).enorm)).pow_const 2
  have hEmeas : Measurable (fun m : ℤ => 16 * (⨆ k : ℕ, ‖Efun k m‖ₑ) ^ (2 : ℝ)) := by
    refine Measurable.const_mul ?_ 16
    exact (Measurable.iSup (fun k => (measurable_of_countable (fun m : ℤ => Efun k m)).enorm)).pow_const 2
  have hxy : Measurable (fun m : ℤ => 16 * (⨆ k : ℕ, ‖Mfun k m‖ₑ) ^ (2 : ℝ)
      + 16 * (⨆ k : ℕ, ‖Efun k m‖ₑ) ^ (2 : ℝ)) := hMmeas.add hEmeas
  have hameas : Measurable (fun m : ℤ => (‖g (m + P.eval (0 : ℤ))‖ₑ) ^ (2 : ℝ)) :=
    (measurable_of_countable (fun m : ℤ => g (m + P.eval (0 : ℤ)))).enorm.pow_const 2
  have hbmeas : Measurable (fun m : ℤ => (‖g (m + P.eval (1 : ℤ))‖ₑ) ^ (2 : ℝ)) :=
    (measurable_of_countable (fun m : ℤ => g (m + P.eval (1 : ℤ)))).enorm.pow_const 2
  -- the bounds coming from the hypothesis and from the family estimate
  have hSm : ∫⁻ m : ℤ, (⨆ k : ℕ, ‖Mfun k m‖ₑ) ^ (2 : ℝ) ∂MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (A ^ 2) * G := by
    have hcorr : (fun m : ℤ => (⨆ k : ℕ, ‖Mfun k m‖ₑ) ^ (2 : ℝ))
        = (fun m : ℤ => (⨆ k : ℕ, ‖polyTkMax P g s k m‖ₑ) ^ (2 : ℝ)) := by
      funext m
      congr 1
      apply iSup_congr
      intro k
      exact congrArg (fun z : ℂ => ‖z‖ₑ) (htk_eq k m)
    rw [hcorr, hG]
    exact hAbound g s hgs
  have hSe : ∫⁻ m : ℤ, (⨆ k : ℕ, ‖Efun k m‖ₑ) ^ (2 : ℝ) ∂MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (S ^ 2) * G := by
    have hfam := Commons.Analysis.Fourier.maximal_l2_of_summable_multiplier_family
      psi Ab hAbnn hpsi_meas hpsi_bd hAb_summable g s hgs
    rw [hEfun, hPg, hW, hS, hG]
    exact hfam
  -- integral identities
  have hIa : ∫⁻ m : ℤ, 16 * (⨆ k : ℕ, ‖Mfun k m‖ₑ) ^ (2 : ℝ) ∂MeasureTheory.Measure.count
      = 16 * (∫⁻ m : ℤ, (⨆ k : ℕ, ‖Mfun k m‖ₑ) ^ (2 : ℝ) ∂MeasureTheory.Measure.count) :=
    lintegral_const_mul' 16 _ (by norm_num : (16 : ℝ≥0∞) ≠ ⊤)
  have hIb : ∫⁻ m : ℤ, 16 * (⨆ k : ℕ, ‖Efun k m‖ₑ) ^ (2 : ℝ) ∂MeasureTheory.Measure.count
      = 16 * (∫⁻ m : ℤ, (⨆ k : ℕ, ‖Efun k m‖ₑ) ^ (2 : ℝ) ∂MeasureTheory.Measure.count) :=
    lintegral_const_mul' 16 _ (by norm_num : (16 : ℝ≥0∞) ≠ ⊤)
  have hIc : ∫⁻ m : ℤ, 16 * ((‖g (m + P.eval (0 : ℤ))‖ₑ) ^ (2 : ℝ)
          + (‖g (m + P.eval (1 : ℤ))‖ₑ) ^ (2 : ℝ)) ∂MeasureTheory.Measure.count
      = 16 * (G + G) := by
    rw [lintegral_const_mul' 16 _ (by norm_num : (16 : ℝ≥0∞) ≠ ⊤)]
    congr 1
    rw [lintegral_add_left hameas]
    rw [lintegral_count_shift_add (fun m : ℤ => (‖g m‖ₑ) ^ (2 : ℝ)) (P.eval (0 : ℤ)),
      lintegral_count_shift_add (fun m : ℤ => (‖g m‖ₑ) ^ (2 : ℝ)) (P.eval (1 : ℤ))]
  have hIsum : ∫⁻ m : ℤ, ((16 * (⨆ k : ℕ, ‖Mfun k m‖ₑ) ^ (2 : ℝ)
          + 16 * (⨆ k : ℕ, ‖Efun k m‖ₑ) ^ (2 : ℝ))
        + 16 * ((‖g (m + P.eval (0 : ℤ))‖ₑ) ^ (2 : ℝ)
            + (‖g (m + P.eval (1 : ℤ))‖ₑ) ^ (2 : ℝ))) ∂MeasureTheory.Measure.count
      = (∫⁻ m : ℤ, (16 * (⨆ k : ℕ, ‖Mfun k m‖ₑ) ^ (2 : ℝ)
            + 16 * (⨆ k : ℕ, ‖Efun k m‖ₑ) ^ (2 : ℝ)) ∂MeasureTheory.Measure.count)
        + (∫⁻ m : ℤ, 16 * ((‖g (m + P.eval (0 : ℤ))‖ₑ) ^ (2 : ℝ)
            + (‖g (m + P.eval (1 : ℤ))‖ₑ) ^ (2 : ℝ)) ∂MeasureTheory.Measure.count) :=
    lintegral_add_left hxy _
  have hIxy : ∫⁻ m : ℤ, (16 * (⨆ k : ℕ, ‖Mfun k m‖ₑ) ^ (2 : ℝ)
          + 16 * (⨆ k : ℕ, ‖Efun k m‖ₑ) ^ (2 : ℝ)) ∂MeasureTheory.Measure.count
      = (∫⁻ m : ℤ, 16 * (⨆ k : ℕ, ‖Mfun k m‖ₑ) ^ (2 : ℝ) ∂MeasureTheory.Measure.count)
        + (∫⁻ m : ℤ, 16 * (⨆ k : ℕ, ‖Efun k m‖ₑ) ^ (2 : ℝ) ∂MeasureTheory.Measure.count) :=
    lintegral_add_left hMmeas _
  -- coefficient comparison
  have hcoe : (16 : ℝ≥0∞) * ENNReal.ofReal (A ^ 2) + 16 * ENNReal.ofReal (S ^ 2) + 32
      ≤ ENNReal.ofReal (C ^ 2) := by
    have h1 : ENNReal.ofReal D
        = 16 * ENNReal.ofReal (A ^ 2) + 16 * ENNReal.ofReal (S ^ 2) + 32 := by
      rw [hD]
      rw [ENNReal.ofReal_add (by positivity) (by norm_num : (0 : ℝ) ≤ 32),
          ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16),
          ENNReal.ofReal_ofNat, ENNReal.ofReal_ofNat]
    rw [← h1]
    exact ENNReal.ofReal_le_ofReal hCsq
  calc ∫⁻ m : ℤ, (⨆ k : ℕ, ‖((2 : ℝ) ^ k)⁻¹ * ∑ i ∈ Finset.range (2 ^ k),
          g (m + P.eval (i : ℤ))‖ₑ) ^ (2 : ℝ) ∂MeasureTheory.Measure.count
      ≤ ∫⁻ m : ℤ, ((16 * (⨆ k : ℕ, ‖Mfun k m‖ₑ) ^ (2 : ℝ)
            + 16 * (⨆ k : ℕ, ‖Efun k m‖ₑ) ^ (2 : ℝ))
          + 16 * ((‖g (m + P.eval (0 : ℤ))‖ₑ) ^ (2 : ℝ)
            + (‖g (m + P.eval (1 : ℤ))‖ₑ) ^ (2 : ℝ))) ∂MeasureTheory.Measure.count :=
        lintegral_mono hpoint
    _ = (16 * (∫⁻ m : ℤ, (⨆ k : ℕ, ‖Mfun k m‖ₑ) ^ (2 : ℝ) ∂MeasureTheory.Measure.count)
          + 16 * (∫⁻ m : ℤ, (⨆ k : ℕ, ‖Efun k m‖ₑ) ^ (2 : ℝ) ∂MeasureTheory.Measure.count))
          + 16 * (G + G) := by
        rw [hIsum, hIxy, hIa, hIb, hIc]
    _ ≤ (16 * (ENNReal.ofReal (A ^ 2) * G) + 16 * (ENNReal.ofReal (S ^ 2) * G)) + 16 * (G + G) := by
        exact add_le_add (add_le_add (mul_le_mul_right hSm 16) (mul_le_mul_right hSe 16)) le_rfl
    _ = (16 * ENNReal.ofReal (A ^ 2) + 16 * ENNReal.ofReal (S ^ 2) + 32) * G := by ring
    _ ≤ ENNReal.ofReal (C ^ 2) * G := mul_le_mul_left hcoe G

end Work.BourgainPlan.Maximal
