import Mathlib
import Submission.Work.BourgainPlan.Oscillation.oscZ_lacunary_defs
import Submission.Work.BourgainPlan.Oscillation.polyErrMultCutN_tsum_sq_le
import Submission.Work.BourgainPlan.Oscillation.plancherel_circle_enorm_sq_Ioc

/-!
# The block oscillation of the profile-replacement error at the lacunary scales

This file proves the third analytic input of Bourgain's oscillation inequality, namely
`OscZErrLacunary P ρ`: the block-oscillation functional `oscZ` of the profile-replacement error
family `polyErrMultCutN P m N₀ (⌊ρ^i⌋)` is bounded, uniformly in the block structure `k` and in the
data, by `(C·2^{-m·polySig P})² · ‖g‖²_{ℓ²(ℤ)}`.

The proof is a square-function argument and uses no circle-method input whatsoever:

* the *pointwise* input is `polyErrMultCutN_tsum_sq_le`: the squared moduli of the error multipliers
  are summable along the lacunary scales, with a sum bounded by `(C·2^{-mσ})²` uniformly in `θ`;
* the *operator* input is Plancherel for a bounded circle multiplier
  (`plancherel_circle_enorm_sq_Ioc`), which identifies the `ℓ²(ℤ)` norm of one error operator with
  the `L²(0,1)` norm of the multiplier times the trigonometric polynomial;
* exchanging the sum over the scale with the integral (Tonelli) and using the uniform bound on the
  multiplier square function gives the square-function bound `errOp_sqFn`;
* `oscZ_le_eight_tsum` converts the square-function bound into a bound for the block-oscillation
  functional, and the switch `if j₀ ≤ i` of the statement only removes terms, so it is harmless.

The final constant is `8 · C` because of the factor `8` in `oscZ_le_eight_tsum`.
-/

namespace Work.BourgainPlan.Oscillation

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open Finset MeasureTheory
open scoped BigOperators ENNReal
open Classical

noncomputable section

open Work.BourgainPlan.Maximal
open Commons.Analysis.ExponentialSums

/-! ## Measurability of the error multiplier -/

lemma measurable_polySharpTermN (P : Polynomial ℤ) (q a : ℕ) (l : ℤ) (N : ℕ) :
    Measurable (polySharpTermN P q a l N) := by
  unfold polySharpTermN
  exact measurable_const.mul (Measurable.ite (by measurability) measurable_const measurable_const)

lemma measurable_polyBlockCoreN (P : Polynomial ℤ) (m N : ℕ) :
    Measurable (polyBlockCoreN P m N) := by
  unfold polyBlockCoreN
  refine Finset.measurable_sum _ (fun i _ => Finset.measurable_sum _ (fun l _ => ?_))
  exact Complex.continuous_conj.measurable.comp (measurable_polySharpTermN P i.1 i.2 l N)

lemma measurable_polyBlockErrN (P : Polynomial ℤ) (m N₀ N : ℕ) :
    Measurable (polyBlockErrN P m N₀ N) := by
  unfold polyBlockErrN
  refine Measurable.sub (Complex.continuous_conj.measurable.comp
    (measurable_polyModelQBlock P m N)) ?_
  exact Measurable.ite (by measurability) (measurable_polyBlockCoreN P m N) measurable_const

lemma measurable_polyErrMultN (P : Polynomial ℤ) (m N₀ N : ℕ) :
    Measurable (polyErrMultN P m N₀ N) := by
  unfold polyErrMultN
  exact Measurable.ite (by measurability) (measurable_polyBlockErrN P m N₀ N) measurable_const

lemma measurable_polyErrMultCutN (P : Polynomial ℤ) (m N₀ N : ℕ) :
    Measurable (polyErrMultCutN P m N₀ N) := by
  unfold polyErrMultCutN
  exact Measurable.ite (by measurability) (measurable_polyErrMultN P m N₀ N) measurable_const

/-! ## The multiplier operator and Plancherel for one multiplier -/

/-- The multiplier operator on `ℤ` associated with the circle multiplier `m` and the finitely
supported data `g` on the support `s`: `x ↦ ∫₀¹ m θ · (Σ_{n∈s} g n e(nθ)) · e(-xθ) dθ`. -/
def errOp (m : ℝ → ℂ) (g : ℤ → ℂ) (s : Finset ℤ) (x : ℤ) : ℂ :=
  ∫ θ in (0 : ℝ)..1, m θ * Lacunary.trigP s g θ * Lacunary.Echar x θ

/-- The `enorm` of a complex number is the `ofReal` of its norm. -/
lemma enorm_complex_eq (z : ℂ) : ‖z‖ₑ = ENNReal.ofReal ‖z‖ := by
  rw [enorm_eq_nnnorm, ENNReal.coe_nnreal_eq]
  norm_cast

/-- **Plancherel for a single bounded circle multiplier, in `ℝ≥0∞` form.**  The `ℓ²(ℤ)` norm of
one multiplier operator is the weighted `L²` norm of the multiplier against the trigonometric
polynomial of the data. -/
lemma lintegral_errOp_eq (m : ℝ → ℂ) (hm : Measurable m) {A : ℝ} (hA : 0 ≤ A)
    (hbd : ∀ θ, θ ∈ Set.Ioc (0:ℝ) 1 → ‖m θ‖ ≤ A) (g : ℤ → ℂ) (s : Finset ℤ) :
    ∫⁻ x : ℤ, ‖errOp m g s x‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count
      = ∫⁻ θ, ‖m θ‖ₑ ^ (2:ℝ) * ‖Lacunary.trigP s g θ‖ₑ ^ (2:ℝ) ∂Lacunary.mu01 := by
  haveI := Lacunary.isFiniteMeasure_mu01
  have hmem : MemLp (Lacunary.trigP s g) 2 Lacunary.mu01 :=
    MemLp.of_bound (Lacunary.measurable_trigP s g).aestronglyMeasurable (∑ j ∈ s, ‖g j‖)
      (Filter.Eventually.of_forall (Lacunary.norm_trigP_le s g))
  have hP := plancherel_circle_enorm_sq_Ioc m (Lacunary.trigP s g) hm ⟨A, hbd⟩ hmem
  have hInt : Integrable (fun θ => ‖m θ‖ ^ 2 * ‖Lacunary.trigP s g θ‖ ^ 2) Lacunary.mu01 := by
    refine Integrable.of_bound ?_ (A ^ 2 * (∑ j ∈ s, ‖g j‖) ^ 2) ?_
    · exact ((hm.norm.pow_const 2).mul
        ((Lacunary.measurable_trigP s g).norm.pow_const 2)).aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem (μ := volume) measurableSet_Ioc] with θ hθ
      rw [Real.norm_of_nonneg (by positivity)]
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hbd θ hθ) 2)
        (pow_le_pow_left₀ (norm_nonneg _) (Lacunary.norm_trigP_le s g θ) 2)
        (by positivity) (by positivity)
  rw [MeasureTheory.lintegral_count]
  rw [show (∑' x : ℤ, ‖errOp m g s x‖ₑ ^ (2:ℝ))
      = ∑' n : ℤ, ‖∫ θ in (0:ℝ)..1, m θ * Lacunary.trigP s g θ *
          Complex.exp (-(2 * Real.pi * Complex.I * ((n : ℤ) : ℂ) * (θ : ℂ)))‖ₑ ^ (2:ℝ) from rfl]
  rw [hP, Lacunary.ofReal_integral_mu01 hInt (Filter.Eventually.of_forall (fun _ => by positivity))]
  refine lintegral_congr (fun θ => ?_)
  rw [Commons.Analysis.Fourier.enorm_complex_pow_two,
    Commons.Analysis.Fourier.enorm_complex_pow_two, ENNReal.ofReal_mul (by positivity)]

/-! ## The square function bound -/

/-- **The square-function bound for a family of multipliers.**  If the squared moduli of a family of
multipliers have bounded finite sums, then the `ℓ²(ℤ)` norm of the square function of the associated
operators is bounded by that bound times the `ℓ²` norm of the data. -/
lemma errOp_sqFn (m : ℕ → ℝ → ℂ) (A : ℝ) (hA : 0 ≤ A) (hm : ∀ j, Measurable (m j))
    (hsum : ∀ (t : Finset ℕ) (θ : ℝ),
      ∑ j ∈ t, ‖m j θ‖ₑ ^ (2:ℝ) ≤ ENNReal.ofReal (A ^ 2))
    (g : ℤ → ℂ) (s : Finset ℤ) (hs : ∀ n, n ∉ s → g n = 0) :
    ∫⁻ x : ℤ, (∑' j : ℕ, ‖errOp (m j) g s x‖ₑ ^ (2:ℝ)) ∂MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (A ^ 2) * ∫⁻ x : ℤ, ‖g x‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count := by
  have hbd : ∀ j θ, θ ∈ Set.Ioc (0:ℝ) 1 → ‖m j θ‖ ≤ A := by
    intro j θ _
    have h := hsum {j} θ
    rw [Finset.sum_singleton] at h
    rw [Commons.Analysis.Fourier.enorm_complex_pow_two] at h
    have h2 := (ENNReal.ofReal_le_ofReal_iff (sq_nonneg A)).mp h
    nlinarith [norm_nonneg (m j θ)]
  have htsum : ∀ θ : ℝ, (∑' j : ℕ, ‖m j θ‖ₑ ^ (2:ℝ)) ≤ ENNReal.ofReal (A ^ 2) := by
    intro θ
    rw [ENNReal.tsum_eq_iSup_sum]
    exact iSup_le (fun t => hsum t θ)
  calc ∫⁻ x : ℤ, (∑' j : ℕ, ‖errOp (m j) g s x‖ₑ ^ (2:ℝ)) ∂MeasureTheory.Measure.count
      = ∑' j : ℕ, ∫⁻ x : ℤ, ‖errOp (m j) g s x‖ₑ ^ (2:ℝ)
          ∂MeasureTheory.Measure.count :=
        MeasureTheory.lintegral_tsum (fun j => (measurable_of_countable _).aemeasurable)
    _ = ∑' j : ℕ, ∫⁻ θ, ‖m j θ‖ₑ ^ (2:ℝ) * ‖Lacunary.trigP s g θ‖ₑ ^ (2:ℝ) ∂Lacunary.mu01 :=
        tsum_congr (fun j => lintegral_errOp_eq (m j) (hm j) hA (hbd j) g s)
    _ = ∫⁻ θ, (∑' j : ℕ, ‖m j θ‖ₑ ^ (2:ℝ)) * ‖Lacunary.trigP s g θ‖ₑ ^ (2:ℝ)
          ∂Lacunary.mu01 := by
        rw [← MeasureTheory.lintegral_tsum (μ := Lacunary.mu01)
          (f := fun j θ => ‖m j θ‖ₑ ^ (2:ℝ) * ‖Lacunary.trigP s g θ‖ₑ ^ (2:ℝ))
          (fun j => (((hm j).enorm.pow_const 2).mul
            ((Lacunary.measurable_trigP s g).enorm.pow_const 2)).aemeasurable)]
        refine lintegral_congr (fun θ => ?_)
        rw [ENNReal.tsum_mul_right]
    _ ≤ ∫⁻ θ, ENNReal.ofReal (A ^ 2) * ‖Lacunary.trigP s g θ‖ₑ ^ (2:ℝ) ∂Lacunary.mu01 :=
        lintegral_mono (fun θ => mul_le_mul_of_nonneg_right (htsum θ) (by positivity))
    _ = ENNReal.ofReal (A ^ 2) * ∫⁻ θ, ‖Lacunary.trigP s g θ‖ₑ ^ (2:ℝ) ∂Lacunary.mu01 :=
        MeasureTheory.lintegral_const_mul _ ((Lacunary.measurable_trigP s g).enorm.pow_const 2)
    _ = ENNReal.ofReal (A ^ 2) * ∫⁻ x : ℤ, ‖g x‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count := by
        rw [Lacunary.trig_lintegral, Lacunary.f_lintegral s g hs]

/-! ## The main theorem -/

theorem oscZ_err_lacunary (P : Polynomial ℤ) (hc : 0 < P.leadingCoeff) (hd : 2 ≤ P.natDegree)
    (ρ : ℝ) (hρ : 1 < ρ)
    (hcard : ∀ (m N : ℕ) (θ : ℝ), 2 ^ (4 * m + 4) ≤ N →
      (Work.BourgainPlan.Oscillation.polyActIdxN P m N θ).card ≤ 1) :
    Work.BourgainPlan.Oscillation.OscZErrLacunary P ρ := by
  have hK : ∀ (m N : ℕ), 0 ≤ N → 2 ^ (4 * m + 4) ≤ N → ∀ θ : ℝ,
      (Work.BourgainPlan.Oscillation.polyActIdxN P m N θ).card ≤ 1 :=
    fun m N _ hN θ => hcard m N θ hN
  obtain ⟨Cε, hCεpos, hCε⟩ := polyErrMultCutN_tsum_sq_le P hc hd hK ρ hρ
  refine ⟨8 * Cε, by positivity, ?_⟩
  intro m N₀ h2mN j₀ J k hk g s hs
  set σ : ℝ := polySig P with hσ
  set dec : ℝ := (2:ℝ) ^ (-(m:ℝ) * σ) with hdec
  have hdec0 : 0 ≤ dec := by rw [hdec]; positivity
  set Ac : ℝ := Cε * dec with hAc
  have hAc0 : 0 ≤ Ac := by rw [hAc]; positivity
  set mFun : ℕ → ℝ → ℂ := fun j θ => polyErrMultCutN P m N₀ (lacScale ρ j) θ with hmFun
  have hsum : ∀ (t : Finset ℕ) (θ : ℝ),
      ∑ j ∈ t, ‖mFun j θ‖ₑ ^ (2:ℝ) ≤ ENNReal.ofReal (Ac ^ 2) := by
    intro t θ
    refine le_trans (ENNReal.sum_le_tsum t) (le_trans (hCε m N₀ (Nat.zero_le N₀) h2mN θ) ?_)
    rw [hAc, ← ENNReal.ofReal_pow hAc0 2]
  have hm : ∀ j : ℕ, Measurable (mFun j) := fun j => measurable_polyErrMultCutN P m N₀ _
  have hsq := errOp_sqFn mFun Ac hAc0 hm hsum g s hs
  set T : ℕ → ℤ → ℂ := fun i x => if j₀ ≤ i then errOp (mFun i) g s x else 0 with hT
  have hTeq : (fun i x => if j₀ ≤ i then ∫ θ in (0:ℝ)..1,
        polyErrMultCutN P m N₀ (lacScale ρ i) θ *
        (∑ n ∈ s, g n * Complex.exp (2 * Real.pi * Complex.I * ((n : ℤ) : ℂ) * (θ : ℂ))) *
        Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (θ : ℂ))) else 0) = T := by
    funext i x
    rw [hT, hmFun]
    by_cases h : j₀ ≤ i <;> simp [h, errOp, Lacunary.trigP, Lacunary.Echar]
  rw [hTeq]
  set I : ℝ≥0∞ := ∫⁻ x : ℤ, ‖g x‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count with hI
  have hpt : ∀ i x, ‖T i x‖ₑ ^ (2:ℝ) ≤ ‖errOp (mFun i) g s x‖ₑ ^ (2:ℝ) := by
    intro i x
    by_cases h : j₀ ≤ i
    · have h1 : T i x = errOp (mFun i) g s x := by rw [hT]; simp [h]
      rw [h1]
    · have h1 : T i x = 0 := by rw [hT]; simp [h]
      rw [h1]
      simp
  have hstep1 : oscZ T J k
      ≤ 8 * ∑' i : ℕ, ∫⁻ x : ℤ, ‖errOp (mFun i) g s x‖ₑ ^ (2:ℝ)
          ∂MeasureTheory.Measure.count := by
    refine le_trans (oscZ_le_eight_tsum T J k hk) ?_
    refine mul_le_mul_of_nonneg_left (ENNReal.tsum_le_tsum (fun i => ?_)) (by norm_num)
    exact lintegral_mono (fun x => hpt i x)
  have hstep2 : (∑' i : ℕ, ∫⁻ x : ℤ, ‖errOp (mFun i) g s x‖ₑ ^ (2:ℝ)
        ∂MeasureTheory.Measure.count)
      = ∫⁻ x : ℤ, (∑' i : ℕ, ‖errOp (mFun i) g s x‖ₑ ^ (2:ℝ))
        ∂MeasureTheory.Measure.count := by
    simp_rw [MeasureTheory.lintegral_count]
    exact ENNReal.tsum_comm
  have hstep3 : 8 * (ENNReal.ofReal (Ac ^ 2) * I)
      ≤ ENNReal.ofReal ((8 * Cε) * dec) ^ 2 * I := by
    have hmain : (8 : ℝ≥0∞) * ENNReal.ofReal (Ac ^ 2) ≤ ENNReal.ofReal ((8 * Cε) * dec) ^ 2 := by
      rw [hAc, ← ENNReal.ofReal_pow (by positivity : (0:ℝ) ≤ (8 * Cε) * dec) 2]
      rw [show (8 : ℝ≥0∞) = ENNReal.ofReal 8 from by norm_num]
      rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 8)]
      refine ENNReal.ofReal_le_ofReal ?_
      nlinarith [sq_nonneg (Cε * dec)]
    calc 8 * (ENNReal.ofReal (Ac ^ 2) * I)
        = ((8 : ℝ≥0∞) * ENNReal.ofReal (Ac ^ 2)) * I := by ring
      _ ≤ ENNReal.ofReal ((8 * Cε) * dec) ^ 2 * I :=
          mul_le_mul_of_nonneg_right hmain bot_le
  have hfinal : oscZ T J k ≤ ENNReal.ofReal ((8 * Cε) * dec) ^ 2 * I := by
    calc oscZ T J k
        ≤ 8 * ∑' i : ℕ, ∫⁻ x : ℤ, ‖errOp (mFun i) g s x‖ₑ ^ (2:ℝ)
            ∂MeasureTheory.Measure.count := hstep1
      _ = 8 * ∫⁻ x : ℤ, (∑' i : ℕ, ‖errOp (mFun i) g s x‖ₑ ^ (2:ℝ))
            ∂MeasureTheory.Measure.count := by rw [hstep2]
      _ ≤ 8 * (ENNReal.ofReal (Ac ^ 2) * I) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          rw [hI]
          exact hsq
      _ ≤ ENNReal.ofReal ((8 * Cε) * dec) ^ 2 * I := hstep3
  refine le_trans hfinal ?_
  rw [hdec, hσ]

end

end Work.BourgainPlan.Oscillation
