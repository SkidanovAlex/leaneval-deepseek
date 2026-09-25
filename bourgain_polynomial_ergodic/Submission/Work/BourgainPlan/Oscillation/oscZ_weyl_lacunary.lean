import Mathlib
import Submission.Work.BourgainPlan.Oscillation.lacunary_defs
import Submission.Work.BourgainPlan.Oscillation.oscWeylDefs
import Submission.Work.BourgainPlan.Oscillation.lacunary_truncated_maximal_l2
import Submission.Work.BourgainPlan.Oscillation.oscZ_of_multiplier_family
import Submission.Work.BourgainPlan.Oscillation.weylModelDiff_lacunary
import Submission.Work.BourgainPlan.Maximal.poly_dyadic_of_model

/-!
# From the major-arc model to the Weyl kernel: the lacunary oscillation inequality

This file proves `oscZ_weyl_lacunary`: if the block-oscillation functional `oscZ` of the
**major-arc model operators** `polyModelOp P g s (⌊ρ^i⌋)` is bounded — the analytic input proved
in the circle-method part of the project — then the same holds for the **true Weyl averages**
`polyWeylOp P g s (⌊ρ^i⌋)`.

The proof is soft.  Write `W i`, `M i`, `E i` for the Weyl, model and error operators at the
lacunary scale `⌊ρ^i⌋`, where the error multiplier is

  `D_i(θ) = conj(WeylKernel(⌊ρ^i⌋,θ)) − conj(MajorArcModel(⌊ρ^i⌋,θ))`.

Then `W i = M i + E i`, so by subadditivity of `oscZ`

  `oscZ W ≤ 4 · oscZ M + 4 · oscZ E`,

and the hypothesis controls the first term.  For the second, `weylModelDiff_lacunary` provides a
uniform bound `B` for `‖D_i‖` on `(0,1]` and a **summable** sequence `a` with
`‖D_{i+1} − D_i‖ ≤ a i` and `Σ_{i∈S} a i ≤ D`.  Feeding these into
`oscZ_of_multiplier_family` (which turns `‖m_{i+1} − m_i‖ ≤ a i` into an `oscZ` bound via
Plancherel) gives `oscZ E ≤ D² ∫|g|²`.
-/

namespace Work.BourgainPlan.Oscillation

open Finset MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

open Work.BourgainPlan.Maximal

/-! ## Subadditivity of the block-oscillation functional -/

/-- **Subadditivity of `oscZ`.**  If `A` is the pointwise sum of `B` and `C`, the block
oscillation of `A` is at most `4` times the sum of the block oscillations of `B` and `C`. -/
theorem oscZ_add_le_c {A B C : ℕ → ℤ → ℂ} (h : ∀ i x, A i x = B i x + C i x)
    (J : ℕ) (k : ℕ → ℕ) :
    oscZ A J k ≤ 4 * oscZ B J k + 4 * oscZ C J k := by
  have hpt : ∀ (j : ℕ) (x : ℤ),
      (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖A i x - A (k j) x‖ₑ) ^ (2 : ℝ)
        ≤ 4 * (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖B i x - B (k j) x‖ₑ) ^ (2 : ℝ)
          + 4 * (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖C i x - C (k j) x‖ₑ) ^ (2 : ℝ) := by
    intro j x
    set W := ⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖A i x - A (k j) x‖ₑ with hW
    set U := ⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖B i x - B (k j) x‖ₑ with hU
    set V := ⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖C i x - C (k j) x‖ₑ with hV
    have hsplit : W ≤ U + V := by
      rw [hW, hU, hV]
      refine iSup₂_le (fun i hi => ?_)
      have hid : A i x - A (k j) x
          = (B i x - B (k j) x) + (C i x - C (k j) x) := by rw [h i x, h (k j) x]; ring
      calc ‖A i x - A (k j) x‖ₑ
          = ‖(B i x - B (k j) x) + (C i x - C (k j) x)‖ₑ := by rw [hid]
        _ ≤ ‖B i x - B (k j) x‖ₑ + ‖C i x - C (k j) x‖ₑ := enorm_add_le _ _
        _ ≤ (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖B i x - B (k j) x‖ₑ)
              + (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖C i x - C (k j) x‖ₑ) :=
            add_le_add
              (le_iSup₂ (f := fun i (_ : i ∈ Finset.Ico (k j) (k (j + 1))) =>
                ‖B i x - B (k j) x‖ₑ) i hi)
              (le_iSup₂ (f := fun i (_ : i ∈ Finset.Ico (k j) (k (j + 1))) =>
                ‖C i x - C (k j) x‖ₑ) i hi)
    have h4 : (U + V) ^ (2 : ℝ) ≤ 4 * U ^ (2 : ℝ) + 4 * V ^ (2 : ℝ) := by
      have h' := Lacunary.add_sq_le U V
      rw [ENNReal.rpow_two, ENNReal.rpow_two, ENNReal.rpow_two] at h'
      rw [ENNReal.rpow_two, ENNReal.rpow_two, ENNReal.rpow_two]
      refine h'.trans (le_of_eq ?_)
      rw [mul_add]
    exact (ENNReal.rpow_le_rpow hsplit (by norm_num : (0 : ℝ) ≤ 2)).trans h4
  have key : ∀ j : ℕ,
      (∫⁻ x : ℤ, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖A i x - A (k j) x‖ₑ) ^ (2 : ℝ)
          ∂MeasureTheory.Measure.count)
        ≤ 4 * (∫⁻ x : ℤ, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
              ‖B i x - B (k j) x‖ₑ) ^ (2 : ℝ) ∂MeasureTheory.Measure.count)
          + 4 * (∫⁻ x : ℤ, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
              ‖C i x - C (k j) x‖ₑ) ^ (2 : ℝ) ∂MeasureTheory.Measure.count) := by
    intro j
    set UB : ℤ → ℝ≥0∞ :=
      fun x => (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖B i x - B (k j) x‖ₑ) ^ (2 : ℝ) with hUB
    set UC : ℤ → ℝ≥0∞ :=
      fun x => (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖C i x - C (k j) x‖ₑ) ^ (2 : ℝ) with hUC
    have h1 : (∫⁻ x : ℤ, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
            ‖A i x - A (k j) x‖ₑ) ^ (2 : ℝ) ∂MeasureTheory.Measure.count)
        ≤ ∫⁻ x : ℤ, (4 * UB x + 4 * UC x) ∂MeasureTheory.Measure.count := by
      refine lintegral_mono (fun x => ?_)
      conv_rhs => rw [hUB, hUC]
      exact hpt j x
    refine h1.trans (le_of_eq ?_)
    rw [lintegral_add_left (measurable_of_countable (fun x : ℤ => 4 * UB x)),
      lintegral_const_mul 4 (measurable_of_countable (fun x : ℤ => UB x)),
      lintegral_const_mul 4 (measurable_of_countable (fun x : ℤ => UC x))]
  calc oscZ A J k
      = ∑ j ∈ Finset.range J, ∫⁻ x : ℤ,
          (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖A i x - A (k j) x‖ₑ) ^ (2 : ℝ)
          ∂MeasureTheory.Measure.count := rfl
    _ ≤ ∑ j ∈ Finset.range J, (4 * (∫⁻ x : ℤ, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
              ‖B i x - B (k j) x‖ₑ) ^ (2 : ℝ) ∂MeasureTheory.Measure.count)
          + 4 * (∫⁻ x : ℤ, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
              ‖C i x - C (k j) x‖ₑ) ^ (2 : ℝ) ∂MeasureTheory.Measure.count)) :=
        Finset.sum_le_sum (fun j _ => key j)
    _ = 4 * oscZ B J k + 4 * oscZ C J k := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        rfl

/-! ## The multiplier of the Weyl average, of the model, and their difference -/

/-- The (conjugated) Weyl multiplier at the lacunary scale `⌊ρ^i⌋`. -/
private noncomputable def kerM (P : Polynomial ℤ) (ρ : ℝ) (i : ℕ) : ℝ → ℂ :=
  fun θ => starRingEnd ℂ (polyWeylKernel P (lacScale ρ i) θ)

/-- The (conjugated) major-arc model multiplier at the lacunary scale `⌊ρ^i⌋`. -/
private noncomputable def mdlM (P : Polynomial ℤ) (ρ : ℝ) (i : ℕ) : ℝ → ℂ :=
  fun θ => starRingEnd ℂ (polyMajorArcModelPre P ((1 : ℝ) / 4) (lacScale ρ i) θ)

/-- The error multiplier `D_i = kerM − mdlM`, truncated to the integration interval `(0,1]`. -/
private noncomputable def errM (P : Polynomial ℤ) (ρ : ℝ) (i : ℕ) : ℝ → ℂ :=
  fun θ => if θ ∈ Set.Ioc (0 : ℝ) 1 then kerM P ρ i θ - mdlM P ρ i θ else 0

private lemma measurable_kerM (P : Polynomial ℤ) (ρ : ℝ) (i : ℕ) : Measurable (kerM P ρ i) :=
  (Complex.continuous_conj.comp (continuous_polyWeylKernel P (lacScale ρ i))).measurable

private lemma measurable_mdlM (P : Polynomial ℤ) (ρ : ℝ) (i : ℕ) : Measurable (mdlM P ρ i) :=
  Complex.continuous_conj.measurable.comp
    (measurable_polyMajorArcModelPre P ((1 : ℝ) / 4) (lacScale ρ i))

private lemma measurable_errM (P : Polynomial ℤ) (ρ : ℝ) (i : ℕ) : Measurable (errM P ρ i) := by
  show Measurable (fun θ : ℝ =>
    if θ ∈ Set.Ioc (0 : ℝ) 1 then kerM P ρ i θ - mdlM P ρ i θ else 0)
  exact Measurable.ite measurableSet_Ioc ((measurable_kerM P ρ i).sub (measurable_mdlM P ρ i))
    measurable_const

/-- The lacunary scale is positive. -/
private lemma one_le_lacScale_c (ρ : ℝ) (hρ : 1 ≤ ρ) (i : ℕ) : 1 ≤ lacScale ρ i :=
  Nat.le_floor (by simpa using one_le_pow₀ (n := i) hρ)

/-- The Weyl kernel is a mean of `N` unit complex numbers. -/
private lemma norm_polyWeylKernel_le_one_c (P : Polynomial ℤ) {N : ℕ} (hN : 1 ≤ N) (θ : ℝ) :
    ‖polyWeylKernel P N θ‖ ≤ 1 := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hscal : ‖((((N : ℝ))⁻¹) : ℂ)‖ = (N : ℝ)⁻¹ := by
    rw [show ((((N : ℝ))⁻¹) : ℂ) = ((N : ℂ))⁻¹ by push_cast; ring, norm_inv,
      Complex.norm_natCast]
  have hsum : ‖∑ n ∈ Finset.range N, Complex.exp (2 * Real.pi * Complex.I *
      (((θ * ((P.eval (n : ℤ) : ℤ) : ℝ) : ℝ)) : ℂ))‖ ≤ (N : ℝ) := by
    calc ‖∑ n ∈ Finset.range N, Complex.exp (2 * Real.pi * Complex.I *
            (((θ * ((P.eval (n : ℤ) : ℤ) : ℝ) : ℝ)) : ℂ))‖
        ≤ ∑ n ∈ Finset.range N, ‖Complex.exp (2 * Real.pi * Complex.I *
            (((θ * ((P.eval (n : ℤ) : ℤ) : ℝ) : ℝ)) : ℂ))‖ := norm_sum_le _ _
      _ = ∑ _n ∈ Finset.range N, (1 : ℝ) :=
          Finset.sum_congr rfl (fun n _ => norm_exp_two_pi_I_mul _)
      _ = (N : ℝ) := by simp
  calc ‖polyWeylKernel P N θ‖
      = ‖((((N : ℝ))⁻¹) : ℂ)‖ * ‖∑ n ∈ Finset.range N, Complex.exp (2 * Real.pi * Complex.I *
          (((θ * ((P.eval (n : ℤ) : ℤ) : ℝ) : ℝ)) : ℂ))‖ := by
        rw [polyWeylKernel, norm_mul]
    _ ≤ (N : ℝ)⁻¹ * (N : ℝ) := by
        rw [hscal]
        exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 1 := inv_mul_cancel₀ (ne_of_gt hN0)

private lemma norm_kerM_le_one (P : Polynomial ℤ) (ρ : ℝ) (hρ : 1 ≤ ρ) (i : ℕ) (θ : ℝ) :
    ‖kerM P ρ i θ‖ ≤ 1 := by
  rw [kerM, Complex.norm_conj]
  exact norm_polyWeylKernel_le_one_c P (one_le_lacScale_c ρ hρ i) θ

private lemma norm_mdlM_le (P : Polynomial ℤ) (ρ : ℝ) (i : ℕ) (θ : ℝ) :
    ‖mdlM P ρ i θ‖
      ≤ ((Nat.floor (((lacScale ρ i : ℕ) : ℝ) ^ ((1 : ℝ) / 4))) : ℝ) ^ 2
          * (((P.leadingCoeff + 2).toNat : ℕ) : ℝ) := by
  rw [mdlM, Complex.norm_conj]
  exact norm_polyMajorArcModelPre_le P ((1 : ℝ) / 4) (lacScale ρ i) θ

/-- `kerM − mdlM` is the conjugate of the Weyl/model difference. -/
private lemma kerM_sub_mdlM (P : Polynomial ℤ) (ρ : ℝ) (i : ℕ) (θ : ℝ) :
    kerM P ρ i θ - mdlM P ρ i θ
      = starRingEnd ℂ (polyWeylKernel P (lacScale ρ i) θ
          - polyMajorArcModelPre P ((1 : ℝ) / 4) (lacScale ρ i) θ) := by
  rw [kerM, mdlM, ← map_sub]

/-! ## `opMul` helpers -/

/-- `opMul` written in the `trigP`/`Echar` shape of the `Lacunary` development. -/
private lemma opMul_eq_trigP (m : ℝ → ℂ) (g : ℤ → ℂ) (s : Finset ℤ) (x : ℤ) :
    opMul m g s x = ∫ θ in (0 : ℝ)..1, m θ * Lacunary.trigP s g θ * Lacunary.Echar x θ := by
  show (∫ θ in (0 : ℝ)..1, m θ *
      (∑ j ∈ s, g j * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (θ : ℂ)))) *
      Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℂ) * (θ : ℂ))))) = _
  simp only [Lacunary.trigP, Lacunary.Echar]
  refine intervalIntegral.integral_congr (fun θ _ => ?_)
  congr 2
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    congr 1
    ring_nf
  · congr 1
    ring_nf

/-- The `opMul` integrand is integrable against `mu01` as soon as the multiplier is bounded. -/
private lemma integrable_opMul_trigP (m : ℝ → ℂ) (hm : Measurable m) {B : ℝ}
    (hB : ∀ θ, ‖m θ‖ ≤ B) (g : ℤ → ℂ) (s : Finset ℤ) (x : ℤ) :
    Integrable (fun θ => m θ * Lacunary.trigP s g θ * Lacunary.Echar x θ) Lacunary.mu01 := by
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  refine Lacunary.integrable_Ioc_of_bound (C := B * ∑ j ∈ s, ‖g j‖) ?_ ?_
  · exact (hm.mul (Lacunary.measurable_trigP s g)).mul (Lacunary.continuous_Echar x).measurable
  · intro θ
    rw [norm_mul, norm_mul, Lacunary.norm_Echar x θ, mul_one]
    refine mul_le_mul (hB θ) (Lacunary.norm_trigP_le s g θ) (by positivity) hB0

/-- Interval integrability of the `opMul` integrand. -/
private lemma intervalIntegrable_opMul_trigP (m : ℝ → ℂ) (hm : Measurable m) {B : ℝ}
    (hB : ∀ θ, ‖m θ‖ ≤ B) (g : ℤ → ℂ) (s : Finset ℤ) (x : ℤ) :
    IntervalIntegrable (fun θ => m θ * Lacunary.trigP s g θ * Lacunary.Echar x θ) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact integrable_opMul_trigP m hm hB g s x

/-- **Linearity of `opMul` in the multiplier.** -/
private lemma opMul_sub_c (m₁ m₂ : ℝ → ℂ) (hm₁ : Measurable m₁) (hm₂ : Measurable m₂)
    {B₁ B₂ : ℝ} (hB₁ : ∀ θ, ‖m₁ θ‖ ≤ B₁) (hB₂ : ∀ θ, ‖m₂ θ‖ ≤ B₂)
    (g : ℤ → ℂ) (s : Finset ℤ) (x : ℤ) :
    opMul (fun θ => m₁ θ - m₂ θ) g s x = opMul m₁ g s x - opMul m₂ g s x := by
  rw [opMul_eq_trigP (fun θ => m₁ θ - m₂ θ) g s x, opMul_eq_trigP m₁ g s x,
    opMul_eq_trigP m₂ g s x]
  rw [← intervalIntegral.integral_sub
    (intervalIntegrable_opMul_trigP m₁ hm₁ hB₁ g s x)
    (intervalIntegrable_opMul_trigP m₂ hm₂ hB₂ g s x)]
  refine intervalIntegral.integral_congr (fun θ _ => ?_)
  ring

/-- **`opMul` only sees the multiplier on `(0,1]`.** -/
private lemma opMul_congr_Ioc {m m' : ℝ → ℂ} (h : ∀ θ ∈ Set.Ioc (0 : ℝ) 1, m θ = m' θ)
    (g : ℤ → ℂ) (s : Finset ℤ) (x : ℤ) :
    opMul m g s x = opMul m' g s x := by
  rw [opMul, opMul, Lacunary.intervalIntegral_eq_mu01, Lacunary.intervalIntegral_eq_mu01]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
  rw [h θ hθ]

/-! ## The main theorem -/

/-- **The pointwise decomposition `W = M + E`.**  The Weyl average at the lacunary scale splits as
the major-arc model plus the operator of the error multiplier `errM`. -/
private lemma polyWeylOp_eq_polyModelOp_add (P : Polynomial ℤ) (ρ : ℝ) (hρ : 1 ≤ ρ)
    (g : ℤ → ℂ) (s : Finset ℤ) (i : ℕ) (x : ℤ) :
    polyWeylOp P g s (lacScale ρ i) x
      = polyModelOp P g s (lacScale ρ i) x + opMul (errM P ρ i) g s x := by
  have hEr : opMul (errM P ρ i) g s x
      = opMul (fun θ => kerM P ρ i θ - mdlM P ρ i θ) g s x :=
    opMul_congr_Ioc (fun θ hθ => by simp only [errM, hθ, if_true]) g s x
  have hlin : opMul (fun θ => kerM P ρ i θ - mdlM P ρ i θ) g s x
      = opMul (kerM P ρ i) g s x - opMul (mdlM P ρ i) g s x :=
    opMul_sub_c (kerM P ρ i) (mdlM P ρ i) (measurable_kerM P ρ i) (measurable_mdlM P ρ i)
      (norm_kerM_le_one P ρ hρ i) (norm_mdlM_le P ρ i) g s x
  have e1 : polyWeylOp P g s (lacScale ρ i) x = opMul (kerM P ρ i) g s x := rfl
  have e2 : polyModelOp P g s (lacScale ρ i) x = opMul (mdlM P ρ i) g s x := rfl
  rw [e1, e2, hEr, hlin]
  ring

theorem oscZ_weyl_lacunary (P : Polynomial ℤ) (hc : 0 < P.leadingCoeff) (hd : 2 ≤ P.natDegree)
    (ρ : ℝ) (hρ : 1 < ρ)
    (hmodel : ∃ A : ℝ, 0 < A ∧ ∀ (g : ℤ → ℂ) (s : Finset ℤ), (∀ n, n ∉ s → g n = 0) →
      ∀ (J : ℕ) (k : ℕ → ℕ), StrictMono k →
        Work.BourgainPlan.Oscillation.oscZ (fun i x =>
            Work.BourgainPlan.Oscillation.polyModelOp P g s
              (Work.BourgainPlan.Oscillation.lacScale ρ i) x) J k
          ≤ ENNReal.ofReal (A^2) *
              ∫⁻ x : ℤ, ‖g x‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count) :
    ∃ C : ℝ, 0 < C ∧ ∀ (g : ℤ → ℂ) (s : Finset ℤ), (∀ n, n ∉ s → g n = 0) →
      ∀ (J : ℕ) (k : ℕ → ℕ), StrictMono k →
        Work.BourgainPlan.Oscillation.oscZ (fun i x =>
            Work.BourgainPlan.Oscillation.polyWeylOp P g s
              (Work.BourgainPlan.Oscillation.lacScale ρ i) x) J k
          ≤ ENNReal.ofReal (C^2) *
              ∫⁻ x : ℤ, ‖g x‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count := by
  obtain ⟨A, hApos, hmod⟩ := hmodel
  obtain ⟨a, B, D, hB0, hD0, hapos, hSum, hBdd, hInc⟩ :=
    weylModelDiff_lacunary P hc hd ρ hρ
  classical
  refine ⟨Real.sqrt (4 * A ^ 2 + 4 * D ^ 2 + 1), Real.sqrt_pos.2 (by positivity), ?_⟩
  intro g s hs J k hk
  -- the error multiplier: bounded on `(0,1]` and with summable increments
  have herr_bdd : ∀ i θ, θ ∈ Set.Ioc (0 : ℝ) 1 → ‖kerM P ρ i θ - mdlM P ρ i θ‖ ≤ B := by
    intro i θ hθ
    rw [kerM_sub_mdlM, Complex.norm_conj]
    exact hBdd i θ hθ
  have herr_inc : ∀ i θ, ‖errM P ρ (i + 1) θ - errM P ρ i θ‖ ≤ a i := by
    intro i θ
    by_cases hθ : θ ∈ Set.Ioc (0 : ℝ) 1
    · simp only [errM, hθ, if_true, kerM_sub_mdlM, ← map_sub, Complex.norm_conj]
      exact hInc i θ hθ
    · simp only [errM, hθ, if_false, sub_self, norm_zero]
      exact le_of_lt (hapos i)
  have herr_bound : ∀ i, ∃ B' : ℝ, ∀ θ, ‖errM P ρ i θ‖ ≤ B' := by
    intro i
    refine ⟨B, fun θ => ?_⟩
    by_cases hθ : θ ∈ Set.Ioc (0 : ℝ) 1
    · simp only [errM, hθ, if_true]; exact herr_bdd i θ hθ
    · simp only [errM, hθ, if_false]; simpa using hB0
  -- the abstract oscillation bound for the error family
  have hE : oscZ (fun i x => opMul (errM P ρ i) g s x) J k
      ≤ ENNReal.ofReal ((∑ i ∈ Finset.range (k J), a i) ^ 2) *
          ∫⁻ x : ℤ, ‖g x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count :=
    oscZ_of_multiplier_family (m := errM P ρ) (measurable_errM P ρ)
      herr_bound a (fun i => le_of_lt (hapos i)) herr_inc g s hs J k hk
  have hE' : oscZ (fun i x => opMul (errM P ρ i) g s x) J k
      ≤ ENNReal.ofReal (D ^ 2) *
          ∫⁻ x : ℤ, ‖g x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count := by
    refine hE.trans ?_
    refine mul_le_mul_of_nonneg_right ?_ bot_le
    refine ENNReal.ofReal_le_ofReal ?_
    exact pow_le_pow_left₀ (Finset.sum_nonneg (fun i _ => le_of_lt (hapos i)))
      (hSum (Finset.range (k J))) 2
  -- the pointwise decomposition `W = M + E`
  have hsplit : ∀ i x, polyWeylOp P g s (lacScale ρ i) x
      = polyModelOp P g s (lacScale ρ i) x + opMul (errM P ρ i) g s x := by
    intro i x
    exact polyWeylOp_eq_polyModelOp_add P ρ (le_of_lt hρ) g s i x
  have h1 := oscZ_add_le_c hsplit J k
  have h2 := hmod g s hs J k hk
  -- the coefficient bookkeeping
  have hcoef : 4 * ENNReal.ofReal (A ^ 2) + 4 * ENNReal.ofReal (D ^ 2)
      ≤ ENNReal.ofReal ((Real.sqrt (4 * A ^ 2 + 4 * D ^ 2 + 1)) ^ 2) := by
    rw [Real.sq_sqrt (by positivity)]
    have h1 : 4 * ENNReal.ofReal (A ^ 2) = ENNReal.ofReal (4 * A ^ 2) := by
      rw [← ENNReal.ofReal_ofNat (n := 4), ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4)]
    have h2 : 4 * ENNReal.ofReal (D ^ 2) = ENNReal.ofReal (4 * D ^ 2) := by
      rw [← ENNReal.ofReal_ofNat (n := 4), ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4)]
    rw [h1, h2, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  calc oscZ (fun i x => polyWeylOp P g s (lacScale ρ i) x) J k
      ≤ 4 * oscZ (fun i x => polyModelOp P g s (lacScale ρ i) x) J k
          + 4 * oscZ (fun i x => opMul (errM P ρ i) g s x) J k := h1
    _ ≤ 4 * (ENNReal.ofReal (A ^ 2) *
            ∫⁻ x : ℤ, ‖g x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count)
          + 4 * (ENNReal.ofReal (D ^ 2) *
            ∫⁻ x : ℤ, ‖g x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count) :=
        add_le_add (mul_le_mul_of_nonneg_left h2 bot_le)
          (mul_le_mul_of_nonneg_left hE' bot_le)
    _ = (4 * ENNReal.ofReal (A ^ 2) + 4 * ENNReal.ofReal (D ^ 2)) *
            ∫⁻ x : ℤ, ‖g x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count := by ring
    _ ≤ ENNReal.ofReal ((Real.sqrt (4 * A ^ 2 + 4 * D ^ 2 + 1)) ^ 2) *
            ∫⁻ x : ℤ, ‖g x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count :=
        mul_le_mul_of_nonneg_right hcoef bot_le

end

end Work.BourgainPlan.Oscillation
