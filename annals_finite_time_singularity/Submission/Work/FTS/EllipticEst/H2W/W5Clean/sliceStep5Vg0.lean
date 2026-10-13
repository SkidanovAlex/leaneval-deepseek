import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.remov.slice5_rel
import Submission.Work.FTS.EllipticEst.remov.slice5_eqn_deriv2
import Submission.Work.FTS.EllipticEst.remov.slice5_idents
import Submission.Work.FTS.EllipticEst.H2W.AngBW.Local.slice5_vweight_le
import Submission.Work.FTS.EllipticEst.remov.slice5_reduce

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W

open scoped Real Topology Interval
open MeasureTheory Set Filter

set_option autoImplicit false

/-- The pointwise bound on `(0, π/2)`. -/
private lemma g_sq_mul_le (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) {u g : ℝ → ℝ}
    (hu4 : ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2)))
    (hode : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ)
      ≤ 4 * ((deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        + 68 * (u θ) ^ 2
        + 4 * ((deriv (fun θ' => u θ' / Real.cos θ') θ) ^ 2 *
            Real.rpow (Real.sin (2 * θ)) (4 - γ)) := by
  have hθI : θ ∈ Work.Spaces.Iθ :=
    ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  -- the two ODE identities in `v`-form
  have hId := (Work.FTS.EllipticEst.remov.slice5_idents u g hu4 hode).1 θ hθ
  have hCV2 := Work.FTS.EllipticEst.remov.slice5_v_CV2 u g hu4 hode θ hθ
  have hodeθ := hode θ hθ
  have hg : g θ = -(deriv (deriv u) θ) - u θ
      + Real.sin θ * deriv (fun θ' => u θ' / Real.cos θ') θ
      - 4 * Real.cos θ * (u θ / Real.cos θ) := by
    linear_combination -hodeθ + hId - hCV2
  have hcos : Real.cos θ ≠ 0 :=
    (Work.FTS.EllipticEst.remov.cos_pos_of_mem_Ioo hθ).ne'
  -- the weight bounds
  have hψnn : 0 ≤ Real.rpow (Real.sin (2 * θ)) (4 - γ) :=
    Work.FTS.EllipticEst.remov.sig4_nonneg_R γ hθI
  have hψ_le_one : Real.rpow (Real.sin (2 * θ)) (4 - γ) ≤ 1 := by
    have hs := Work.FTS.EllipticEst.remov.sin_two_nonneg_R hθI
    exact Real.rpow_le_one hs (Real.sin_le_one _) (by linarith)
  have hψ_le_sEta : Real.rpow (Real.sin (2 * θ)) (4 - γ)
      ≤ Work.FTS.EllipticEst.sEta θ :=
    Work.FTS.EllipticEst.remov.sig4_le_sEta_R γ hγ1 hγ2 hθI
  have hS2 : Real.sin θ ^ 2 ≤ 1 := Real.sin_sq_le_one θ
  have hC2V0 : Real.cos θ ^ 2 * (u θ / Real.cos θ) ^ 2 = (u θ) ^ 2 := by
    field_simp
  -- the square bound
  have hsq : (g θ) ^ 2 ≤ 4 * ((deriv (deriv u) θ) ^ 2 + 17 * (u θ) ^ 2
      + (Real.sin θ * deriv (fun θ' => u θ' / Real.cos θ') θ) ^ 2) := by
    have h4 := Work.FTS.EllipticEst.remov.add_sq_le_four (-(deriv (deriv u) θ)) (-(u θ))
      (Real.sin θ * deriv (fun θ' => u θ' / Real.cos θ') θ)
      (-((4 * Real.cos θ) * (u θ / Real.cos θ)))
    calc (g θ) ^ 2
        = ((-(deriv (deriv u) θ)) + (-(u θ))
            + (Real.sin θ * deriv (fun θ' => u θ' / Real.cos θ') θ)
            + (-((4 * Real.cos θ) * (u θ / Real.cos θ)))) ^ 2 := by
          rw [hg]; ring
      _ ≤ 4 * ((-(deriv (deriv u) θ)) ^ 2 + (-(u θ)) ^ 2
            + (Real.sin θ * deriv (fun θ' => u θ' / Real.cos θ') θ) ^ 2
            + (-((4 * Real.cos θ) * (u θ / Real.cos θ))) ^ 2) := h4
      _ = 4 * ((deriv (deriv u) θ) ^ 2 + (u θ) ^ 2
            + (Real.sin θ * deriv (fun θ' => u θ' / Real.cos θ') θ) ^ 2
            + 16 * (Real.cos θ ^ 2 * (u θ / Real.cos θ) ^ 2)) := by ring
      _ = 4 * ((deriv (deriv u) θ) ^ 2 + 17 * (u θ) ^ 2
            + (Real.sin θ * deriv (fun θ' => u θ' / Real.cos θ') θ) ^ 2) := by
          rw [hC2V0]; ring
  -- multiply by the weight
  have hstep := mul_le_mul_of_nonneg_right hsq hψnn
  -- and bound the three pieces
  have h1 : (deriv (deriv u) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ)
      ≤ (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
    mul_le_mul_of_nonneg_left hψ_le_sEta (sq_nonneg _)
  have h2 : 17 * (u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ) ≤ 17 * (u θ) ^ 2 := by
    calc 17 * (u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ)
        ≤ 17 * (u θ) ^ 2 * 1 := mul_le_mul_of_nonneg_left hψ_le_one (by positivity)
      _ = 17 * (u θ) ^ 2 := by ring
  have h3 : (Real.sin θ * deriv (fun θ' => u θ' / Real.cos θ') θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (4 - γ)
      ≤ 1 * ((deriv (fun θ' => u θ' / Real.cos θ') θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (4 - γ)) := by
    rw [show (Real.sin θ * deriv (fun θ' => u θ' / Real.cos θ') θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (4 - γ)
        = Real.sin θ ^ 2 * ((deriv (fun θ' => u θ' / Real.cos θ') θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (4 - γ)) by ring]
    exact mul_le_mul_of_nonneg_right hS2 (mul_nonneg (sq_nonneg _) hψnn)
  nlinarith [hstep, h1, h2, h3]

theorem sliceStep5Vg0 : ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ) (u g : ℝ → ℝ),
    1 ≤ γ → γ ≤ 3 / 2 →
    ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2)) →
    ContinuousOn u (Set.Icc 0 (Real.pi / 2)) →
    u 0 = 0 → u (Real.pi / 2) = 0 →
    (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ) →
    MeasureTheory.IntegrableOn (fun θ => (deriv (deriv (deriv (deriv u))) θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (4 - γ)) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ => (deriv (deriv (deriv u)) θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2 *
      Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ => (deriv (deriv g) θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (4 - γ)) Work.Spaces.Iθ →
    (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ))
      ≤ C * ((∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ))
          + (∫ θ in Work.Spaces.Iθ, (deriv (deriv (deriv u)) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (2 - γ))
          + (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 *
              Work.FTS.EllipticEst.sEta θ)
          + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
          + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)) := by
  -- The constant is fixed *before* `γ` is introduced: we use the `v`-bound of
  -- `slice5_vweight_le` at the single weight `sin(2θ)^{4 - 3/2} = sin(2θ)^{5/2}`, which
  -- dominates `sin(2θ)^{4-γ}` for every `γ ∈ [1, 3/2]`.
  obtain ⟨Cv, hCvpos, hv⟩ :=
    Work.FTS.EllipticEst.remov.slice5_vweight_le (3 / 2 : ℝ) (by norm_num) (by norm_num)
  refine ⟨max 20000 (4 * Cv + 20000), lt_max_of_lt_left (by norm_num), ?_⟩
  intro γ u g hγ1 hγ2 hu4 hucont hu0 hu1 hode _hI4 _hI3 hI2 hI1 hI0 _hIg2
  have hu2 : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)) := hu4.of_le (by norm_num)
  obtain ⟨_, hFv32_int, _, hFv32_bnd⟩ := hv u hu2 hucont hu0 hu1 hI2 hI1 hI0
  rw [show (4 : ℝ) - 3 / 2 = 5 / 2 by norm_num] at hFv32_int hFv32_bnd
  -- a.e. the point is interior
  have hae : ∀ᵐ θ ∂(volume : Measure ℝ).restrict Work.Spaces.Iθ,
      θ ∈ Set.Ioo 0 (Real.pi / 2) := Work.FTS.EllipticEst.remov.ae_mem_Ioo_Iθ_R
  -- the weight `sin(2θ)^{4-γ}` is dominated by `sin(2θ)^{5/2}`
  have hψ_le32 : ∀ᵐ θ ∂(volume : Measure ℝ).restrict Work.Spaces.Iθ,
      Real.rpow (Real.sin (2 * θ)) (4 - γ) ≤ Real.rpow (Real.sin (2 * θ)) (5 / 2) := by
    filter_upwards [hae] with θ hθ
    have hbpos : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    exact Real.rpow_le_rpow_of_exponent_ge hbpos (Real.sin_le_one _) (by linarith)
  -- integrability of `(v')² ψ`
  have hFv_int : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun θ' => u θ' / Real.cos θ') θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (4 - γ)) Work.Spaces.Iθ := by
    refine MeasureTheory.Integrable.mono
      (g := fun θ => (deriv (fun θ' => u θ' / Real.cos θ') θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (5 / 2)) hFv32_int ?_ ?_
    · exact (MeasureTheory.AEStronglyMeasurable.mul
        ((measurable_deriv (fun θ' => u θ' / Real.cos θ')).pow_const 2).aestronglyMeasurable
        (((Real.continuous_rpow_const (by linarith : (0 : ℝ) ≤ 4 - γ)).measurable.comp
          (Real.continuous_sin.measurable.comp
            (continuous_const.mul continuous_id).measurable))).aestronglyMeasurable)
    · filter_upwards [hae, hψ_le32] with θ hθ hle
      have h0 : 0 ≤ Real.sin (2 * θ) :=
        (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
          (by linarith [hθ.2, Real.pi_pos])).le
      have hw1 : 0 ≤ Real.rpow (Real.sin (2 * θ)) (4 - γ) := Real.rpow_nonneg h0 _
      have hw2 : 0 ≤ Real.rpow (Real.sin (2 * θ)) (5 / 2) := Real.rpow_nonneg h0 _
      have hnn : 0 ≤ (deriv (fun θ' => u θ' / Real.cos θ') θ) ^ 2 := sq_nonneg _
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hnn hw1),
        abs_of_nonneg (mul_nonneg hnn hw2)]
      exact mul_le_mul_of_nonneg_left hle hnn
  -- the same for `(v')² ψ`
  have hpv : (fun θ => (deriv (fun θ' => u θ' / Real.cos θ') θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (4 - γ))
      ≤ᵐ[(volume : Measure ℝ).restrict Work.Spaces.Iθ]
      (fun θ => (deriv (fun θ' => u θ' / Real.cos θ') θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (5 / 2)) := by
    filter_upwards [hψ_le32] with θ hle
    exact mul_le_mul_of_nonneg_left hle (sq_nonneg _)
  -- the bound on `∫ (v')² ψ` (with the fixed constant `Cv`)
  have hWvle : (∫ θ in Work.Spaces.Iθ, (deriv (fun θ' => u θ' / Real.cos θ') θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (4 - γ))
      ≤ Cv * ((∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 *
            Work.FTS.EllipticEst.sEta θ)
          + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
          + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)) := by
    refine le_trans (MeasureTheory.integral_mono_of_nonneg ?_ hFv32_int hpv) hFv32_bnd
    filter_upwards [hae] with θ hθ
    have h0 : 0 ≤ Real.sin (2 * θ) :=
      (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos])).le
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg h0 _)
  -- abbreviations for the five integrals
  set M : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 *
      Work.FTS.EllipticEst.sEta θ with hMdef
  set B : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 with hBdef
  set A : ℝ := ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 with hAdef
  set Wv : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv (fun θ' => u θ' / Real.cos θ') θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (4 - γ) with hWvdef
  set B2 : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (4 - γ) with hB2def
  set A3 : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv (deriv (deriv u)) θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (2 - γ) with hA3def
  have hWvle' : Wv ≤ Cv * (M + B + A) := by
    rw [hWvdef, hMdef, hBdef, hAdef] at hWvle ⊢
    exact hWvle
  -- the dominating function
  have hFint : MeasureTheory.Integrable
      (fun θ => 4 * ((deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        + 68 * (u θ) ^ 2
        + 4 * ((deriv (fun θ' => u θ' / Real.cos θ') θ) ^ 2 *
            Real.rpow (Real.sin (2 * θ)) (4 - γ)))
      ((volume : Measure ℝ).restrict Work.Spaces.Iθ) :=
    ((hI2.const_mul 4).add (hI0.const_mul 68)).add (hFv_int.const_mul 4)
  have hpt : (fun θ => (g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ))
      ≤ᵐ[(volume : Measure ℝ).restrict Work.Spaces.Iθ]
      (fun θ => 4 * ((deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        + 68 * (u θ) ^ 2
        + 4 * ((deriv (fun θ' => u θ' / Real.cos θ') θ) ^ 2 *
            Real.rpow (Real.sin (2 * θ)) (4 - γ))) := by
    filter_upwards [hae] with θ hθ
    exact g_sq_mul_le γ hγ1 hγ2 hu4 hode hθ
  have hnn : 0 ≤ᵐ[(volume : Measure ℝ).restrict Work.Spaces.Iθ]
      (fun θ => (g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ)) := by
    filter_upwards [hae] with θ hθ
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    exact mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.remov.sig4_nonneg_R γ hθI)
  have hmain : (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ))
      ≤ 4 * M + 68 * A + 4 * Wv := by
    have h1 := MeasureTheory.integral_mono_of_nonneg hnn hFint hpt
    have hAi1 : MeasureTheory.Integrable
        (fun θ => 4 * ((deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
        ((volume : Measure ℝ).restrict Work.Spaces.Iθ) := hI2.const_mul 4
    have hAi2 : MeasureTheory.Integrable (fun θ => 68 * (u θ) ^ 2)
        ((volume : Measure ℝ).restrict Work.Spaces.Iθ) := hI0.const_mul 68
    have hAi3 : MeasureTheory.Integrable
        (fun θ => 4 * ((deriv (fun θ' => u θ' / Real.cos θ') θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (4 - γ)))
        ((volume : Measure ℝ).restrict Work.Spaces.Iθ) := hFv_int.const_mul 4
    have hAi12 : MeasureTheory.Integrable
        (fun θ => 4 * ((deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          + 68 * (u θ) ^ 2)
        ((volume : Measure ℝ).restrict Work.Spaces.Iθ) := hAi1.add hAi2
    have h2 : (∫ θ in Work.Spaces.Iθ,
          4 * ((deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          + 68 * (u θ) ^ 2
          + 4 * ((deriv (fun θ' => u θ' / Real.cos θ') θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ))) = 4 * M + 68 * A + 4 * Wv := by
      rw [MeasureTheory.integral_add hAi12 hAi3,
        MeasureTheory.integral_add hAi1 hAi2,
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
        MeasureTheory.integral_const_mul]
    rw [h2] at h1
    exact h1
  -- nonnegativity of the five integrals
  have hM0 : 0 ≤ M := by
    rw [hMdef]
    exact MeasureTheory.setIntegral_nonneg (Work.FTS.EllipticEst.remov.Iθ_measurable_R)
      (fun θ hθ => mul_nonneg (sq_nonneg _)
        (Work.FTS.EllipticEst.remov.sEta_nonneg_Iθ hθ))
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    exact MeasureTheory.setIntegral_nonneg (Work.FTS.EllipticEst.remov.Iθ_measurable_R)
      (fun θ _ => sq_nonneg _)
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    exact MeasureTheory.setIntegral_nonneg (Work.FTS.EllipticEst.remov.Iθ_measurable_R)
      (fun θ _ => sq_nonneg _)
  have hB20 : 0 ≤ B2 := by
    rw [hB2def]
    exact MeasureTheory.setIntegral_nonneg (Work.FTS.EllipticEst.remov.Iθ_measurable_R)
      (fun θ hθ => mul_nonneg (sq_nonneg _)
        (Work.FTS.EllipticEst.remov.sig4_nonneg_R γ hθ))
  have hA30 : 0 ≤ A3 := by
    rw [hA3def]
    exact MeasureTheory.setIntegral_nonneg (Work.FTS.EllipticEst.remov.Iθ_measurable_R)
      (fun θ hθ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg
        (Work.FTS.EllipticEst.remov.sin_two_nonneg_R hθ) _))
  have hmax : (4 * Cv + 20000) ≤ max 20000 (4 * Cv + 20000) := le_max_right _ _
  have hsum : 0 ≤ B2 + A3 + M + B + A := by linarith
  calc (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ))
      ≤ 4 * M + 68 * A + 4 * Wv := hmain
    _ ≤ 4 * M + 68 * A + 4 * (Cv * (M + B + A)) := by linarith
    _ ≤ max 20000 (4 * Cv + 20000) * (B2 + A3 + M + B + A) := by
        nlinarith [hmax, hCvpos, hM0, hB0, hA0, hB20, hA30, hsum]

end Work.FTS.EllipticEst.H2W
