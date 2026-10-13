/-
# `Assembly/AnsatzAsymB.lean` — the angular asymptotics of the counterexample, part 2

The lower bound on the *difference* of the two `i = 1` slots:

`Sc (hA δ) 1 η - Sc (hA δ) 1 γ ≥ C₁/δ`,

obtained from `D_θ h_δ = sin(2θ)·χ'((·-θ₀)/δ)/δ`:

* on the sub-interval `[θ₀+δ, θ₀+2δ]` the factor `sin(2θ)² ≥ sin(1)²` is bounded below, and
  the substitution `θ = θ₀ + δu` turns the integral of `(χ')²` into `δ·∫_1^2 (χ')² ≥ δ`,
* the weight gap `sin(2θ)^{-η} - sin(2θ)^{-γ}` is bounded below by its value at `sin(3/2)`
  on the whole support (by `rpow_sub_mono`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.CoercivityFix.Assembly.AnsatzAsym

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Assembly

set_option autoImplicit false

/-! ## Two elementary conversions -/

theorem setIntegral_Icc_eq_intervalIntegral {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) :
    (∫ x in Set.Icc a b, f x) = ∫ x in a..b, f x := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]

theorem sub_Icc_subset_Iθ (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 8) :
    Set.Icc (th0 + δ) (th0 + 2 * δ) ⊆ Work.Spaces.Iθ := by
  intro θ hθ
  rw [Set.mem_Icc] at hθ
  rw [Work.Spaces.Iθ, Set.mem_Icc]
  rw [th0] at hθ
  constructor
  · linarith [hθ.1]
  · have := Real.pi_gt_three; linarith [hθ.2]

/-! ## The chain rule for `hA` -/

theorem deriv_hA (δ θ : ℝ) :
    deriv (hA δ) θ = deriv Work.Stability.chi ((θ - th0) / δ) / δ := by
  have h1 : HasDerivAt (fun θ' : ℝ => (θ' - th0) / δ) (1 / δ) θ := by
    simpa using ((hasDerivAt_id θ).sub_const th0).div_const δ
  have h2 : HasDerivAt Work.Stability.chi
      (deriv Work.Stability.chi ((θ - th0) / δ)) ((θ - th0) / δ) :=
    (differentiableAt_chi _).hasDerivAt
  have h3 := h2.comp θ h1
  have h4 : deriv (hA δ) θ = deriv Work.Stability.chi ((θ - th0) / δ) * (1 / δ) := h3.deriv
  rw [h4]
  exact mul_one_div _ _

/-! ## The lower bound `sin(1)²/δ ≤ ∫ (D_θ hA δ)²` -/

theorem deriv_sq_integral_lower (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 8) :
    Real.sin 1 ^ 2 / δ ≤ ∫ θ in Work.Spaces.Iθ, (vthIter 1 (hA δ) θ) ^ 2 := by
  have hδ2 : (0 : ℝ) < δ ^ 2 := by positivity
  have hab : th0 + δ ≤ th0 + 2 * δ := by linarith
  -- the pointwise lower bound on the sub-interval
  have hD : ∀ θ ∈ Set.Icc (th0 + δ) (th0 + 2 * δ),
      Real.sin 1 ^ 2 * (deriv Work.Stability.chi ((θ - th0) / δ)) ^ 2 / δ ^ 2
        ≤ (vthIter 1 (hA δ) θ) ^ 2 := by
    intro θ hθ
    rw [Set.mem_Icc] at hθ
    rw [th0] at hθ
    have hsin : Real.sin 1 ≤ Real.sin (2 * θ) := by
      refine Real.sin_le_sin_of_le_of_le_pi_div_two (by
        have := Real.pi_pos; linarith) ?_ (by linarith [hθ.1])
      have := Real.pi_gt_three
      linarith [hθ.2]
    have hs2 : Real.sin 1 ^ 2 ≤ (Real.sin (2 * θ)) ^ 2 := by
      nlinarith [sin_one_pos, hsin]
    have hd2 : 0 ≤ (deriv Work.Stability.chi ((θ - th0) / δ)) ^ 2 / δ ^ 2 := by positivity
    rw [vthIter_succ, vthIter_zero, vth, deriv_hA]
    calc Real.sin 1 ^ 2 * (deriv Work.Stability.chi ((θ - th0) / δ)) ^ 2 / δ ^ 2
        = Real.sin 1 ^ 2 * ((deriv Work.Stability.chi ((θ - th0) / δ)) ^ 2 / δ ^ 2) := by ring
      _ ≤ (Real.sin (2 * θ)) ^ 2 * ((deriv Work.Stability.chi ((θ - th0) / δ)) ^ 2 / δ ^ 2) :=
          mul_le_mul_of_nonneg_right hs2 hd2
      _ = (Real.sin (2 * θ) * (deriv Work.Stability.chi ((θ - th0) / δ) / δ)) ^ 2 := by ring
  -- integrability on the sub-interval
  have hcInt : Continuous
      (fun θ : ℝ => Real.sin 1 ^ 2 * (deriv Work.Stability.chi ((θ - th0) / δ)) ^ 2 / δ ^ 2) :=
    ((continuous_const.mul (((continuous_deriv_chi.comp
      ((continuous_id.sub continuous_const).div_const δ)).pow 2)))).div_const (δ ^ 2)
  have hcIntB : Continuous (fun θ : ℝ => (vthIter 1 (hA δ) θ) ^ 2) :=
    ((contDiff_vthIter_hA δ 1).continuous).pow 2
  have hintA : IntervalIntegrable
      (fun θ : ℝ => Real.sin 1 ^ 2 * (deriv Work.Stability.chi ((θ - th0) / δ)) ^ 2 / δ ^ 2)
      volume (th0 + δ) (th0 + 2 * δ) := hcInt.intervalIntegrable _ _
  have hintB : IntervalIntegrable (fun θ : ℝ => (vthIter 1 (hA δ) θ) ^ 2)
      volume (th0 + δ) (th0 + 2 * δ) := hcIntB.intervalIntegrable _ _
  -- the substitution `θ = θ₀ + δu`
  have hfun : (fun θ : ℝ => (deriv Work.Stability.chi ((θ - th0) / δ)) ^ 2)
      = fun θ : ℝ => (deriv Work.Stability.chi ((1 / δ) * θ + (-(th0) / δ))) ^ 2 := by
    funext θ
    congr 1
    ring_nf
  have hsub : (∫ θ in (th0 + δ)..(th0 + 2 * δ),
        (deriv Work.Stability.chi ((θ - th0) / δ)) ^ 2)
      = δ * ∫ u in (1 : ℝ)..2, (deriv Work.Stability.chi u) ^ 2 := by
    rw [hfun, intervalIntegral.integral_comp_mul_add
      (f := fun u : ℝ => (deriv Work.Stability.chi u) ^ 2)
      (ne_of_gt (by positivity : (0 : ℝ) < 1 / δ)) (-(th0) / δ)]
    have h1 : (1 / δ) * (th0 + δ) + -(th0) / δ = 1 := by
      field_simp; ring
    have h2 : (1 / δ) * (th0 + 2 * δ) + -(th0) / δ = 2 := by
      field_simp; ring
    rw [h1, h2, smul_eq_mul, one_div, inv_inv]
  -- the value of the lower-bound integral on the sub-interval
  have hval : (∫ θ in (th0 + δ)..(th0 + 2 * δ),
        Real.sin 1 ^ 2 * (deriv Work.Stability.chi ((θ - th0) / δ)) ^ 2 / δ ^ 2)
      = Real.sin 1 ^ 2 / δ ^ 2 * (δ * ∫ u in (1 : ℝ)..2, (deriv Work.Stability.chi u) ^ 2) := by
    have hfun2 : (fun θ : ℝ => Real.sin 1 ^ 2 * (deriv Work.Stability.chi ((θ - th0) / δ)) ^ 2 / δ ^ 2)
        = fun θ : ℝ => (Real.sin 1 ^ 2 / δ ^ 2)
            * (deriv Work.Stability.chi ((θ - th0) / δ)) ^ 2 := by
      funext θ
      ring
    rw [hfun2, intervalIntegral.integral_const_mul, hsub]
  -- assemble
  have hstep1 : Real.sin 1 ^ 2 / δ
      ≤ ∫ θ in (th0 + δ)..(th0 + 2 * δ),
          Real.sin 1 ^ 2 * (deriv Work.Stability.chi ((θ - th0) / δ)) ^ 2 / δ ^ 2 := by
    rw [hval]
    have hK := one_le_integral_deriv_chi_sq
    have hpos : 0 < Real.sin 1 ^ 2 / δ ^ 2 := div_pos (pow_pos sin_one_pos 2) hδ2
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hK (le_of_lt hδ0))
      (le_of_lt hpos)
    calc Real.sin 1 ^ 2 / δ
        = Real.sin 1 ^ 2 / δ ^ 2 * (δ * 1) := by field_simp
      _ ≤ Real.sin 1 ^ 2 / δ ^ 2
            * (δ * ∫ u in (1 : ℝ)..2, (deriv Work.Stability.chi u) ^ 2) := this
  have hstep2 : (∫ θ in (th0 + δ)..(th0 + 2 * δ),
        Real.sin 1 ^ 2 * (deriv Work.Stability.chi ((θ - th0) / δ)) ^ 2 / δ ^ 2)
      ≤ ∫ θ in (th0 + δ)..(th0 + 2 * δ), (vthIter 1 (hA δ) θ) ^ 2 :=
    intervalIntegral.integral_mono_on hab hintA hintB (fun θ hθ => hD θ hθ)
  have hstep3 : (∫ θ in (th0 + δ)..(th0 + 2 * δ), (vthIter 1 (hA δ) θ) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, (vthIter 1 (hA δ) θ) ^ 2 := by
    rw [← setIntegral_Icc_eq_intervalIntegral hab]
    have hIntdh : IntegrableOn (fun θ => (vthIter 1 (hA δ) θ) ^ 2) Work.Spaces.Iθ := by
      have h := integrableOn_vthIter_sq δ hδ0 hδ1 1 (0 : ℝ)
      simpa using h
    refine MeasureTheory.setIntegral_mono_set hIntdh
      (Filter.Eventually.of_forall fun θ => sq_nonneg _)
      (Filter.Eventually.of_forall fun θ hθ => sub_Icc_subset_Iθ δ hδ0 hδ1 hθ)
  linarith [hstep1, hstep2, hstep3]

/-! ## The lower bound on the difference of the two `i = 1` slots -/

theorem Sc_diff_bound (α : ℝ) (hα : α < -(1 / 10 : ℝ))
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 8) :
    (Real.sin (3 / 2 : ℝ) ^ (-(Work.Spaces.eta))
        - Real.sin (3 / 2 : ℝ) ^ (-(Work.Spaces.gam α))) * Real.sin 1 ^ 2 / δ
      ≤ Sc (hA δ) 1 Work.Spaces.eta - Sc (hA δ) 1 (Work.Spaces.gam α) := by
  set c₀ : ℝ := Real.sin (3 / 2 : ℝ) ^ (-(Work.Spaces.eta))
    - Real.sin (3 / 2 : ℝ) ^ (-(Work.Spaces.gam α)) with hc₀
  have hc₀pos : 0 < c₀ := gap_pos α hα
  have hγη : Work.Spaces.gam α ≤ Work.Spaces.eta := le_of_lt (by
    rw [Work.Spaces.gam, Work.Spaces.eta]; linarith)
  -- integrability
  have hIntη : IntegrableOn (fun θ => (vthIter 1 (hA δ) θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ :=
    integrableOn_vthIter_sq δ hδ0 hδ1 1 Work.Spaces.eta
  have hIntγ : IntegrableOn (fun θ => (vthIter 1 (hA δ) θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ :=
    integrableOn_vthIter_sq δ hδ0 hδ1 1 (Work.Spaces.gam α)
  have hIntsq : IntegrableOn (fun θ => (vthIter 1 (hA δ) θ) ^ 2) Work.Spaces.Iθ := by
    have h := integrableOn_vthIter_sq δ hδ0 hδ1 1 (0 : ℝ)
    simpa using h
  have hIntd : IntegrableOn (fun θ => (vthIter 1 (hA δ) θ) ^ 2
      * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        - (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) Work.Spaces.Iθ :=
    (hIntη.sub hIntγ).congr (Filter.Eventually.of_forall fun θ => by
      simp only [Pi.sub_apply]; ring)
  -- the pointwise bound
  have hpt : ∀ θ, (vthIter 1 (hA δ) θ) ^ 2 * c₀
      ≤ (vthIter 1 (hA δ) θ) ^ 2
        * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          - (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
    intro θ
    by_cases hθJ : θ ∈ acidJ
    · have hb : c₀ ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          - (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
        rw [hc₀]
        exact rpow_sub_mono (sin_two_pos hθJ) (sin_two_bounds hθJ).2
          (le_of_lt sin_three_halves_lt_one) hγη Work.Spaces.eta_pos
      exact mul_le_mul_of_nonneg_left hb (sq_nonneg _)
    · have h0 : vthIter 1 (hA δ) θ = 0 :=
        vthIter_hA_eq_zero hδ0 (i := 1) (fun h => hθJ (mem_acidJ_of_mem_Icc δ hδ1 h))
      rw [h0]
      simp
  -- the identity for the difference of the two slots
  have hEq : Sc (hA δ) 1 Work.Spaces.eta - Sc (hA δ) 1 (Work.Spaces.gam α)
      = ∫ θ in Work.Spaces.Iθ, (vthIter 1 (hA δ) θ) ^ 2
        * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          - (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
    rw [Sc, Sc, ← MeasureTheory.integral_sub hIntη hIntγ]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
    ring
  rw [hEq]
  have hbound := MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun θ => mul_nonneg (sq_nonneg _) (le_of_lt hc₀pos))
    hIntd (Filter.Eventually.of_forall hpt)
  have hval : (∫ θ in Work.Spaces.Iθ, (vthIter 1 (hA δ) θ) ^ 2 * c₀)
      = c₀ * ∫ θ in Work.Spaces.Iθ, (vthIter 1 (hA δ) θ) ^ 2 := by
    rw [MeasureTheory.integral_mul_const, mul_comm]
  have hlow := deriv_sq_integral_lower δ hδ0 hδ1
  calc c₀ * Real.sin 1 ^ 2 / δ = c₀ * (Real.sin 1 ^ 2 / δ) := by ring
    _ ≤ c₀ * ∫ θ in Work.Spaces.Iθ, (vthIter 1 (hA δ) θ) ^ 2 :=
        mul_le_mul_of_nonneg_left hlow (le_of_lt hc₀pos)
    _ = ∫ θ in Work.Spaces.Iθ, (vthIter 1 (hA δ) θ) ^ 2 * c₀ := by rw [hval]
    _ ≤ ∫ θ in Work.Spaces.Iθ, (vthIter 1 (hA δ) θ) ^ 2
          * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            - (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := hbound

/-! ## The two asymptotics -/

/-- **The angular asymptotics of the counterexample.** -/
theorem thBounds (α : ℝ) (hα : α < -(1 / 10 : ℝ)) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 8 →
        Sc (hA δ) 0 Work.Spaces.eta ≤ C₂ * δ ∧
        C₁ / δ ≤ Sc (hA δ) 1 Work.Spaces.eta - Sc (hA δ) 1 (Work.Spaces.gam α) := by
  refine ⟨(Real.sin (3 / 2 : ℝ) ^ (-(Work.Spaces.eta))
      - Real.sin (3 / 2 : ℝ) ^ (-(Work.Spaces.gam α))) * Real.sin 1 ^ 2,
    4 * Real.sin (1 / 2 : ℝ) ^ (-(Work.Spaces.eta)), ?_, ?_, ?_⟩
  · exact mul_pos (gap_pos α hα) (pow_pos sin_one_pos 2)
  · exact mul_pos (by norm_num) (Real.rpow_pos_of_pos sin_half_pos _)
  · intro δ hδ0 hδ1
    exact ⟨Sc_zero_bound δ hδ0 hδ1, Sc_diff_bound α hα δ hδ0 hδ1⟩

end Work.FTS.CoercivityFix.Assembly
