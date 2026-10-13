import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.Mine.cs_interval_le
import Submission.Work.FTS.EllipticEst.Mine.slice_u_sq_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Mine

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## Elementary facts about the angular weight `sEta θ = sin(2θ)^{-η}`

The weight is `≥ 0` on the slice `Iθ = [0,π/2]`, and `≥ 1` on the open interval `(0,π/2)`
(because `0 < sin(2θ) ≤ 1` and the exponent `-η` is nonpositive). -/

theorem sp_sEta_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.sEta θ := by
  rw [Work.FTS.EllipticEst.sEta]
  apply Real.rpow_nonneg
  apply Real.sin_nonneg_of_nonneg_of_le_pi (x := 2 * θ) (by linarith [hθ.1])
  linarith [hθ.2, Real.pi_pos]

theorem sp_one_le_sEta {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    1 ≤ Work.FTS.EllipticEst.sEta θ := by
  have hpos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hle1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have h := Real.rpow_le_rpow_of_exponent_ge hpos hle1
    (show -(Work.Spaces.eta) ≤ (0 : ℝ) by have := Work.Spaces.eta_pos; linarith)
  simpa [Work.FTS.EllipticEst.sEta, Real.rpow_zero] using h

/-! ## The derivative Poincaré inequality

This is the main step: a function `u` of class `C²` on `(0,π/2)`, continuous on `[0,π/2]`,
vanishing at both endpoints, satisfies `∫ (u')² ≤ (π/2)² ∫ (u'')² σ`.

The proof is the *two-point* (Rolle) form of the Hardy/Poincaré argument: Rolle gives an
interior point `θ₀` with `u'(θ₀) = 0`; the fundamental theorem of calculus on the interior
interval between `θ₀` and `θ` gives `u'(θ) = ∫_{θ₀}^{θ} u''`, and Cauchy–Schwarz against the
weight `σ^{-1} = sin(2θ)^{η} ≤ 1` bounds the last integral by `(π/2) ∫ (u'')² σ` uniformly in
`θ`.  Integrating the resulting *pointwise* bound over `(0,π/2)` (a set of measure `π/2`)
gives the claim. -/

theorem slice_deriv_sq_le {u : ℝ → ℝ}
    (hC : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hcont : ContinuousOn u (Set.Icc 0 (Real.pi / 2)))
    (h0 : u 0 = 0) (hpi : u (Real.pi / 2) = 0)
    (hint : MeasureTheory.IntegrableOn
      (fun θ => (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
        ≤ (Real.pi / 2) ^ 2 *
          (∫ θ in Work.Spaces.Iθ,
            (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
  set R : ℝ := ∫ θ in Work.Spaces.Iθ,
    (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ with hRdef
  have hpi2 : (0 : ℝ) < Real.pi / 2 := by positivity
  -- ## continuity of the two derivatives on the open interval
  have hdC1 : ContDiffOn ℝ 1 (deriv u) (Set.Ioo 0 (Real.pi / 2)) :=
    hC.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hcont_d : ContinuousOn (deriv u) (Set.Ioo 0 (Real.pi / 2)) :=
    hC.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hcont_g : ContinuousOn (deriv (deriv u)) (Set.Ioo 0 (Real.pi / 2)) :=
    hdC1.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hderiv_has : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (deriv u) (deriv (deriv u) x) x := by
    intro x hx
    exact (((hdC1.differentiableOn (by norm_num)).differentiableAt
      (Ioo_mem_nhds hx.1 hx.2))).hasDerivAt
  -- ## `R ≥ 0`: the integrand is a product of nonnegative factors on `Iθ`
  have hRnn : 0 ≤ R := by
    rw [hRdef]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc fun θ hθ =>
      mul_nonneg (sq_nonneg _) (sp_sEta_nonneg hθ)
  -- ## Rolle: an interior critical point of `u`
  obtain ⟨θ₀, hθ₀S, hθ₀d⟩ := exists_deriv_eq_zero hpi2 hcont (by rw [h0, hpi])
  -- ## the intervals between two interior points are contained in `(0,π/2)`
  have hsub : ∀ ⦃a b : ℝ⦄, a ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      b ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) → Set.Icc a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    fun a b ha hb x hx =>
      ⟨lt_of_lt_of_le ha.1 hx.1, lt_of_le_of_lt hx.2 hb.2⟩
  have hsubIoo : ∀ ⦃a b : ℝ⦄, a ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      b ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      Set.Ioo a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    fun a b ha hb x hx => ⟨lt_trans ha.1 hx.1, lt_trans hx.2 hb.2⟩
  -- ## the fundamental theorem of calculus on the interior interval between `θ₀` and `θ`
  have hFTC : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      deriv u θ - deriv u θ₀ = ∫ x in θ₀..θ, deriv (deriv u) x := by
    intro θ hθ
    rcases le_total θ₀ θ with hle | hle
    · have hcs : ContinuousOn (deriv u) (Set.Icc θ₀ θ) :=
        hcont_d.mono (hsub hθ₀S hθ)
      have hder : ∀ x ∈ Set.Ioo θ₀ θ, HasDerivAt (deriv u) (deriv (deriv u) x) x :=
        fun x hx => hderiv_has x (hsubIoo hθ₀S hθ hx)
      have hi : IntervalIntegrable (deriv (deriv u)) volume θ₀ θ :=
        (hcont_g.mono (hsub hθ₀S hθ)).intervalIntegrable_of_Icc hle
      exact (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle hcs hder hi).symm
    · have hcs : ContinuousOn (deriv u) (Set.Icc θ θ₀) :=
        hcont_d.mono (hsub hθ hθ₀S)
      have hder : ∀ x ∈ Set.Ioo θ θ₀, HasDerivAt (deriv u) (deriv (deriv u) x) x :=
        fun x hx => hderiv_has x (hsubIoo hθ hθ₀S hx)
      have hi : IntervalIntegrable (deriv (deriv u)) volume θ θ₀ :=
        (hcont_g.mono (hsub hθ hθ₀S)).intervalIntegrable_of_Icc hle
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle hcs hder hi
      rw [intervalIntegral.integral_symm θ θ₀, h]
      ring
  -- ## the pointwise bound `(u' θ)² ≤ (π/2) · R`
  have hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (deriv u θ) ^ 2 ≤ (Real.pi / 2) * R := by
    intro θ hθ
    have h1 : deriv u θ - deriv u θ₀ = ∫ x in θ₀..θ, deriv (deriv u) x := hFTC θ hθ
    have h2 : (deriv u θ) ^ 2 = (∫ x in θ₀..θ, deriv (deriv u) x) ^ 2 := by
      rw [← h1, hθ₀d]; ring
    have ha : 0 ≤ min θ₀ θ := le_min (le_of_lt hθ₀S.1) (le_of_lt hθ.1)
    have hb : max θ₀ θ ≤ Real.pi / 2 := max_le (le_of_lt hθ₀S.2) (le_of_lt hθ.2)
    have hab : min θ₀ θ ≤ max θ₀ θ := min_le_max
    have hcs := cs_interval_le hcont_g hint (a := min θ₀ θ)
      (b := max θ₀ θ) ha hb hab
    rw [h2, hRdef]
    rcases le_total θ₀ θ with hle | hle
    · rwa [min_eq_left hle, max_eq_right hle] at hcs
    · rw [min_eq_right hle, max_eq_left hle] at hcs
      rw [intervalIntegral.integral_symm θ θ₀, neg_sq]
      exact hcs
  -- ## integrability on the open interval `(0,π/2)` (finite measure, bounded integrand)
  have hvolS : (volume : Measure ℝ).real (Set.Ioo (0 : ℝ) (Real.pi / 2)) = Real.pi / 2 := by
    rw [MeasureTheory.measureReal_def, Real.volume_Ioo, sub_zero,
      ENNReal.toReal_ofReal (by positivity)]
  have hint_fin : IsFiniteMeasure (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioo]; exact ENNReal.ofReal_lt_top⟩
  have hmeas : AEStronglyMeasurable (fun θ => (deriv u θ) ^ 2)
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    (hcont_d.aestronglyMeasurable isOpen_Ioo.measurableSet).pow 2
  have hptS : ∀ᵐ θ ∂(volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))),
      (deriv u θ) ^ 2 ≤ (Real.pi / 2) * R :=
    (ae_restrict_iff' isOpen_Ioo.measurableSet).mpr (Eventually.of_forall hpt)
  have hIntS : IntegrableOn (fun θ => (deriv u θ) ^ 2) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (integrable_const ((Real.pi / 2) * R)).mono' hmeas
      (hptS.mono fun θ hθ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hθ)
  -- ## transfer to `Iθ = [0,π/2]`, which differs from `(0,π/2)` by a null set
  have hpairab : ∀ᵐ x : ℝ, x ∉ ({(0 : ℝ), Real.pi / 2} : Set ℝ) := by
    rw [MeasureTheory.ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using
      Set.Finite.measure_zero (by simp) MeasureTheory.volume
  have haeeq : Work.Spaces.Iθ =ᵐ[MeasureTheory.volume]
      Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    filter_upwards [hpairab] with x hx
    refine propext ⟨?_, ?_⟩
    · intro h
      rw [Work.Spaces.Iθ, Set.mem_Icc] at h
      rw [Set.mem_Ioo]
      exact ⟨lt_of_le_of_ne h.1 (fun hc => hx (Or.inl hc.symm)),
             lt_of_le_of_ne h.2 (fun hc => hx (Or.inr hc))⟩
    · intro h
      rw [Work.Spaces.Iθ, Set.mem_Icc]
      rw [Set.mem_Ioo] at h
      exact ⟨le_of_lt h.1, le_of_lt h.2⟩
  refine ⟨hIntS.congr_set_ae haeeq, ?_⟩
  have hmono : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (deriv u θ) ^ 2)
      ≤ ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ((Real.pi / 2) * R) :=
    integral_mono_ae hIntS (integrable_const _) hptS
  calc (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
      = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (deriv u θ) ^ 2 :=
        MeasureTheory.setIntegral_congr_set haeeq
    _ ≤ ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ((Real.pi / 2) * R) := hmono
    _ = (Real.pi / 2) * ((Real.pi / 2) * R) := by
        rw [MeasureTheory.setIntegral_const, hvolS]
        simp
    _ = (Real.pi / 2) ^ 2 * R := by ring

theorem SlicePoincare : ∃ K : ℝ, 0 < K ∧ ∀ u : ℝ → ℝ,
    ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)) →
    ContinuousOn u (Set.Icc 0 (Real.pi / 2)) →
    u 0 = 0 → u (Real.pi / 2) = 0 →
    MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2 *
      Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ ∧
    MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ ∧
    (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
      ≤ K * (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) ∧
    (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)
      ≤ K * (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
  refine ⟨(Real.pi / 2) ^ 4, by positivity, fun u hC hcont h0 hpi hint => ?_⟩
  obtain ⟨hInt1, hb1⟩ := slice_deriv_sq_le hC hcont h0 hpi hint
  obtain ⟨hInt2, hb2⟩ := slice_u_sq_le hC hcont h0 hInt1
  -- `R ≥ 0` for the integral against `sEta`
  have hRnn : 0 ≤ ∫ θ in Work.Spaces.Iθ,
      (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc fun θ hθ =>
      mul_nonneg (sq_nonneg _) (sp_sEta_nonneg hθ)
  refine ⟨hInt1, hInt2, ?_, ?_⟩
  · calc (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
        ≤ (Real.pi / 2) ^ 2 *
            (∫ θ in Work.Spaces.Iθ,
              (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := hb1
      _ ≤ (Real.pi / 2) ^ 4 *
            (∫ θ in Work.Spaces.Iθ,
              (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
          apply mul_le_mul_of_nonneg_right _ hRnn
          nlinarith [Real.pi_gt_three, sq_nonneg ((Real.pi / 2) ^ 2 - 1)]
  · calc (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)
        ≤ (Real.pi / 2) ^ 2 * (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2) := hb2
      _ ≤ (Real.pi / 2) ^ 2 * ((Real.pi / 2) ^ 2 *
            (∫ θ in Work.Spaces.Iθ,
              (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) :=
          mul_le_mul_of_nonneg_left hb1 (by positivity)
      _ = (Real.pi / 2) ^ 4 *
            (∫ θ in Work.Spaces.Iθ,
              (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by ring

end Work.FTS.EllipticEst.Mine
