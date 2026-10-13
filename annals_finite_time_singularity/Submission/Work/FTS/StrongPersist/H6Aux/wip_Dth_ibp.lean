import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.Coercivity.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongPersist.H6Aux.hasDerivAt_ibpPrim
import Submission.Work.FTS.StrongPersist.H6Aux.tendsto_sin_mul_zero_of_integrable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Aux

set_option autoImplicit false
set_option linter.unusedVariables false

/-- `sin(2θ)^{-q}·H²` -/
def IbpU (q : ℝ) (H : ℝ → ℝ) : ℝ → ℝ := fun θ => (Real.sin (2*θ))^(-q) * (H θ)^2

/-- `sin(2θ)·∂_θH·H·sin(2θ)^{-q}` -/
def IbpA (q : ℝ) (H : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => Real.sin (2*θ) * deriv H θ * H θ * (Real.sin (2*θ))^(-q)

/-- `cos(2θ)·sin(2θ)^{-q}·H²` -/
def IbpE (q : ℝ) (H : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => Real.cos (2*θ) * (Real.sin (2*θ))^(-q) * (H θ)^2

theorem slice_ibp_base {q : ℝ} {H : ℝ → ℝ}
    (hH : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2), HasDerivAt H (deriv H θ) θ)
    (hU : MeasureTheory.IntegrableOn (IbpU q H) Work.Spaces.Iθ)
    (hA : MeasureTheory.IntegrableOn (IbpA q H) Work.Spaces.Iθ)
    (hE : MeasureTheory.IntegrableOn (IbpE q H) Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, IbpA q H θ) = (q-1) * (∫ θ in Work.Spaces.Iθ, IbpE q H θ) := by
  have hpi : (0:ℝ) < Real.pi/2 := by positivity
  set v' : ℝ → ℝ := fun θ => 2 * IbpA q H θ - 2*(q-1) * IbpE q H θ
  have hderiv : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2),
      HasDerivAt (fun θ' => Real.sin (2*θ') * ((Real.sin (2*θ'))^(-q) * (H θ')^2))
        (v' θ) θ := by
    intro θ hθ
    have h1 := hasDerivAt_ibpPrim (q := q) hH θ hθ
    simpa only [v', IbpA, IbpE] using h1
  have hu_nonneg : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2), 0 ≤ IbpU q H θ := by
    intro θ hθ
    have hs : 0 < Real.sin (2*θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    exact mul_nonneg (Real.rpow_nonneg hs.le _) (sq_nonneg _)
  have hv'_int : MeasureTheory.IntegrableOn v' Work.Spaces.Iθ := by
    rw [show v' = fun θ => 2 * IbpA q H θ - 2*(q-1) * IbpE q H θ from rfl]
    exact hA.const_mul 2 |>.sub (hE.const_mul (2*(q-1)))
  have hlim := tendsto_sin_mul_zero_of_integrable hU hu_nonneg hderiv hv'_int
  have hInt : IntervalIntegrable v' volume (0:ℝ) (Real.pi/2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hpi.le).mpr
      (hv'_int.mono_set Set.Ioc_subset_Icc_self)
  have hFTC : (∫ θ in (0:ℝ)..(Real.pi/2), v' θ) = 0 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hpi hderiv hInt hlim.1 hlim.2
    simpa using h
  have hconv : ∀ g : ℝ → ℝ,
      (∫ θ in Work.Spaces.Iθ, g θ) = ∫ θ in (0:ℝ)..(Real.pi/2), g θ := by
    intro g
    rw [show Work.Spaces.Iθ = Set.Icc 0 (Real.pi/2) from rfl,
      MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hpi.le]
  have h0 : (∫ θ in Work.Spaces.Iθ, v' θ) = 0 := by rw [hconv]; exact hFTC
  have hdecomp : (∫ θ in Work.Spaces.Iθ, v' θ)
      = 2 * (∫ θ in Work.Spaces.Iθ, IbpA q H θ)
        - 2*(q-1) * (∫ θ in Work.Spaces.Iθ, IbpE q H θ) := by
    rw [show v' = fun θ => 2 * IbpA q H θ - 2*(q-1) * IbpE q H θ from rfl]
    rw [MeasureTheory.integral_sub (hA.const_mul 2) (hE.const_mul (2*(q-1))),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  rw [hdecomp] at h0
  linarith

theorem slice_ibp_mul {q : ℝ} {H : ℝ → ℝ} (c : ℝ)
    (hH : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2), HasDerivAt H (deriv H θ) θ)
    (hU : MeasureTheory.IntegrableOn (fun θ => IbpU q H θ * c) Work.Spaces.Iθ)
    (hA : MeasureTheory.IntegrableOn (fun θ => IbpA q H θ * c) Work.Spaces.Iθ)
    (hE : MeasureTheory.IntegrableOn (fun θ => IbpE q H θ * c) Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, IbpA q H θ * c) = (q-1) * (∫ θ in Work.Spaces.Iθ, IbpE q H θ * c) := by
  by_cases hc : c = 0
  · simp [hc]
  · have key : ∀ f : ℝ → ℝ, MeasureTheory.IntegrableOn (fun θ => f θ * c) Work.Spaces.Iθ →
        MeasureTheory.IntegrableOn f Work.Spaces.Iθ := by
      intro f hf
      have h1 : MeasureTheory.IntegrableOn (fun θ => c⁻¹ * (f θ * c)) Work.Spaces.Iθ :=
        hf.const_mul c⁻¹
      refine h1.congr_fun (fun θ _ => ?_) measurableSet_Icc
      show c⁻¹ * (f θ * c) = f θ
      rw [mul_comm (f θ) c, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    have hU' := key _ hU
    have hA' := key _ hA
    have hE' := key _ hE
    have hbase := slice_ibp_base hH hU' hA' hE'
    rw [MeasureTheory.integral_mul_const, MeasureTheory.integral_mul_const, hbase]
    ring

set_option maxHeartbeats 1000000 in
theorem wip_Dth_ibp {h : ℝ → ℝ → ℝ} {Φ : ℝ → ℝ} {q : ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen h)
    (hint0 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => h z θ ^ 2 * Φ z * (Real.sin (2 * θ)) ^ (-q)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hint1 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dth h z θ * h z θ * Φ z
        * (Real.sin (2 * θ)) ^ (-q)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hint2 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => h z θ ^ 2 * Φ z * Real.cos (2 * θ)
        * (Real.sin (2 * θ)) ^ (-q)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    Work.Coercivity.wip (fun z θ => Φ z * (Real.sin (2 * θ)) ^ (-q))
        (Work.Spaces.Dth h) h
      = (q - 1) * (∫ z in Work.Spaces.Iz, Φ z * ∫ θ in Work.Spaces.Iθ,
          Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q) * h z θ ^ 2) := by
  have hsliceU : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      MeasureTheory.IntegrableOn (fun θ => IbpU q (fun θ' => h z θ') θ * Φ z)
        Work.Spaces.Iθ := by
    have h0 : MeasureTheory.Integrable
        (Function.uncurry (fun z θ => h z θ ^ 2 * Φ z * (Real.sin (2*θ))^(-q)))
        (volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) := hint0
    have h0' : MeasureTheory.Integrable
        (Function.uncurry (fun z θ => IbpU q (fun θ' => h z θ') θ * Φ z))
        (volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :=
      h0.congr (Eventually.of_forall fun p => by
        simp only [Function.uncurry, IbpU]
        ring)
    have hmeas : (volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :
          MeasureTheory.Measure (ℝ × ℝ))
        = (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) :=
      (MeasureTheory.Measure.prod_restrict (μ := (volume : MeasureTheory.Measure ℝ))
        (ν := (volume : MeasureTheory.Measure ℝ)) Work.Spaces.Iz Work.Spaces.Iθ).symm
    rw [hmeas] at h0'
    simpa only [MeasureTheory.IntegrableOn, Function.uncurry] using h0'.prod_right_ae
  have hsliceA : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      MeasureTheory.IntegrableOn (fun θ => IbpA q (fun θ' => h z θ') θ * Φ z)
        Work.Spaces.Iθ := by
    have h0 : MeasureTheory.Integrable
        (Function.uncurry (fun z θ => Work.Spaces.Dth h z θ * h z θ * Φ z
          * (Real.sin (2*θ))^(-q)))
        (volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) := hint1
    have h0' : MeasureTheory.Integrable
        (Function.uncurry (fun z θ => IbpA q (fun θ' => h z θ') θ * Φ z))
        (volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :=
      h0.congr (Eventually.of_forall fun p => by
        simp only [Function.uncurry, IbpA, Work.Spaces.Dth, Work.Spaces.pth]
        ring)
    have hmeas : (volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :
          MeasureTheory.Measure (ℝ × ℝ))
        = (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) :=
      (MeasureTheory.Measure.prod_restrict (μ := (volume : MeasureTheory.Measure ℝ))
        (ν := (volume : MeasureTheory.Measure ℝ)) Work.Spaces.Iz Work.Spaces.Iθ).symm
    rw [hmeas] at h0'
    simpa only [MeasureTheory.IntegrableOn, Function.uncurry] using h0'.prod_right_ae
  have hsliceE : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      MeasureTheory.IntegrableOn (fun θ => IbpE q (fun θ' => h z θ') θ * Φ z)
        Work.Spaces.Iθ := by
    have h0 : MeasureTheory.Integrable
        (Function.uncurry (fun z θ => h z θ ^ 2 * Φ z * Real.cos (2*θ)
          * (Real.sin (2*θ))^(-q)))
        (volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) := hint2
    have h0' : MeasureTheory.Integrable
        (Function.uncurry (fun z θ => IbpE q (fun θ' => h z θ') θ * Φ z))
        (volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :=
      h0.congr (Eventually.of_forall fun p => by
        simp only [Function.uncurry, IbpE]
        ring)
    have hmeas : (volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :
          MeasureTheory.Measure (ℝ × ℝ))
        = (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) :=
      (MeasureTheory.Measure.prod_restrict (μ := (volume : MeasureTheory.Measure ℝ))
        (ν := (volume : MeasureTheory.Measure ℝ)) Work.Spaces.Iz Work.Spaces.Iθ).symm
    rw [hmeas] at h0'
    simpa only [MeasureTheory.IntegrableOn, Function.uncurry] using h0'.prod_right_ae
  have hzpos : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz), (0:ℝ) < z := by
    have hzeq : volume.restrict Work.Spaces.Iz = volume.restrict (Set.Ioi (0:ℝ)) := by
      apply MeasureTheory.Measure.restrict_congr_set
      rw [MeasureTheory.ae_eq_set]
      have h1 : Work.Spaces.Iz \ Set.Ioi (0:ℝ) = {(0:ℝ)} := by
        ext x
        simp only [Work.Spaces.Iz, Set.mem_sdiff, Set.mem_Ici, Set.mem_Ioi,
          Set.mem_singleton_iff]
        constructor
        · rintro ⟨h1, h2⟩; linarith
        · rintro rfl; exact ⟨le_refl 0, lt_irrefl 0⟩
      constructor
      · rw [h1, measure_singleton]
      · rw [show Work.Spaces.Iz = Set.Ici (0:ℝ) from rfl]
        rw [Set.sdiff_eq_empty.mpr Set.Ioi_subset_Ici_self, measure_empty]
    rw [hzeq]
    exact MeasureTheory.ae_restrict_mem measurableSet_Ioi
  have hkey : (fun z => Φ z * ∫ θ in Work.Spaces.Iθ, IbpA q (fun θ' => h z θ') θ)
      =ᵐ[volume.restrict Work.Spaces.Iz]
      (fun z => Φ z * ((q-1) * ∫ θ in Work.Spaces.Iθ,
        IbpE q (fun θ' => h z θ') θ)) := by
    filter_upwards [hsliceU, hsliceA, hsliceE, hzpos] with z hU hA hE hz
    have hH : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2),
        HasDerivAt (fun θ' => h z θ') (deriv (fun θ' => h z θ') θ) θ := by
      intro θ hθ
      exact (((hsm.curry_θ hz).differentiableOn (by simp)).differentiableAt
        (isOpen_Ioo.mem_nhds hθ)).hasDerivAt
    have hb := slice_ibp_mul (q := q) (H := fun θ' => h z θ') (Φ z) hH hU hA hE
    have e1 : Φ z * (∫ θ in Work.Spaces.Iθ, IbpA q (fun θ' => h z θ') θ)
        = (∫ θ in Work.Spaces.Iθ, IbpA q (fun θ' => h z θ') θ * Φ z) := by
      rw [MeasureTheory.integral_mul_const]; ring
    have e2 : Φ z * (∫ θ in Work.Spaces.Iθ, IbpE q (fun θ' => h z θ') θ)
        = (∫ θ in Work.Spaces.Iθ, IbpE q (fun θ' => h z θ') θ * Φ z) := by
      rw [MeasureTheory.integral_mul_const]; ring
    rw [show Φ z * ((q-1) * (∫ θ in Work.Spaces.Iθ, IbpE q (fun θ' => h z θ') θ))
        = (q-1) * (Φ z * (∫ θ in Work.Spaces.Iθ, IbpE q (fun θ' => h z θ') θ))
        from by ring, e1, e2]
    exact hb
  simp only [Work.Coercivity.wip]
  have hstep1 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.Dth h z θ * h z θ * (Φ z * (Real.sin (2*θ))^(-q)))
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          IbpA q (fun θ' => h z θ') θ * Φ z := by
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun z => ?_)
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun θ => ?_)
    simp only [IbpA, Work.Spaces.Dth, Work.Spaces.pth]
    ring
  rw [hstep1]
  rw [show (fun z => ∫ θ in Work.Spaces.Iθ, IbpA q (fun θ' => h z θ') θ * Φ z)
      = fun z => Φ z * ∫ θ in Work.Spaces.Iθ, IbpA q (fun θ' => h z θ') θ
      from funext fun z => by rw [MeasureTheory.integral_mul_const]; ring]
  rw [MeasureTheory.integral_congr_ae hkey]
  rw [show (fun z => Φ z * ((q-1) * ∫ θ in Work.Spaces.Iθ,
          IbpE q (fun θ' => h z θ') θ))
      = fun z => (q-1) * (Φ z * ∫ θ in Work.Spaces.Iθ, IbpE q (fun θ' => h z θ') θ)
      from funext fun z => by ring,
    MeasureTheory.integral_const_mul]
  rfl

end Work.FTS.StrongPersist.H6Aux
