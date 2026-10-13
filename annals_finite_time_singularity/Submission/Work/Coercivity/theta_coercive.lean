import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Coercivity.thetaAux
import Submission.Work.Coercivity.thetaBoxAux
import Submission.Work.Coercivity.EDth_eq_wip
import Submission.Work.Coercivity.dth_LGammaT_expansion
import Submission.Work.Coercivity.monotone_interval
import Submission.Work.Coercivity.dth_integrands_continuousOn
import Submission.Work.Coercivity.pth_bounds_box
import Submission.Work.Coercivity.dth_slice_z_ibp
import Submission.Work.Coercivity.dth_slice_theta_ibp
import Submission.Work.Coercivity.dth_box_domination
import Submission.Work.Coercivity.dth_bd0_of_IBP
import Submission.Work.Coercivity.box_ineq

import Submission.Work.Spaces.HkAux
import Submission.Work.Spaces.CurrySmooth

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-! ## The two integrands of the `D_θ`-coercivity estimate -/

/-- The energy integrand `D_θ f · D_θ f · thetaW α` (whose integral is `EDth α f`). -/
def dthEnergyIntegrand (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Spaces.Dth f z θ * Spaces.Dth f z θ * thetaW α z θ

/-- The coercivity integrand `Aop (D_θ f) · D_θ f · thetaW α`. -/
def dthAopIntegrand (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Aop (Spaces.Dth f) z θ * Spaces.Dth f z θ * thetaW α z θ

/-- `EDth α f` is the iterated integral of the energy integrand. -/
theorem EDth_eq_iterated (α : ℝ) (f : ℝ → ℝ → ℝ) :
    EDth α f = ∫ z in Spaces.Iz, ∫ θ in Spaces.Iθ, dthEnergyIntegrand α f z θ := by
  rw [EDth_eq_wip]
  rfl

/-- `wip` of the coercivity integrand is its iterated integral. -/
theorem wip_Aop_eq_iterated (α : ℝ) (f : ℝ → ℝ → ℝ) :
    wip (thetaW α) (Aop (Spaces.Dth f)) (Spaces.Dth f)
      = ∫ z in Spaces.Iz, ∫ θ in Spaces.Iθ, dthAopIntegrand α f z θ := rfl

/-! ## The `Aop` pairing is integrable on the quadrant -/

/-- The `z`-marginal of the coercivity integrand is integrable: Fubini applied to `hint`. -/
theorem integrableOn_aopMarginal (α : ℝ) (f : ℝ → ℝ → ℝ)
    (hint : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Aop (Spaces.Dth f) z θ * Spaces.Dth f z θ * thetaW α z θ))
      (Spaces.Iz ×ˢ Spaces.Iθ)) :
    MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Spaces.Iθ, Aop (Spaces.Dth f) z θ * Spaces.Dth f z θ * thetaW α z θ)
      Spaces.Iz := by
  have hμν : (volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ)
      = (volume : Measure (ℝ × ℝ)).restrict (Spaces.Iz ×ˢ Spaces.Iθ) := by
    rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod]
  have h1 : MeasureTheory.Integrable
      (Function.uncurry (fun z θ => Aop (Spaces.Dth f) z θ * Spaces.Dth f z θ * thetaW α z θ))
      ((volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ)) := by
    rw [hμν]
    exact hint
  have h2 := h1.integral_prod_left
  exact h2

/-! ## Measurability of the energy integrand -/

/-- The uncurried `D_θ f` is continuous on the neighbourhood `U` of the closed quadrant. -/
theorem continuousOn_uncurry_dth (f : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd f) :
    ContinuousOn (Function.uncurry (Spaces.Dth f)) Spaces.U := by
  have h := (Spaces.contDiffOn_uncurry_pth Spaces.isOpen_U hsm).continuousOn
  have hsin : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Spaces.U :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
  have hfun : Function.uncurry (Spaces.Dth f)
      = fun p : ℝ × ℝ => Real.sin (2 * p.2) * Function.uncurry (Spaces.pth f) p := by
    funext p; rfl
  rw [hfun]
  exact hsin.mul h

/-- The weight `thetaW α` is continuous on the open quadrant. -/
theorem continuousOn_thetaW (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => thetaW α p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have hw : ContinuousOn (fun p : ℝ × ℝ => ((1 + p.1) ^ 2 / p.1 ^ 2) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => ((1 + p.1) ^ 2 : ℝ))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
      (continuousOn_const.add continuousOn_fst).pow 2
    have h2 : ContinuousOn (fun p : ℝ × ℝ => (p.1 ^ 2 : ℝ))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := continuousOn_fst.pow 2
    exact (h1.div h2 (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))).pow 2
  have hs : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Spaces.gam α)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    have hsin : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
      (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
    refine hsin.rpow_const (fun p hp => Or.inl ?_)
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1])
      (by linarith [hp.2.2, Real.pi_pos]))
  have hfun : (fun p : ℝ × ℝ => thetaW α p.1 p.2)
      = fun p : ℝ × ℝ =>
        ((1 + p.1) ^ 2 / p.1 ^ 2) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Spaces.gam α)) := by
    funext p
    rw [thetaW, Spaces.w]
  rw [hfun]
  exact hw.mul hs

/-- The energy integrand `D_θ f · D_θ f · thetaW α` is a.e. strongly measurable on the
open quadrant. -/
theorem aeStronglyMeasurable_energyIntegrand (α : ℝ) (f : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd f) :
    AEStronglyMeasurable
      (Function.uncurry (fun z θ => Spaces.Dth f z θ * Spaces.Dth f z θ * thetaW α z θ))
      (MeasureTheory.volume.restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) := by
  have hv : ContinuousOn (Function.uncurry (Spaces.Dth f)) Spaces.U :=
    continuousOn_uncurry_dth f hsm
  have hsubset : (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) ⊆ Spaces.U := by
    rintro ⟨z, θ⟩ ⟨hz, hθ⟩
    simp only [Set.mem_Ioi, Set.mem_Ioo] at hz hθ
    refine ⟨?_, ?_⟩
    · simp only [Set.mem_Ioi]; linarith
    · simp only [Set.mem_Ioo]; exact ⟨by linarith, by linarith [Real.pi_pos]⟩
  have hvc : ContinuousOn (Function.uncurry (Spaces.Dth f))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := hv.mono hsubset
  have h1 : AEStronglyMeasurable
      (fun p : ℝ × ℝ => Function.uncurry (Spaces.Dth f) p * Function.uncurry (Spaces.Dth f) p)
      (MeasureTheory.volume.restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :=
    (hvc.mul hvc).aestronglyMeasurable (measurableSet_Ioi.prod measurableSet_Ioo)
  have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ => thetaW α p.1 p.2)
      (MeasureTheory.volume.restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :=
    (continuousOn_thetaW α).aestronglyMeasurable (measurableSet_Ioi.prod measurableSet_Ioo)
  have hfun : (Function.uncurry (fun z θ => Spaces.Dth f z θ * Spaces.Dth f z θ * thetaW α z θ))
      = fun p : ℝ × ℝ =>
        (Function.uncurry (Spaces.Dth f) p * Function.uncurry (Spaces.Dth f) p) * thetaW α p.1 p.2 := by
    funext p; rfl
  rw [hfun]
  exact h1.mul h2


/-- The closed half-line and the open half-line are almost everywhere equal. -/
theorem ae_eq_Ioi_Ici (a : ℝ) : Set.Ioi a =ᵐ[(volume : Measure ℝ)] Set.Ici a := by
  rw [MeasureTheory.ae_eq_set]
  constructor
  · rw [Set.sdiff_eq_empty.mpr Set.Ioi_subset_Ici_self, MeasureTheory.measure_empty]
  · have hnull : (MeasureTheory.volume : Measure ℝ) ({a} : Set ℝ) = 0 :=
      (Set.finite_singleton a).measure_zero (MeasureTheory.volume : Measure ℝ)
    refine MeasureTheory.measure_mono_null (fun x hx => ?_) hnull
    rw [Set.mem_sdiff, Set.mem_Ici, Set.mem_Ioi] at hx
    simp only [Set.mem_singleton_iff]
    exact le_antisymm (not_lt.mp hx.2) hx.1

/-- The open quadrant and the closed quadrant carry the same restricted Lebesgue measure. -/
theorem restrict_quadrant_eq :
    (MeasureTheory.volume : Measure (ℝ × ℝ)).restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))
      = (MeasureTheory.volume : Measure (ℝ × ℝ)).restrict (Spaces.Iz ×ˢ Spaces.Iθ) := by
  have h1 : (MeasureTheory.volume : Measure (ℝ × ℝ))
      = (MeasureTheory.volume : Measure ℝ).prod (MeasureTheory.volume : Measure ℝ) :=
    MeasureTheory.Measure.volume_eq_prod ℝ ℝ
  rw [h1, ← MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.prod_restrict]
  rw [MeasureTheory.Measure.restrict_congr_set (ae_eq_Ioi_Ici 0),
    MeasureTheory.Measure.restrict_congr_set (ae_eq_Ioo_Icc 0 (π / 2))]
  rfl

/-- The energy integrand is a.e. strongly measurable on the closed quadrant. -/
theorem aeStronglyMeasurable_energyIntegrand_quadrant (α : ℝ) (f : ℝ → ℝ → ℝ)
    (hsm : Spaces.SmoothNbhd f) :
    AEStronglyMeasurable
      (Function.uncurry (fun z θ => Spaces.Dth f z θ * Spaces.Dth f z θ * thetaW α z θ))
      (MeasureTheory.volume.restrict (Spaces.Iz ×ˢ Spaces.Iθ)) := by
  rw [← restrict_quadrant_eq]
  exact aeStronglyMeasurable_energyIntegrand α f hsm

/-- The `z`-marginal of the energy integrand is a.e. strongly measurable. -/
theorem aeStronglyMeasurable_energyMarginal (α : ℝ) (f : ℝ → ℝ → ℝ)
    (hsm : Spaces.SmoothNbhd f) :
    AEStronglyMeasurable
      (fun z => ∫ θ in Spaces.Iθ, Spaces.Dth f z θ * Spaces.Dth f z θ * thetaW α z θ)
      (MeasureTheory.volume.restrict Spaces.Iz) := by
  have hμ : (MeasureTheory.volume.restrict Spaces.Iz).prod
        (MeasureTheory.volume.restrict Spaces.Iθ)
      = (MeasureTheory.volume : Measure (ℝ × ℝ)).restrict (Spaces.Iz ×ˢ Spaces.Iθ) := by
    rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod]
  have h := aeStronglyMeasurable_energyIntegrand_quadrant α f hsm
  rw [← hμ] at h
  exact h.integral_prod_right'


/-! ## Bounds on the box for the two integrands of the one-dimensional by-parts lemmas -/

/-- `(w z)² · z⁴ = (1+z)⁴`. -/
theorem w_sq_mul_z4 (z : ℝ) (hz : z ≠ 0) : Spaces.w z ^ 2 * z ^ 4 = (1 + z) ^ 4 := by
  rw [Spaces.w, div_pow]
  field_simp

/-- From the Taylor bounds on the box one gets the two boundedness hypotheses needed by
the finite-`z`-interval integration by parts: `D_θ f · w` and `L(D_θ f) · D_θ f · w²`
are bounded on `(0,R)` for every fixed `θ ∈ Iθ`. -/
theorem dth_slice_bounds_of_taylor (f : ℝ → ℝ → ℝ) (R : ℝ)
    (hb : ∃ C : ℝ, 0 < C ∧ ∀ z ∈ Set.Ioo 0 R, ∀ θ ∈ Spaces.Iθ,
      |Spaces.pth f z θ| ≤ C * z ^ 2 ∧ |Spaces.pz f z θ| ≤ C * z
        ∧ |Spaces.pz (Spaces.pth f) z θ| ≤ C * z ∧ |Spaces.pth (Spaces.pth f) z θ| ≤ C) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ ∈ Spaces.Iθ,
      (∀ z ∈ Set.Ioo 0 R, |Spaces.Dth f z θ * Spaces.w z| ≤ C)
      ∧ (∀ z ∈ Set.Ioo 0 R, |L (Spaces.Dth f) z θ * Spaces.Dth f z θ * Spaces.w z ^ 2| ≤ C) := by
  obtain ⟨K, hKpos, hK⟩ := hb
  refine ⟨4 * K ^ 2 * (1 + |R|) ^ 4 + K * (1 + |R|) ^ 2 + 1, by positivity, fun θ hθ => ⟨?_, ?_⟩⟩
  · intro z hz
    have hz0 : z ≠ 0 := ne_of_gt hz.1
    have hsin0 : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have hsin1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have h1 : |Spaces.pth f z θ| ≤ K * z ^ 2 := (hK z hz θ hθ).1
    rw [Spaces.Dth, Spaces.w, abs_mul, abs_mul, abs_of_nonneg hsin0,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 + z) ^ 2 / z ^ 2)]
    calc Real.sin (2 * θ) * |Spaces.pth f z θ| * ((1 + z) ^ 2 / z ^ 2)
        ≤ (1 * (K * z ^ 2)) * ((1 + z) ^ 2 / z ^ 2) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul hsin1 h1 (abs_nonneg _) (by norm_num)
      _ = K * (1 + z) ^ 2 := by field_simp
      _ ≤ K * (1 + |R|) ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hKpos)
          have h7 : (1 : ℝ) + z ≤ 1 + |R| := by linarith [hz.2, le_abs_self R]
          exact pow_le_pow_left₀ (by linarith [hz.1]) h7 2
      _ ≤ 4 * K ^ 2 * (1 + |R|) ^ 4 + K * (1 + |R|) ^ 2 + 1 := by
          have h8 : (0 : ℝ) ≤ (1 + |R|) ^ 2 := sq_nonneg _
          have h9 : (0 : ℝ) ≤ 4 * K ^ 2 * (1 + |R|) ^ 4 := by positivity
          linarith
  · intro z hz
    have hsin0 : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have hsin1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have hz0 : z ≠ 0 := ne_of_gt hz.1
    have hz1 : (0 : ℝ) < 1 + z := by linarith [hz.1]
    have hK1 : |Spaces.pth f z θ| ≤ K * z ^ 2 := (hK z hz θ hθ).1
    have hK2 : |Spaces.pz (Spaces.pth f) z θ| ≤ K * z := (hK z hz θ hθ).2.2.1
    have hv : |Spaces.Dth f z θ| ≤ Real.sin (2 * θ) * (K * z ^ 2) := by
      rw [Spaces.Dth, abs_mul, abs_of_nonneg hsin0]
      exact mul_le_mul_of_nonneg_left hK1 hsin0
    have hpzv : |Spaces.pz (Spaces.Dth f) z θ| ≤ Real.sin (2 * θ) * (K * z) := by
      rw [pz_Dth_val, abs_mul, abs_of_nonneg hsin0]
      exact mul_le_mul_of_nonneg_left hK2 hsin0
    have hA : (0 : ℝ) ≤ Real.sin (2 * θ) * (K * z ^ 2) := mul_nonneg hsin0 (by positivity)
    have hLs : |L (Spaces.Dth f) z θ| ≤ 4 * (Real.sin (2 * θ) * (K * z ^ 2)) := by
      have hdecomp : L (Spaces.Dth f) z θ
          = Spaces.Dth f z θ + (z * Spaces.pz (Spaces.Dth f) z θ
              - 2 * Spaces.Dth f z θ / (1 + z)) := by
        rw [L, Spaces.Dz]; ring
      rw [hdecomp]
      have h1 := abs_add_le (Spaces.Dth f z θ)
        (z * Spaces.pz (Spaces.Dth f) z θ - 2 * Spaces.Dth f z θ / (1 + z))
      have h2 : |z * Spaces.pz (Spaces.Dth f) z θ - 2 * Spaces.Dth f z θ / (1 + z)|
          ≤ |z * Spaces.pz (Spaces.Dth f) z θ| + |2 * Spaces.Dth f z θ / (1 + z)| := by
        have h := abs_add_le (z * Spaces.pz (Spaces.Dth f) z θ)
          (-(2 * Spaces.Dth f z θ / (1 + z)))
        rw [abs_neg] at h
        calc |z * Spaces.pz (Spaces.Dth f) z θ - 2 * Spaces.Dth f z θ / (1 + z)|
            = |z * Spaces.pz (Spaces.Dth f) z θ + (-(2 * Spaces.Dth f z θ / (1 + z)))| := by ring_nf
          _ ≤ _ := h
      have h3 : |z * Spaces.pz (Spaces.Dth f) z θ| ≤ Real.sin (2 * θ) * (K * z ^ 2) := by
        rw [abs_mul, abs_of_pos hz.1]
        calc z * |Spaces.pz (Spaces.Dth f) z θ| ≤ z * (Real.sin (2 * θ) * (K * z)) :=
              mul_le_mul_of_nonneg_left hpzv (le_of_lt hz.1)
          _ = Real.sin (2 * θ) * (K * z ^ 2) := by ring
      have h4 : |2 * Spaces.Dth f z θ / (1 + z)| ≤ 2 * (Real.sin (2 * θ) * (K * z ^ 2)) := by
        rw [abs_div, abs_of_pos hz1]
        have h5 : |2 * Spaces.Dth f z θ| ≤ 2 * (Real.sin (2 * θ) * (K * z ^ 2)) := by
          rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
          exact mul_le_mul_of_nonneg_left hv (by norm_num)
        calc |2 * Spaces.Dth f z θ| / (1 + z)
            ≤ 2 * (Real.sin (2 * θ) * (K * z ^ 2)) / (1 + z) :=
              div_le_div_of_nonneg_right h5 (le_of_lt hz1)
          _ ≤ 2 * (Real.sin (2 * θ) * (K * z ^ 2)) := by
              rw [div_le_iff₀ hz1]
              nlinarith [hA, hz.1]
      linarith [h1, h2, h3, h4, hv, hA]
    have hstep : |L (Spaces.Dth f) z θ * Spaces.Dth f z θ * Spaces.w z ^ 2|
        ≤ 4 * K ^ 2 * (1 + |R|) ^ 4 := by
      have hw2 : |Spaces.w z ^ 2| = Spaces.w z ^ 2 := abs_of_nonneg (sq_nonneg _)
      rw [abs_mul, abs_mul, hw2]
      have h2 : |L (Spaces.Dth f) z θ| * |Spaces.Dth f z θ| * Spaces.w z ^ 2
          ≤ (4 * (Real.sin (2 * θ) * (K * z ^ 2))) * (Real.sin (2 * θ) * (K * z ^ 2))
              * Spaces.w z ^ 2 := by
        refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        exact mul_le_mul hLs hv (abs_nonneg _) (by positivity)
      have h3 : (4 * (Real.sin (2 * θ) * (K * z ^ 2))) * (Real.sin (2 * θ) * (K * z ^ 2))
            * Spaces.w z ^ 2 = 4 * (Real.sin (2 * θ)) ^ 2 * K ^ 2 * (1 + z) ^ 4 := by
        rw [show (4 * (Real.sin (2 * θ) * (K * z ^ 2))) * (Real.sin (2 * θ) * (K * z ^ 2))
              = 4 * (Real.sin (2 * θ)) ^ 2 * K ^ 2 * z ^ 4 by ring]
        rw [show 4 * (Real.sin (2 * θ)) ^ 2 * K ^ 2 * z ^ 4 * Spaces.w z ^ 2
              = 4 * (Real.sin (2 * θ)) ^ 2 * K ^ 2 * (Spaces.w z ^ 2 * z ^ 4) by ring]
        rw [w_sq_mul_z4 z hz0]
      have h4 : (Real.sin (2 * θ)) ^ 2 ≤ 1 := by nlinarith [hsin0, hsin1]
      have h5 : 4 * (Real.sin (2 * θ)) ^ 2 * K ^ 2 * (1 + z) ^ 4
          ≤ 4 * K ^ 2 * (1 + |R|) ^ 4 := by
        have h6 : (1 + z) ^ 4 ≤ (1 + |R|) ^ 4 := by
          have h7 : (1 : ℝ) + z ≤ 1 + |R| := by linarith [hz.2, le_abs_self R]
          exact pow_le_pow_left₀ (by linarith [hz.1]) h7 4
        calc 4 * (Real.sin (2 * θ)) ^ 2 * K ^ 2 * (1 + z) ^ 4
            = (4 * K ^ 2 * (1 + z) ^ 4) * (Real.sin (2 * θ)) ^ 2 := by ring
          _ ≤ (4 * K ^ 2 * (1 + |R|) ^ 4) * 1 := by
              refine mul_le_mul ?_ h4 (sq_nonneg _) (by positivity)
              exact mul_le_mul_of_nonneg_left h6 (by positivity)
          _ = 4 * K ^ 2 * (1 + |R|) ^ 4 := by ring
      calc |L (Spaces.Dth f) z θ| * |Spaces.Dth f z θ| * Spaces.w z ^ 2
          ≤ (4 * (Real.sin (2 * θ) * (K * z ^ 2))) * (Real.sin (2 * θ) * (K * z ^ 2))
              * Spaces.w z ^ 2 := h2
        _ = 4 * (Real.sin (2 * θ)) ^ 2 * K ^ 2 * (1 + z) ^ 4 := h3
        _ ≤ 4 * K ^ 2 * (1 + |R|) ^ 4 := h5
    have hK2nn : (0 : ℝ) ≤ K * (1 + |R|) ^ 2 := by positivity
    linarith [hstep, hK2nn]


/-! ## The two limit ingredients of the coercivity estimate -/

/-- The `z`-box integrals of the coercivity integrand converge to `wip`. -/
theorem tendsto_aopBox (α : ℝ) (f : ℝ → ℝ → ℝ)
    (hint : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Aop (Spaces.Dth f) z θ * Spaces.Dth f z θ * thetaW α z θ))
      (Spaces.Iz ×ˢ Spaces.Iθ)) :
    Filter.Tendsto
      (fun n : ℕ => ∫ z in Set.Icc 0 ((n : ℝ) + 1),
        ∫ θ in Spaces.Iθ, Aop (Spaces.Dth f) z θ * Spaces.Dth f z θ * thetaW α z θ)
      Filter.atTop
      (nhds (wip (thetaW α) (Aop (Spaces.Dth f)) (Spaces.Dth f))) := by
  have hInt := integrableOn_aopMarginal α f hint
  have hmono : Monotone (fun n : ℕ => Set.Icc (0 : ℝ) ((n : ℝ) + 1)) := by
    intro n m hnm z hz
    refine ⟨hz.1, ?_⟩
    have h1 : (n : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hnm
    linarith [hz.2]
  have hunion : (⋃ n : ℕ, Set.Icc (0 : ℝ) ((n : ℝ) + 1)) = Spaces.Iz := by
    ext z
    constructor
    · intro hz
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hz
      exact hn.1
    · intro hz
      have hz0 : 0 ≤ z := hz
      obtain ⟨n, hn⟩ := exists_nat_ge z
      exact Set.mem_iUnion.mpr ⟨n, ⟨hz0, by push_cast; linarith⟩⟩
  have h := MeasureTheory.tendsto_setIntegral_of_monotone (μ := volume)
    (f := fun z => ∫ θ in Spaces.Iθ, Aop (Spaces.Dth f) z θ * Spaces.Dth f z θ * thetaW α z θ)
    (s := fun n : ℕ => Set.Icc (0 : ℝ) ((n : ℝ) + 1)) (fun n => measurableSet_Icc) hmono
    (by rw [hunion]; exact hInt)
  simpa only [hunion, wip] using h

/-- The `z`-box integrals of the coercivity integrand are bounded by its `L¹`-norm on the
quadrant. -/
theorem normBound_aopBox (α : ℝ) (f : ℝ → ℝ → ℝ)
    (hint : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Aop (Spaces.Dth f) z θ * Spaces.Dth f z θ * thetaW α z θ))
      (Spaces.Iz ×ˢ Spaces.Iθ)) :
    ∀ n : ℕ, (∫ z in Set.Icc 0 ((n : ℝ) + 1),
        ∫ θ in Spaces.Iθ, Aop (Spaces.Dth f) z θ * Spaces.Dth f z θ * thetaW α z θ)
      ≤ ∫ p in Spaces.Iz ×ˢ Spaces.Iθ,
          |Aop (Spaces.Dth f) p.1 p.2 * Spaces.Dth f p.1 p.2 * thetaW α p.1 p.2| := by
  intro n
  set FF : ℝ → ℝ → ℝ := fun z θ => Aop (Spaces.Dth f) z θ * Spaces.Dth f z θ * thetaW α z θ
    with hFF
  set B : Set (ℝ × ℝ) := Set.Icc 0 ((n : ℝ) + 1) ×ˢ Spaces.Iθ with hB
  have hmem : B ⊆ Spaces.Iz ×ˢ Spaces.Iθ := by
    intro p hp
    exact ⟨hp.1.1, hp.2⟩
  have hIntB : MeasureTheory.IntegrableOn (Function.uncurry FF) B := by
    refine hint.mono_set hmem
  have hfub : (∫ z in Set.Icc 0 ((n : ℝ) + 1), ∫ θ in Spaces.Iθ, FF z θ)
      = ∫ p in B, FF p.1 p.2 := by
    have hintB' : MeasureTheory.IntegrableOn (Function.uncurry FF)
        (Set.Icc 0 ((n : ℝ) + 1) ×ˢ Spaces.Iθ) ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
      have hme : (volume : Measure ℝ).prod (volume : Measure ℝ) = (volume : Measure (ℝ × ℝ)) :=
        (MeasureTheory.Measure.volume_eq_prod ℝ ℝ).symm
      rw [hme]
      exact hIntB
    have h := MeasureTheory.setIntegral_prod (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      (s := Set.Icc 0 ((n : ℝ) + 1)) (t := Spaces.Iθ) (Function.uncurry FF) hintB'
    rw [← MeasureTheory.Measure.volume_eq_prod] at h
    exact h.symm
  have hIntabs : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => |FF p.1 p.2|) (Spaces.Iz ×ˢ Spaces.Iθ) := hint.abs
  calc (∫ z in Set.Icc 0 ((n : ℝ) + 1), ∫ θ in Spaces.Iθ, FF z θ)
      = ∫ p in B, FF p.1 p.2 := hfub
    _ ≤ ∫ p in B, |FF p.1 p.2| := by
        refine MeasureTheory.integral_mono_ae hIntB hIntB.abs ?_
        exact Filter.Eventually.of_forall (fun p => le_abs_self _)
    _ ≤ ∫ p in Spaces.Iz ×ˢ Spaces.Iθ, |FF p.1 p.2| := by
        refine MeasureTheory.setIntegral_mono_set hIntabs ?_ ?_
        · exact Filter.Eventually.of_forall (fun p => abs_nonneg _)
        · exact Filter.Eventually.of_forall (fun x hx => hmem hx)


/-! ## The final assembly (given the finite-box coercivity) -/

/-- The `D_θ`-coercivity estimate, assembled from the finite-box coercivity `hbox`. -/
theorem theta_coercive_of_box (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ)
    (hint : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Aop (Spaces.Dth f) z θ * Spaces.Dth f z θ * thetaW α z θ))
      (Spaces.Iz ×ˢ Spaces.Iθ))
    (hgm : AEStronglyMeasurable
      (fun z => ∫ θ in Spaces.Iθ, Spaces.Dth f z θ * Spaces.Dth f z θ * thetaW α z θ)
      (MeasureTheory.volume.restrict Spaces.Iz))
    (hgnn : ∀ z, 0 ≤ ∫ θ in Spaces.Iθ, Spaces.Dth f z θ * Spaces.Dth f z θ * thetaW α z θ)
    (hgi : ∀ n : ℕ, MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Spaces.Iθ, Spaces.Dth f z θ * Spaces.Dth f z θ * thetaW α z θ)
      (Set.Icc 0 ((n : ℝ) + 1)))
    (hbox : ∀ n : ℕ, (1 / 2 - 3 * α / 10) *
          (∫ z in Set.Icc 0 ((n : ℝ) + 1),
            ∫ θ in Spaces.Iθ, Spaces.Dth f z θ * Spaces.Dth f z θ * thetaW α z θ)
        ≤ ∫ z in Set.Icc 0 ((n : ℝ) + 1),
            ∫ θ in Spaces.Iθ, Aop (Spaces.Dth f) z θ * Spaces.Dth f z θ * thetaW α z θ) :
    (1 / 2 - 3 * α / 10) * EDth α f ≤ wip (thetaW α) (Aop (Spaces.Dth f)) (Spaces.Dth f) := by
  have hcpos : (0 : ℝ) < 1 / 2 - 3 * α / 10 := by
    have h := Spaces.gam_sub_one α
    rw [Spaces.gam] at h
    nlinarith [hα1, hα]
  set M : ℝ := ∫ p in Spaces.Iz ×ˢ Spaces.Iθ,
    |Aop (Spaces.Dth f) p.1 p.2 * Spaces.Dth f p.1 p.2 * thetaW α p.1 p.2| with hMdef
  have hHconv := tendsto_aopBox α f hint
  have hHbdd := normBound_aopBox α f hint
  have hbdd : ∀ n : ℕ, (∫ z in Set.Icc 0 ((n : ℝ) + 1),
      ∫ θ in Spaces.Iθ, Spaces.Dth f z θ * Spaces.Dth f z θ * thetaW α z θ)
      ≤ M / (1 / 2 - 3 * α / 10) := by
    intro n
    have h1 := hbox n
    have h2 := hHbdd n
    have h3 : (1 / 2 - 3 * α / 10) * (∫ z in Set.Icc 0 ((n : ℝ) + 1),
        ∫ θ in Spaces.Iθ, Spaces.Dth f z θ * Spaces.Dth f z θ * thetaW α z θ) ≤ M := by
      exact le_trans h1 h2
    rw [le_div_iff₀ hcpos]
    linarith [h3]
  obtain ⟨hgi', hglim, hgle⟩ := monotone_interval
    (fun z => ∫ θ in Spaces.Iθ, Spaces.Dth f z θ * Spaces.Dth f z θ * thetaW α z θ)
    (M / (1 / 2 - 3 * α / 10)) hgm hgnn hgi hbdd
  have h1 : Filter.Tendsto (fun n : ℕ => (1 / 2 - 3 * α / 10) *
        (∫ z in Set.Icc 0 ((n : ℝ) + 1),
          ∫ θ in Spaces.Iθ, Spaces.Dth f z θ * Spaces.Dth f z θ * thetaW α z θ))
      Filter.atTop (nhds ((1 / 2 - 3 * α / 10) *
        ∫ z in Spaces.Iz, ∫ θ in Spaces.Iθ,
          Spaces.Dth f z θ * Spaces.Dth f z θ * thetaW α z θ)) :=
    hglim.const_mul (1 / 2 - 3 * α / 10)
  have hle := le_of_tendsto_of_tendsto' h1 hHconv hbox
  rw [EDth_eq_iterated]
  exact hle


/-! ## Integrability of the joint energy integrand on a box -/

/-- Integrability on the open box transfers to the closed box. -/
theorem integrableOn_box_congr {F : ℝ × ℝ → ℝ} {R : ℝ}
    (h : MeasureTheory.IntegrableOn F (Set.Ioo 0 R ×ˢ Set.Ioo 0 (π / 2))) :
    MeasureTheory.IntegrableOn F (Set.Icc 0 R ×ˢ Spaces.Iθ) := by
  have h2 : MeasureTheory.Integrable F (volume.restrict (Set.Icc 0 R ×ˢ Spaces.Iθ)) := by
    rw [← restrict_box_eq R]
    exact h
  exact h2

/-- The joint energy integrand is integrable on the closed box as soon as it is continuous
and bounded on the open box. -/
theorem integrableOn_energyBox (α : ℝ) (f : ℝ → ℝ → ℝ) (R K : ℝ)
    (hcont : ContinuousOn
      (Function.uncurry (fun z θ => Spaces.Dth f z θ * Spaces.Dth f z θ * thetaW α z θ))
      (Set.Ioo 0 R ×ˢ Set.Ioo 0 (π / 2)))
    (hdom : ∀ z ∈ Set.Ioo 0 R, ∀ θ ∈ Spaces.Iθ,
      |Spaces.Dth f z θ * Spaces.Dth f z θ * thetaW α z θ| ≤ K) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Spaces.Dth f z θ * Spaces.Dth f z θ * thetaW α z θ))
      (Set.Icc 0 R ×ˢ Spaces.Iθ) := by
  have h1 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Spaces.Dth f z θ * Spaces.Dth f z θ * thetaW α z θ))
      (Set.Ioo 0 R ×ˢ Set.Ioo 0 (π / 2)) := by
    refine integrableOn_Ioo_prod_of_continuousOn (K := K) hcont ?_
    intro p hp
    rw [Real.norm_eq_abs]
    exact hdom p.1 hp.1 p.2 ⟨le_of_lt hp.2.1, le_of_lt hp.2.2⟩
  exact integrableOn_box_congr h1

/-- The `z`-marginal of the joint energy integrand is integrable on the box. -/
theorem integrableOn_energyMarginal (α : ℝ) (f : ℝ → ℝ → ℝ) (R : ℝ)
    (h : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Spaces.Dth f z θ * Spaces.Dth f z θ * thetaW α z θ))
      (Set.Icc 0 R ×ˢ Spaces.Iθ)) :
    MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Spaces.Iθ, Spaces.Dth f z θ * Spaces.Dth f z θ * thetaW α z θ)
      (Set.Icc 0 R) := by
  have hμν : (volume.restrict (Set.Icc 0 R)).prod (volume.restrict Spaces.Iθ)
      = (volume : Measure (ℝ × ℝ)).restrict (Set.Icc 0 R ×ˢ Spaces.Iθ) := by
    rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod]
  have h1 : MeasureTheory.Integrable
      (Function.uncurry (fun z θ => Spaces.Dth f z θ * Spaces.Dth f z θ * thetaW α z θ))
      ((volume.restrict (Set.Icc 0 R)).prod (volume.restrict Spaces.Iθ)) := by
    rw [hμν]
    exact h
  have h2 := h1.integral_prod_left
  exact h2


/-- The `D_θ`-coercivity estimate, assembled from the open-box coercivity `hbox` and the
domination `hdom`. -/
theorem theta_coercive_of_child_estimates (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (f : ℝ → ℝ → ℝ) (hf : IBP f)
    (hint : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Aop (Spaces.Dth f) z θ * Spaces.Dth f z θ * thetaW α z θ))
      (Spaces.Iz ×ˢ Spaces.Iθ))
    (hdomAll : ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ z ∈ Set.Ioo 0 ((n : ℝ) + 1),
      ∀ θ ∈ Spaces.Iθ,
      |L (Spaces.Dth f) z θ * Spaces.Dth f z θ * Spaces.w z ^ 2
          * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))| ≤ C * (1 + z) ^ 4
      ∧ |(3 / (1 + z)) * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))
            * Spaces.Dth (Spaces.Dth f) z θ * Spaces.Dth f z θ| ≤ C * (1 + z) ^ 4
      ∧ |(Spaces.Dth f z θ) ^ 2 * Spaces.w z ^ 2
            * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))| ≤ C * (1 + z) ^ 4
      ∧ |(Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (Spaces.Dth f z θ) ^ 2| ≤ C * (1 + z) ^ 4)
    (hboxAll : ∀ n : ℕ, (1 / 2 - 3 * α / 10) *
          (∫ p in Set.Ioo 0 ((n : ℝ) + 1) ×ˢ Set.Ioo 0 (π / 2),
            Spaces.Dth f p.1 p.2 * Spaces.Dth f p.1 p.2 * thetaW α p.1 p.2)
        ≤ ∫ p in Set.Ioo 0 ((n : ℝ) + 1) ×ˢ Set.Ioo 0 (π / 2),
            Aop (Spaces.Dth f) p.1 p.2 * Spaces.Dth f p.1 p.2 * thetaW α p.1 p.2) :
    (1 / 2 - 3 * α / 10) * EDth α f ≤ wip (thetaW α) (Aop (Spaces.Dth f)) (Spaces.Dth f) := by
  have hsm : Spaces.SmoothNbhd f := hf.smooth
  -- integrability of the joint energy integrand on each closed box
  have hEb : ∀ n : ℕ, MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Spaces.Dth f z θ * Spaces.Dth f z θ * thetaW α z θ))
      (Set.Icc 0 ((n : ℝ) + 1) ×ˢ Spaces.Iθ) := by
    intro n
    obtain ⟨C, hCpos, hC⟩ := hdomAll n
    have hcont0 := (dth_integrands_continuousOn α f hsm ((n : ℝ) + 1) (by positivity)).2.2.1
    have hcont : ContinuousOn
        (Function.uncurry (fun z θ => Spaces.Dth f z θ * Spaces.Dth f z θ * thetaW α z θ))
        (Set.Ioo 0 ((n : ℝ) + 1) ×ˢ Set.Ioo 0 (π / 2)) := by
      refine hcont0.congr (fun p _ => ?_)
      simp only [Function.uncurry]
      rw [thetaW]; ring
    refine integrableOn_energyBox α f ((n : ℝ) + 1) (C * (1 + ((n : ℝ) + 1)) ^ 4)
      hcont ?_
    intro z hz θ hθ
    have h1 : (1 + z) ^ 4 ≤ (1 + ((n : ℝ) + 1)) ^ 4 := by
      refine pow_le_pow_left₀ (by linarith [hz.1]) ?_ 4
      linarith [hz.2]
    calc |Spaces.Dth f z θ * Spaces.Dth f z θ * thetaW α z θ|
        = |Spaces.Dth f z θ ^ 2 * Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))| := by
          rw [thetaW]; ring_nf
      _ ≤ C * (1 + z) ^ 4 := (hC z hz θ hθ).2.2.1
      _ ≤ C * (1 + ((n : ℝ) + 1)) ^ 4 := by
          exact mul_le_mul_of_nonneg_left h1 (le_of_lt hCpos)
  -- the closed-box form of the box inequality
  have hboxCl : ∀ n : ℕ, (1 / 2 - 3 * α / 10) *
          (∫ p in Set.Icc 0 ((n : ℝ) + 1) ×ˢ Spaces.Iθ,
            Spaces.Dth f p.1 p.2 * Spaces.Dth f p.1 p.2 * thetaW α p.1 p.2)
        ≤ ∫ p in Set.Icc 0 ((n : ℝ) + 1) ×ˢ Spaces.Iθ,
            Aop (Spaces.Dth f) p.1 p.2 * Spaces.Dth f p.1 p.2 * thetaW α p.1 p.2 := by
    intro n
    rw [← restrict_box_eq ((n : ℝ) + 1)]
    exact hboxAll n
  refine theta_coercive_of_box α hα hα1 f hint
    (aeStronglyMeasurable_energyMarginal α f hsm) ?_
    (fun n => integrableOn_energyMarginal α f ((n : ℝ) + 1) (hEb n)) ?_
  · intro z
    refine MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ => ?_)
    rw [thetaW]
    have hsin : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos])
    exact mul_nonneg (mul_self_nonneg _)
      (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin _))
  · intro n
    have hme : (volume : Measure ℝ).prod (volume : Measure ℝ) = (volume : Measure (ℝ × ℝ)) :=
      (MeasureTheory.Measure.volume_eq_prod ℝ ℝ).symm
    have hE' : MeasureTheory.Integrable
        (Function.uncurry (fun z θ => Spaces.Dth f z θ * Spaces.Dth f z θ * thetaW α z θ))
        ((volume.restrict (Set.Icc 0 ((n : ℝ) + 1))).prod (volume.restrict Spaces.Iθ)) := by
      rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod]
      exact hEb n
    have hA' : MeasureTheory.Integrable
        (Function.uncurry (fun z θ => Aop (Spaces.Dth f) z θ * Spaces.Dth f z θ * thetaW α z θ))
        ((volume.restrict (Set.Icc 0 ((n : ℝ) + 1))).prod (volume.restrict Spaces.Iθ)) := by
      rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod]
      exact hint.mono_set (fun p hp => ⟨hp.1.1, hp.2⟩)
    have hfub1 : (∫ z in Set.Icc 0 ((n : ℝ) + 1),
          ∫ θ in Spaces.Iθ, Spaces.Dth f z θ * Spaces.Dth f z θ * thetaW α z θ)
        = ∫ p in Set.Icc 0 ((n : ℝ) + 1) ×ˢ Spaces.Iθ,
          Spaces.Dth f p.1 p.2 * Spaces.Dth f p.1 p.2 * thetaW α p.1 p.2 := by
      have h := MeasureTheory.setIntegral_prod (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
        (s := Set.Icc 0 ((n : ℝ) + 1)) (t := Spaces.Iθ)
        (fun p : ℝ × ℝ => Spaces.Dth f p.1 p.2 * Spaces.Dth f p.1 p.2 * thetaW α p.1 p.2) ?_
      · rw [hme] at h
        exact h.symm
      · rw [hme]
        exact hEb n
    have hfub2 : (∫ z in Set.Icc 0 ((n : ℝ) + 1),
          ∫ θ in Spaces.Iθ, Aop (Spaces.Dth f) z θ * Spaces.Dth f z θ * thetaW α z θ)
        = ∫ p in Set.Icc 0 ((n : ℝ) + 1) ×ˢ Spaces.Iθ,
          Aop (Spaces.Dth f) p.1 p.2 * Spaces.Dth f p.1 p.2 * thetaW α p.1 p.2 := by
      have h := MeasureTheory.setIntegral_prod (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
        (s := Set.Icc 0 ((n : ℝ) + 1)) (t := Spaces.Iθ)
        (fun p : ℝ × ℝ => Aop (Spaces.Dth f) p.1 p.2 * Spaces.Dth f p.1 p.2 * thetaW α p.1 p.2) ?_
      · rw [hme] at h
        exact h.symm
      · rw [hme]
        exact hint.mono_set (fun p hp => ⟨hp.1.1, hp.2⟩)
    rw [hfub1, hfub2]
    exact hboxCl n



/-- The `D_θ`-coercivity estimate, with the domination discharged from the Taylor bounds. -/
theorem theta_coercive_of_boxAll (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ)
    (hf : IBP f)
    (hint : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Aop (Spaces.Dth f) z θ * Spaces.Dth f z θ * thetaW α z θ))
      (Spaces.Iz ×ˢ Spaces.Iθ))
    (hboxAll : ∀ n : ℕ, (1 / 2 - 3 * α / 10) *
          (∫ p in Set.Ioo 0 ((n : ℝ) + 1) ×ˢ Set.Ioo 0 (π / 2),
            Spaces.Dth f p.1 p.2 * Spaces.Dth f p.1 p.2 * thetaW α p.1 p.2)
        ≤ ∫ p in Set.Ioo 0 ((n : ℝ) + 1) ×ˢ Set.Ioo 0 (π / 2),
            Aop (Spaces.Dth f) p.1 p.2 * Spaces.Dth f p.1 p.2 * thetaW α p.1 p.2) :
    (1 / 2 - 3 * α / 10) * EDth α f ≤ wip (thetaW α) (Aop (Spaces.Dth f)) (Spaces.Dth f) := by
  have h0 : ∀ θ ∈ Spaces.Iθ, f 0 θ = 0 ∧ Spaces.pz f 0 θ = 0 := zeros_of_IBP f hf
  refine theta_coercive_of_child_estimates α hα hα1 f hf hint ?_ hboxAll
  intro n
  have hR : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  obtain ⟨K, hKpos, hK⟩ := pth_bounds_box f hf.smooth ((n : ℝ) + 1) hR h0
  refine dth_box_domination α hα hα1 f ((n : ℝ) + 1) hR ?_
  exact ⟨K, hKpos, fun z hz θ hθ =>
    ⟨(hK z hz θ hθ).1, (hK z hz θ hθ).2.2.1, (hK z hz θ hθ).2.2.2⟩⟩


/-- **The `D_θ`-coercivity estimate `theta_coercive`.** -/
theorem theta_coercive (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ) (hf : IBP f)
    (hint : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Aop (Spaces.Dth f) z θ * Spaces.Dth f z θ * thetaW α z θ))
      (Spaces.Iz ×ˢ Spaces.Iθ)) :
    (1 / 2 - 3 * α / 10) * EDth α f ≤ wip (thetaW α) (Aop (Spaces.Dth f)) (Spaces.Dth f) := by
  refine theta_coercive_of_boxAll α hα hα1 f hf hint ?_
  intro n
  have hR : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h0 : ∀ θ ∈ Spaces.Iθ, f 0 θ = 0 ∧ Spaces.pz f 0 θ = 0 := zeros_of_IBP f hf
  obtain ⟨K, hKpos, hK⟩ := pth_bounds_box f hf.smooth ((n : ℝ) + 1) hR h0
  obtain ⟨C, hCpos, hC⟩ := dth_box_domination α hα hα1 f ((n : ℝ) + 1) hR
    ⟨K, hKpos, fun z hz θ hθ =>
      ⟨(hK z hz θ hθ).1, (hK z hz θ hθ).2.2.1, (hK z hz θ hθ).2.2.2⟩⟩
  have hcont := dth_integrands_continuousOn α f hf.smooth ((n : ℝ) + 1) hR
  -- the uniform bound `K' = C (1+R)^4`
  have hzR : ∀ z ∈ Set.Ioo 0 ((n : ℝ) + 1),
      (1 + z) ^ 4 ≤ (1 + ((n : ℝ) + 1)) ^ 4 := by
    intro z hz
    exact pow_le_pow_left₀ (by linarith [hz.1]) (by linarith [hz.2]) 4
  have hdom : (∀ z ∈ Set.Ioo 0 ((n : ℝ) + 1), ∀ θ ∈ Spaces.Iθ,
        |L (Spaces.Dth f) z θ * Spaces.Dth f z θ * Spaces.w z ^ 2
          * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))|
          ≤ C * (1 + ((n : ℝ) + 1)) ^ 4)
      ∧ (∀ z ∈ Set.Ioo 0 ((n : ℝ) + 1), ∀ θ ∈ Spaces.Iθ,
        |(3 / (1 + z)) * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))
          * Spaces.Dth (Spaces.Dth f) z θ * Spaces.Dth f z θ|
          ≤ C * (1 + ((n : ℝ) + 1)) ^ 4)
      ∧ (∀ z ∈ Set.Ioo 0 ((n : ℝ) + 1), ∀ θ ∈ Spaces.Iθ,
        |(Spaces.Dth f z θ) ^ 2 * Spaces.w z ^ 2
          * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))|
          ≤ C * (1 + ((n : ℝ) + 1)) ^ 4)
      ∧ (∀ z ∈ Set.Ioo 0 ((n : ℝ) + 1), ∀ θ ∈ Spaces.Iθ,
        |(Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (Spaces.Dth f z θ) ^ 2|
          ≤ C * (1 + ((n : ℝ) + 1)) ^ 4) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro z hz θ hθ
      exact le_trans (hC z hz θ hθ).1
        (mul_le_mul_of_nonneg_left (hzR z hz) (le_of_lt hCpos))
    · intro z hz θ hθ
      exact le_trans (hC z hz θ hθ).2.1
        (mul_le_mul_of_nonneg_left (hzR z hz) (le_of_lt hCpos))
    · intro z hz θ hθ
      exact le_trans (hC z hz θ hθ).2.2.1
        (mul_le_mul_of_nonneg_left (hzR z hz) (le_of_lt hCpos))
    · intro z hz θ hθ
      exact le_trans (hC z hz θ hθ).2.2.2
        (mul_le_mul_of_nonneg_left (hzR z hz) (le_of_lt hCpos))
  -- the two one-dimensional by-parts
  obtain ⟨B, hBpos, hBs⟩ := dth_slice_bounds_of_taylor f ((n : ℝ) + 1) ⟨K, hKpos, hK⟩
  have hzibp : ∀ θ ∈ Spaces.Iθ,
      ∫ z in Set.Icc 0 ((n : ℝ) + 1),
          L (Spaces.Dth f) z θ * Spaces.Dth f z θ * Spaces.w z ^ 2
        = (1 / 2) * (∫ z in Set.Icc 0 ((n : ℝ) + 1),
            (Spaces.Dth f z θ * Spaces.w z) ^ 2)
          + (1 / 2) * (((n : ℝ) + 1)
            * (Spaces.Dth f ((n : ℝ) + 1) θ * Spaces.w ((n : ℝ) + 1)) ^ 2) :=
    fun θ hθ => dth_slice_z_ibp f hf.smooth ((n : ℝ) + 1) hR hθ
      ⟨B, (hBs θ hθ).1⟩ ⟨B, (hBs θ hθ).2⟩
  have hθibp : ∀ z ∈ Set.Ioo 0 ((n : ℝ) + 1),
      ∫ θ in Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Spaces.gam α))
          * Spaces.Dth (Spaces.Dth f) z θ * Spaces.Dth f z θ
        = (Spaces.gam α - 1) * ∫ θ in Spaces.Iθ, Real.cos (2 * θ)
            * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) * (Spaces.Dth f z θ) ^ 2 :=
    fun z hz => dth_slice_theta_ibp α hα hα1 f hf.smooth hz.1
  -- integrability of the `w²`-weighted transport term: `F₂w² = F₁ - Aop`
  have hIntT : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (3 / (1 + z)) * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))
        * Spaces.Dth (Spaces.Dth f) z θ * Spaces.Dth f z θ * Spaces.w z ^ 2))
      (Set.Icc 0 ((n : ℝ) + 1) ×ˢ Spaces.Iθ) := by
    have hF1 : MeasureTheory.IntegrableOn
        (Function.uncurry (fun z θ => L (Spaces.Dth f) z θ * Spaces.Dth f z θ
          * Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))))
        (Set.Icc 0 ((n : ℝ) + 1) ×ˢ Spaces.Iθ) := by
      have h1 : MeasureTheory.IntegrableOn
          (Function.uncurry (fun z θ => L (Spaces.Dth f) z θ * Spaces.Dth f z θ
            * Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))))
          (Set.Ioo 0 ((n : ℝ) + 1) ×ˢ Set.Ioo 0 (π / 2)) := by
        refine integrableOn_Ioo_prod_of_continuousOn (K := C * (1 + ((n : ℝ) + 1)) ^ 4)
          hcont.1 ?_
        intro p hp
        rw [Real.norm_eq_abs]
        exact le_trans (hC p.1 hp.1 p.2 ⟨le_of_lt hp.2.1, le_of_lt hp.2.2⟩).1
          (mul_le_mul_of_nonneg_left (hzR p.1 hp.1) (le_of_lt hCpos))
      exact integrableOn_box_congr h1
    have hAop : MeasureTheory.IntegrableOn
        (Function.uncurry (fun z θ => Aop (Spaces.Dth f) z θ * Spaces.Dth f z θ
          * thetaW α z θ)) (Set.Icc 0 ((n : ℝ) + 1) ×ˢ Spaces.Iθ) :=
      hint.mono_set (fun p hp => ⟨hp.1.1, hp.2⟩)
    refine (hF1.sub hAop).congr ?_
    filter_upwards with p
    obtain ⟨z, θ⟩ := p
    simp only [Pi.sub_apply, Function.uncurry_apply_pair, Aop, thetaW]
    ring
  exact box_ineq α hα hα1 f ((n : ℝ) + 1) (C * (1 + ((n : ℝ) + 1)) ^ 4) hR hcont hdom
    hIntT hzibp hθibp

end Work.Coercivity
