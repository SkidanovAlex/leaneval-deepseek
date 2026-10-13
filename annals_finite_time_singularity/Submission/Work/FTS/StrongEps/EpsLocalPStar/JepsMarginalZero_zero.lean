import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel
import Submission.Work.FTS.StrongEps.Jeps_tendsto
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.AeSlotOneAe.Interp.TkA_slotIntegrable
import Submission.Work.FTS.StrongEps.EpsLocalPStar.JepsMarginalDefs
import Submission.Work.FTS.StrongEps.EpsLocalPStar.MarginalTransferIntegrable
import Submission.Work.FTS.StrongEps.EpsLocalPStar.IbdLocalIntegrable
import Submission.Work.FTS.StrongEps.EpsLocalPStar.JkerDomDensityIntegrable
import Submission.Work.FTS.StrongEps.EpsLocalPStar.AEShiftProfile
import Submission.Work.FTS.StrongEps.EpsLocalPStar.AEShiftPreimage
import Submission.Work.FTS.StrongEps.EpsLocalPStar.HbdPointwiseLe
import Submission.Work.FTS.StrongEps.EpsLocalPStar.ThShiftSmall

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 800000

theorem JepsMarginalZero_zero {α : ℝ} (hα : α ∈ Set.Ioc 0 1)
    {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε)
    {f : ℝ → ℝ → ℝ} {lam : ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α 1 f)
    (hlamm : Measurable lam)
    (hint : MeasureTheory.Integrable (fun u : ℝ => lam (Real.exp u)))
    (htr : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))),
        Filter.Tendsto (fun θ => f z θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds (lam z)))
    (hbd : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))), ∀ θ ∈ Set.Ioo 0 (Real.pi/4),
        (f z θ - lam z)^2
          ≤ 100 / (Work.Spaces.gam α - 1) * (Real.sin (2*θ))^(Work.Spaces.gam α - 1)
            * (∫ σ in Work.Spaces.Iθ,
                (Real.sin (2*σ))^(2 - Work.Spaces.gam α) * (Work.Spaces.pth f z σ)^2))
    (hjtr : ∀ z ∈ Set.Ioi (0:ℝ), Filter.Tendsto (fun θ => Work.FTS.StrongEps.Jeps ρ ε f z θ)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) :
    ∀ z ∈ Set.Ioi (0:ℝ),
      (∫ s : ℝ, (∫ t : ℝ, ρ (s, t)) * lam (z * Real.exp (-(ε * s)))) = 0 := by
  intro z hz
  -- the two constants of the estimate
  have hgam : (1 : ℝ) < Work.Spaces.gam α := by
    rw [Work.Spaces.gam]; linarith [hα.1]
  set A : ℝ := 100 / (Work.Spaces.gam α - 1) with hAdef
  have hAnn : 0 ≤ A := by rw [hAdef]; positivity
  set Kb : ℝ := max 1 A with hKbdef
  have hKb1 : 1 ≤ Kb := by rw [hKbdef]; exact le_max_left _ _
  have hKbA : A ≤ Kb := by rw [hKbdef]; exact le_max_right _ _
  have hKb0 : 0 ≤ Kb := le_trans zero_le_one hKb1
  -- the linear pointwise bound of `hbd`, valid a.e. in `z`
  have hbdlin : ∀ᵐ w ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))),
      ∀ θ ∈ Set.Ioo 0 (Real.pi/4), |f w θ - lam w| ≤ (A * Ibd α f w + 1) / 2 := by
    have h := HbdPointwiseLe hα hbd
    filter_upwards [h] with w hw
    intro θ hθ
    have h2 := hw θ hθ
    rw [hAdef]
    exact h2
  -- transport the a.e. statements to the `p`-variable
  have hbdp : ∀ᵐ p ∂(MeasureTheory.volume : Measure (ℝ × ℝ)), ∀ θ ∈ Set.Ioo 0 (Real.pi/4),
      |f (z * Real.exp (-p.1)) θ - lam (z * Real.exp (-p.1))|
        ≤ (A * Ibd α f (z * Real.exp (-p.1)) + 1) / 2 :=
    AEShiftPreimage hz hbdlin
  have htrp : ∀ᵐ p ∂(MeasureTheory.volume : Measure (ℝ × ℝ)),
      Filter.Tendsto (fun θ => f (z * Real.exp (-p.1)) θ) (nhdsWithin (0:ℝ) (Set.Ioi 0))
        (nhds (lam (z * Real.exp (-p.1)))) :=
    AEShiftPreimage hz htr
  -- the `θ`-shift converges to `0⁺`
  have hshift : ∀ p₂ : ℝ, Filter.Tendsto (fun θ : ℝ => Real.arctan (Real.tan θ * Real.exp (-p₂)))
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhdsWithin (0:ℝ) (Set.Ioi 0)) := by
    intro p₂
    have hcont : ContinuousAt (fun θ : ℝ => Real.arctan (Real.tan θ * Real.exp (-p₂))) 0 :=
      Real.continuous_arctan.continuousAt.comp
        ((Real.continuousAt_tan.mpr (by rw [Real.cos_zero]; norm_num)).mul_const _)
    have htend : Filter.Tendsto (fun θ : ℝ => Real.arctan (Real.tan θ * Real.exp (-p₂)))
        (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) := by
      have h1 : Filter.Tendsto (fun θ : ℝ => Real.arctan (Real.tan θ * Real.exp (-p₂)))
          (nhds (0 : ℝ)) (nhds (Real.arctan (Real.tan 0 * Real.exp (-p₂)))) := hcont.tendsto
      have h2 : Real.arctan (Real.tan 0 * Real.exp (-p₂)) = 0 := by simp
      rw [h2] at h1
      exact h1.mono_left nhdsWithin_le_nhds
    refine tendsto_nhdsWithin_iff.mpr ⟨htend, ?_⟩
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < Real.pi/2 by positivity)] with θ hθ
    exact (Real.arctan_pos).2
      (mul_pos (Real.tan_pos_of_pos_of_lt_pi_div_two hθ.1 hθ.2) (Real.exp_pos _))
  -- the integrability of the dominating density
  have hIbdint : ∀ a b : ℝ, 0 < a → a ≤ b →
      MeasureTheory.IntegrableOn (fun w : ℝ => Ibd α f w) (Set.Icc a b) :=
    fun a b ha hab => IbdLocalIntegrable hso hm ha hab
  have hdom : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => ‖Work.FTS.StrongEps.Jker ρ ε p‖ *
        (|lam (z * Real.exp (-p.1))| + Ibd α f (z * Real.exp (-p.1))))
      (MeasureTheory.volume : Measure (ℝ × ℝ)) :=
    JkerDomDensityIntegrable hρ hε hz hlamm hint hIbdint
  have hJ : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => ‖Work.FTS.StrongEps.Jker ρ ε p‖)
      (MeasureTheory.volume : Measure (ℝ × ℝ)) :=
    (Work.FTS.StrongEps.Jker_integrable hρ.moll hε).norm
  have hbdd : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Kb * (‖Work.FTS.StrongEps.Jker ρ ε p‖ *
        (|lam (z * Real.exp (-p.1))| + Ibd α f (z * Real.exp (-p.1)))
        + ‖Work.FTS.StrongEps.Jker ρ ε p‖))
      (MeasureTheory.volume : Measure (ℝ × ℝ)) :=
    (hdom.add hJ).const_mul Kb
  -- the three inputs of the dominated convergence theorem
  have hmeas : ∀ᶠ θ in nhdsWithin (0:ℝ) (Set.Ioi 0), MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.FTS.StrongEps.Jker ρ ε p *
        f (z * Real.exp (-p.1)) (Real.arctan (Real.tan θ * Real.exp (-p.2))))
      (MeasureTheory.volume : Measure (ℝ × ℝ)) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < Real.pi/2 by positivity)] with θ hθ
    exact (Work.FTS.StrongEps.Jker_continuous hρ.moll ε).aestronglyMeasurable.mul
      (AEShiftProfile hso hz hθ)
  obtain ⟨θ₀, hθ₀pos, hθ₀mem⟩ := ThShiftSmall hε
  have hbound : ∀ᶠ θ in nhdsWithin (0:ℝ) (Set.Ioi 0),
      ∀ᵐ p ∂(MeasureTheory.volume : Measure (ℝ × ℝ)),
      ‖Work.FTS.StrongEps.Jker ρ ε p *
        f (z * Real.exp (-p.1)) (Real.arctan (Real.tan θ * Real.exp (-p.2)))‖
      ≤ Kb * (‖Work.FTS.StrongEps.Jker ρ ε p‖ *
        (|lam (z * Real.exp (-p.1))| + Ibd α f (z * Real.exp (-p.1)))
        + ‖Work.FTS.StrongEps.Jker ρ ε p‖) := by
    filter_upwards [Ioo_mem_nhdsGT hθ₀pos] with θ hθ
    filter_upwards [hbdp] with p hp
    by_cases hJ0 : Work.FTS.StrongEps.Jker ρ ε p = 0
    · rw [hJ0, zero_mul, norm_zero]
      simp
    · have hp2 : |p.2| ≤ ε := by
        have hsup := Work.FTS.StrongEps.Jker_ne_zero_support hρ.moll hε hJ0
        have hsq : p.2 ^ 2 ≤ ε ^ 2 := by nlinarith [sq_nonneg p.1]
        have h2 := (sq_le_sq.mp hsq : |p.2| ≤ |ε|)
        rwa [abs_of_pos hε] at h2
      have hΘ : Real.arctan (Real.tan θ * Real.exp (-p.2)) ∈ Set.Ioo 0 (Real.pi/4) :=
        hθ₀mem θ hθ p.2 hp2
      have hfl := hp _ hΘ
      have hJnn : 0 ≤ ‖Work.FTS.StrongEps.Jker ρ ε p‖ := norm_nonneg _
      have hLnn : 0 ≤ |lam (z * Real.exp (-p.1))| := abs_nonneg _
      have hInn : 0 ≤ Ibd α f (z * Real.exp (-p.1)) := Ibd_nonneg α f _
      have hf : |f (z * Real.exp (-p.1)) (Real.arctan (Real.tan θ * Real.exp (-p.2)))|
          ≤ |lam (z * Real.exp (-p.1))|
            + (A * Ibd α f (z * Real.exp (-p.1)) + 1) / 2 := by
        have h1 := abs_add_le
          (f (z * Real.exp (-p.1)) (Real.arctan (Real.tan θ * Real.exp (-p.2)))
            - lam (z * Real.exp (-p.1))) (lam (z * Real.exp (-p.1)))
        simp only [sub_add_cancel] at h1
        linarith
      calc ‖Work.FTS.StrongEps.Jker ρ ε p *
            f (z * Real.exp (-p.1)) (Real.arctan (Real.tan θ * Real.exp (-p.2)))‖
          = ‖Work.FTS.StrongEps.Jker ρ ε p‖ *
            |f (z * Real.exp (-p.1)) (Real.arctan (Real.tan θ * Real.exp (-p.2)))| := by
              rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        _ ≤ ‖Work.FTS.StrongEps.Jker ρ ε p‖ *
            (|lam (z * Real.exp (-p.1))|
              + (A * Ibd α f (z * Real.exp (-p.1)) + 1) / 2) :=
              mul_le_mul_of_nonneg_left hf hJnn
        _ ≤ ‖Work.FTS.StrongEps.Jker ρ ε p‖ *
            (Kb * (|lam (z * Real.exp (-p.1))| + Ibd α f (z * Real.exp (-p.1)) + 1)) := by
              refine mul_le_mul_of_nonneg_left ?_ hJnn
              have hexp : Kb * (|lam (z * Real.exp (-p.1))| + Ibd α f (z * Real.exp (-p.1)) + 1)
                  = Kb * |lam (z * Real.exp (-p.1))| + Kb * Ibd α f (z * Real.exp (-p.1))
                    + Kb := by ring
              have h3 : A * Ibd α f (z * Real.exp (-p.1)) / 2
                  ≤ Kb * Ibd α f (z * Real.exp (-p.1)) := by
                have h4 := mul_le_mul_of_nonneg_right (by linarith : A / 2 ≤ Kb) hInn
                linarith
              have h4 : |lam (z * Real.exp (-p.1))| ≤ Kb * |lam (z * Real.exp (-p.1))| := by
                have h5 := mul_le_mul_of_nonneg_right hKb1 hLnn
                simpa using h5
              have h5 : (1 : ℝ) / 2 ≤ Kb := by linarith
              linarith
        _ = Kb * (‖Work.FTS.StrongEps.Jker ρ ε p‖ *
            (|lam (z * Real.exp (-p.1))| + Ibd α f (z * Real.exp (-p.1)))
            + ‖Work.FTS.StrongEps.Jker ρ ε p‖) := by ring
  have hlimae : ∀ᵐ p ∂(MeasureTheory.volume : Measure (ℝ × ℝ)), Filter.Tendsto
      (fun θ => Work.FTS.StrongEps.Jker ρ ε p *
        f (z * Real.exp (-p.1)) (Real.arctan (Real.tan θ * Real.exp (-p.2))))
      (nhdsWithin (0:ℝ) (Set.Ioi 0))
      (nhds (Work.FTS.StrongEps.Jker ρ ε p * lam (z * Real.exp (-p.1)))) := by
    filter_upwards [htrp] with p hp
    exact Tendsto.const_mul _ (hp.comp (hshift p.2))
  -- dominated convergence
  have hdct : Filter.Tendsto
      (fun θ => ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p *
        f (z * Real.exp (-p.1)) (Real.arctan (Real.tan θ * Real.exp (-p.2))))
      (nhdsWithin (0:ℝ) (Set.Ioi 0))
      (nhds (∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p * lam (z * Real.exp (-p.1)))) :=
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := (MeasureTheory.volume : Measure (ℝ × ℝ)))
      (l := nhdsWithin (0:ℝ) (Set.Ioi 0))
      (F := fun θ p => Work.FTS.StrongEps.Jker ρ ε p *
        f (z * Real.exp (-p.1)) (Real.arctan (Real.tan θ * Real.exp (-p.2))))
      (f := fun p => Work.FTS.StrongEps.Jker ρ ε p * lam (z * Real.exp (-p.1)))
      (fun p : ℝ × ℝ => Kb * (‖Work.FTS.StrongEps.Jker ρ ε p‖ *
        (|lam (z * Real.exp (-p.1))| + Ibd α f (z * Real.exp (-p.1)))
        + ‖Work.FTS.StrongEps.Jker ρ ε p‖))
      hmeas hbound hbdd hlimae
  -- rewrite `Jeps` into the `p`-integral form and the limit into the marginal integral
  have hcoe : ∀ θ ∈ Set.Ioo 0 (Real.pi/2), Work.FTS.StrongEps.Jeps ρ ε f z θ
      = ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p *
          f (z * Real.exp (-p.1)) (Real.arctan (Real.tan θ * Real.exp (-p.2))) := by
    intro θ hθ
    rw [Work.FTS.StrongEps.Jeps_eq_integral ρ ε f hz hθ]
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun p => ?_)
    simp only [Work.FTS.StrongEps.zShift, Work.FTS.StrongEps.thShift]
  have hjeps : Filter.Tendsto (fun θ => Work.FTS.StrongEps.Jeps ρ ε f z θ)
      (nhdsWithin (0:ℝ) (Set.Ioi 0))
      (nhds (∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p * lam (z * Real.exp (-p.1)))) :=
    hdct.congr' (by
      filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < Real.pi/2 by positivity)] with θ hθ
      exact (hcoe θ hθ).symm)
  rw [MarginalTransferIntegrable hρ.moll hε hz hlamm hint] at hjeps
  -- uniqueness of the limit: the trace hypothesis says the same limit is `0`
  exact (tendsto_nhds_unique (hjtr z hz) hjeps).symm

end Work.FTS.StrongEps.EpsLocalPStar
