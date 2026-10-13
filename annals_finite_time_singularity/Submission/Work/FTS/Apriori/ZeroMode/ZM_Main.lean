/-
# The `L₁₂` zero-mode identity: the main computation

This file assembles the identity `L₁₂(𝓛_Γ f)(0) = -L₁₂(f)(0)` from the pieces proved in the
sibling files.  The hypotheses of `zm_main` are exactly the ingredients furnished by those
pieces:

* `ZM_slice_relation` (a.e. fibre FTC, `θ`-slice integrability, `∫_θ K f = -NOf`);
* `ZM_Nfun_zero`, `ZM_Nfun_limits` (the boundary values/limits of `NOf` and `ROf`);
* `ZM_mderiv_fubini` (Fubini for `mdOf`);
* `ZM_IBP_R` (integration by parts for `ROf`);
* `ZM_density_ae` (the a.e. identity `G - u = md - 2u/(1+r) - 2R/(1+r)²`).

The argument: put `w r = NOf f r - 2 ROf f r/(1+r)`.  Integrating the a.e. identity over
`(ε,ρ]` and using Fubini + integration by parts gives `∫_{(ε,ρ]}(G-u) = w ε - w ρ`; letting
`ρ → ∞` (using `NOf → 0`, `ROf/(1+r) → 0`) gives `∫_{(ε,∞)}(G-u) = w ε`; letting `ε → 0⁺`
(using `NOf 0 = 0` and `ROf 0 = ∫₀^∞ L₁₂dens f`) gives
`∫_{(0,∞)}(G-u) = -2∫₀^∞L₁₂dens f`, i.e. `L₁₂(𝓛_Γ f)(0) = -L₁₂(f)(0)`.
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.Apriori.ZeroMode.L12_ZMDefs
import Submission.Work.FTS.Apriori.ZeroMode.ZM_Limits_L1

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Apriori.ZeroMode

set_option autoImplicit false

/-- **The main computation of the `L₁₂` zero-mode identity.** -/
theorem zm_main {α : ℝ} {f : ℝ → ℝ → ℝ} (H : L12Hyp α f)
    (hslice : ∀ r : ℝ, 0 < r →
      MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.K θ * f r θ) Work.Spaces.Iθ)
    (hrel : ∀ r : ℝ, 0 < r → r * uOf f r = - NOf f r)
    (hNcont : ContinuousOn (NOf f) (Set.Ici 0))
    (hNtop : Filter.Tendsto (NOf f) Filter.atTop (𝓝 0))
    (hR0 : Filter.Tendsto (ROf f) (𝓝[>] (0:ℝ)) (𝓝 (ROf f 0)))
    (hRtop : Filter.Tendsto (fun r : ℝ => ROf f r / (1 + r)) Filter.atTop (𝓝 0))
    (hN0 : NOf f 0 = 0)
    (hmdInt : MeasureTheory.IntegrableOn (mdOf f) (Set.Ioi 0))
    (hmdIoc : ∀ ε ρ : ℝ, 0 < ε → ε < ρ →
      ∫ r in Set.Ioc ε ρ, mdOf f r = NOf f ε - NOf f ρ)
    (hibp : ∀ ε ρ : ℝ, 0 < ε → ε < ρ →
      ∫ r in Set.Ioc ε ρ, ROf f r / (1 + r) ^ 2
        = -(ROf f ρ / (1 + ρ)) + ROf f ε / (1 + ε)
          - ∫ r in Set.Ioc ε ρ, uOf f r / (1 + r))
    (hae : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      GOf α f r - uOf f r = mdOf f r - 2 * uOf f r / (1 + r) - 2 * ROf f r / (1 + r) ^ 2)
    (hGint : MeasureTheory.IntegrableOn (GOf α f) (Set.Ioi 0))
    (huint : MeasureTheory.IntegrableOn (uOf f) (Set.Ioi 0)) :
    Work.Construction.L12 (Work.Coercivity.LGamma α f) 0 = - Work.Construction.L12 f 0 := by
  have hL12G : Work.Construction.L12 (Work.Coercivity.LGamma α f) 0
      = ∫ r in Set.Ioi 0, GOf α f r := rfl
  have hL12f : Work.Construction.L12 f 0 = ∫ r in Set.Ioi 0, uOf f r := rfl
  rw [hL12G, hL12f]
  have hdiffint : IntegrableOn (fun r : ℝ => GOf α f r - uOf f r) (Set.Ioi 0) :=
    hGint.sub huint
  -- ### integrability of the pieces on `(ε,ρ]`
  have hI_md : ∀ ε ρ : ℝ, 0 < ε → IntegrableOn (mdOf f) (Set.Ioc ε ρ) :=
    fun ε ρ hε => hmdInt.mono_set fun _ hx => lt_trans hε hx.1
  have hI_u : ∀ ε ρ : ℝ, 0 < ε →
      IntegrableOn (fun r : ℝ => uOf f r / (1 + r)) (Set.Ioc ε ρ) := by
    intro ε ρ hε
    have hsub : Set.Ioc ε ρ ⊆ Set.Ioi 0 := fun x hx => lt_trans hε hx.1
    have hg : Integrable (fun r : ℝ => ‖uOf f r‖) (volume.restrict (Set.Ioc ε ρ)) :=
      (huint.mono_set hsub).norm
    have hmeas : AEStronglyMeasurable (fun r : ℝ => uOf f r / (1 + r))
        (volume.restrict (Set.Ioc ε ρ)) := by
      have h1 : AEStronglyMeasurable (fun r : ℝ => uOf f r)
          (volume.restrict (Set.Ioc ε ρ)) := (huint.mono_set hsub).aestronglyMeasurable
      have h2 : AEStronglyMeasurable (fun r : ℝ => (1:ℝ) / (1 + r))
          (volume.restrict (Set.Ioc ε ρ)) :=
        (continuousOn_const.div (continuousOn_const.add continuousOn_id)
          (fun x hx => by
            have hx0 := hx.1
            simp only [Pi.add_apply, id_eq]
            linarith)).aestronglyMeasurable measurableSet_Ioc
      refine AEStronglyMeasurable.congr (h1.mul h2) ?_
      filter_upwards with r
      rw [Pi.mul_apply, one_div, div_eq_mul_inv]
    refine hg.mono' hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hr1 : (0:ℝ) < 1 + r := by have := hr.1; linarith
    have h1r : (1:ℝ) ≤ 1 + r := by have := hr.1; linarith
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_of_pos hr1]
    exact div_le_self (abs_nonneg _) h1r
  have hI_2u : ∀ ε ρ : ℝ, 0 < ε →
      IntegrableOn (fun r : ℝ => 2 * (uOf f r / (1 + r))) (Set.Ioc ε ρ) :=
    fun ε ρ hε =>
      (show Integrable (fun r : ℝ => uOf f r / (1 + r)) (volume.restrict (Set.Ioc ε ρ)) from
        hI_u ε ρ hε).const_mul 2
  have hI_2u' : ∀ ε ρ : ℝ, 0 < ε →
      IntegrableOn (fun r : ℝ => 2 * uOf f r / (1 + r)) (Set.Ioc ε ρ) :=
    fun ε ρ hε => (hI_2u ε ρ hε).congr (Eventually.of_forall fun r => by ring)
  -- the whole right-hand side is integrable on `(ε,ρ]` because it is a.e. `G - u`
  have hI_A : ∀ ε ρ : ℝ, 0 < ε → ε < ρ →
      IntegrableOn (fun r : ℝ => mdOf f r - 2 * uOf f r / (1 + r)
        - 2 * ROf f r / (1 + r) ^ 2) (Set.Ioc ε ρ) :=
    fun ε ρ hε _ => (hdiffint.mono_set (fun x hx => lt_trans hε hx.1)).congr
      (ae_restrict_of_ae_restrict_of_subset (fun x hx => lt_trans hε hx.1) hae)
  have hI_B : ∀ ε ρ : ℝ, 0 < ε →
      IntegrableOn (fun r : ℝ => mdOf f r - 2 * uOf f r / (1 + r)) (Set.Ioc ε ρ) :=
    fun ε ρ hε => (hI_md ε ρ hε).sub (hI_2u' ε ρ hε)
  have hI_R : ∀ ε ρ : ℝ, 0 < ε → ε < ρ →
      IntegrableOn (fun r : ℝ => 2 * ROf f r / (1 + r) ^ 2) (Set.Ioc ε ρ) := by
    intro ε ρ hε hερ
    have h := (hI_A ε ρ hε hερ).sub (hI_B ε ρ hε)
    refine h.neg.congr ?_
    filter_upwards with r
    simp only [Pi.neg_apply, Pi.sub_apply]
    ring
  -- ### the strip identity
  have hstrip : ∀ ε ρ : ℝ, 0 < ε → ε < ρ →
      ∫ r in Set.Ioc ε ρ, (GOf α f r - uOf f r)
        = (NOf f ε - 2 * ROf f ε / (1 + ε)) - (NOf f ρ - 2 * ROf f ρ / (1 + ρ)) := by
    intro ε ρ hε hερ
    have hae' : ∀ᵐ r ∂(volume.restrict (Set.Ioc ε ρ)),
        GOf α f r - uOf f r
          = mdOf f r - 2 * uOf f r / (1 + r) - 2 * ROf f r / (1 + r) ^ 2 :=
      ae_restrict_of_ae_restrict_of_subset (fun x hx => lt_trans hε hx.1) hae
    rw [integral_congr_ae hae']
    rw [integral_sub (hI_B ε ρ hε) (hI_R ε ρ hε hερ), integral_sub (hI_md ε ρ hε) (hI_2u' ε ρ hε)]
    rw [show (∫ r in Set.Ioc ε ρ, 2 * uOf f r / (1 + r))
          = 2 * ∫ r in Set.Ioc ε ρ, uOf f r / (1 + r) from by
        rw [← integral_const_mul]; exact MeasureTheory.integral_congr_ae (Eventually.of_forall fun r => by ring),
      show (∫ r in Set.Ioc ε ρ, 2 * ROf f r / (1 + r) ^ 2)
          = 2 * ∫ r in Set.Ioc ε ρ, ROf f r / (1 + r) ^ 2 from by
        rw [← integral_const_mul]; exact MeasureTheory.integral_congr_ae (Eventually.of_forall fun r => by ring)]
    rw [hmdIoc ε ρ hε hερ, hibp ε ρ hε hερ]
    ring
  -- ### the limit `ρ → ∞`
  have hlim_rho : ∀ ε : ℝ, 0 < ε →
      ∫ r in Set.Ioi ε, (GOf α f r - uOf f r) = NOf f ε - 2 * ROf f ε / (1 + ε) := by
    intro ε hε
    have hg : IntegrableOn (fun r : ℝ => GOf α f r - uOf f r) (Set.Ioi ε) :=
      hdiffint.mono_set (Set.Ioi_subset_Ioi (le_of_lt hε))
    have h1 : Tendsto (fun ρ : ℝ => ∫ r in Set.Ioc ε ρ, (GOf α f r - uOf f r)) atTop
        (𝓝 (∫ r in Set.Ioi ε, (GOf α f r - uOf f r))) := zm_tendsto_Ioc_atTop hg
    have h2 : Tendsto (fun ρ : ℝ => (NOf f ε - 2 * ROf f ε / (1 + ε))
        - (NOf f ρ - 2 * ROf f ρ / (1 + ρ))) atTop
        (𝓝 (NOf f ε - 2 * ROf f ε / (1 + ε))) := by
      have h4 : Tendsto (fun ρ : ℝ => 2 * ROf f ρ / (1 + ρ)) atTop (𝓝 0) := by
        have h5 : Tendsto (fun ρ : ℝ => 2 * (ROf f ρ / (1 + ρ))) atTop (𝓝 (2 * (0:ℝ))) :=
          hRtop.const_mul 2
        rw [mul_zero] at h5
        refine h5.congr' ?_
        filter_upwards with ρ
        ring
      have h3 : Tendsto (fun ρ : ℝ => NOf f ρ - 2 * ROf f ρ / (1 + ρ)) atTop (𝓝 0) := by
        have h6 := hNtop.sub h4
        simpa using h6
      simpa using (tendsto_const_nhds.sub h3)
    have h3 : Tendsto (fun ρ : ℝ => ∫ r in Set.Ioc ε ρ, (GOf α f r - uOf f r)) atTop
        (𝓝 (NOf f ε - 2 * ROf f ε / (1 + ε))) := by
      refine h2.congr' ?_
      filter_upwards [Ioi_mem_atTop ε] with ρ hρ
      exact (hstrip ε ρ hε hρ).symm
    exact tendsto_nhds_unique h1 h3
  -- ### the limit `ε → 0⁺` of the tails
  have hlim_eps : Tendsto (fun ε : ℝ => ∫ r in Set.Ioi ε, (GOf α f r - uOf f r))
      (𝓝[>] (0:ℝ)) (𝓝 (∫ r in Set.Ioi 0, (GOf α f r - uOf f r))) := by
    have h1 : Tendsto (fun ε : ℝ => (∫ r in Set.Ioi 0, (GOf α f r - uOf f r))
        - (∫ r in Set.Ioc 0 ε, (GOf α f r - uOf f r))) (𝓝[>] (0:ℝ))
        (𝓝 ((∫ r in Set.Ioi 0, (GOf α f r - uOf f r)) - 0)) :=
      tendsto_const_nhds.sub (zm_tendsto_Ioc_zero hdiffint)
    have h1' : Tendsto (fun ε : ℝ => (∫ r in Set.Ioi 0, (GOf α f r - uOf f r))
        - (∫ r in Set.Ioc 0 ε, (GOf α f r - uOf f r))) (𝓝[>] (0:ℝ))
        (𝓝 (∫ r in Set.Ioi 0, (GOf α f r - uOf f r))) := by
      simpa using h1
    refine h1'.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have h2 : (∫ r in Set.Ioc 0 ε, (GOf α f r - uOf f r))
        + (∫ r in Set.Ioi ε, (GOf α f r - uOf f r))
        = ∫ r in Set.Ioi 0, (GOf α f r - uOf f r) := by
      have h3 := intervalIntegral.integral_interval_add_Ioi
        (f := fun r : ℝ => GOf α f r - uOf f r) (a := 0) (b := ε) hdiffint
        (hdiffint.mono_set (Set.Ioi_subset_Ioi (le_of_lt hε)))
      rwa [intervalIntegral.integral_of_le (le_of_lt hε)] at h3
    linarith
  -- ### the limit `ε → 0⁺` of the boundary terms
  have hlim_w : Tendsto (fun ε : ℝ => NOf f ε - 2 * ROf f ε / (1 + ε)) (𝓝[>] (0:ℝ))
      (𝓝 (-2 * ∫ r in Set.Ioi 0, uOf f r)) := by
    have hc : ContinuousWithinAt (NOf f) (Set.Ioi 0) 0 :=
      (hNcont.continuousWithinAt (by simp)).mono (Set.Ioi_subset_Ici_self)
    have h1 : Tendsto (NOf f) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      have h := hc.tendsto
      rw [hN0] at h
      exact h
    have h2 : Tendsto (fun ε : ℝ => 2 * ROf f ε / (1 + ε)) (𝓝[>] (0:ℝ))
        (𝓝 (2 * ∫ r in Set.Ioi 0, uOf f r)) := by
      have hROf0 : ROf f 0 = ∫ r in Set.Ioi 0, uOf f r := rfl
      have h5 : Tendsto (fun ε : ℝ => 2 * (ROf f ε / (1 + ε))) (𝓝[>] (0:ℝ))
          (𝓝 (2 * ROf f 0)) := by
        have hden : Tendsto (fun ε : ℝ => 1 + ε) (𝓝[>] (0:ℝ)) (𝓝 (1 + (0:ℝ))) :=
          tendsto_const_nhds.add
            ((tendsto_id : Tendsto (fun x : ℝ => x) (𝓝 (0:ℝ)) (𝓝 0)).mono_left
              nhdsWithin_le_nhds)
        have h := (hR0.div hden (by norm_num)).const_mul 2
        simpa using h
      rw [hROf0] at h5
      refine h5.congr' ?_
      filter_upwards with ε
      ring
    have h3 := h1.sub h2
    simpa using h3
  -- ### conclusion
  have hfinal : ∫ r in Set.Ioi 0, (GOf α f r - uOf f r) = -2 * ∫ r in Set.Ioi 0, uOf f r := by
    have h1 : Tendsto (fun ε : ℝ => NOf f ε - 2 * ROf f ε / (1 + ε)) (𝓝[>] (0:ℝ))
        (𝓝 (∫ r in Set.Ioi 0, (GOf α f r - uOf f r))) := by
      refine hlim_eps.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact hlim_rho ε hε
    exact tendsto_nhds_unique h1 hlim_w
  have hsub : (∫ r in Set.Ioi 0, (GOf α f r - uOf f r))
      = (∫ r in Set.Ioi 0, GOf α f r) - (∫ r in Set.Ioi 0, uOf f r) :=
    integral_sub hGint huint
  rw [hsub] at hfinal
  linarith

end Work.FTS.Apriori.ZeroMode
