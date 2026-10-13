import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongEps.EpsCorrTendsto
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.E5Aux3.L12_slice_eq_zero_of_IsEpsSolP
import Submission.Work.FTS.StrongEps.E5Aux3.hasDerivWithinAt_L12_slice_of_majorant
import Submission.Work.FTS.StrongEps.E5Aux2.L12_epsRHSP_zero
import Submission.Work.FTS.GalBasis.cc.L12_add_of_HkMem
import Submission.Work.FTS.StrongEps.RhsCont
import Submission.Work.FTS.GalBasis.cc.integral_abs_L12dens_le_Ioi
import Submission.Work.Spaces.integrable_prod_of_iterated
import Submission.Work.FTS.StrongEps.E5Aux3.epsRHSP_dens_aesm_slice
import Submission.Work.FTS.StrongEps.E5Aux3.epsRHSP_dens_aesm_prod
import Submission.Work.FTS.StrongEps.E5Aux3.integrable_angleDens_of_hkMem
import Submission.Work.FTS.StrongEps.E5Aux3.integrableOn_L12dens_of_aem

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5Aux3

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-!
# Conservation of the `L₁₂`-zero mode along a `P₀`-solution, from `ℋ⁴` data

The route (a Fubini/Volterra argument, avoiding any `σ`-uniform majorant — which the
hypotheses do **not** supply, only the *uniform* `ℋ⁴` bound `B` on the scheme's right-hand
side):

    L₁₂ (slice g τ) 0 − L₁₂ g₀ 0
      = ∫_r ∫_θ ∫_σ K θ · (∂_σ g)(r,θ,σ) / r
      = ∫_σ ∫_r ∫_θ K θ · epsRHSP σ r θ / r      (Fubini, using the uniform bound B)
      = ∫_σ L₁₂ (epsRHSP σ) 0 = 0                (the projection kills every zero mode)
-/

theorem L12_slice_eq_zero_of_hkMem_proof {α ε T : ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {g₀ : Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam} {B : ℝ}
    (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε) (hT : 0 < T)
    (hsol : Work.FTS.StrongEps.IsEpsSolP α ρ ε T Φs E g₀ g)
    (hc1 : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Icc 0 T))
    (hsm : ∀ τ ∈ Set.Icc 0 T, Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Galerkin.slice g τ))
    (hmem : ∀ τ ∈ Set.Icc 0 T, Work.Spaces.HkMem α 4 (Work.FTS.Galerkin.slice g τ))
    (hRm : ∀ τ ∈ Set.Icc 0 T,
      Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g τ) ∧
        Work.Spaces.HkNorm α 4 (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g τ) ≤ B)
    (hWm : ∀ τ ∈ Set.Icc 0 T, Work.Spaces.HkMem α 4
      (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g τ)))
    (h0 : Work.Construction.L12 g₀ 0 = 0) :
    ∀ τ ∈ Set.Icc 0 T, Work.Construction.L12 (Work.FTS.Galerkin.slice g τ) 0 = 0 := by
  intro τ hτ
  have hT0 : (0 : ℝ) ≤ T := le_of_lt hT
  have hτ0 : (0 : ℝ) ≤ τ := hτ.1
  have hτT : τ ≤ T := hτ.2
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_refl 0, hT0⟩
  -- ### the measures and the abbreviated objects
  set μr : Measure ℝ := volume.restrict (Set.Ioi (0 : ℝ)) with hμr
  set μθ : Measure ℝ := volume.restrict Work.Spaces.Iθ with hμθ
  set μpx : Measure (ℝ × ℝ) := μr.prod μθ with hμpx
  set μσ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) τ) with hμσ
  set F : ℝ → ℝ → ℝ → ℝ := fun σ z θ => Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g σ z θ with hF
  -- ### the slice at fake time `0` is the datum
  have hslice0 : Work.FTS.Galerkin.slice g 0 = g₀ :=
    funext fun z => funext fun θ => hsol.1 z θ
  -- ### integrability of the plain `L₁₂`-densities
  have hval : ∀ τ' ∈ Set.Icc (0 : ℝ) T,
      Integrable (Work.Construction.L12dens (Work.FTS.Galerkin.slice g τ')) μr :=
    fun τ' hτ' => Work.FTS.GalBasis.cc.integrableOn_L12dens_of_SmoothOpen_HkMem
      (hsm τ' hτ') (hmem τ' hτ')
  -- ### the fundamental theorem of calculus in the fake time, at a fixed point of the quadrant
  have hFTC : ∀ r θ : ℝ, 0 < r → θ ∈ Set.Ioo 0 (π / 2) →
      ∫ σ in (0 : ℝ)..τ, F σ r θ = g r θ τ - g r θ 0 := by
    intro r θ hr hθ
    have hcontR : ContinuousOn (fun σ : ℝ => F σ r θ) (Set.Icc (0 : ℝ) T) :=
      Work.FTS.StrongEps.continuousOn_rhs_of_contDiffOn_one hT hc1
        (fun z θ' σ hz hθ' hσ => hsol.2 z θ' σ hz hθ' hσ) r θ hr hθ
    have hcontg : ContinuousOn (fun s : ℝ => g r θ s) (Set.Icc (0 : ℝ) τ) := by
      have hmap : ContinuousOn (fun s : ℝ => (r, (θ, s))) (Set.Icc (0 : ℝ) τ) :=
        (continuous_const.prodMk (continuous_const.prodMk continuous_id)).continuousOn
      have hcomp := hc1.continuousOn.comp hmap
        (fun s hs => ⟨hr, hθ, ⟨hs.1, le_trans hs.2 hτT⟩⟩)
      exact hcomp.congr (fun s _ => rfl)
    have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) τ, HasDerivAt (fun s : ℝ => g r θ s) (F x r θ) x := by
      intro x hx
      have hxI : x ∈ Set.Icc (0 : ℝ) T := ⟨hx.1.le, le_trans hx.2.le hτT⟩
      exact (hsol.2 r θ x hr hθ hxI).hasDerivAt (Icc_mem_nhds hx.1 (lt_of_lt_of_le hx.2 hτT))
    have hint : IntervalIntegrable (fun σ : ℝ => F σ r θ) volume (0 : ℝ) τ := by
      have h1 : ContinuousOn (fun σ : ℝ => F σ r θ) (Set.uIcc (0 : ℝ) τ) := by
        rw [Set.uIcc_of_le hτ0]
        exact hcontR.mono (Set.Icc_subset_Icc le_rfl hτT)
      exact h1.intervalIntegrable
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hτ0 hcontg hderiv hint
  -- ### measurability of the density integrand, for interior fake times
  have hmeasSlice : ∀ σ ∈ Set.Ioo (0 : ℝ) T, ∀ r ∈ Set.Ioi (0 : ℝ),
      AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.K θ * F σ r θ / r) μθ :=
    fun σ hσ r hr => aeStronglyMeasurable_K_mul_epsRHSP_slice hsol hc1 hr hσ
  -- ### interior fake times have full measure
  have haeIoo : ∀ᵐ σ ∂μσ, σ ∈ Set.Ioo (0 : ℝ) T := by
    rw [hμσ, MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    rw [MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null
      (s := {x : ℝ | ¬ (x ∈ Set.Ioc (0 : ℝ) τ → x ∈ Set.Ioo (0 : ℝ) T)}) (t := {T}) ?_ ?_
    · intro x hx
      simp only [Set.mem_ofPred_eq, not_imp] at hx
      obtain ⟨hx1, hx2⟩ := hx
      rcases lt_trichotomy x T with h | h | h
      · exact absurd ⟨hx1.1, h⟩ hx2
      · exact Set.mem_singleton_iff.mpr h
      · exact absurd (le_trans hx1.2 hτT) (not_le.mpr h)
    · simp
  -- ### the `(r,θ)`-product integrability of the density at an interior fake time
  have hI3 : ∀ σ ∈ Set.Ioo (0 : ℝ) T,
      Integrable (fun p : ℝ × ℝ => Work.Spaces.K p.2 * F σ p.1 p.2 / p.1) μpx := by
    intro σ hσ
    have hσIcc : σ ∈ Set.Icc (0 : ℝ) T := ⟨hσ.1.le, hσ.2.le⟩
    have hslice : ∀ᵐ r ∂μr,
        AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.K θ * F σ r θ / r) μθ := by
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with r hr
      exact hmeasSlice σ hσ r hr
    exact (integrable_angleDens_of_hkMem (F := F σ) (hRm σ hσIcc).1
      (epsRHSP_dens_aesm_slice hsol hc1 hσ) hslice).1
  -- ### the uniform bound on the integrated density
  have hbound : ∀ σ ∈ Set.Ioo (0 : ℝ) T,
      (∫ p : ℝ × ℝ, ‖Work.Spaces.K p.2 * F σ p.1 p.2 / p.1‖ ∂μpx)
        ≤ 3 * Real.sqrt (π / 2) * Real.sqrt Work.FTS.GalBasis.cc.W2 * B := by
    intro σ hσ
    have hσIcc : σ ∈ Set.Icc (0 : ℝ) T := ⟨hσ.1.le, hσ.2.le⟩
    have hslice : ∀ᵐ r ∂μr,
        AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.K θ * F σ r θ / r) μθ := by
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with r hr
      exact hmeasSlice σ hσ r hr
    have h := (integrable_angleDens_of_hkMem (F := F σ) (hRm σ hσIcc).1
      (epsRHSP_dens_aesm_slice hsol hc1 hσ) hslice).2
    have hnn : (0 : ℝ) ≤ 3 * Real.sqrt (π / 2) * Real.sqrt Work.FTS.GalBasis.cc.W2 := by
      positivity
    exact le_trans h (mul_le_mul_of_nonneg_left (hRm σ hσIcc).2 hnn)
  -- ### the three-variable measurability on `μσ × μpx`
  have hsubσ : Set.Ioc (0 : ℝ) τ ⊆ Set.Icc (0 : ℝ) T :=
    fun x hx => ⟨hx.1.le, le_trans hx.2 hτT⟩
  have hAE3 : AEStronglyMeasurable
      (fun q : ℝ × (ℝ × ℝ) => Work.Spaces.K q.2.2 * F q.1 q.2.1 q.2.2 / q.2.1)
      (μσ.prod μpx) :=
    (epsRHSP_dens_aesm_prod hsol hc1).mono_measure
      (MeasureTheory.Measure.prod_mono
        (MeasureTheory.Measure.restrict_mono hsubσ le_rfl) le_rfl)
  -- ### integrability of the absolute value on `μσ × μpx`
  have hHintNorm : Integrable
      (fun q : ℝ × (ℝ × ℝ) => ‖Work.Spaces.K q.2.2 * F q.1 q.2.1 q.2.2 / q.2.1‖)
      (μσ.prod μpx) := by
    have hsliceN : ∀ᵐ σ ∂μσ, Integrable
        (fun p : ℝ × ℝ => ‖Work.Spaces.K p.2 * F σ p.1 p.2 / p.1‖) μpx := by
      filter_upwards [haeIoo] with σ hσ
      exact (hI3 σ hσ).norm
    have houterN : Integrable
        (fun σ : ℝ => ∫ p : ℝ × ℝ, ‖Work.Spaces.K p.2 * F σ p.1 p.2 / p.1‖ ∂μpx) μσ := by
      refine MeasureTheory.Integrable.mono'
        (MeasureTheory.integrable_const
          (3 * Real.sqrt (π / 2) * Real.sqrt Work.FTS.GalBasis.cc.W2 * B))
        hAE3.norm.integral_prod_right' ?_
      filter_upwards [haeIoo] with σ hσ
      rw [Real.norm_of_nonneg (MeasureTheory.integral_nonneg fun p => norm_nonneg _)]
      exact hbound σ hσ
    exact (Work.Spaces.integrable_prod_of_iterated (μ := μσ) (ν := μpx)
      (G := fun σ p => ‖Work.Spaces.K p.2 * F σ p.1 p.2 / p.1‖)
      (fun _ _ => norm_nonneg _) hAE3.norm hsliceN houterN).1
  -- ### integrability of the signed integrand on `μσ × μpx`
  have hHint : Integrable
      (fun q : ℝ × (ℝ × ℝ) => Work.Spaces.K q.2.2 * F q.1 q.2.1 q.2.2 / q.2.1)
      (μσ.prod μpx) :=
    ⟨hAE3, hHintNorm.hasFiniteIntegral.mono'
      (Filter.Eventually.of_forall fun q => le_refl _)⟩
  -- ### the same, on `μpx × μσ` (swap of the product measure)
  have hHint' : Integrable
      (fun z : (ℝ × ℝ) × ℝ => Work.Spaces.K z.1.2 * F z.2 z.1.1 z.1.2 / z.1.1)
      (μpx.prod μσ) := by
    have key : Integrable
        (fun q : ℝ × (ℝ × ℝ) => Work.Spaces.K q.2.2 * F q.1 q.2.1 q.2.2 / q.2.1)
        (Measure.map Prod.swap (μpx.prod μσ)) := by
      rw [MeasureTheory.Measure.prod_swap]
      exact hHint
    exact key.comp_measurable measurable_swap
  -- ### the iterated `(p,σ)` integrability
  have hI2 : Integrable
      (fun p : ℝ × ℝ => ∫ σ : ℝ, Work.Spaces.K p.2 * F σ p.1 p.2 / p.1 ∂μσ) μpx := by
    refine ⟨hHint'.aestronglyMeasurable.integral_prod_right', ?_⟩
    refine HasFiniteIntegral.mono'
      ((MeasureTheory.integrable_prod_iff hHint'.aestronglyMeasurable).mp hHint').2.hasFiniteIntegral
      (Filter.Eventually.of_forall fun p => MeasureTheory.norm_integral_le_integral_norm _)
  -- ### the left-hand side is the triple iterated integral
  have hA : Work.Construction.L12 (Work.FTS.Galerkin.slice g τ) 0
        - Work.Construction.L12 (Work.FTS.Galerkin.slice g 0) 0
      = ∫ r : ℝ, ∫ θ : ℝ, (∫ σ : ℝ, Work.Spaces.K θ * F σ r θ / r ∂μσ) ∂μθ ∂μr := by
    have hL12 : ∀ f : ℝ → ℝ → ℝ, Work.Construction.L12 f 0
        = ∫ s : ℝ, Work.Construction.L12dens f s ∂μr := fun f => rfl
    rw [hL12, hL12, ← MeasureTheory.integral_sub (hval τ hτ) (hval 0 h0mem)]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with r hr
    have hsτ : Integrable (fun θ : ℝ => Work.Spaces.K θ * g r θ τ / r) μθ :=
      Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem (hsm τ hτ) (hmem τ hτ) hr
    have hs0 : Integrable (fun θ : ℝ => Work.Spaces.K θ * g r θ 0 / r) μθ :=
      Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem (hsm 0 h0mem)
        (hmem 0 h0mem) hr
    have e1 : Work.Construction.L12dens (Work.FTS.Galerkin.slice g τ) r
        = ∫ θ : ℝ, Work.Spaces.K θ * g r θ τ / r ∂μθ := rfl
    have e2 : Work.Construction.L12dens (Work.FTS.Galerkin.slice g 0) r
        = ∫ θ : ℝ, Work.Spaces.K θ * g r θ 0 / r ∂μθ := rfl
    rw [e1, e2, ← MeasureTheory.integral_sub hsτ hs0]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [ae_mem_Ioo_Icc] with θ hθ
    have h1 : (∫ σ : ℝ, Work.Spaces.K θ * F σ r θ / r ∂μσ)
        = Work.Spaces.K θ * (g r θ τ - g r θ 0) / r := by
      have hsub : (∫ σ : ℝ, Work.Spaces.K θ * F σ r θ / r ∂μσ)
          = ∫ σ in (0 : ℝ)..τ, Work.Spaces.K θ * F σ r θ / r :=
        (intervalIntegral.integral_of_le hτ0).symm
      rw [hsub]
      have hfac : ∀ σ : ℝ,
          Work.Spaces.K θ * F σ r θ / r = (Work.Spaces.K θ / r) * F σ r θ := by
        intro σ; ring
      simp only [hfac]
      rw [intervalIntegral.integral_const_mul, hFTC r θ hr hθ]
      ring
    rw [h1]
    ring
  -- ### Fubini: `(r,θ)` versus the product measure, then the σ-swap
  have hB : (∫ r : ℝ, ∫ θ : ℝ, (∫ σ : ℝ, Work.Spaces.K θ * F σ r θ / r ∂μσ) ∂μθ ∂μr)
      = ∫ p : ℝ × ℝ, (∫ σ : ℝ, Work.Spaces.K p.2 * F σ p.1 p.2 / p.1 ∂μσ) ∂μpx :=
    MeasureTheory.integral_integral (μ := μr) (ν := μθ)
      (f := fun r θ => ∫ σ : ℝ, Work.Spaces.K θ * F σ r θ / r ∂μσ) hI2
  have hC : (∫ p : ℝ × ℝ, (∫ σ : ℝ, Work.Spaces.K p.2 * F σ p.1 p.2 / p.1 ∂μσ) ∂μpx)
      = ∫ σ : ℝ, (∫ p : ℝ × ℝ, Work.Spaces.K p.2 * F σ p.1 p.2 / p.1 ∂μpx) ∂μσ :=
    MeasureTheory.integral_integral_swap (μ := μpx) (ν := μσ)
      (f := fun p σ => Work.Spaces.K p.2 * F σ p.1 p.2 / p.1) hHint'
  have hD : (∫ σ : ℝ, (∫ p : ℝ × ℝ, Work.Spaces.K p.2 * F σ p.1 p.2 / p.1 ∂μpx) ∂μσ)
      = ∫ σ : ℝ, Work.Construction.L12 (F σ) 0 ∂μσ := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [haeIoo] with σ hσ
    rw [MeasureTheory.integral_prod
      (fun p : ℝ × ℝ => Work.Spaces.K p.2 * F σ p.1 p.2 / p.1) (hI3 σ hσ)]
    rfl
  -- ### each projected right-hand side has vanishing zero mode
  have hzero : ∀ σ ∈ Set.Ioo (0 : ℝ) T, Work.Construction.L12 (F σ) 0 = 0 := by
    intro σ hσ
    have hσIcc : σ ∈ Set.Icc (0 : ℝ) T := ⟨hσ.1.le, hσ.2.le⟩
    have hslice : ∀ᵐ r ∂μr,
        AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.K θ * F σ r θ / r) μθ := by
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with r hr
      exact hmeasSlice σ hσ r hr
    have hD3 := integrable_angleDens_of_hkMem (F := F σ) (hRm σ hσIcc).1
      (epsRHSP_dens_aesm_slice hsol hc1 hσ) hslice
    have hdensMeas : AEStronglyMeasurable (Work.Construction.L12dens (F σ)) μr :=
      (epsRHSP_dens_aesm_slice hsol hc1 hσ).integral_prod_right'
    have hdens : MeasureTheory.IntegrableOn (Work.Construction.L12dens (F σ)) (Set.Ioi 0) :=
      integrableOn_L12dens_of_aem (F := F σ) (hRm σ hσIcc).1 hdensMeas
    have hsl : ∀ᵐ r ∂μr, MeasureTheory.IntegrableOn
        (fun θ : ℝ => Work.Spaces.K θ * F σ r θ / r) Work.Spaces.Iθ :=
      ((MeasureTheory.integrable_prod_iff (epsRHSP_dens_aesm_slice hsol hc1 hσ)).mp hD3.1).1
    exact Work.FTS.StrongEps.E5Aux2.L12_epsRHSP_zero hdens hsl
  -- ### the σ-integral vanishes
  have hInt : ∫ σ : ℝ, Work.Construction.L12 (F σ) 0 ∂μσ = 0 := by
    rw [MeasureTheory.integral_congr_ae (haeIoo.mono fun σ hσ => hzero σ hσ)]
    simp
  -- ### assemble
  have hmain : Work.Construction.L12 (Work.FTS.Galerkin.slice g τ) 0
      - Work.Construction.L12 (Work.FTS.Galerkin.slice g 0) 0
      = ∫ σ in (0 : ℝ)..τ, Work.Construction.L12 (F σ) 0 := by
    rw [hA, hB, hC, hD]
    exact (intervalIntegral.integral_of_le hτ0).symm
  have h2 : Work.Construction.L12 (Work.FTS.Galerkin.slice g τ) 0
      - Work.Construction.L12 g₀ 0 = 0 := by
    rw [← hslice0, hmain, intervalIntegral.integral_of_le hτ0]
    exact hInt
  have h3 : Work.Construction.L12 (Work.FTS.Galerkin.slice g τ) 0
      = Work.Construction.L12 g₀ 0 := sub_eq_zero.mp h2
  rw [h3, h0]

end Work.FTS.StrongEps.E5Aux3
