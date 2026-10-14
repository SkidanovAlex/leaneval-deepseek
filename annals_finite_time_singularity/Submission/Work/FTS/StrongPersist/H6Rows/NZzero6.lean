import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.Psg
import Submission.Work.FTS.OpenPkg.Pieces4
import Submission.Work.FTS.StrongEps.EpsLimitDefs
import Submission.Work.FTS.StrongEps.EpsRHSP_slotSup
import Submission.Work.FTS.StrongEps.EpsRLX.DeltaSlotJeps
import Submission.Work.FTS.StrongEps.PZeroAux.mixed_Pz
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.RhsCont
import Submission.Work.FTS.StrongEps.SmoothOpen_Jeps
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Aux.E2Facts
import Submission.Work.FTS.StrongPersist.H6Rows.NZaux.L12AddFstar
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.radialSupMul_cd6
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.StrongPersist.L3Rhs.N3ssPriced
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBound
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundE
import Submission.Work.FTS.StrongPersist.SP6.RadialSlot6
import Submission.Work.FTS.StrongPersist.StarPkg6Assembly
import Submission.Work.FTS.StrongPersist.Vocab
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.TransportS.sup_dz_le_hk
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux3.L12_slice_eq_zero_of_hkMem_proof =====
section

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
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5G.slice_lip_norm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5G

theorem slice_lip_norm {α T ε B : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g₀ : Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hsol : Work.FTS.StrongEps.IsEpsSolP α ρ ε T Φs E g₀ g)
    (hcont : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      ContinuousOn (fun s : ℝ => Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s z θ) (Set.Icc (0 : ℝ) T))
    (hsmR : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s))
    (h4 : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s))
    (hb4 : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.Spaces.HkNorm α 4 (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s) ≤ B)
    (hslotb : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ (j i : ℕ), j + i ≤ 4 → ∀ p : ℝ × ℝ, p ∈ K →
        |Work.Spaces.mixed j i (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s) p.1 p.2| ≤ C) :
    ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ τ' ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.Nonlin.Xn α (fun z θ => Work.FTS.Galerkin.slice g τ z θ - Work.FTS.Galerkin.slice g τ' z θ)
        ≤ B * |τ - τ'| := by
  intro τ hτ τ' hτ'
  rcases le_total τ' τ with hle | hle
  · have h := slice_lip_ordered hsol hcont hsmR h4 hb4 hslotb hτ hτ' hle
    rw [abs_of_nonneg (sub_nonneg.mpr hle)]
    exact h
  · have h := slice_lip_ordered hsol hcont hsmR h4 hb4 hslotb hτ' hτ hle
    have hneg : Work.Spaces.HkNorm α 4
          (fun z θ => Work.FTS.Galerkin.slice g τ z θ - Work.FTS.Galerkin.slice g τ' z θ)
        = Work.Spaces.HkNorm α 4
          (fun z θ => Work.FTS.Galerkin.slice g τ' z θ - Work.FTS.Galerkin.slice g τ z θ) := by
      rw [show (fun z θ => Work.FTS.Galerkin.slice g τ z θ - Work.FTS.Galerkin.slice g τ' z θ)
            = -(fun z θ => Work.FTS.Galerkin.slice g τ' z θ - Work.FTS.Galerkin.slice g τ z θ)
            from by funext z θ; simp only [Pi.neg_apply]; ring,
        Work.FTS.EllipticEst.HkNorm_neg]
    show Work.Spaces.HkNorm α 4
        (fun z θ => Work.FTS.Galerkin.slice g τ z θ - Work.FTS.Galerkin.slice g τ' z θ)
        ≤ B * |τ - τ'|
    rw [hneg, abs_of_nonpos (sub_nonpos.mpr hle),
      show -(τ - τ') = τ' - τ from by ring]
    exact h

end Work.FTS.StrongEps.E5G
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsHlim =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000


end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.NZzero6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `H6Rows/NZzero6` — the `N`-zero-mode bound `|L₁₂(N)(0)| ≤ K(1+|Ce|+|Cs|)⁴α^{-9}(1+M)⁴`

Elgindi's Proposition `muestimate` (tex 1508--1526) needs the zero mode `L₁₂(N)(0)` of the
nonlinear term `N` of the modulation (`Work.Construction.N`), on the level-six coercivity class
`H6Adm` with the *split* elliptic context `Ell6Ctx`.

## Route

Write `F = F_* + f`, `Ψ = Φs + E f` (`Ell6Ctx.hsum`), `Ξ := PhiTil α F Ψ = Ξ_s + Ξ_p` with
`Ξ_s := PhiTs α Φs`, `Ξ_p := PhiTg α f (E f)` (linearity of `L₁₂` at every `z > 0`,
`NZaux.L12AddFstar`), and group the five terms of `N` by the *slot* `{F, D_θF, D_zF}`:

`N α F Ψ = A₁·F + A₂·D_θF + A₃·D_zF` on the open quadrant, with
`A₁ := 2ℛ(Ξ) - sin²θ·FK F`, `A₂ := -(2𝒰(Ξ)/sin2θ + FK F/2)`, `A₃ := -2α𝒱(Ξ)`

(using `D_θF = sin(2θ)·∂_θF` and `K θ/sin(2θ) = (3/2)cos θ`).  The four majorants
`|ℛ(Ξ)|, |𝒰(Ξ)|, |𝒱(Ξ)|, |FK F| ≤ Kcoef` are `NZaux.NZ_coefs` (where the star parts are priced by
`StarPkgo` and the perturbation parts by `EllPkgGo` + the `ℋ⁴`-Agmon bound
`TransportS.sup_dz_le_hk`, i.e. the paper's Corollary `Linfty`), the pointwise domination of
`|K θ·N|` by the six slots is `NZaux.NZ_pt` (file `NZaux/PtBound.lean`), and the slot bounds
(`FaU f`, `FaU (D_θf)`, `FaU (D_zf)` by `√(π/2)|f|_{ℋ⁴}`, `FAU F_*` etc. by `Cf·α`) plus
`NZaux.Fa_le_slots` (the six-slot additivity of the `L₁₂`-density) give the estimate.
-/

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlinear.Pieces (Fa)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

theorem NZzero6 : ∀ Ce : ℝ, 0 < Ce → ∃ K α₂ : ℝ, 0 < K ∧ 0 < α₂ ∧ α₂ ≤ 1 ∧
    ∀ α ∈ Set.Ioc 0 α₂, ∀ (f Ψ Φs : Work.FTS.Galerkin.Fn) (M Cs : ℝ)
      (E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn),
      Work.FTS.StrongPersist.H6Adm α f → Work.Spaces.HkMem α 7 f →
      Work.FTS.Nonlin.Xn α f ≤ M →
      Work.FTS.StrongPersist.Ell6Ctx α Ce Cs E Φs f Ψ →
      |Work.Construction.L12 (Work.Construction.N α
          (fun z θ => Work.Construction.Fstar α z θ + f z θ) Ψ) 0|
        ≤ K * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(9 : ℝ)) * (1 + M) ^ 4 := by
  intro Ce hCe
  obtain ⟨Cp, hCp0, hCpbd⟩ := NZaux.PertResidPt
  obtain ⟨Cu, hCu0, hCubd⟩ := Work.FTS.NonlinRows.Rl1.starUopBound
  obtain ⟨Cag, hCag0, hCagbd⟩ := Work.FTS.TransportS.sup_dz_le_hk
  obtain ⟨Cf, hCf0, hCfbd⟩ := NZaux.FstarSlotsFa
  set Cp' : ℝ := max Cp 1 with hCp'def
  set Cu' : ℝ := max Cu 1 with hCu'def
  set Cag' : ℝ := max (Cag * 4) 1 with hCag'def
  set Cf' : ℝ := max Cf 1 with hCf'def
  have hCp'0 : 0 < Cp' := lt_of_lt_of_le zero_lt_one (le_max_right Cp 1)
  have hCu'0 : 0 < Cu' := lt_of_lt_of_le zero_lt_one (le_max_right Cu 1)
  have hCag'0 : 0 < Cag' := lt_of_lt_of_le zero_lt_one (le_max_right (Cag * 4) 1)
  have hCf'0 : 0 < Cf' := lt_of_lt_of_le zero_lt_one (le_max_right Cf 1)
  have hCple : Cp ≤ Cp' := le_max_left Cp 1
  have hCule : Cu ≤ Cu' := le_max_left Cu 1
  have hCagle : Cag ≤ Cag' := le_trans (by linarith [hCag0]) (le_max_left (Cag * 4) 1)
  have hCfle : Cf ≤ Cf' := le_max_left Cf 1
  have hApos : 0 < Cp' + Cu' + Cag' + Cf' + 1 := by linarith
  have hBpos : 0 < Real.sqrt (Real.pi / 2) + Cf' := by
    have := Real.sqrt_nonneg (Real.pi / 2); linarith
  have hKpos : 0 < 54000 * (Cp' + Cu' + Cag' + Cf' + 1) * (Real.sqrt (Real.pi / 2) + Cf' + 1) + 1 := by
    have h2 : 0 < Cp' + Cu' + Cag' + Cf' + 1 := by linarith
    have h3 : 0 < Real.sqrt (Real.pi / 2) + Cf' + 1 := by
      have := Real.sqrt_nonneg (Real.pi / 2)
      linarith
    have h4 : 0 < (Cp' + Cu' + Cag' + Cf' + 1) * (Real.sqrt (Real.pi / 2) + Cf' + 1) :=
      mul_pos h2 h3
    nlinarith [h4]
  refine ⟨54000 * (Cp' + Cu' + Cag' + Cf' + 1) * (Real.sqrt (Real.pi / 2) + Cf' + 1) + 1, 1,
    hKpos, one_pos, le_refl 1, ?_⟩
  intro α hα f Ψ Φs M Cs E hreg h7 hM hctx
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hso : Work.FTS.EllipticEst.SmoothOpen f := hreg.reg.1
  have hmem6 : Work.Spaces.HkMem α 6 f := hreg.reg.2
  have hmem4 : Work.Spaces.HkMem α 4 f := Work.FTS.IPGen.HkMem_mono_le hso 4 (by norm_num) hmem6
  have hM0 : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hM
  have hstar : Work.FTS.VocabO.StarPkgo α Cs Φs := hctx.hstar.toStarPkgo
  have hgo : Work.FTS.VocabO.EllPkgGo α Ce f (E f) := hctx.hgo
  -- the pointwise data of the two elliptic packages, with the normalised constants
  have hresR' : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Construction.Rop α (Work.Construction.PhiTil α f (E f)) z θ|
        ≤ Cp' * α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f := by
    intro z θ hz hθ hθ2
    refine le_trans ((hCpbd hα0 hα1 hgo).1 z θ hz hθ hθ2) ?_
    have h0 : 0 ≤ α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f :=
      mul_nonneg (mul_nonneg (Real.rpow_nonneg hα0.le _) hCe.le)
        (Work.Spaces.HkNorm_nonneg α 4 f)
    calc Cp * α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f
        = Cp * (α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f) := by ring
      _ ≤ Cp' * (α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f) :=
          mul_le_mul_of_nonneg_right hCple h0
      _ = Cp' * α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f := by ring
  have hresU' : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Construction.Uop α (Work.Construction.PhiTil α f (E f)) z θ / Work.Construction.s2 θ|
        ≤ Cp' * α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f := by
    intro z θ hz hθ hθ2
    refine le_trans ((hCpbd hα0 hα1 hgo).2.1 z θ hz hθ hθ2) ?_
    have h0 : 0 ≤ α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f :=
      mul_nonneg (mul_nonneg (Real.rpow_nonneg hα0.le _) hCe.le)
        (Work.Spaces.HkNorm_nonneg α 4 f)
    calc Cp * α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f
        = Cp * (α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f) := by ring
      _ ≤ Cp' * (α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f) :=
          mul_le_mul_of_nonneg_right hCple h0
      _ = Cp' * α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f := by ring
  have hresV' : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Construction.Vop (Work.Construction.PhiTil α f (E f)) z θ|
        ≤ Cp' * α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f := by
    intro z θ hz hθ hθ2
    refine le_trans ((hCpbd hα0 hα1 hgo).2.2 z θ hz hθ hθ2) ?_
    have h0 : 0 ≤ α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f :=
      mul_nonneg (mul_nonneg (Real.rpow_nonneg hα0.le _) hCe.le)
        (Work.Spaces.HkNorm_nonneg α 4 f)
    calc Cp * α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f
        = Cp * (α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f) := by ring
      _ ≤ Cp' * (α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f) :=
          mul_le_mul_of_nonneg_right hCple h0
      _ = Cp' * α ^ (-(1 / 2 : ℝ)) * Ce * Work.FTS.Nonlin.Xn α f := by ring
  have hUstar' : ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
      |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ| ≤ Cu' * max Cs 0 * α := by
    intro z θ hz hθI
    refine le_trans (hCubd hα0 hα1 hstar z hz θ hθI) ?_
    have h0 : 0 ≤ max Cs 0 * α := mul_nonneg (le_max_right Cs 0) hα0.le
    calc Cu * max Cs 0 * α = Cu * (max Cs 0 * α) := by ring
      _ ≤ Cu' * (max Cs 0 * α) := mul_le_mul_of_nonneg_right hCule h0
      _ = Cu' * max Cs 0 * α := by ring
  have hsupf' : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |f z θ| ≤ Cag' * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f := by
    intro z θ hz hθ hθ2
    have h := hCagbd α f hα0 hα1 hso hmem4 0 (by norm_num) z θ hz hθ hθ2
    simp only [Work.Spaces.DzIter_zero] at h
    have h0 : 0 ≤ α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f :=
      mul_nonneg (Real.rpow_nonneg hα0.le _) (Work.Spaces.HkNorm_nonneg α 4 f)
    have hsqrt := inv_sqrt_gam_sub_one hα0
    have h10 : Real.sqrt 10 ≤ 4 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 10 by norm_num), Real.sqrt_nonneg 10]
    have hCag4 : Cag * 4 ≤ Cag' := le_max_left (Cag * 4) 1
    calc |f z θ| ≤ Cag * (Real.sqrt (Work.Spaces.gam α - 1))⁻¹ * Work.FTS.Nonlin.Xn α f := by
          rw [div_eq_mul_inv] at h
          exact h
      _ = Cag * (Real.sqrt 10 * α ^ (-(1 / 2 : ℝ))) * Work.FTS.Nonlin.Xn α f := by rw [hsqrt]
      _ = Cag * Real.sqrt 10 * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f) := by ring
      _ ≤ Cag * 4 * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h10 hCag0.le) h0
      _ ≤ Cag' * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f) :=
          mul_le_mul_of_nonneg_right hCag4 h0
      _ = Cag' * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f := by ring
  -- =============== the four coefficient majorants and the pointwise bound
  have hcoef := NZ_coefs (α := α) (M := M) (Ce := Ce) (Cs := Cs) (f := f) (Ef := E f)
    (Φs := Φs) (Cp := Cp') (Cu := Cu') (Cag := Cag') hα0 hα1 hM0 hCe hso hmem4 h7 hM hstar hgo
    hCp'0 hCu'0 hCag'0 hresR' hresU' hresV' hUstar' hsupf'
  have hpt : ∀ r θ : ℝ, 0 < r → 0 < θ → θ < π / 2 →
      |Work.Spaces.K θ * Work.Construction.N α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
          (fun z θ => Φs z θ + E f z θ) r θ|
        ≤ 9 * Kcoef α M Ce Cs Cp' Cu' Cag' * (∑ j : Fin 6, |slots α f j r θ|) := by
    intro r θ hr hθ hθ2
    obtain ⟨h1, h2, h3, h4⟩ := hcoef r θ hr hθ hθ2
    exact NZ_pt hα0 hα1 hM0 hCp'0 hCu'0 hCag'0 hso hr hθ hθ2 h1 h2 h3 h4
  -- =============== the slot continuity
  have hFsm : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.OpenPkg.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)
  have hFdth : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dth (Work.Construction.Fstar α)) :=
    hFsm.Dth
  have hFdz : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz (Work.Construction.Fstar α)) :=
    hFsm.Dz
  have hm : ∀ j : Fin 6, ContinuousOn (Function.uncurry (slots α f j))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    intro j
    fin_cases j <;>
      simp only [slots, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
        Matrix.cons_val]
    · exact hso.continuousOn
    · exact hso.Dth.continuousOn
    · exact hso.Dz.continuousOn
    · exact hFsm.continuousOn
    · exact hFdth.continuousOn
    · exact hFdz.continuousOn
  -- =============== the six slot bounds
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α f := Work.Spaces.HkNorm_nonneg α 4 f
  have hbound : ∀ j : Fin 6, FaU (slots α f j)
      ≤ ENNReal.ofReal (Real.sqrt (Real.pi / 2) * M + Cf' * α) := by
    intro j
    have hc0 : 0 ≤ Real.sqrt (Real.pi / 2) * M + Cf' * α := by
      have h1 := Real.sqrt_nonneg (Real.pi / 2)
      have h2 : 0 ≤ Cf' * α := mul_nonneg hCf'0.le hα0.le
      nlinarith [hM0]
    fin_cases j <;>
      simp only [slots, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
        Matrix.cons_val]
    · refine le_trans (FaU_data_slots hα0 hso hmem4).1 (ENNReal.ofReal_le_ofReal ?_)
      have h1 := Real.sqrt_nonneg (Real.pi / 2)
      have h2 : 0 ≤ Cf' * α := mul_nonneg hCf'0.le hα0.le
      nlinarith [hM, hM0]
    · refine le_trans (FaU_data_slots hα0 hso hmem4).2.1 (ENNReal.ofReal_le_ofReal ?_)
      have h1 := Real.sqrt_nonneg (Real.pi / 2)
      have h2 : 0 ≤ Cf' * α := mul_nonneg hCf'0.le hα0.le
      nlinarith [hM, hM0]
    · refine le_trans (FaU_data_slots hα0 hso hmem4).2.2 (ENNReal.ofReal_le_ofReal ?_)
      have h1 := Real.sqrt_nonneg (Real.pi / 2)
      have h2 : 0 ≤ Cf' * α := mul_nonneg hCf'0.le hα0.le
      nlinarith [hM, hM0]
    · refine le_trans ((hCfbd α hα0 hα1).1) (ENNReal.ofReal_le_ofReal ?_)
      have h1 := Real.sqrt_nonneg (Real.pi / 2)
      have h2 : 0 ≤ Real.sqrt (Real.pi / 2) * M := mul_nonneg h1 hM0
      have h3 : Cf * α ≤ Cf' * α := mul_le_mul_of_nonneg_right hCfle hα0.le
      linarith
    · refine le_trans ((hCfbd α hα0 hα1).2.1) (ENNReal.ofReal_le_ofReal ?_)
      have h1 := Real.sqrt_nonneg (Real.pi / 2)
      have h2 : 0 ≤ Real.sqrt (Real.pi / 2) * M := mul_nonneg h1 hM0
      have h3 : Cf * α ^ 2 ≤ Cf' * α := by
        refine le_trans (mul_le_mul_of_nonneg_left (by nlinarith [hα0, hα1]) hCf0.le)
          (mul_le_mul_of_nonneg_right hCfle hα0.le)
      linarith
    · refine le_trans ((hCfbd α hα0 hα1).2.2) (ENNReal.ofReal_le_ofReal ?_)
      have h1 := Real.sqrt_nonneg (Real.pi / 2)
      have h2 : 0 ≤ Real.sqrt (Real.pi / 2) * M := mul_nonneg h1 hM0
      have h3 : Cf * α ≤ Cf' * α := mul_le_mul_of_nonneg_right hCfle hα0.le
      linarith
  have hslots : (∑ j : Fin 6, FaU (slots α f j))
      ≤ ENNReal.ofReal (6 * (Real.sqrt (Real.pi / 2) * M + Cf' * α)) := by
    refine le_trans (Finset.sum_le_sum (fun j _ => hbound j)) ?_
    have h6 : ((6 : ℕ) : ℝ≥0∞) = ENNReal.ofReal 6 := (ENNReal.ofReal_natCast 6).symm
    rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, h6,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 6)]
  -- =============== the `Fa` bound
  have hFa := Fa_le_slots (Kc := 9 * Kcoef α M Ce Cs Cp' Cu' Cag')
    (N := Work.Construction.N α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
      (fun z θ => Φs z θ + E f z θ)) (G := slots α f)
    (by
      have h : (0 : ℝ) < Kcoef α M Ce Cs Cp' Cu' Cag' :=
        Kcoef_pos hα0 hCp'0 hCu'0 hCag'0 hM0
      linarith) hpt hm
  have hFa2 : Fa (Work.Construction.N α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
        (fun z θ => Φs z θ + E f z θ))
      ≤ ENNReal.ofReal (9 * Kcoef α M Ce Cs Cp' Cu' Cag'
          * (6 * (Real.sqrt (Real.pi / 2) * M + Cf' * α))) := by
    refine le_trans hFa ?_
    have hA0 : (0 : ℝ) ≤ 9 * Kcoef α M Ce Cs Cp' Cu' Cag' := by
      have h : (0 : ℝ) < Kcoef α M Ce Cs Cp' Cu' Cag' :=
        Kcoef_pos hα0 hCp'0 hCu'0 hCag'0 hM0
      linarith
    have hof : ENNReal.ofReal (9 * Kcoef α M Ce Cs Cp' Cu' Cag'
          * (6 * (Real.sqrt (Real.pi / 2) * M + Cf' * α)))
        = ENNReal.ofReal (9 * Kcoef α M Ce Cs Cp' Cu' Cag')
          * ENNReal.ofReal (6 * (Real.sqrt (Real.pi / 2) * M + Cf' * α)) :=
      ENNReal.ofReal_mul hA0
    rw [hof]
    exact mul_le_mul_of_nonneg_left hslots
      (by positivity : (0 : ℝ≥0∞) ≤ ENNReal.ofReal (9 * Kcoef α M Ce Cs Cp' Cu' Cag'))
  -- =============== the quantitative conclusion
  have hKbadge0 : 0 ≤ (54000 * (Cp' + Cu' + Cag' + Cf' + 1)
      * (Real.sqrt (Real.pi / 2) + Cf' + 1) + 1) * (1 + |Ce| + |Cs|) ^ 4
      * α ^ (-(9 : ℝ)) * (1 + M) ^ 4 := by
    have h1 : (0 : ℝ) ≤ 54000 * (Cp' + Cu' + Cag' + Cf' + 1)
        * (Real.sqrt (Real.pi / 2) + Cf' + 1) + 1 := hKpos.le
    have h2 : (0 : ℝ) ≤ (1 + |Ce| + |Cs|) ^ 4 := by positivity
    have h3 : (0 : ℝ) ≤ α ^ (-(9 : ℝ)) := Real.rpow_nonneg hα0.le _
    have h4 : (0 : ℝ) ≤ (1 + M) ^ 4 := by positivity
    exact mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) h4
  have hL12 := Work.FTS.Nonlinear.Pieces.ofReal_L12_le
    (Work.Construction.N α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
      (fun z θ => Φs z θ + E f z θ))
  have hbig : ENNReal.ofReal |Work.Construction.L12 (Work.Construction.N α
        (fun z θ => Work.Construction.Fstar α z θ + f z θ)
        (fun z θ => Φs z θ + E f z θ)) 0|
      ≤ ENNReal.ofReal ((54000 * (Cp' + Cu' + Cag' + Cf' + 1)
          * (Real.sqrt (Real.pi / 2) + Cf' + 1) + 1) * (1 + |Ce| + |Cs|) ^ 4
          * α ^ (-(9 : ℝ)) * (1 + M) ^ 4) := by
    refine le_trans hL12 (le_trans hFa2 ?_)
    exact ENNReal.ofReal_le_ofReal
      (NZ_arith hα0 hα1 hM0 hCf'0 hCp'0 hCu'0 hCag'0)
  exact (ENNReal.ofReal_le_ofReal_iff hKbadge0).mp (by
    rw [hctx.hsum]
    exact hbig)

end Work.FTS.StrongPersist.H6Rows
end
end
