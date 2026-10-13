import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.AeI1Fts.N_bound
import Submission.Work.FTS.EllipticEst.SliceMixedAux.smoothCutoffIoo
import Submission.Work.FTS.EllipticEst.AeI1Fts.Defs
import Submission.Work.FTS.EllipticEst.AeI1Fts.slice_rate
import Submission.Work.FTS.EllipticEst.AeI1Fts.identity_defs
import Submission.Work.FTS.EllipticEst.TT.AeI1.aeDzTraceHk
import Submission.Work.FTS.EllipticEst.RPFresh.HkMem_of_agreeOnQ
import Submission.Work.RPFresh.slice_sq_le
import Submission.Work.RPFresh.slice_sq_le_right

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end


/-!
# `AeI1Fts/psiDeriv_setup` - helper lemmas for `psiDeriv_tendsto_zero`

All the analytic scaffolding of the target `psiDeriv_tendsto_zero`: the pointwise angular
facts, the slicewise integrability of `sigma U^2` and `sigma V^2`, the Clairaut transfer of the
mixed honesty, the a.e. endpoint bounds for the slice of `U u`, the a.e. strong measurability of
the inner `theta`-integral, the vanishing of the layer energies, the support of `(chi_eps)'` and
the elementary arithmetic used in the assembly.
-/
/-!
# `AeI1Fts/psiDeriv_tendsto_zero`

The `θ`-layer (boundary) term of the angular integration by parts with the cut-off
`χ_ε = SliceMixedAux.cut ε` vanishes as `ε → 0⁺`:

`∫_z cut n z · w z² · ∫_θ σ θ (χ_ε)' θ (U u z θ · V u z θ) dθ dz ⟶ 0`,

where `U u = z ∂_z u`, `V u = z ∂_z ∂_θ u = ∂_θ (U u)` (Clairaut) and `σ = sigE θ = sin(2θ)^{-η}`.

## Route

* `(χ_ε)'` is supported in `(ε/2,ε) ∪ (π/2-ε,π/2-ε/2)` and `|(χ_ε)'| ≤ 2M/ε` where `M` bounds
  `|prof'|`; hence the `θ`-integral is bounded by `(2M/ε)(L + R)` with `L`, `R` the two layer
  integrals of `σ|U||V|`.
* On each layer Cauchy–Schwarz gives `∫_layer σ|U||V| ≤ √(∫_layer σU²)√(∫_layer σV²)`
  (`Work.FTS.EllipticEst.AeI1Fts.layer_inner_le`), and the *sharp* endpoint bound for the slice
  of `U` (`Work.RPFresh.slice_sq_le` on the left, `Work.RPFresh.slice_sq_le_right` on the right,
  both with the explicit constant `2^η/(1+η)` and the *total* `σ`-energy `∫_θ σ V²`) gives
  `√(∫_layer σU²) ≤ ε √(2^η(π/4)^η/(2(1+η))) √(∫_θ σV²)`.  The `1/ε` cancels and the remaining
  factor is `√(∫_{(0,ε)} σV²) + √(∫_{(π/2-ε,π/2)} σV²) ⟶ 0`.
* The trace hypothesis `U u z · → 0` at both endpoints is `TT.AeI1.aeDzTraceHk` (a.e. in `z`).
* The `z`-integration is a dominated convergence with dominating function
  `4M · cut n z · w z² · ∫_θ σ V²`, integrable by `HkMem α 0 (V u)`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AeI1Fts

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

local notation "Iθo" => Set.Ioo (0 : ℝ) (Real.pi / 2)

/-! ## Pointwise angular facts -/

/-- `σ θ = sin(2θ)^{-η}` is continuous on the open interval. -/
theorem continuousOn_sigE : ContinuousOn sigE Iθo := by
  have h1 : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) Iθo :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  refine h1.rpow_const (fun θ hθ => Or.inl ?_)
  exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos]))

/-- The radial weight `w` is continuous on `(0,∞)`. -/
theorem continuousOn_w_Ioi : ContinuousOn (fun z : ℝ => Work.Spaces.w z) (Set.Ioi 0) := by
  rw [show (fun z : ℝ => Work.Spaces.w z) = fun z => (1 + z) ^ 2 / z ^ 2 from rfl]
  refine ContinuousOn.div ?_ ?_ ?_
  · exact (continuousOn_const.add continuousOn_id).pow 2
  · exact continuousOn_id.pow 2
  · intro z hz
    exact pow_ne_zero 2 (ne_of_gt hz)

/-- `w²` is a.e. strongly measurable on `(0,∞)`. -/
theorem aestronglyMeasurable_w_sq :
    AEStronglyMeasurable (fun z : ℝ => (Work.Spaces.w z) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
  (continuousOn_w_Ioi.pow 2).aestronglyMeasurable measurableSet_Ioi

/-! ## `σ U²` and `σ V²` are slicewise integrable -/

/-- The `θ`-slice of the `σ`-energy of an honestly `ℋ⁰` datum is integrable. -/
theorem integrableOn_sq_sigE {α : ℝ} {f : ℝ → ℝ → ℝ} (hf : Work.Spaces.HkMem α 0 f)
    {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => (f z θ) ^ 2 * sigE θ) Work.Spaces.Iθ := by
  have h1 : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 0 f z θ)
      Work.Spaces.Iθ := hf.1 z (le_of_lt hz)
  have h2 : MeasureTheory.IntegrableOn
      (fun θ => (f z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ :=
    h1.congr_fun (fun θ hθ => (Work.FTS.EllipticEst.TT.AeI1.HkIntegrand_zero_eq α f hθ))
      measurableSet_Icc
  have hw : (Work.Spaces.w z) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (ne_of_gt (Work.FTS.EllipticEst.TT.AeI1.w_pos_of_pos hz))
  refine MeasureTheory.IntegrableOn.congr_fun (h2.const_mul ((Work.Spaces.w z) ^ 2)⁻¹)
    ?_ measurableSet_Icc
  intro θ _
  show ((Work.Spaces.w z) ^ 2)⁻¹
      * ((f z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ)
    = (f z θ) ^ 2 * sigE θ
  rw [show Work.FTS.EllipticEst.sEta θ = sigE θ from rfl]
  rw [show ((Work.Spaces.w z) ^ 2)⁻¹
        * ((f z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * sigE θ)
      = (((Work.Spaces.w z) ^ 2)⁻¹ * (Work.Spaces.w z) ^ 2)
        * ((f z θ) ^ 2 * sigE θ) from by ring,
    inv_mul_cancel₀ hw, one_mul]

/-! ## The mixed honesty of `V u` -/

/-- `V u = z ∂_z ∂_θ u` and `z ∂_θ∂_z u` agree on the open quadrant (Clairaut), so `HkMem`
transfers. -/
theorem hkMem_pz_pth {α : ℝ} {u : ℝ → ℝ → ℝ} (hS : SmoothOpen u)
    (hV : Work.Spaces.HkMem α 0 (V u)) :
    Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pth (Work.Spaces.pz u) z θ) :=
  Work.FTS.EllipticEst.RPFresh.HkMem_of_agreeOnQ (f := V u) (fun z θ hz hθ0 hθπ => by
    show z * Work.Spaces.pz (Work.Spaces.pth u) z θ = z * Work.Spaces.pth (Work.Spaces.pz u) z θ
    rw [Work.Spaces.pz_pth_comm (contDiffAt_uncurry hS hz ⟨hθ0, hθπ⟩ 2)]) hV

/-! ## The a.e. slice bound for `U u` -/

/-- **The two endpoint bounds for the slice of `U u = z ∂_z u`**, a.e. in `z`, together with
the slicewise integrability of `σ U²` and `σ V²`.

Both bounds are the sharp boundary-rate estimates of `Work.RPFresh.slice_sq_le` and its mirror
`slice_sq_le_right`, with the explicit constant `2^η/(1+η)` and the total slice energy
`∫_θ σ V²`; the trace hypothesis is `TT.AeI1.aeDzTraceHk`. -/
theorem sliceBoundAe {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hU : Work.Spaces.HkMem α 0 (U u)) (hV : Work.Spaces.HkMem α 0 (V u)) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      (∀ θ ∈ Iθo, (U u z θ) ^ 2
          ≤ (2 ^ Work.Spaces.eta / (1 + Work.Spaces.eta))
              * (∫ θ' in Iθo, (V u z θ') ^ 2 * sigE θ') * θ ^ (1 + Work.Spaces.eta))
      ∧ (∀ θ ∈ Iθo, (U u z θ) ^ 2
          ≤ (2 ^ Work.Spaces.eta / (1 + Work.Spaces.eta))
              * (∫ θ' in Iθo, (V u z θ') ^ 2 * sigE θ')
              * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta))
      ∧ MeasureTheory.IntegrableOn (fun θ => (U u z θ) ^ 2 * sigE θ) Iθo
      ∧ MeasureTheory.IntegrableOn (fun θ => (V u z θ) ^ 2 * sigE θ) Iθo := by
  have hS : SmoothOpen u := smoothOpen_of_forall h.smooth
  have hMix := hkMem_pz_pth hS hV
  have htr := Work.FTS.EllipticEst.TT.AeI1.aeDzTraceHk α u G h hU hMix
  filter_upwards [htr, MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hztr hz
  have hzpos : 0 < z := hz
  have hsub : Iθo ⊆ Work.Spaces.Iθ := fun θ hθ => ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hUintIθ : MeasureTheory.IntegrableOn (fun θ => (U u z θ) ^ 2 * sigE θ) Work.Spaces.Iθ :=
    integrableOn_sq_sigE hU hzpos
  have hVintIθ : MeasureTheory.IntegrableOn (fun θ => (V u z θ) ^ 2 * sigE θ) Work.Spaces.Iθ :=
    integrableOn_sq_sigE hV hzpos
  have hUint : MeasureTheory.IntegrableOn (fun θ => (U u z θ) ^ 2 * sigE θ) Iθo :=
    hUintIθ.mono_set hsub
  have hVint : MeasureTheory.IntegrableOn (fun θ => (V u z θ) ^ 2 * sigE θ) Iθo :=
    hVintIθ.mono_set hsub
  have hcd : ContDiffOn ℝ 1 (fun θ => U u z θ) Iθo := contDiffOn_slice_U_one hS hzpos
  -- the interval integrand of the two slice estimates
  have hint : MeasureTheory.IntegrableOn
      (fun θ => Work.FTS.EllipticEst.RPFresh.sg θ * (deriv (fun θ' => U u z θ') θ) ^ 2)
      Iθo :=
    hVint.congr_fun (fun θ hθ => by
      show (V u z θ) ^ 2 * sigE θ
        = Work.FTS.EllipticEst.RPFresh.sg θ * (deriv (fun θ' => U u z θ') θ) ^ 2
      rw [slice_deriv_U hS hzpos hθ]
      rw [show Work.FTS.EllipticEst.RPFresh.sg θ = sigE θ from rfl]
      ring) measurableSet_Ioo
  -- the interval integral is the total slice energy
  have hE : (∫ t in (0 : ℝ)..(Real.pi / 2),
        Work.FTS.EllipticEst.RPFresh.sg t * (deriv (fun θ' => U u z θ') t) ^ 2)
      = ∫ θ' in Iθo, (V u z θ') ^ 2 * sigE θ' := by
    rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2),
      MeasureTheory.integral_Ioc_eq_integral_Ioo]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ hθ => ?_)
    rw [slice_deriv_U hS hzpos hθ]
    rw [show Work.FTS.EllipticEst.RPFresh.sg θ = sigE θ from rfl]
    ring
  refine ⟨?_, ?_, hUint, hVint⟩
  · intro θ hθ
    have hbd := Work.RPFresh.slice_sq_le (fun θ' => U u z θ') hcd hztr.1 hint θ hθ
    rw [hE] at hbd
    calc (U u z θ) ^ 2
        ≤ (∫ θ' in Iθo, (V u z θ') ^ 2 * sigE θ')
            * (2 ^ Work.Spaces.eta * θ ^ (1 + Work.Spaces.eta) / (1 + Work.Spaces.eta)) := hbd
      _ = (2 ^ Work.Spaces.eta / (1 + Work.Spaces.eta))
            * (∫ θ' in Iθo, (V u z θ') ^ 2 * sigE θ') * θ ^ (1 + Work.Spaces.eta) := by ring
  · intro θ hθ
    have hbd : (U u z θ) ^ 2
        ≤ (∫ θ' in Iθo, (V u z θ') ^ 2 * sigE θ')
            * (2 ^ Work.Spaces.eta * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta)
                / (1 + Work.Spaces.eta)) := by
      have hs := Work.RPFresh.slice_sq_le_right (fun θ' => U u z θ') hcd hztr.2 hint θ hθ
      rw [hE] at hs
      exact hs
    calc (U u z θ) ^ 2
        ≤ (∫ θ' in Iθo, (V u z θ') ^ 2 * sigE θ')
            * (2 ^ Work.Spaces.eta * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta)
                / (1 + Work.Spaces.eta)) := hbd
      _ = (2 ^ Work.Spaces.eta / (1 + Work.Spaces.eta))
            * (∫ θ' in Iθo, (V u z θ') ^ 2 * sigE θ')
            * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta) := by ring

/-! ## Measurability of the inner integral -/

/-- The inner `θ`-integral of the target is a.e. strongly measurable in `z`. -/
theorem aestronglyMeasurable_inner {u : ℝ → ℝ → ℝ} (hS : SmoothOpen u) (ε : ℝ) :
    AEStronglyMeasurable (fun z => ∫ θ in Iθo,
        sigE θ * deriv (Work.FTS.EllipticEst.SliceMixedAux.cut ε) θ * (U u z θ * V u z θ))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
  have hcut : Continuous (deriv (Work.FTS.EllipticEst.SliceMixedAux.cut ε)) :=
    (Work.FTS.EllipticEst.SliceMixedAux.cut_contDiff ε).continuous_deriv (by norm_num)
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ => sigE p.2 * deriv (Work.FTS.EllipticEst.SliceMixedAux.cut ε) p.2
        * (Function.uncurry (U u) p * Function.uncurry (V u) p))
      (Set.Ioi 0 ×ˢ Iθo) := by
    refine ContinuousOn.mul (ContinuousOn.mul ?_ ?_) ?_
    · exact continuousOn_sigE.comp continuous_snd.continuousOn (fun p hp => hp.2)
    · exact hcut.comp_continuousOn continuous_snd.continuousOn
    · exact (continuousOn_U hS).mul (continuousOn_V hS)
  have hmain : AEStronglyMeasurable
      (fun p : ℝ × ℝ => sigE p.2 * deriv (Work.FTS.EllipticEst.SliceMixedAux.cut ε) p.2
        * (Function.uncurry (U u) p * Function.uncurry (V u) p))
      ((MeasureTheory.volume.prod MeasureTheory.volume).restrict (Set.Ioi 0 ×ˢ Iθo)) :=
    hcont.aestronglyMeasurable (isOpen_Ioi.prod isOpen_Ioo).measurableSet
  rw [← MeasureTheory.Measure.prod_restrict] at hmain
  refine (hmain.integral_prod_right').congr (Filter.Eventually.of_forall fun z => ?_)
  rfl

/-! ## The layer energies tend to zero -/

/-- The two shrinking layer integrals of an integrable angular function tend to `0`. -/
theorem tendsto_layerEnergy_zero {f : ℝ → ℝ}
    (hf : MeasureTheory.IntegrableOn f Iθo) :
    Filter.Tendsto (fun ε : ℝ => ∫ θ in Set.Ioo 0 ε, f θ)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)
      ∧ Filter.Tendsto (fun ε : ℝ => ∫ θ in Set.Ioo (Real.pi / 2 - ε) (Real.pi / 2), f θ)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hpi4 : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hsmall : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), ε < Real.pi / 4 :=
    nhdsWithin_le_nhds (isOpen_Iio.mem_nhds hpi4)
  have hid : Filter.Tendsto (fun ε : ℝ => ε) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
    (tendsto_id : Filter.Tendsto (fun ε : ℝ => ε) (nhds 0) (nhds 0)).mono_left
      nhdsWithin_le_nhds
  constructor
  · have hμ : Filter.Tendsto
        (fun ε : ℝ => (MeasureTheory.volume.restrict Iθo) (Set.Ioo 0 ε))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      refine Tendsto.congr' ?_ (by simpa using ENNReal.tendsto_ofReal hid)
      filter_upwards [hsmall] with ε hε
      have hsub : Set.Ioo 0 ε ⊆ Iθo :=
        fun t ht => ⟨ht.1, by linarith [ht.2, hε, Real.pi_pos]⟩
      rw [Measure.restrict_apply measurableSet_Ioo,
        Set.inter_eq_left.mpr hsub, Real.volume_Ioo, sub_zero]
    have h := hf.tendsto_setIntegral_nhds_zero (l := nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (s := fun ε : ℝ => Set.Ioo 0 ε) hμ
    refine Tendsto.congr' (hsmall.mono fun ε hε => ?_) h
    show (∫ θ in Set.Ioo 0 ε, f θ ∂(MeasureTheory.volume.restrict Iθo))
        = ∫ θ in Set.Ioo 0 ε, f θ
    have hsub2 : Set.Ioo 0 ε ⊆ Iθo :=
      fun t ht => ⟨ht.1, by linarith [ht.2, hε, Real.pi_pos]⟩
    rw [Measure.restrict_restrict_of_subset hsub2]
  · have hμ : Filter.Tendsto
        (fun ε : ℝ =>
          (MeasureTheory.volume.restrict Iθo) (Set.Ioo (Real.pi / 2 - ε) (Real.pi / 2)))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      refine Tendsto.congr' ?_ (by simpa using ENNReal.tendsto_ofReal hid)
      filter_upwards [hsmall] with ε hε
      have hsub : Set.Ioo (Real.pi / 2 - ε) (Real.pi / 2) ⊆ Iθo :=
        fun t ht => ⟨by linarith [hε, ht.1, Real.pi_pos], ht.2⟩
      rw [Measure.restrict_apply measurableSet_Ioo,
        Set.inter_eq_left.mpr hsub,
        Real.volume_Ioo, show Real.pi / 2 - (Real.pi / 2 - ε) = ε by ring]
    have h := hf.tendsto_setIntegral_nhds_zero (l := nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (s := fun ε : ℝ => Set.Ioo (Real.pi / 2 - ε) (Real.pi / 2)) hμ
    refine Tendsto.congr' (hsmall.mono fun ε hε => ?_) h
    show (∫ θ in Set.Ioo (Real.pi / 2 - ε) (Real.pi / 2),
          f θ ∂(MeasureTheory.volume.restrict Iθo))
        = ∫ θ in Set.Ioo (Real.pi / 2 - ε) (Real.pi / 2), f θ
    have hsub2 : Set.Ioo (Real.pi / 2 - ε) (Real.pi / 2) ⊆ Iθo :=
      fun t ht => ⟨by linarith [hε, ht.1, Real.pi_pos], ht.2⟩
    rw [Measure.restrict_restrict_of_subset hsub2]

/-! ## The radial cut-off is measurable -/

theorem measurable_cut (n : ℕ) : Measurable (Work.FTS.EllipticEst.cut n) := by
  show Measurable (fun z : ℝ =>
    Real.smoothTransition ((n + 1 : ℝ) * z - 1)
      * (1 - Real.smoothTransition (z / (n + 1 : ℝ) - 2)))
  have h1 : Continuous (fun z : ℝ => Real.smoothTransition ((n + 1 : ℝ) * z - 1)) :=
    Real.smoothTransition.continuous.comp
      ((continuous_const.mul continuous_id).sub continuous_const)
  have h2 : Continuous (fun z : ℝ => Real.smoothTransition (z / (n + 1 : ℝ) - 2)) :=
    Real.smoothTransition.continuous.comp ((continuous_id.div_const _).sub continuous_const)
  exact (h1.mul (continuous_const.sub h2)).measurable

/-! ## The support of `(χ_ε)'` -/

/-- `(χ_ε)'` vanishes on the open middle interval `(ε, π/2-ε)`, and on `(0,π/2)` it is dominated
by `2S₁/ε` on the two layer intervals `[0,ε]`, `[π/2-ε,π/2]` (the indicators `1_{θ ≤ ε}` and
`1_{π/2-ε ≤ θ}` are added, so that the right-hand side is `2S₁/ε` everywhere, which is the
sharp bound `SliceMixedAux.abs_deriv_cut_le` off the middle interval). -/
theorem deriv_cut_support {ε S₁ : ℝ} (hε : 0 < ε) (hεπ : ε ≤ Real.pi / 4)
    (hS₁ : ∀ s : ℝ, |deriv Work.FTS.EllipticEst.SliceMixedAux.prof s| ≤ S₁) :
    (∀ θ ∈ Set.Ioo ε (Real.pi / 2 - ε),
        deriv (Work.FTS.EllipticEst.SliceMixedAux.cut ε) θ = 0)
    ∧ (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |deriv (Work.FTS.EllipticEst.SliceMixedAux.cut ε) θ|
        ≤ (2 * S₁ / ε) * ((Set.Iic ε).indicator (fun _ => (1 : ℝ)) θ
            + (Set.Ici (Real.pi / 2 - ε)).indicator (fun _ => (1 : ℝ)) θ)) := by
  have hS₁0 : 0 ≤ S₁ := le_trans (abs_nonneg _) (hS₁ 0)
  have hK : 0 ≤ 2 * S₁ / ε := by positivity
  have hmid : ∀ θ ∈ Set.Ioo ε (Real.pi / 2 - ε),
      deriv (Work.FTS.EllipticEst.SliceMixedAux.cut ε) θ = 0 := by
    intro θ hθ
    rw [Work.FTS.EllipticEst.SliceMixedAux.deriv_cut]
    have h1 : (1 : ℝ) < θ / ε := (lt_div_iff₀ hε).mpr (by linarith [hθ.1])
    have h2 : (1 : ℝ) < (Real.pi / 2 - θ) / ε := (lt_div_iff₀ hε).mpr (by linarith [hθ.2])
    rw [Work.FTS.EllipticEst.SliceMixedAux.prof_deriv_eq_zero_of_notMem
          (s := θ / ε) (by
            rw [Set.mem_Icc, not_and_or]
            exact Or.inr (not_le.mpr h1)),
      Work.FTS.EllipticEst.SliceMixedAux.prof_deriv_eq_zero_of_notMem
          (s := (Real.pi / 2 - θ) / ε) (by
            rw [Set.mem_Icc, not_and_or]
            exact Or.inr (not_le.mpr h2))]
    ring
  refine ⟨hmid, fun θ hθ => ?_⟩
  have hindnn : ∀ s : Set ℝ, 0 ≤ s.indicator (fun _ => (1 : ℝ)) θ := by
    intro s
    by_cases h : θ ∈ s
    · simp only [Set.indicator_of_mem h]; norm_num
    · simp only [Set.indicator_of_notMem h]; norm_num
  have hcut := Work.FTS.EllipticEst.SliceMixedAux.abs_deriv_cut_le hε hS₁ θ
  by_cases hle : θ ≤ ε
  · have h1 : (Set.Iic ε).indicator (fun _ => (1 : ℝ)) θ = 1 :=
      Set.indicator_of_mem (s := Set.Iic ε) hle _
    rw [h1]
    calc |deriv (Work.FTS.EllipticEst.SliceMixedAux.cut ε) θ| ≤ 2 * S₁ / ε := hcut
      _ = (2 * S₁ / ε) * 1 := (mul_one _).symm
      _ ≤ (2 * S₁ / ε) * (1 + (Set.Ici (Real.pi / 2 - ε)).indicator (fun _ => (1 : ℝ)) θ) :=
          mul_le_mul_of_nonneg_left (by linarith [hindnn (Set.Ici (Real.pi / 2 - ε))]) hK
  · have hgt : ε < θ := not_le.mp hle
    by_cases hge : Real.pi / 2 - ε ≤ θ
    · have h1 : (Set.Ici (Real.pi / 2 - ε)).indicator (fun _ => (1 : ℝ)) θ = 1 :=
        Set.indicator_of_mem (s := Set.Ici (Real.pi / 2 - ε)) hge _
      rw [h1]
      calc |deriv (Work.FTS.EllipticEst.SliceMixedAux.cut ε) θ| ≤ 2 * S₁ / ε := hcut
        _ = (2 * S₁ / ε) * 1 := (mul_one _).symm
        _ ≤ (2 * S₁ / ε) * ((Set.Iic ε).indicator (fun _ => (1 : ℝ)) θ + 1) :=
            mul_le_mul_of_nonneg_left (by linarith [hindnn (Set.Iic ε)]) hK
    · have hlt : θ < Real.pi / 2 - ε := not_le.mp hge
      rw [hmid θ ⟨hgt, hlt⟩]
      simp only [abs_zero]
      exact mul_nonneg hK (add_nonneg (hindnn _) (hindnn _))

/-! ## Auxiliary arithmetic -/

theorem sqrt_layer_le {A AL AR : ℝ} (hAL : 0 ≤ AL) (hAR : 0 ≤ AR)
    (hALle : AL ≤ A) (hARle : AR ≤ A) (hA : 0 ≤ A) :
    Real.sqrt AL + Real.sqrt AR ≤ 2 * Real.sqrt A := by
  have h1 : Real.sqrt AL ≤ Real.sqrt A := Real.sqrt_le_sqrt hALle
  have h2 : Real.sqrt AR ≤ Real.sqrt A := Real.sqrt_le_sqrt hARle
  linarith [Real.sqrt_nonneg A]

theorem layer_arith {M K A L : ℝ} (hM : 0 ≤ M) (hK0 : 0 ≤ K) (hK1 : K ≤ 1)
    (hA : 0 ≤ A) (hL0 : 0 ≤ L) (hL : L ≤ 2 * Real.sqrt A) :
    2 * M * K * Real.sqrt A * L ≤ 4 * M * A := by
  have h1 : 2 * M * K * Real.sqrt A ≤ 2 * M * 1 * Real.sqrt A := by
    have h3 : (0 : ℝ) ≤ 2 * M := by linarith
    have := mul_le_mul_of_nonneg_left hK1 h3
    exact mul_le_mul_of_nonneg_right this (Real.sqrt_nonneg A)
  have h4 : (0 : ℝ) ≤ 2 * M * 1 * Real.sqrt A := by positivity
  have h5 : 2 * M * 1 * Real.sqrt A * L ≤ 2 * M * 1 * Real.sqrt A * (2 * Real.sqrt A) :=
    mul_le_mul_of_nonneg_left hL h4
  have hs : Real.sqrt A * Real.sqrt A = A := Real.mul_self_sqrt hA
  calc 2 * M * K * Real.sqrt A * L ≤ 2 * M * 1 * Real.sqrt A * L :=
        mul_le_mul_of_nonneg_right h1 hL0
    _ ≤ 2 * M * 1 * Real.sqrt A * (2 * Real.sqrt A) := h5
    _ = 4 * M * A := by
        rw [show (2 * M * 1 * Real.sqrt A) * (2 * Real.sqrt A)
            = 4 * M * (Real.sqrt A * Real.sqrt A) by ring, hs]

end Work.FTS.EllipticEst.AeI1Fts
