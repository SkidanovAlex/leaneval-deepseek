import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.TransportS.SupDzAux.SdaAux
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.uncurry_partial_c1
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.HonSliceRightTendsto =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## Elementary facts about the angular weight `σ = sEta` -/

theorem sin_two_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem sin_two_le_one (θ : ℝ) : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _

/-- `σ > 0` on the open interval. -/
theorem sEta_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < Work.FTS.EllipticEst.sEta θ := by
  have hs : 0 < Real.sin (2 * θ) := sin_two_pos_of_mem_Ioo hθ
  simpa only [Work.FTS.EllipticEst.sEta] using Real.rpow_pos_of_pos hs (-(Work.Spaces.eta))

/-- On `Iθ`, `σ⁻¹ = sin(2θ)^{η} ≤ 1`. -/
theorem inv_sEta_le_one {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.FTS.EllipticEst.sEta θ)⁻¹ ≤ 1 := by
  have hne : -(Work.Spaces.eta) ≠ 0 := by
    have : (0 : ℝ) < Work.Spaces.eta := by norm_num [Work.Spaces.eta]
    linarith
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  rcases eq_or_lt_of_le hθ.1 with h0 | h0
  · rw [← h0, Work.FTS.EllipticEst.sEta]
    simp only [mul_zero, Real.sin_zero]
    rw [Real.zero_rpow hne]
    norm_num
  · rcases eq_or_lt_of_le hθ.2 with hpi | hpi
    · rw [hpi, Work.FTS.EllipticEst.sEta]
      have hzero : Real.sin (2 * (Real.pi / 2)) = 0 := by
        rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
      rw [hzero, Real.zero_rpow hne]
      norm_num
    · have hs0 : 0 ≤ Real.sin (2 * θ) :=
        sin_two_nonneg_of_mem_Iθ ⟨le_of_lt h0, le_of_lt hpi⟩
      have hs1 : Real.sin (2 * θ) ≤ 1 := sin_two_le_one θ
      have hη : 0 ≤ Work.Spaces.eta := by norm_num [Work.Spaces.eta]
      have hinv : (Work.FTS.EllipticEst.sEta θ)⁻¹
          = (Real.sin (2 * θ)) ^ Work.Spaces.eta := by
        rw [Work.FTS.EllipticEst.sEta, Real.rpow_neg hs0 Work.Spaces.eta, inv_inv]
      rw [hinv]
      exact Real.rpow_le_one hs0 hs1 hη

/-- A `C^n` function on the open interval is a.e. strongly measurable for `volume.restrict Iθ`
(it agrees a.e. with a continuous function). -/
theorem aesm_of_contDiffOn_Ioo {u : ℝ → ℝ} {n : ℕ}
    (h : ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2))) :
    AEStronglyMeasurable u (volume.restrict Work.Spaces.Iθ) := by
  obtain ⟨g, hgm, hge⟩ := h.continuousOn.aemeasurable measurableSet_Ioo
  refine ⟨g, hgm.stronglyMeasurable, ?_⟩
  have h1 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ (0 : ℝ) := by
    rw [MeasureTheory.ae_iff]; simpa using MeasureTheory.measure_singleton (0 : ℝ)
  have h2 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ Real.pi / 2 := by
    rw [MeasureTheory.ae_iff]; simpa using MeasureTheory.measure_singleton (Real.pi / 2)
  have h3 : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Set.Ioo 0 (Real.pi / 2) → u x = g x := by
    rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_Ioo] at hge
    exact hge
  rw [Filter.EventuallyEq, Work.Spaces.Iθ, MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  filter_upwards [h1, h2, h3] with x hx1 hx2 hx3 hxI
  exact hx3 ⟨lt_of_le_of_ne hxI.1 (Ne.symm hx1), lt_of_le_of_ne hxI.2 hx2⟩

/-- **Smoothness of a `θ`-slice.**  A function that is `C^n` on the open quadrant is `C^n`
along every slice `θ ↦ Ψ z θ` with `z > 0`. -/
theorem contDiffOn_slice (Ψ : ℝ → ℝ → ℝ) {z : ℝ} (hz : 0 < z) {n : ℕ}
    (h : ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ContDiffOn ℝ n (fun θ => Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) := by
  have hc : ContDiff ℝ n (fun θ : ℝ => (z, θ)) := contDiff_prodMk_right z
  have h1 : ContDiffOn ℝ n (Function.uncurry Ψ ∘ fun θ : ℝ => (z, θ))
      (Set.Ioo 0 (Real.pi / 2)) :=
    h.comp hc.contDiffOn (fun θ hθ => ⟨hz, hθ⟩)
  refine h1.congr (fun θ _ => ?_)
  simp [Function.comp, Function.uncurry]

/-- A `C¹`-function on an open subset of `ℝ × ℝ` has differentiable `z`-slices on that set,
with derivative the `z`-partial `pz`. -/
theorem hasDerivAt_slice_of_contDiffOn_open {G : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hG : ContDiffOn ℝ 1 (Function.uncurry G) U) {u θ : ℝ} (hmem : (u, θ) ∈ U) :
    HasDerivAt (fun u' => G u' θ) (Work.Spaces.pz G u θ) u := by
  have hd : DifferentiableAt ℝ (Function.uncurry G) (u, θ) :=
    (hG.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hmem)
  have hcur : DifferentiableAt ℝ (fun u' => G u' θ) u :=
    Work.Spaces.differentiableAt_curry_left hd
  simpa [Work.Spaces.pz] using hcur.hasDerivAt

/-- The open quadrant on which the honest class is smooth. -/
abbrev Qd : Set (ℝ × ℝ) := Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)

theorem isOpen_Qd : IsOpen Qd := isOpen_Ioi.prod isOpen_Ioo

/-- `pzIter 2 Ψ` is `pz (pz Ψ)`. -/
theorem pzIter_two_eq (Ψ : ℝ → ℝ → ℝ) :
    Work.Spaces.pzIter 2 Ψ = Work.Spaces.pz (Work.Spaces.pz Ψ) := by
  have h2 : (2 : ℕ) = 1 + 1 := by norm_num
  rw [h2, Work.Spaces.pzIter_succ, Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero]

/-- `pthIter 2 Ψ` is `deriv (deriv (slice))`. -/
theorem pthIter_two_eq (Ψ : ℝ → ℝ → ℝ) (z : ℝ) :
    (fun θ => Work.Spaces.pthIter 2 Ψ z θ)
      = deriv (fun θ' => deriv (fun θ'' => Ψ z θ'') θ') := rfl

/-- `pthIter 2 Ψ` is `pth (pth Ψ)`. -/
theorem pthIter_two_eq_fun (Ψ : ℝ → ℝ → ℝ) :
    Work.Spaces.pthIter 2 Ψ = Work.Spaces.pth (Work.Spaces.pth Ψ) := by
  have h2 : (2 : ℕ) = 1 + 1 := by norm_num
  rw [h2, Work.Spaces.pthIter_succ, Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero]

/-! ## Slice integrability from `HkMem` -/

/-- At level `0`, on the angular interval, the `Hk`-integrand is `(g z θ)² · w z² · σ θ`. -/
theorem HkIntegrand_zero_eq_Iθ (α : ℝ) (g : ℝ → ℝ → ℝ) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
  rw [HkIntegrand_zero_eq α g z θ, mul_pow, sq_weight_eq (sin_two_nonneg_of_mem_Iθ hθ),
    Work.FTS.EllipticEst.sEta]
  ring

/-- **Slicewise integrability from `HkMem`**: for `z > 0` the `σ`-weighted square of the slice
is integrable in `θ`. -/
theorem HkMemSliceSqSigma {α : ℝ} {g : ℝ → ℝ → ℝ} (hg : Work.Spaces.HkMem α 0 g) {z : ℝ}
    (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => (g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := by
  have hw : Work.Spaces.w z ≠ 0 := by
    rw [Work.Spaces.w]; positivity
  have h1 : MeasureTheory.IntegrableOn
      (fun θ => (g z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ :=
    (hg.1 z (Set.mem_Ici.mpr (le_of_lt hz))).congr_fun
      (fun θ hθ => HkIntegrand_zero_eq_Iθ α g hθ) measurableSet_Icc
  have h2 := h1.const_mul ((Work.Spaces.w z) ^ 2)⁻¹
  refine MeasureTheory.IntegrableOn.congr_fun h2 (fun θ _ => ?_) measurableSet_Icc
  field_simp

/-- **The `σ`-weighted square of a slice is locally `z`-integrable** (in the extended-value
sense), from the honest `z`-integral of `HkMem α 0 g`. -/
theorem HkMemSliceGammaLinTop {α : ℝ} {g : ℝ → ℝ → ℝ} (hg : Work.Spaces.HkMem α 0 g) {z₀ : ℝ}
    (hz : 0 < z₀) :
    ∫⁻ s in Set.Icc z₀ (z₀ + 1), ENNReal.ofReal
      (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) < ⊤ := by
  have hG : ∀ s, (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g s θ)
      = (Work.Spaces.w s) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
    intro s
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      (fun θ hθ => by rw [HkIntegrand_zero_eq_Iθ α g hθ]; ring)
  have hmem := hg.2.congr_fun (fun s _ => hG s) measurableSet_Ici
  have hnonneg : 0 ≤ᵐ[volume.restrict Work.Spaces.Iz]
      (fun s => (Work.Spaces.w s) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) :=
    Filter.Eventually.of_forall (fun s => mul_nonneg (sq_nonneg _)
      (MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg hθ))))
  have hfin : ∫⁻ s in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w s) ^ 2
      * (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) < ⊤ := by
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hmem hnonneg]
    exact ENNReal.ofReal_lt_top
  have hAEM : AEMeasurable (fun s => ENNReal.ofReal ((Work.Spaces.w s) ^ 2
      * (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)))
      (volume.restrict Work.Spaces.Iz) :=
    hmem.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hAEMK : AEMeasurable (fun s => ENNReal.ofReal ((Work.Spaces.w s) ^ 2
      * (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)))
      (volume.restrict (Set.Icc z₀ (z₀ + 1))) :=
    ((hmem.mono_set (fun s hs => Set.mem_Ici.mpr (le_trans (le_of_lt hz) hs.1))).aestronglyMeasurable.aemeasurable).ennreal_ofReal
  have hscale : ∀ s ∈ Set.Icc z₀ (z₀ + 1),
      1 ≤ ((z₀ + 1) ^ 4) * (Work.Spaces.w s) ^ 2 := by
    intro s hs
    have hs0 : 0 ≤ s := le_trans (le_of_lt hz) hs.1
    have hs4 : 0 < s ^ 4 := pow_pos (lt_of_lt_of_le hz hs.1) 4
    have h3 : s ^ 4 ≤ (z₀ + 1) ^ 4 * (1 + s) ^ 4 := by
      have hA : s ^ 4 ≤ (z₀ + 1) ^ 4 := pow_le_pow_left₀ hs0 hs.2 4
      have hB : (1 : ℝ) ≤ (1 + s) ^ 4 := one_le_pow₀ (by linarith)
      have hC : (0 : ℝ) ≤ (z₀ + 1) ^ 4 := by positivity
      nlinarith [hA, hB, hC]
    rw [Work.Spaces.w]
    have hws : ((1 + s) ^ 2 / s ^ 2) ^ 2 = (1 + s) ^ 4 / s ^ 4 := by ring
    rw [hws, mul_div_assoc', le_div_iff₀ hs4]
    nlinarith [h3]
  have hstep : ∫⁻ s in Set.Icc z₀ (z₀ + 1), ENNReal.ofReal
        (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      ≤ ENNReal.ofReal ((z₀ + 1) ^ 4) * ∫⁻ s in Set.Icc z₀ (z₀ + 1), ENNReal.ofReal
          (((Work.Spaces.w s) ^ 2)
            * (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) := by
    rw [← MeasureTheory.lintegral_const_mul'' _ hAEMK]
    refine MeasureTheory.lintegral_mono_ae ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun s hs => ?_)
    have hγ : 0 ≤ ∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
      MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg hθ))
    have h1 : (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        ≤ (((z₀ + 1) ^ 4) * (Work.Spaces.w s) ^ 2)
          * (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
      have := mul_le_mul_of_nonneg_right (hscale s hs) hγ
      simpa [one_mul] using this
    calc ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        ≤ ENNReal.ofReal ((((z₀ + 1) ^ 4) * (Work.Spaces.w s) ^ 2)
            * (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) := by
          refine (ENNReal.ofReal_le_ofReal_iff ?_).mpr h1
          positivity
      _ = ENNReal.ofReal ((z₀ + 1) ^ 4) * ENNReal.ofReal (((Work.Spaces.w s) ^ 2)
            * (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) := by
          rw [mul_assoc, ENNReal.ofReal_mul (by positivity)]
  calc ∫⁻ s in Set.Icc z₀ (z₀ + 1), ENNReal.ofReal
        (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      ≤ ENNReal.ofReal ((z₀ + 1) ^ 4) * ∫⁻ s in Set.Icc z₀ (z₀ + 1), ENNReal.ofReal
          (((Work.Spaces.w s) ^ 2)
            * (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) := hstep
    _ ≤ ENNReal.ofReal ((z₀ + 1) ^ 4) * ∫⁻ s in Work.Spaces.Iz, ENNReal.ofReal
          (((Work.Spaces.w s) ^ 2)
            * (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact MeasureTheory.lintegral_mono_set
          (fun s hs => Set.mem_Ici.mpr (le_trans (le_of_lt hz) hs.1))
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

/-! ## Differentiation under the `θ`-integral sign -/

/-- **Differentiation under the `θ`-integral sign.**  If `ψ` is jointly continuous on the closed
rectangle `[z/2, 2z] × [a,b]`, so is its `z`-partial `pz ψ`, and `x ↦ ψ x t` has derivative
`pz ψ x t` on `(z/2, 2z)` for each `t ∈ [a,b]`, then `s ↦ ∫_a^b ψ s θ dθ` has derivative
`∫_a^b pz ψ z θ dθ` at `z`. -/
theorem hasDerivAt_sliceIntegral {ψ : ℝ → ℝ → ℝ} {a b z : ℝ} (hab : a ≤ b) (ha : 0 < a)
    (hb : b < Real.pi / 2) (hz : 0 < z)
    (hsz : ContinuousOn (fun p : ℝ × ℝ => ψ p.1 p.2)
      (Set.Icc (z / 2) (2 * z) ×ˢ Set.Icc a b))
    (hsz' : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz ψ p.1 p.2)
      (Set.Icc (z / 2) (2 * z) ×ˢ Set.Icc a b))
    (hdiff : ∀ t ∈ Set.Icc a b, ∀ x ∈ Set.Ioo (z / 2) (2 * z),
      HasDerivAt (fun x' => ψ x' t) (Work.Spaces.pz ψ x t) x) :
    HasDerivAt (fun s => ∫ θ in a..b, ψ s θ) (∫ θ in a..b, Work.Spaces.pz ψ z θ) z := by
  have hs_nhds : Set.Ioo (z / 2) (2 * z) ∈ 𝓝 z :=
    isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hsz'
  have hcurve : ContinuousOn (fun θ' : ℝ => (z, θ')) (Set.Icc a b) :=
    (show Continuous (fun θ' : ℝ => (z, θ')) by continuity).continuousOn
  have hslice : ContinuousOn (fun θ : ℝ => ψ z θ) (Set.Icc a b) :=
    hsz.comp hcurve (fun θ hθ => ⟨⟨by linarith, by linarith⟩, hθ⟩)
  have hslice' : ContinuousOn (fun θ : ℝ => Work.Spaces.pz ψ z θ) (Set.Icc a b) :=
    hsz'.comp hcurve (fun θ hθ => ⟨⟨by linarith, by linarith⟩, hθ⟩)
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (a := a) (b := b) (F := fun x θ => ψ x θ) (F' := fun x θ => Work.Spaces.pz ψ x θ)
    (x₀ := z) (s := Set.Ioo (z / 2) (2 * z)) (μ := volume) (bound := fun _ => C)
    hs_nhds ?_ ?_ ?_ ?_ ?_ ?_).2
  · refine Filter.Eventually.mono (p := fun x => x ∈ Set.Ioo (z / 2) (2 * z)) hs_nhds
      (fun x hx => ?_)
    have h2 : ContinuousOn (fun θ : ℝ => ψ x θ) (Set.Icc a b) :=
      hsz.comp (show Continuous (fun θ : ℝ => (x, θ)) by continuity).continuousOn (fun θ hθ => ⟨⟨le_of_lt hx.1, le_of_lt hx.2⟩, hθ⟩)
    have h3 : ContinuousOn (fun θ : ℝ => ψ x θ) (Set.uIcc a b) := by
      rwa [Set.uIcc_of_le hab]
    exact (h3.aestronglyMeasurable measurableSet_uIcc).mono_measure
      (Measure.restrict_mono Set.uIoc_subset_uIcc le_rfl)
  · have h3 : ContinuousOn (fun θ : ℝ => ψ z θ) (Set.uIcc a b) := by
      rwa [Set.uIcc_of_le hab]
    exact h3.intervalIntegrable
  · have h3 : ContinuousOn (fun θ : ℝ => Work.Spaces.pz ψ z θ) (Set.uIcc a b) := by
      rwa [Set.uIcc_of_le hab]
    exact (h3.aestronglyMeasurable measurableSet_uIcc).mono_measure
      (Measure.restrict_mono Set.uIoc_subset_uIcc le_rfl)
  · refine (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mp
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_uIoc (fun t ht x hx => ?_))
    rw [Set.uIoc_of_le hab] at ht
    exact hC (x, t) ⟨⟨le_of_lt hx.1, le_of_lt hx.2⟩, ⟨le_of_lt ht.1, ht.2⟩⟩
  · exact intervalIntegrable_const
  · refine (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mp
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_uIoc (fun t ht x hx => ?_))
    rw [Set.uIoc_of_le hab] at ht
    exact hdiff t ⟨le_of_lt ht.1, ht.2⟩ x hx

/-- **Boundedness of a slice and of its derivative.**  If `(u'')²·σ` is integrable on `Iθ` then
`u'' ∈ L¹` on the open interval (`σ ≥ 1` there), so `u'` has the oscillation bound
`|u' x - u' y| ≤ ∫|u''|`, and `u` is bounded by integrating once more. -/
theorem SliceBddSqSigma {u : ℝ → ℝ}
    (hsm : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (h2 : MeasureTheory.IntegrableOn (fun θ => (deriv (fun t => deriv u t) θ) ^ 2
        * sEta θ) Work.Spaces.Iθ) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |deriv u θ| ≤ C ∧ |u θ| ≤ C := by
  have hq0 : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hq : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hIq : Real.pi / 4 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hq0, hq⟩
  have hsq : MeasureTheory.IntegrableOn (fun θ => (deriv (fun t => deriv u t) θ) ^ 2)
      (Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.sliceLim_integrableOn_sq_of_integrableOn_mul_sEta u h2
  have habs2 : MeasureTheory.IntegrableOn (fun θ => |deriv (fun t => deriv u t) θ|)
      (Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.sliceLim_integrableOn_abs_of_integrableOn_sq u hsq
  have hderiv2 : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (deriv u) (deriv (fun t => deriv u t) x) x := by
    intro x hx
    have h2' : ContDiffAt ℝ 2 u x := (hsm.contDiffAt (isOpen_Ioo.mem_nhds hx)).of_le (by norm_num)
    have h1 : ContDiffAt ℝ 1 (deriv u) x := h2'.derivWithin (by norm_num)
    exact (h1.differentiableAt (by norm_num)).hasDerivAt
  have hMono : ∀ {a b : ℝ}, a ≤ b → Set.Icc a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      ∫ s in a..b, |deriv (fun t => deriv u t) s|
        ≤ ∫ s in Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv (fun t => deriv u t) s| := by
    intro a b hab hsub
    rw [intervalIntegral.integral_of_le hab]
    exact MeasureTheory.setIntegral_mono_set habs2
      (Filter.Eventually.of_forall fun s => abs_nonneg _)
      (Filter.Eventually.of_forall fun s hs => hsub ⟨le_of_lt hs.1, hs.2⟩)
  have hFTC2 : ∀ {a b : ℝ}, a ≤ b → Set.Icc a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      ∫ s in a..b, deriv (fun t => deriv u t) s = deriv u b - deriv u a := by
    intro a b hab hsub
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab ?_ ?_ ?_
    · intro z hz
      exact ((hderiv2 z (hsub hz)).continuousAt).continuousWithinAt
    · intro z hz
      exact hderiv2 z (hsub ⟨le_of_lt hz.1, le_of_lt hz.2⟩)
    · have h1 : MeasureTheory.IntegrableOn (fun s => deriv (fun t => deriv u t) s)
          (Set.Ioc a b) :=
        MeasureTheory.Integrable.mono'
          (habs2.mono_set fun z hz => hsub ⟨le_of_lt hz.1, hz.2⟩)
          (measurable_deriv _).aestronglyMeasurable
          (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs])
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr h1
  have hosc : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), ∀ y ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |deriv u x - deriv u y|
        ≤ ∫ s in Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv (fun t => deriv u t) s| := by
    intro x hx y hy
    rcases le_total x y with hxy | hyx
    · have hsub : Set.Icc x y ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun z hz =>
        ⟨lt_of_lt_of_le hx.1 hz.1, lt_of_le_of_lt hz.2 hy.2⟩
      rw [abs_sub_comm, ← hFTC2 hxy hsub]
      have h1 := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
        (f := fun s => deriv (fun t => deriv u t) s) hxy
      simp only [Real.norm_eq_abs] at h1
      exact h1.trans (hMono hxy hsub)
    · have hsub : Set.Icc y x ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun z hz =>
        ⟨lt_of_lt_of_le hy.1 hz.1, lt_of_le_of_lt hz.2 hx.2⟩
      rw [← hFTC2 hyx hsub]
      have h1 := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
        (f := fun s => deriv (fun t => deriv u t) s) hyx
      simp only [Real.norm_eq_abs] at h1
      exact h1.trans (hMono hyx hsub)
  have hud : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |deriv u θ| ≤ |deriv u (Real.pi / 4)|
        + ∫ s in Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv (fun t => deriv u t) s| := by
    intro θ hθ
    have h := hosc θ hθ (Real.pi / 4) hIq
    have h1 : |deriv u θ| ≤ |deriv u θ - deriv u (Real.pi / 4)| + |deriv u (Real.pi / 4)| := by
      have := abs_add_le (deriv u θ - deriv u (Real.pi / 4)) (deriv u (Real.pi / 4))
      simpa using this
    linarith
  have hIint : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |∫ s in (Real.pi / 4)..θ, deriv u s|
        ≤ (|deriv u (Real.pi / 4)|
            + ∫ s in Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv (fun t => deriv u t) s|)
          * (Real.pi / 2) := by
    intro θ hθ
    have hb : ∀ s ∈ Set.uIoc (Real.pi / 4) θ,
        ‖deriv u s‖ ≤ |deriv u (Real.pi / 4)|
          + ∫ s in Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv (fun t => deriv u t) s| := by
      intro s hs
      rw [Set.uIoc, Set.mem_Ioc] at hs
      have hs' : s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
        ⟨lt_trans (lt_min hq0 hθ.1) hs.1, lt_of_le_of_lt hs.2 (max_lt hq hθ.2)⟩
      rw [Real.norm_eq_abs]
      exact hud s hs'
    have h1 := intervalIntegral.norm_integral_le_of_norm_le_const (f := deriv u)
      (C := |deriv u (Real.pi / 4)|
        + ∫ s in Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv (fun t => deriv u t) s|) hb
    have h2 : |θ - Real.pi / 4| ≤ Real.pi / 2 := by
      refine abs_sub_le_iff.mpr ⟨?_, ?_⟩
      · linarith [hθ.1, hθ.2, hq0, Real.pi_pos]
      · linarith [hθ.1, hθ.2, hq0, Real.pi_pos]
    have h3 : 0 ≤ |deriv u (Real.pi / 4)|
        + ∫ s in Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv (fun t => deriv u t) s| := by
      have hI : 0 ≤ ∫ s in Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv (fun t => deriv u t) s| :=
        integral_nonneg fun s => abs_nonneg _
      linarith [abs_nonneg (deriv u (Real.pi / 4)), hI]
    calc |∫ s in (Real.pi / 4)..θ, deriv u s|
        ≤ (|deriv u (Real.pi / 4)|
            + ∫ s in Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv (fun t => deriv u t) s|)
          * |θ - Real.pi / 4| := by
          simpa only [Real.norm_eq_abs] using h1
      _ ≤ (|deriv u (Real.pi / 4)|
            + ∫ s in Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv (fun t => deriv u t) s|)
          * (Real.pi / 2) := mul_le_mul_of_nonneg_left h2 h3
  have hFTCu : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ∫ s in (Real.pi / 4)..θ, deriv u s = u θ - u (Real.pi / 4) := by
    intro θ hθ
    rcases le_total (Real.pi / 4) θ with hle | hle
    · have hsub : Set.Icc (Real.pi / 4) θ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun z hz =>
        ⟨lt_of_lt_of_le hq0 hz.1, lt_of_le_of_lt hz.2 hθ.2⟩
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle ?_ ?_ ?_
      · intro z hz
        exact ((hsm.contDiffAt (isOpen_Ioo.mem_nhds (hsub hz))).continuousAt).continuousWithinAt
      · intro z hz
        exact ((hsm.contDiffAt (isOpen_Ioo.mem_nhds
          (hsub ⟨le_of_lt hz.1, le_of_lt hz.2⟩))).differentiableAt (by norm_num)).hasDerivAt
      · have hcd : ContinuousOn (deriv u) (Set.uIcc (Real.pi / 4) θ) := fun z hz => by
          rw [Set.uIcc_of_le hle] at hz
          exact ((hderiv2 z (hsub hz)).continuousAt).continuousWithinAt
        exact hcd.intervalIntegrable
    · have hsub : Set.Icc θ (Real.pi / 4) ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun z hz =>
        ⟨lt_of_lt_of_le hθ.1 hz.1, lt_of_le_of_lt hz.2 hq⟩
      have h1 : ∫ s in θ..(Real.pi / 4), deriv u s = u (Real.pi / 4) - u θ := by
        refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle ?_ ?_ ?_
        · intro z hz
          exact ((hsm.contDiffAt (isOpen_Ioo.mem_nhds (hsub hz))).continuousAt).continuousWithinAt
        · intro z hz
          exact ((hsm.contDiffAt (isOpen_Ioo.mem_nhds
            (hsub ⟨le_of_lt hz.1, le_of_lt hz.2⟩))).differentiableAt (by norm_num)).hasDerivAt
        · have hcd : ContinuousOn (deriv u) (Set.uIcc θ (Real.pi / 4)) := fun z hz => by
            rw [Set.uIcc_of_le hle] at hz
            exact ((hderiv2 z (hsub hz)).continuousAt).continuousWithinAt
          exact hcd.intervalIntegrable
      rw [intervalIntegral.integral_symm (a := θ) (b := Real.pi / 4), h1]
      ring
  have hubd : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |u θ| ≤ |u (Real.pi / 4)|
        + (|deriv u (Real.pi / 4)|
            + ∫ s in Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv (fun t => deriv u t) s|)
          * (Real.pi / 2) := by
    intro θ hθ
    have h1 : |u θ| ≤ |u (Real.pi / 4)| + |u θ - u (Real.pi / 4)| := by
      have := abs_add_le (u (Real.pi / 4)) (u θ - u (Real.pi / 4))
      simpa using this
    have h2 : |u θ - u (Real.pi / 4)| ≤ (|deriv u (Real.pi / 4)|
        + ∫ s in Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv (fun t => deriv u t) s|)
        * (Real.pi / 2) := by
      rw [(congrArg abs (hFTCu θ hθ)).symm]
      exact hIint θ hθ
    linarith
  set I0 : ℝ := ∫ s in Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv (fun t => deriv u t) s| with hI0def
  have hI0 : 0 ≤ I0 := by
    rw [hI0def]; exact integral_nonneg fun _ => abs_nonneg _
  have hA : 0 ≤ |u (Real.pi / 4)| := abs_nonneg _
  have hB : 0 ≤ |deriv u (Real.pi / 4)| := abs_nonneg _
  have hP' : 0 ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have h1P' : 1 ≤ 1 + Real.pi / 2 := by linarith [Real.pi_pos]
  have hS0 : 0 ≤ |u (Real.pi / 4)| + |deriv u (Real.pi / 4)| + I0 + 1 := by linarith [hA, hB, hI0]
  have hSpos : 0 < |u (Real.pi / 4)| + |deriv u (Real.pi / 4)| + I0 + 1 := by linarith [hA, hB, hI0]
  refine ⟨(|u (Real.pi / 4)| + |deriv u (Real.pi / 4)| + I0 + 1) * (1 + Real.pi / 2), ?_, ?_⟩
  · exact mul_pos hSpos (by linarith [h1P'])
  · intro θ hθ
    have hud' : |deriv u θ| ≤ |deriv u (Real.pi / 4)| + I0 := by
      rw [hI0def]; exact hud θ hθ
    have hubd' : |u θ| ≤ |u (Real.pi / 4)|
        + (|deriv u (Real.pi / 4)| + I0) * (Real.pi / 2) := by
      rw [hI0def]; exact hubd θ hθ
    have h9 : |deriv u θ| ≤ |deriv u (Real.pi / 4)| + I0 + 1 := by linarith [hud', hI0]
    have h10 : |deriv u (Real.pi / 4)| + I0 + 1
        ≤ (|u (Real.pi / 4)| + |deriv u (Real.pi / 4)| + I0 + 1) * (1 + Real.pi / 2) := by
      have hle : |deriv u (Real.pi / 4)| + I0 + 1
          ≤ |u (Real.pi / 4)| + |deriv u (Real.pi / 4)| + I0 + 1 := by linarith [hA]
      calc |deriv u (Real.pi / 4)| + I0 + 1
          ≤ (|u (Real.pi / 4)| + |deriv u (Real.pi / 4)| + I0 + 1) * 1 := by
            rw [mul_one]; exact hle
        _ ≤ (|u (Real.pi / 4)| + |deriv u (Real.pi / 4)| + I0 + 1) * (1 + Real.pi / 2) :=
            mul_le_mul_of_nonneg_left h1P' hS0
    have h12 : |u (Real.pi / 4)| + (|deriv u (Real.pi / 4)| + I0) * (Real.pi / 2)
        ≤ (|u (Real.pi / 4)| + |deriv u (Real.pi / 4)| + I0 + 1) * (1 + Real.pi / 2) := by
      have hleA : |u (Real.pi / 4)| ≤ (|u (Real.pi / 4)| + |deriv u (Real.pi / 4)| + I0 + 1) * 1 := by
        rw [mul_one]; linarith [hB, hI0]
      have hleX : (|deriv u (Real.pi / 4)| + I0) * (Real.pi / 2)
          ≤ (|u (Real.pi / 4)| + |deriv u (Real.pi / 4)| + I0 + 1) * (Real.pi / 2) :=
        mul_le_mul_of_nonneg_right (by linarith [hA]) hP'
      calc |u (Real.pi / 4)| + (|deriv u (Real.pi / 4)| + I0) * (Real.pi / 2)
          ≤ (|u (Real.pi / 4)| + |deriv u (Real.pi / 4)| + I0 + 1) * 1
            + (|u (Real.pi / 4)| + |deriv u (Real.pi / 4)| + I0 + 1) * (Real.pi / 2) :=
            add_le_add hleA hleX
        _ = (|u (Real.pi / 4)| + |deriv u (Real.pi / 4)| + I0 + 1) * (1 + Real.pi / 2) := by ring
    exact ⟨h9.trans h10, hubd'.trans h12⟩

/-! ## The `tan θ`-identity -/

/-- **The `tan θ`-identity.**  If `(tan θ · u)' = A + u'' + 6u` on `(a,b)` and the three
integrability hypotheses hold, then
`tan b · u b − tan a · u a = ∫_a^b A + (deriv u b − deriv u a) + 6 ∫_a^b u`. -/
theorem TanSliceFTC {u A : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hu : ∀ θ ∈ Set.uIcc a b, HasDerivAt u (deriv u θ) θ)
    (hu1 : ∀ θ ∈ Set.uIcc a b, HasDerivAt (deriv u) (deriv (fun t => deriv u t) θ) θ)
    (ht : ∀ θ ∈ Set.uIcc a b,
      HasDerivAt (fun t => Real.tan t * u t) (deriv (fun t => Real.tan t * u t) θ) θ)
    (hint1 : IntervalIntegrable (fun θ => deriv (fun t => deriv u t) θ) volume a b)
    (hint2 : IntervalIntegrable (fun θ => deriv (fun t => Real.tan t * u t) θ) volume a b)
    (hint3 : IntervalIntegrable A volume a b)
    (hint4 : IntervalIntegrable u volume a b)
    (heq : ∀ θ ∈ Set.Ioo a b, deriv (fun t => Real.tan t * u t) θ
              = A θ + deriv (fun t => deriv u t) θ + 6 * u θ) :
    Real.tan b * u b - Real.tan a * u a
      = (∫ θ in a..b, A θ) + (deriv u b - deriv u a) + 6 * ∫ θ in a..b, u θ := by
  have h1 : (∫ θ in a..b, deriv (fun t => Real.tan t * u t) θ)
      = Real.tan b * u b - Real.tan a * u a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt ht hint2
  have h2 : (∫ θ in a..b, deriv (fun t => deriv u t) θ) = deriv u b - deriv u a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hu1 hint1
  have h3 : (∫ θ in a..b, deriv (fun t => Real.tan t * u t) θ)
      = ∫ θ in a..b, (A θ + deriv (fun t => deriv u t) θ + 6 * u θ) := by
    refine intervalIntegral.integral_congr_ae ?_
    have hb : ∀ᵐ θ ∂(volume : Measure ℝ), θ ≠ b := by
      rw [MeasureTheory.ae_iff]; simpa using MeasureTheory.measure_singleton b
    filter_upwards [hb] with θ hθ hmem
    rw [Set.uIoc_of_le hab, Set.mem_Ioc] at hmem
    exact heq θ ⟨hmem.1, lt_of_le_of_ne hmem.2 hθ⟩
  have h4 : (∫ θ in a..b, (A θ + deriv (fun t => deriv u t) θ + 6 * u θ))
      = (∫ θ in a..b, A θ) + (∫ θ in a..b, deriv (fun t => deriv u t) θ)
        + 6 * ∫ θ in a..b, u θ := by
    rw [intervalIntegral.integral_add (hint3.add hint1) (hint4.const_mul 6),
      intervalIntegral.integral_add hint3 hint1, intervalIntegral.integral_const_mul]
  rw [← h1, h3, h4, h2]

/-! ## Elementary bounds -/

/-- For a nonnegative real function, the Bochner set integral is bounded by the `toReal` of its
`lintegral`; this needs no measurability hypothesis (the non-integrable case is `0`). -/
theorem setIntegral_le_toReal_lintegral {f : ℝ → ℝ} (s : Set ℝ)
    (hf : ∀ᵐ x ∂volume.restrict s, 0 ≤ f x) :
    (∫ x in s, f x) ≤ ENNReal.toReal (∫⁻ x in s, ENNReal.ofReal (f x)) := by
  by_cases h : AEStronglyMeasurable f (volume.restrict s)
  · rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae hf h]
  · have hni : ¬ MeasureTheory.Integrable f (volume.restrict s) :=
      fun hi => h (Integrable.aestronglyMeasurable hi)
    rw [show (∫ x in s, f x) = ∫ x, f x ∂(volume.restrict s) from rfl,
      MeasureTheory.integral_undef hni]
    exact ENNReal.toReal_nonneg

/-- The AM–GM inequality `2|g| ≤ g²·σ + σ⁻¹` for `σ > 0`. -/
theorem two_mul_abs_le_sq_add_inv (g σ : ℝ) (hσ : 0 < σ) :
    2 * |g| ≤ g ^ 2 * σ + σ⁻¹ := by
  have h : 0 ≤ (|g| * Real.sqrt σ - 1 / Real.sqrt σ) ^ 2 := sq_nonneg _
  have h1 : (|g| * Real.sqrt σ) ^ 2 = g ^ 2 * σ := by
    rw [mul_pow, sq_abs, Real.sq_sqrt (le_of_lt hσ)]
  have h2 : (1 / Real.sqrt σ) ^ 2 = σ⁻¹ := by
    rw [div_pow, one_pow, Real.sq_sqrt (le_of_lt hσ), one_div]
  have h3 : 2 * (|g| * Real.sqrt σ) * (1 / Real.sqrt σ) = 2 * |g| := by
    field_simp
  nlinarith [h, h1, h2, h3]


/-- **The `θ`-`L¹` bound of a slice**: `∫_a^b |g| ≤ (1/2)(∫_{Iθ} g²σ + π/2)`. -/
theorem Ioc_abs_le_half {g : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hb : b < Real.pi / 2) (hab : a ≤ b)
    (hint : MeasureTheory.IntegrableOn
      (fun θ => (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ) :
    (∫ θ in a..b, |g θ|)
      ≤ (1 / 2) * ((∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          + Real.pi / 2) := by
  set Q : ℝ := ∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ with hQdef
  have hQnn : 0 ≤ Q := by
    rw [hQdef]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg hθ))
  have hsub : Set.Ioc a b ⊆ Work.Spaces.Iθ := fun θ hθ =>
    ⟨le_of_lt (lt_trans ha hθ.1), le_of_lt (lt_of_le_of_lt hθ.2 hb)⟩
  have hQeq : ENNReal.ofReal Q = ∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal ((g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
    rw [hQdef]
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
        (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg hθ)))
  have hpt : ∀ θ ∈ Set.Ioc a b, ENNReal.ofReal |g θ| ≤ ENNReal.ofReal (1 / 2)
      * (ENNReal.ofReal ((g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) + 1) := by
    intro θ hθ
    have hθp : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨lt_trans ha hθ.1, lt_of_le_of_lt hθ.2 hb⟩
    have hσ : 0 < Work.FTS.EllipticEst.sEta θ := sEta_pos_of_mem_Ioo hθp
    have hσinv : (Work.FTS.EllipticEst.sEta θ)⁻¹ ≤ 1 := inv_sEta_le_one (hsub hθ)
    have h1 : |g θ| ≤ (1 / 2) * ((g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ + 1) := by
      linarith [two_mul_abs_le_sq_add_inv (g θ) (Work.FTS.EllipticEst.sEta θ) hσ, hσinv]
    have hpos : (0 : ℝ) ≤ (1 / 2) * ((g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ + 1) := by
      positivity
    calc ENNReal.ofReal |g θ|
        ≤ ENNReal.ofReal ((1 / 2) * ((g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ + 1)) :=
          (ENNReal.ofReal_le_ofReal_iff hpos).mpr h1
      _ = ENNReal.ofReal (1 / 2)
            * (ENNReal.ofReal ((g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) + 1) := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add (by positivity) (by norm_num),
            ENNReal.ofReal_one]
  have h1AEM : AEMeasurable (fun θ => ENNReal.ofReal ((g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
      (volume.restrict (Set.Ioc a b)) :=
    ((hint.mono_set hsub).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
  have hAEM : AEMeasurable (fun θ => ENNReal.ofReal ((g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      + (1 : ℝ≥0∞)) (volume.restrict (Set.Ioc a b)) :=
    h1AEM.add aemeasurable_const
  have hfin : ∫⁻ θ in Set.Ioc a b, ENNReal.ofReal (1 / 2)
      * (ENNReal.ofReal ((g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) + 1) < ⊤ := by
    rw [MeasureTheory.lintegral_const_mul'' _ hAEM, MeasureTheory.lintegral_add_left' h1AEM]
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.mpr ⟨?_, ?_⟩)
    · exact lt_of_le_of_lt (le_trans (MeasureTheory.lintegral_mono_set hsub)
        (le_of_eq hQeq.symm)) ENNReal.ofReal_lt_top
    · rw [MeasureTheory.lintegral_const, one_mul, Measure.restrict_apply_univ]
      rw [Real.volume_Ioc]
      exact ENNReal.ofReal_lt_top
  calc (∫ θ in a..b, |g θ|) = ∫ θ in Set.Ioc a b, |g θ| := intervalIntegral.integral_of_le hab
    _ ≤ ENNReal.toReal (∫⁻ θ in Set.Ioc a b, ENNReal.ofReal |g θ|) :=
        setIntegral_le_toReal_lintegral _ (Filter.Eventually.of_forall (fun θ => abs_nonneg _))
    _ ≤ ENNReal.toReal (∫⁻ θ in Set.Ioc a b, ENNReal.ofReal (1 / 2)
          * (ENNReal.ofReal ((g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) + 1)) :=
        ENNReal.toReal_mono (ne_of_lt hfin) (MeasureTheory.lintegral_mono_ae
          (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc hpt))
    _ = ENNReal.toReal (ENNReal.ofReal (1 / 2) * (∫⁻ θ in Set.Ioc a b,
          (ENNReal.ofReal ((g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) + 1))) := by
        rw [MeasureTheory.lintegral_const_mul'' _ hAEM]
    _ = ENNReal.toReal (ENNReal.ofReal (1 / 2) * ((∫⁻ θ in Set.Ioc a b,
          ENNReal.ofReal ((g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
          + ∫⁻ θ in Set.Ioc a b, (1 : ℝ≥0∞))) := by
        rw [MeasureTheory.lintegral_add_left' h1AEM]
    _ ≤ ENNReal.toReal (ENNReal.ofReal (1 / 2) * (ENNReal.ofReal Q
          + ENNReal.ofReal (Real.pi / 2))) := by
        refine ENNReal.toReal_mono (by finiteness)
          (mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by simp))
        · exact le_trans (MeasureTheory.lintegral_mono_set hsub) (le_of_eq hQeq.symm)
        · rw [MeasureTheory.lintegral_const, one_mul, Measure.restrict_apply_univ, Real.volume_Ioc]
          refine (ENNReal.ofReal_le_ofReal_iff ?_).mpr ?_
          · positivity
          · linarith [Real.pi_pos, hab]
    _ = (1 / 2) * (Q + Real.pi / 2) := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
          ENNReal.toReal_ofReal (by norm_num), ENNReal.toReal_ofReal hQnn,
          ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
    _ = (1 / 2) * ((∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          + Real.pi / 2) := by rw [hQdef]



end Work.FTS.EllipticEst.Honest
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6.Swap6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6

open Work.Spaces

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **Tonelli for the `ℋ⁶`-integrand of an open-class datum.**  For `f` of class `C^∞` on the
open quadrant with `HkMem α 6 f`, the iterated integral of `HkIntegrand α 6 f` in the order
`∫_θ ∫_z` equals `HkSq α 6 f`, its partially integrated function is integrable on the angles,
and for almost every angle the radial slice is integrable. -/
theorem sda_HkSqSwap_open6 (α : ℝ) (f : ℝ → ℝ → ℝ)
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : HkMem α 6 f) :
    (∫ σ in Iθ, ∫ s in Iz, HkIntegrand α 6 f s σ = HkSq α 6 f) ∧
      Integrable (fun σ : ℝ => ∫ s in Iz, HkIntegrand α 6 f s σ) (volume.restrict Iθ) ∧
      (∀ᵐ σ ∂(volume.restrict Iθ),
        IntegrableOn (fun s => HkIntegrand α 6 f s σ) Iz) := by
  have hnn : ∀ z θ : ℝ, 0 ≤ HkIntegrand α 6 f z θ :=
    fun z θ => HkIntegrand_nonneg α 6 f z θ
  have haesm : AEStronglyMeasurable
      (Function.uncurry fun z θ : ℝ => HkIntegrand α 6 f z θ)
      ((volume.restrict Iz).prod (volume.restrict Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ (hF.continuousOn_HkIntegrand α 6)
  have hslice : ∀ᵐ z ∂(volume.restrict Iz),
      Integrable (fun θ : ℝ => HkIntegrand α 6 f z θ) (volume.restrict Iθ) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => hmem.1 z hz)
  have houter : Integrable (fun z : ℝ => ∫ θ in Iθ, HkIntegrand α 6 f z θ)
      (volume.restrict Iz) := hmem.2
  obtain ⟨h1, h2, h3⟩ :=
    Work.FTS.H2.swap_iterated_integral_of_nonneg
      (μ := volume.restrict Iz) (ν := volume.restrict Iθ) hnn haesm hslice houter
  exact ⟨by rw [HkSq]; exact h1, h2, h3⟩

end Work.FTS.StrongPersist.N6
end
end
