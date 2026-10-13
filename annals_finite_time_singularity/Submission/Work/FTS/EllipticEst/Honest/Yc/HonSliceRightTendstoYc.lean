import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.Honest.Basic
import Submission.Work.FTS.EllipticEst.Honest.HonSliceFinite
import Submission.Work.FTS.EllipticEst.Honest.HonEnergyAux
-- `Blocks.PzIterTwoContinuousOn` is needed for `contDiffOn_uncurry_pz_succ` /
-- `PzIterTwoContinuousOn` (the `z`-regularity of `pzIter 2 Ψ`); it is in the
-- `HonDifQuotBound`/`HonFirstMoment` cone, so importing it is safe.
-- `StraightDefs`, `sliceLimitLeftExists` and `Spaces.CurrySmooth` are already in the
-- transitive closure of the three modules above and are therefore not imported explicitly.
import Submission.Work.FTS.EllipticEst.Blocks.PzIterTwoContinuousOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest.Yc.RightTendsto

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## Elementary facts about the angular weight `σ = sEta` -/

theorem sin_two_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem sin_two_le_one (θ : ℝ) : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _

/-- `σ = sin(2θ)^{-η} ≥ 0` on `Iθ`. -/
theorem sEta_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Work.FTS.EllipticEst.sEta θ := by
  rw [Work.FTS.EllipticEst.sEta]
  exact Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ hθ) _

/-- `σ > 0` on the open interval. -/
theorem sEta_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < Work.FTS.EllipticEst.sEta θ := by
  have hs : 0 < Real.sin (2 * θ) := sin_two_pos_of_mem_Ioo hθ
  simpa only [Work.FTS.EllipticEst.sEta] using Real.rpow_pos_of_pos hs (-(Work.Spaces.eta))

/-- `σ ≥ 1` on the open interval. -/
theorem one_le_sEta {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    1 ≤ Work.FTS.EllipticEst.sEta θ := by
  rw [Work.FTS.EllipticEst.sEta]
  have hpos := sin_two_pos_of_mem_Ioo hθ
  have hle := sin_two_le_one θ
  have hz : -(Work.Spaces.eta) ≤ 0 := by
    have : (0 : ℝ) ≤ Work.Spaces.eta := by norm_num [Work.Spaces.eta]
    linarith
  simpa using Real.rpow_le_rpow_of_nonpos hpos hle hz

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

/-- `∫_a^b σ^{-1} ≤ π/2` when `[a,b] ⊆ Iθ`. -/
theorem intervalIntegral_inv_sEta_le {a b : ℝ} (hab : a ≤ b) (hsub : Set.Ioc a b ⊆ Work.Spaces.Iθ) :
    (∫ θ in a..b, (Work.FTS.EllipticEst.sEta θ)⁻¹) ≤ Real.pi / 2 := by
  rw [intervalIntegral.integral_of_le hab]
  refine le_trans (setIntegral_le_toReal_lintegral (Set.Ioc a b)
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc (fun θ hθ =>
      inv_nonneg.mpr (sEta_nonneg (hsub hθ))))) ?_
  have h2 : (∫⁻ θ in Set.Ioc a b, ENNReal.ofReal ((Work.FTS.EllipticEst.sEta θ)⁻¹))
      ≤ ∫⁻ θ in Work.Spaces.Iθ, (1 : ℝ≥0∞) := by
    refine le_trans (MeasureTheory.lintegral_mono_ae
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc (fun θ hθ => ?_)))
      (MeasureTheory.lintegral_mono_set hsub)
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_le_ofReal_iff zero_le_one).mpr (inv_sEta_le_one (hsub hθ))
  have h3 : (∫⁻ θ in Work.Spaces.Iθ, (1 : ℝ≥0∞)) = ENNReal.ofReal (Real.pi / 2) := by
    rw [MeasureTheory.lintegral_const, Work.Spaces.Iθ, one_mul, Measure.restrict_apply_univ,
      Real.volume_Icc, sub_zero]
  refine le_trans (ENNReal.toReal_mono (by finiteness) (le_trans h2 (le_of_eq h3))) ?_
  rw [ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]

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

end Work.FTS.EllipticEst.Honest.Yc.RightTendsto

open Work.FTS.EllipticEst.Honest.Yc.RightTendsto

namespace Work.FTS.EllipticEst.Honest.Yc

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- **The `θ → (π/2)⁻` endpoint limit of an honest slice vanishes (for every `z > 0`).**  For
`h : Hon α F Ψ` (the honest class of `Submission/Work/FTS/EllipticEst/Honest/Basic.lean`) and every
`z > 0`, the slice `u = Ψ z ·` has limit `0` at `(π/2)⁻`.

CONE WARNING (important).  A sorry-free proof of this very statement already exists as
`Work.FTS.EllipticEst.Honest.HonSliceRightTendsto`
(`Submission/Work/FTS/EllipticEst/Honest/HonSliceRightTendsto.lean`), but that module DEFINES
`Work.FTS.EllipticEst.Honest.contDiffOn_slice`, a name that is *also* defined (with a different
type) by `Honest/HonDifQuotBound.lean`; consequently no module can import both, and the consumers
of the present statement need the `HonDifQuotBound`/`HonFirstMoment` cone.  So do NOT import
`Honest.HonSliceRightTendsto`, `Honest.HonSliceBdd`, `Honest.HonDifQuotBound`,
`Honest.HonFirstMoment` or `Honest.I4UpperHonest`; a direct proof in the cone
`{Basic, HonSliceFinite, HonEnergyAux}` is wanted (porting the existing proof into this cone is
acceptable if done without those imports).

ROUTE (corrected).  Put `g θ := Real.tan θ * u θ` with `u := Ψ z ·`, and `σ θ = sin(2θ)^{-η}`
(`η = 99/100`).  Rearranging `bslOp α Ψ = F` (`Hon.eq_solve`) on the open interval gives

`g' = F z · + α²z²·(∂_zzΨ(z,·)) + (∂_θθΨ(z,·)) + α(5+α)z·(∂_zΨ(z,·)) + 6·Ψ(z,·)`,

and each of the five terms has square-integrable product with `σ` over `Iθ`:
`Hon.memF`, `hon_memA_sigma` (for `z²∂_zzΨ`), `hon_memB_sigma` (for `∂_θθΨ`),
`HonSliceFinite.integrableOn_zpz_sigma'` (for `z∂_zΨ`) and `HonSliceFinite.integrableOn_sq_sEta_psi`
(for `Ψ`).  Hence `∫_θ (g')² σ < ∞`.

For `0 < a < b < π/2`, Cauchy–Schwarz in the form `(∫_a^b g')² ≤ (∫_a^b (g')²σ)(∫_a^b σ^{-1})` and
the bound `σ^{-1} = sin(2θ)^η ≤ 2^η (b-a)^η` on `[a,b]` give
`|g b - g a| ≤ √A · 2^{η/2} (b-a)^{(1+η)/2}`: `g` is Hölder of exponent `(1+η)/2 > 0` on
`(0, π/2)`, hence `g` is Cauchy along `𝓝[<] (π/2)` and therefore has a *finite* limit there
(`ℝ` is complete).  Finally `u = g · (cos θ / sin θ)` with `cos θ → 0` and `sin θ → 1` as
`θ → (π/2)⁻`, so `u → 0`. -/
theorem HonSliceRightTendstoYc (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.Honest.Hon α F Ψ) :
    ∀ z : ℝ, 0 < z →
      Filter.Tendsto (fun θ : ℝ => Ψ z θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  intro z hz
  -- the base point `a` of the `θ`-integration
  set a : ℝ := Real.pi / 4 with hadef
  have ha_pos : 0 < a := by rw [hadef]; linarith [Real.pi_pos]
  have ha_lt : a < Real.pi / 2 := by rw [hadef]; linarith [Real.pi_pos]
  have hz1 : 0 < z + 1 := by linarith
  -- slicewise `L²(σ)`-integrability of `∂_θθΨ` at every `s > 0` (from `memB`)
  have hth : ∀ s : ℝ, 0 < s → MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv (fun θ' => Ψ s θ') t) θ) ^ 2
        * sEta θ) Work.Spaces.Iθ := by
    intro s hs
    have h0 := HkMemSliceSqSigma h.memB hs
    refine h0.congr_fun (fun θ _ => ?_) measurableSet_Icc
    have h1 : Work.Spaces.pthIter 2 Ψ s θ
        = deriv (fun t => deriv (fun θ' => Ψ s θ') t) θ := by
      simp only [show (2 : ℕ) = 1 + 1 from rfl, Work.Spaces.pthIter_succ,
        Work.Spaces.pthIter_zero, Work.Spaces.pth]
    show (Work.Spaces.pthIter 2 Ψ s θ) ^ 2 * sEta θ
      = (deriv (fun t => deriv (fun θ' => Ψ s θ') t) θ) ^ 2 * sEta θ
    rw [h1]
  -- boundedness of the slices and of their `θ`-derivatives at `z` and at `z + 1`
  obtain ⟨M, hMpos, hMb⟩ :=
    SliceBddSqSigma (contDiffOn_slice Ψ hz (h.sm 2)) (hth z hz)
  obtain ⟨M₁, hM₁pos, hM₁b⟩ :=
    SliceBddSqSigma (contDiffOn_slice Ψ hz1 (h.sm 2)) (hth (z + 1) hz1)
  -- the `σ`-weighted square of the `z`-slice of `∂_z²Ψ` (from `memA`, divided by `z⁴`)
  have hp_int : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * sEta θ) Work.Spaces.Iθ := by
    have h0 := HkMemSliceSqSigma h.memA hz
    have hz2 : (z ^ 2) ≠ 0 := by positivity
    have h1 := h0.const_mul ((z ^ 2) ^ 2)⁻¹
    refine MeasureTheory.IntegrableOn.congr_fun h1 (fun θ _ => ?_) measurableSet_Icc
    field_simp
  -- the `σ`-weighted square of the `F`-slice
  have hF_int : MeasureTheory.IntegrableOn
      (fun θ => (F z θ) ^ 2 * sEta θ) Work.Spaces.Iθ := HkMemSliceSqSigma h.memF hz
  -- a.e. measurability of the `σ`-weighted slice norm of `∂_z²Ψ` (from the honest `z`-integral
  -- `h.memA.2`, after dividing by the measurable weight `w s²·s⁴`)
  have hγaem : AEMeasurable
      (fun s => ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)
      (volume.restrict Work.Spaces.Iz) := by
    have hG : ∀ s, (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
          (fun s θ => s ^ 2 * Work.Spaces.pzIter 2 Ψ s θ) s θ)
        = (Work.Spaces.w s) ^ 2 * (s ^ 4)
          * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ) := by
      intro s
      rw [← MeasureTheory.integral_const_mul]
      exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => by
        rw [HkIntegrand_zero_eq_Iθ α (fun s θ => s ^ 2 * Work.Spaces.pzIter 2 Ψ s θ) hθ]
        ring)
    have hm : AEMeasurable (fun s => (Work.Spaces.w s) ^ 2 * (s ^ 4)
        * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ))
        (volume.restrict Work.Spaces.Iz) :=
      (h.memA.2.congr_fun (fun s _ => hG s) measurableSet_Ici).aestronglyMeasurable.aemeasurable
    have hden : AEMeasurable (fun s : ℝ => (Work.Spaces.w s) ^ 2 * s ^ 4)
        (volume.restrict Work.Spaces.Iz) := by
      refine Measurable.aemeasurable ?_
      have hw : Measurable fun s : ℝ => Work.Spaces.w s := by
        show Measurable fun s : ℝ => (1 + s) ^ 2 / s ^ 2
        fun_prop
      exact (hw.pow_const 2).mul (measurable_id.pow_const 4)
    refine (hm.div hden).congr ?_
    have h0 : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ 0 := by
      rw [MeasureTheory.ae_iff]; simpa using MeasureTheory.measure_singleton (0 : ℝ)
    have h0' : ∀ᵐ s ∂(volume.restrict Work.Spaces.Iz), s ∈ Set.Ioi (0 : ℝ) := by
      rw [Work.Spaces.Iz, MeasureTheory.ae_restrict_iff' measurableSet_Ici]
      filter_upwards [h0] with s hs hmem
      exact lt_of_le_of_ne hmem (Ne.symm hs)
    filter_upwards [h0'] with s hs
    have hw : (Work.Spaces.w s) ^ 2 * s ^ 4 ≠ 0 := by
      have h1 : Work.Spaces.w s ≠ 0 := by
        show (1 + s) ^ 2 / s ^ 2 ≠ 0
        have hs' : s ≠ 0 := ne_of_gt hs
        have h1' : (1 : ℝ) + s ≠ 0 := by
          have hs0 : (0 : ℝ) < s := hs
          have : (0 : ℝ) < 1 + s := by linarith
          exact ne_of_gt this
        exact div_ne_zero (pow_ne_zero 2 h1') (pow_ne_zero 2 hs')
      exact mul_ne_zero (pow_ne_zero 2 h1) (pow_ne_zero 4 (ne_of_gt hs))
    exact mul_div_cancel_left₀ _ hw
  -- `γ` written with the `s⁴`-weight of `memA` (the form `HkMemSliceGammaLinTop` bounds)
  have hγw : ∀ s, (∫ θ in Work.Spaces.Iθ, ((s ^ 2) * Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)
      = (s ^ 2) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ) := by
    intro s
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => by ring)
  -- a.e. measurability of the *weighted* slice norm, on `Icc z (z+1)`
  have hγw_aem : AEMeasurable (fun s => ENNReal.ofReal
      (∫ θ in Work.Spaces.Iθ, ((s ^ 2) * Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ))
      (volume.restrict (Set.Icc z (z + 1))) := by
    have hG : ∀ s, (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
          (fun s θ => s ^ 2 * Work.Spaces.pzIter 2 Ψ s θ) s θ)
        = (Work.Spaces.w s) ^ 2 * (∫ θ in Work.Spaces.Iθ,
            ((s ^ 2) * Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ) := by
      intro s
      rw [← MeasureTheory.integral_const_mul]
      exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => by
        rw [HkIntegrand_zero_eq_Iθ α (fun s θ => s ^ 2 * Work.Spaces.pzIter 2 Ψ s θ) hθ]
        ring)
    have h1 : AEMeasurable (fun s => (Work.Spaces.w s) ^ 2 * (∫ θ in Work.Spaces.Iθ,
        ((s ^ 2) * Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)) (volume.restrict Work.Spaces.Iz) :=
      (h.memA.2.congr_fun (fun s _ => hG s) measurableSet_Ici).aestronglyMeasurable.aemeasurable
    -- remove the weight `w s²` (multiply the *unweighted* norm, whose measurability is `hγaem`,
    -- by the measurable factor `(s²)²`)
    have h2 : AEMeasurable (fun s => ∫ θ in Work.Spaces.Iθ,
        ((s ^ 2) * Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)
        (volume.restrict Work.Spaces.Iz) := by
      refine (hγaem.mul ((measurable_id.pow_const 2).pow_const 2).aemeasurable).congr ?_
      refine Filter.Eventually.of_forall fun s => ?_
      show (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ) * (s ^ 2) ^ 2
        = ∫ θ in Work.Spaces.Iθ, (s ^ 2 * Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ
      rw [mul_comm, (hγw s).symm]
    exact (h2.ennreal_ofReal).mono_measure
      (Measure.restrict_mono (fun s hs => Set.mem_Ici.mpr (le_trans (le_of_lt hz) hs.1)) le_rfl)
  -- the weighted version is exactly `HkMemSliceGammaLinTop`
  have hγw_lin : ∫⁻ s in Set.Icc z (z + 1), ENNReal.ofReal
      (∫ θ in Work.Spaces.Iθ, ((s ^ 2) * Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ) < ⊤ := by
    refine lt_of_eq_of_lt ?_ (HkMemSliceGammaLinTop h.memA hz)
    exact MeasureTheory.lintegral_congr fun s => by rw [hγw s]
  -- the unweighted lintegral, via the pointwise scaling `γ s ≤ (z⁴)⁻¹ · γ_w s` on `Icc z (z+1)`
  have hgamma : ∫⁻ s in Set.Icc z (z + 1), ENNReal.ofReal
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ) < ⊤ := by
    have hpt : ∀ s ∈ Set.Icc z (z + 1), ENNReal.ofReal
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)
        ≤ ENNReal.ofReal ((z ^ 4)⁻¹) * ENNReal.ofReal
            (∫ θ in Work.Spaces.Iθ, ((s ^ 2) * Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ) := by
      intro s hs
      have hs0 : 0 < s := lt_of_lt_of_le hz hs.1
      have hs4 : 0 < s ^ 4 := pow_pos hs0 4
      have hle : (s ^ 4)⁻¹ ≤ (z ^ 4)⁻¹ :=
        inv_anti₀ (pow_pos hz 4) (pow_le_pow_left₀ (le_of_lt hz) hs.1 4)
      have h1 : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)
          ≤ ((z ^ 4)⁻¹) * (∫ θ in Work.Spaces.Iθ,
              ((s ^ 2) * Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ) := by
        rw [hγw s]
        have heq : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)
            = (s ^ 4)⁻¹ * ((s ^ 2) ^ 2 * (∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)) := by
          rw [show (s ^ 2) ^ 2 = s ^ 4 from by ring, ← mul_assoc,
            inv_mul_cancel₀ (ne_of_gt hs4), one_mul]
        conv_lhs => rw [heq]
        refine mul_le_mul_of_nonneg_right hle (mul_nonneg (sq_nonneg (s ^ 2)) ?_)
        exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
          (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg hθ))
      calc ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)
          ≤ ENNReal.ofReal (((z ^ 4)⁻¹) * (∫ θ in Work.Spaces.Iθ,
              ((s ^ 2) * Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)) :=
            (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by positivity)
              (MeasureTheory.setIntegral_nonneg measurableSet_Icc
                (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg hθ))))).mpr h1
        _ = ENNReal.ofReal ((z ^ 4)⁻¹) * ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
              ((s ^ 2) * Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ) := by
            rw [ENNReal.ofReal_mul (by positivity)]
    calc ∫⁻ s in Set.Icc z (z + 1), ENNReal.ofReal
          (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)
        ≤ ∫⁻ s in Set.Icc z (z + 1), ENNReal.ofReal ((z ^ 4)⁻¹) * ENNReal.ofReal
            (∫ θ in Work.Spaces.Iθ, ((s ^ 2) * Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ) :=
          MeasureTheory.lintegral_mono_ae
            (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc hpt)
      _ = ENNReal.ofReal ((z ^ 4)⁻¹) * ∫⁻ s in Set.Icc z (z + 1), ENNReal.ofReal
            (∫ θ in Work.Spaces.Iθ, ((s ^ 2) * Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ) :=
          MeasureTheory.lintegral_const_mul'' _ hγw_aem
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hγw_lin
  -- a.e. measurability of `ofReal γ` on `Icc z (z+1)` (transfer from `hγaem`)
  have hγaemK : AEMeasurable (fun s => ENNReal.ofReal
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ))
      (volume.restrict (Set.Icc z (z + 1))) :=
    (hγaem.ennreal_ofReal).mono_measure (Measure.restrict_mono_set volume
      (fun s hs => Set.mem_Ici.mpr (le_trans (le_of_lt hz) hs.1)))
  -- the lintegral of `(1/2)(γ + π/2)` is finite (this is the constant `c` below)
  have hb_lin : ∫⁻ s in Set.Icc z (z + 1), ENNReal.ofReal
      ((1 / 2) * ((∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)
        + Real.pi / 2)) < ⊤ := by
    -- it suffices to bound the *decomposed* integrand `ofReal γ + ofReal (π/2)`, since
    -- `(1/2)(γ + π/2) ≤ γ + π/2`; this avoids pulling out the constant `ofReal (1/2)`
    have hsum : ∫⁻ s in Set.Icc z (z + 1), (ENNReal.ofReal
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)
        + ENNReal.ofReal (Real.pi / 2)) < ⊤ := by
      rw [MeasureTheory.lintegral_add_left' hγaemK]
      refine ENNReal.add_lt_top.mpr ⟨hgamma, ?_⟩
      rw [MeasureTheory.lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
    refine lt_of_le_of_lt ?_ hsum
    refine MeasureTheory.lintegral_mono_ae
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun s _ => ?_))
    have hγnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ :=
      MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg hθ))
    have hle : (1 / 2) * ((∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)
        + Real.pi / 2) ≤ (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)
        + Real.pi / 2 := by linarith [Real.pi_pos]
    calc ENNReal.ofReal ((1 / 2) * ((∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ) + Real.pi / 2))
        ≤ ENNReal.ofReal ((∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)
            + Real.pi / 2) := (ENNReal.ofReal_le_ofReal_iff (by linarith [Real.pi_pos])).mpr hle
      _ = ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)
            + ENNReal.ofReal (Real.pi / 2) := by
          rw [ENNReal.ofReal_add hγnn (by linarith [Real.pi_pos])]
  -- the `b`-independent constant bounding `|P_b(z)|`
  set c : ℝ := ENNReal.toReal (∫⁻ s in Set.Icc z (z + 1), ENNReal.ofReal
      ((1 / 2) * ((∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ)
        + Real.pi / 2))) with hcdef
  have hcnonneg : 0 ≤ c := by rw [hcdef]; exact ENNReal.toReal_nonneg
  -- joint continuity of `pz Ψ` on the open quadrant (finite order: `∂_z` of a `C¹` function)
  have hpz_cont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz Ψ p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have hU : IsOpen (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      isOpen_Ioi.prod isOpen_Ioo
    have hfd : ContinuousOn (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry Ψ) p)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
      have h1 : ContDiffOn ℝ 0 (fun p : ℝ × ℝ => fderivWithin ℝ (Function.uncurry Ψ)
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) p)
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
        (h.sm 1).fderivWithin (m := 0) hU.uniqueDiffOn (by norm_num)
      refine (contDiffOn_zero.mp h1).congr (fun p hp => ?_)
      show fderiv ℝ (Function.uncurry Ψ) p
        = fderivWithin ℝ (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) p
      rw [fderivWithin_of_isOpen hU hp]
    have h2 : ContinuousOn (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry Ψ) p (1, 0))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      hfd.clm_apply (continuousOn_const : ContinuousOn (fun _ : ℝ × ℝ => ((1 : ℝ), (0 : ℝ)))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    refine h2.congr (fun p hp => ?_)
    show Work.Spaces.pz Ψ p.1 p.2 = fderiv ℝ (Function.uncurry Ψ) p (1, 0)
    exact Work.Spaces.pz_eq_fderiv
      (((h.sm 1).differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hp))
  -- **first application**: `∂_z ∫_a^b Ψ s θ dθ = ∫_a^b pz Ψ s θ dθ` for `s ∈ [z, z+1]`
  have hZderiv : ∀ b ∈ Set.Ioo a (Real.pi / 2), ∀ s ∈ Set.Icc z (z + 1), HasDerivAt
      (fun t => ∫ θ in a..b, Ψ t θ) (∫ θ in a..b, Work.Spaces.pz Ψ s θ) s := by
    intro b hb s hs
    have hU : IsOpen (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      isOpen_Ioi.prod isOpen_Ioo
    have hsub : Set.Icc (s / 2) (2 * s) ×ˢ Set.Icc a b
        ⊆ Set.Icc (z / 2) (2 * (z + 1)) ×ˢ Set.Icc a b := by
      intro p hp
      exact ⟨⟨by linarith [hp.1.1, hs.1], by linarith [hp.1.2, hs.2]⟩, hp.2⟩
    have hrect : Set.Icc (z / 2) (2 * (z + 1)) ×ˢ Set.Icc a b
        ⊆ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) := by
      intro p hp
      exact ⟨lt_of_lt_of_le (by linarith [hz]) hp.1.1,
        ⟨lt_of_lt_of_le ha_pos hp.2.1, lt_of_le_of_lt hp.2.2 hb.2⟩⟩
    refine hasDerivAt_sliceIntegral (le_of_lt hb.1) ha_pos hb.2 (lt_of_lt_of_le hz hs.1)
      ?_ ?_ ?_
    · exact ((h.sm 0).continuousOn.mono hrect).mono hsub
    · exact (hpz_cont.mono hrect).mono hsub
    · intro t ht x hx
      have hxU : (x, t) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) :=
        ⟨lt_trans (by linarith [hz, hs.1] : (0 : ℝ) < s / 2) hx.1,
          lt_of_lt_of_le ha_pos ht.1, lt_of_le_of_lt ht.2 hb.2⟩
      exact (Work.Spaces.differentiableAt_curry_left
        (((h.sm 1).differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hxU))).hasDerivAt
  -- *** Stage A ***
  -- `F` is smooth on the open quadrant (it *is* `bslOp α Ψ` there), so each of its `θ`-slices
  -- is continuous on `(0, π/2)`; in particular `F z ·` is a genuine interval integral on `[a,b]`.
  have hFcont : ContinuousOn (fun θ => F z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have hU : IsOpen Qd := isOpen_Qd
    have hpz1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz Ψ)) Qd :=
      Work.FTS.EllipticEst.Blocks.contDiffOn_uncurry_pz_succ hU (n := 1) (h.sm 2)
    have hpz2 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pzIter 2 Ψ)) Qd := by
      have h2 : ContDiffOn ℝ (2 : WithTop ℕ∞) (Function.uncurry (Work.Spaces.pz Ψ)) Qd :=
        Work.FTS.EllipticEst.Blocks.contDiffOn_uncurry_pz_succ hU (n := 2) (h.sm 3)
      have h1 := Work.FTS.EllipticEst.Blocks.contDiffOn_uncurry_pz_succ hU (n := 1) h2
      rw [pzIter_two_eq Ψ]
      exact h1
    have hp2 : ContinuousOn (fun θ => Work.Spaces.pzIter 2 Ψ z θ)
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      (contDiffOn_slice (Work.Spaces.pzIter 2 Ψ) hz hpz2).continuousOn
    have hp1 : ContinuousOn (fun θ => Work.Spaces.pz Ψ z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      (contDiffOn_slice (Work.Spaces.pz Ψ) hz hpz1).continuousOn
    have hpsi : ContinuousOn (fun θ => Ψ z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      (contDiffOn_slice Ψ hz (h.sm 0)).continuousOn
    have hslice2 : ContDiffOn ℝ 2 (fun θ => Ψ z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      contDiffOn_slice Ψ hz (h.sm 2)
    have hpth2 : ContinuousOn (fun θ => Work.Spaces.pthIter 2 Ψ z θ)
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
      have h1 : ContDiffOn ℝ 1 (deriv (fun θ' => Ψ z θ')) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
        hslice2.deriv_of_isOpen isOpen_Ioo (by norm_num)
      have h2 : ContDiffOn ℝ 0 (deriv (fun θ' => deriv (fun θ'' => Ψ z θ'') θ'))
          (Set.Ioo (0 : ℝ) (Real.pi / 2)) := h1.deriv_of_isOpen isOpen_Ioo (by norm_num)
      rw [pthIter_two_eq Ψ z]
      exact h2.continuousOn
    have htan : ContDiffOn ℝ 2 Real.tan (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
      have h : ContDiffOn ℝ (2 : WithTop ℕ∞) (fun θ => Real.sin θ / Real.cos θ)
          (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
        ContDiffOn.div (Real.contDiff_sin.contDiffOn) (Real.contDiff_cos.contDiffOn)
          (fun θ hθ => ne_of_gt (Real.cos_pos_of_mem_Ioo
            ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩))
      have htanfun : Real.tan = fun θ : ℝ => Real.sin θ / Real.cos θ :=
        funext Real.tan_eq_sin_div_cos
      rw [htanfun]
      exact h
    have hpthtan : ContinuousOn (fun θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ)
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
      have htw : ContDiffOn ℝ 2 (fun θ => Real.tan θ * Ψ z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
        htan.mul hslice2
      have h1 : ContDiffOn ℝ 1 (deriv (fun θ => Real.tan θ * Ψ z θ))
          (Set.Ioo (0 : ℝ) (Real.pi / 2)) := htw.deriv_of_isOpen isOpen_Ioo (by norm_num)
      have hfun : (fun θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ)
          = deriv (fun θ => Real.tan θ * Ψ z θ) := rfl
      rw [hfun]
      exact h1.continuousOn
    have hcomb : ContinuousOn (fun θ => -(α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 Ψ z θ
        - (α * (5 + α) * z) * Work.Spaces.pz Ψ z θ
        + (-Work.Spaces.pthIter 2 Ψ z θ + Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ
            - 6 * Ψ z θ)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      ((hp2.const_mul (-(α ^ 2 * z ^ 2))).sub (hp1.const_mul (α * (5 + α) * z))).add
        ((hpth2.neg.add hpthtan).sub (hpsi.const_mul 6))
    refine hcomb.congr (fun θ hθ => ?_)
    simpa only [Work.Elliptic.bslOp_apply, Work.Elliptic.Lzero]
      using (h.eq z hz θ hθ.1 hθ.2).symm
  -- the `σ`-weighted square of the `∂_z²Ψ`-slice, for every `s > 0`
  have hps_int : ∀ s : ℝ, 0 < s → MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ) Work.Spaces.Iθ := by
    intro s hs
    have h0 := HkMemSliceSqSigma h.memA hs
    have h2 : (s ^ 2) ≠ 0 := by positivity
    have h1 := h0.const_mul ((s ^ 2) ^ 2)⁻¹
    refine MeasureTheory.IntegrableOn.congr_fun h1 (fun θ _ => ?_) measurableSet_Icc
    field_simp
  -- joint continuity of `pz Ψ` on the open quadrant
  have hUq : IsOpen (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    isOpen_Ioi.prod isOpen_Ioo
  have hpz1c : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz Ψ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.Blocks.contDiffOn_uncurry_pz_succ hUq (n := 1) (h.sm 2)
  have hpz2c : ContinuousOn (Function.uncurry (Work.Spaces.pzIter 2 Ψ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.Blocks.PzIterTwoContinuousOn hUq (h.sm 2)
  -- **second application**: `∂_z ∫_a^b pz Ψ s θ dθ = ∫_a^b pzIter 2 Ψ s θ dθ`
  have hPderiv : ∀ b ∈ Set.Ioo a (Real.pi / 2), ∀ s ∈ Set.Icc z (z + 1), HasDerivAt
      (fun t => ∫ θ in a..b, Work.Spaces.pz Ψ t θ) (∫ θ in a..b, Work.Spaces.pzIter 2 Ψ s θ)
      s := by
    intro b hb s hs
    have hsub : Set.Icc (s / 2) (2 * s) ×ˢ Set.Icc a b
        ⊆ Set.Icc (z / 2) (2 * (z + 1)) ×ˢ Set.Icc a b := by
      intro p hp
      exact ⟨⟨by linarith [hp.1.1, hs.1], by linarith [hp.1.2, hs.2]⟩, hp.2⟩
    have hrect : Set.Icc (z / 2) (2 * (z + 1)) ×ˢ Set.Icc a b
        ⊆ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) := by
      intro p hp
      exact ⟨lt_of_lt_of_le (by linarith [hz]) hp.1.1,
        ⟨lt_of_lt_of_le ha_pos hp.2.1, lt_of_le_of_lt hp.2.2 hb.2⟩⟩
    refine hasDerivAt_sliceIntegral (le_of_lt hb.1) ha_pos hb.2 (lt_of_lt_of_le hz hs.1) ?_ ?_ ?_
    · exact (hpz_cont.mono hrect).mono hsub
    · exact (hpz2c.mono hrect).mono hsub
    · intro t ht x hx
      have hxU : (x, t) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) :=
        ⟨lt_trans (by linarith [hz, hs.1] : (0 : ℝ) < s / 2) hx.1,
          lt_of_lt_of_le ha_pos ht.1, lt_of_le_of_lt ht.2 hb.2⟩
      have h := hasDerivAt_slice_of_contDiffOn_open hUq hpz1c hxU
      simpa only [show (2 : ℕ) = 1 + 1 from rfl, Work.Spaces.pzIter_succ,
        show (1 : ℕ) = 0 + 1 from rfl, Work.Spaces.pzIter_zero] using h
  -- *** Stage B ***
  -- the two `b`-independent `σ`-weighted slice norms
  set QP : ℝ := ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * sEta θ with hQPdef
  set QF : ℝ := ∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2 * sEta θ with hQFdef
  have hQPnn : 0 ≤ QP := by
    rw [hQPdef]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg hθ))
  have hQFnn : 0 ≤ QF := by
    rw [hQFdef]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg hθ))
  -- the third application: `Q_b` is differentiable, hence continuous
  have hpz2cd : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.pzIter 2 Ψ)) Qd := by
    have h1 : ContDiffOn ℝ (4 : WithTop ℕ∞) (Function.uncurry Ψ) Qd := h.sm 4
    have h2 : ContDiffOn ℝ (3 : WithTop ℕ∞) (Function.uncurry (Work.Spaces.pz Ψ)) Qd :=
      Work.FTS.EllipticEst.Blocks.contDiffOn_uncurry_pz_succ isOpen_Qd (n := 3) h1
    have h3 := Work.FTS.EllipticEst.Blocks.contDiffOn_uncurry_pz_succ isOpen_Qd (n := 2) h2
    rw [pzIter_two_eq Ψ]
    exact h3
  have hpz3cd : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pzIter 3 Ψ)) Qd := by
    have h4 := Work.FTS.EllipticEst.Blocks.contDiffOn_uncurry_pz_succ isOpen_Qd (n := 1) hpz2cd
    have h5 : Work.Spaces.pzIter 3 Ψ = Work.Spaces.pz (Work.Spaces.pzIter 2 Ψ) := rfl
    rw [h5]
    exact h4
  have hQderiv : ∀ b ∈ Set.Ioo a (Real.pi / 2), ∀ s ∈ Set.Icc z (z + 1), HasDerivAt
      (fun t => ∫ θ in a..b, Work.Spaces.pzIter 2 Ψ t θ)
      (∫ θ in a..b, Work.Spaces.pzIter 3 Ψ s θ) s := by
    intro b hb s hs
    have hsub : Set.Icc (s / 2) (2 * s) ×ˢ Set.Icc a b
        ⊆ Set.Icc (z / 2) (2 * (z + 1)) ×ˢ Set.Icc a b := by
      intro p hp
      exact ⟨⟨by linarith [hp.1.1, hs.1], by linarith [hp.1.2, hs.2]⟩, hp.2⟩
    have hrect : Set.Icc (z / 2) (2 * (z + 1)) ×ˢ Set.Icc a b
        ⊆ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) := by
      intro p hp
      exact ⟨lt_of_lt_of_le (by linarith [hz]) hp.1.1,
        ⟨lt_of_lt_of_le ha_pos hp.2.1, lt_of_le_of_lt hp.2.2 hb.2⟩⟩
    refine hasDerivAt_sliceIntegral (le_of_lt hb.1) ha_pos hb.2 (lt_of_lt_of_le hz hs.1) ?_ ?_ ?_
    · exact (hpz2c.mono hrect).mono hsub
    · exact ((hpz3cd.continuousOn).mono hrect).mono hsub
    · intro t ht x hx
      have hxU : (x, t) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) :=
        ⟨lt_trans (by linarith [hz, hs.1] : (0 : ℝ) < s / 2) hx.1,
          lt_of_lt_of_le ha_pos ht.1, lt_of_le_of_lt ht.2 hb.2⟩
      exact hasDerivAt_slice_of_contDiffOn_open hUq (hpz2cd.of_le (by norm_num)) hxU
  -- **the bound on `P_b(z)`** — the only place where the `z`-dependence of the data is used
  have hPb : ∀ b ∈ Set.Ioo a (Real.pi / 2),
      |∫ θ in a..b, Work.Spaces.pz Ψ z θ| ≤ (Real.pi / 2) * (M + M₁) + c := by
    intro b hb
    have hZder := hZderiv b hb
    have hPder := hPderiv b hb
    have hQder := hQderiv b hb
    have hcontP : ContinuousOn (fun s => ∫ θ in a..b, Work.Spaces.pz Ψ s θ)
        (Set.Icc z (z + 1)) := fun s hs => (hPder s hs).continuousAt.continuousWithinAt
    have hcontQ : ContinuousOn (fun s => ∫ θ in a..b, Work.Spaces.pzIter 2 Ψ s θ)
        (Set.Icc z (z + 1)) := fun s hs => (hQder s hs).continuousAt.continuousWithinAt
    have hceq : Set.uIcc z (z + 1) = Set.Icc z (z + 1) := Set.uIcc_of_le (by linarith)
    have hcontPu : ContinuousOn (fun s => ∫ θ in a..b, Work.Spaces.pz Ψ s θ)
        (Set.uIcc z (z + 1)) := by rw [hceq]; exact hcontP
    -- first fundamental-theorem step: `∫_z^{z+1} P_b = Z(z+1) - Z(z)`
    have h1 : (∫ t in z..(z + 1), (∫ θ in a..b, Work.Spaces.pz Ψ t θ))
        = (∫ θ in a..b, Ψ (z + 1) θ) - (∫ θ in a..b, Ψ z θ) := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun t => ∫ θ in a..b, Ψ t θ)
        (f' := fun s => ∫ θ in a..b, Work.Spaces.pz Ψ s θ) ?_ hcontPu.intervalIntegrable
      intro s hs
      rw [hceq] at hs
      exact hZder s hs
    -- second step: `P_b(t) - P_b(z) = ∫_z^t Q_b`
    have h2 : ∀ t ∈ Set.Icc z (z + 1),
        (∫ θ in a..b, Work.Spaces.pz Ψ t θ) - (∫ θ in a..b, Work.Spaces.pz Ψ z θ)
          = ∫ s in z..t, (∫ θ in a..b, Work.Spaces.pzIter 2 Ψ s θ) := by
      intro t ht
      have hle : z ≤ t := ht.1
      have hsub : Set.uIcc z t ⊆ Set.Icc z (z + 1) := by
        rw [Set.uIcc_of_le hle]
        exact Set.Icc_subset_Icc le_rfl ht.2
      have hint : IntervalIntegrable (fun s => ∫ θ in a..b, Work.Spaces.pzIter 2 Ψ s θ)
          volume z t := (hcontQ.mono hsub).intervalIntegrable
      exact (intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun s hs => hPder s (hsub hs)) hint).symm
    -- the algebraic consequence
    have h3 : (∫ θ in a..b, Work.Spaces.pz Ψ z θ)
        = ((∫ θ in a..b, Ψ (z + 1) θ) - (∫ θ in a..b, Ψ z θ))
          - ∫ t in z..(z + 1), ((∫ θ in a..b, Work.Spaces.pz Ψ t θ)
              - (∫ θ in a..b, Work.Spaces.pz Ψ z θ)) := by
      have hsub2 : (∫ t in z..(z + 1), ((∫ θ in a..b, Work.Spaces.pz Ψ t θ)
            - (∫ θ in a..b, Work.Spaces.pz Ψ z θ)))
          = (∫ t in z..(z + 1), (∫ θ in a..b, Work.Spaces.pz Ψ t θ))
            - ∫ t in z..(z + 1), (∫ θ in a..b, Work.Spaces.pz Ψ z θ) :=
        intervalIntegral.integral_sub hcontPu.intervalIntegrable intervalIntegrable_const
      rw [hsub2, h1, intervalIntegral.integral_const]
      ring
    -- the uniform bound on the subtracted term
    have hB : ∀ t ∈ Set.Icc z (z + 1),
        |(∫ θ in a..b, Work.Spaces.pz Ψ t θ) - (∫ θ in a..b, Work.Spaces.pz Ψ z θ)| ≤ c := by
      intro t ht
      rcases eq_or_lt_of_le ht.1 with hzt | hzt
      · rw [← hzt, sub_self, abs_zero]; exact hcnonneg
      · rw [h2 t ht]
        have hQint : IntegrableOn (fun s => ∫ θ in a..b, Work.Spaces.pzIter 2 Ψ s θ)
            (Set.Icc z (z + 1)) := hcontQ.integrableOn_Icc
        have hQabs : IntegrableOn (fun s => |∫ θ in a..b, Work.Spaces.pzIter 2 Ψ s θ|)
            (Set.Icc z (z + 1)) := by
          simpa only [Real.norm_eq_abs, MeasureTheory.IntegrableOn] using hQint.norm
        have hstep : |∫ s in z..t, (∫ θ in a..b, Work.Spaces.pzIter 2 Ψ s θ)|
            ≤ ∫ s in Set.Icc z (z + 1), |∫ θ in a..b, Work.Spaces.pzIter 2 Ψ s θ| := by
          refine le_trans (intervalIntegral.abs_integral_le_integral_abs hzt.le) ?_
          rw [intervalIntegral.integral_of_le hzt.le]
          refine MeasureTheory.setIntegral_mono_set hQabs
            (Filter.Eventually.of_forall (fun s => abs_nonneg _))
            (Filter.Eventually.of_forall (fun s hs => ?_))
          exact ⟨le_of_lt hs.1, le_trans hs.2 ht.2⟩
        refine le_trans hstep ?_
        calc (∫ s in Set.Icc z (z + 1), |∫ θ in a..b, Work.Spaces.pzIter 2 Ψ s θ|)
              ≤ ENNReal.toReal (∫⁻ s in Set.Icc z (z + 1), ENNReal.ofReal
                  |∫ θ in a..b, Work.Spaces.pzIter 2 Ψ s θ|) :=
                setIntegral_le_toReal_lintegral _
                  (Filter.Eventually.of_forall (fun s => abs_nonneg _))
            _ ≤ ENNReal.toReal (∫⁻ s in Set.Icc z (z + 1), ENNReal.ofReal
                  ((1 / 2) * ((∫ θ in Work.Spaces.Iθ,
                      (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ) + Real.pi / 2))) := by
                refine ENNReal.toReal_mono (ne_of_lt hb_lin) (MeasureTheory.lintegral_mono_ae ?_)
                refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun s hs => ?_)
                have hs0 : 0 < s := lt_of_lt_of_le hz hs.1
                have hQb := le_trans
                  (intervalIntegral.abs_integral_le_integral_abs (le_of_lt hb.1))
                  (Ioc_abs_le_half ha_pos hb.2 (le_of_lt hb.1) (hps_int s hs0))
                have hnn : 0 ≤ (1 / 2) * ((∫ θ in Work.Spaces.Iθ,
                    (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * sEta θ) + Real.pi / 2) :=
                  mul_nonneg (by norm_num) (add_nonneg
                    (MeasureTheory.setIntegral_nonneg measurableSet_Icc
                      (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg hθ)))
                    (by linarith [Real.pi_pos]))
                exact (ENNReal.ofReal_le_ofReal_iff hnn).mpr hQb
            _ = c := rfl
    -- the two slice integrals at `z` and `z + 1`
    have hZc : ∀ C : ℝ, 0 ≤ C → (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |Ψ z θ| ≤ C) →
        |∫ θ in a..b, Ψ z θ| ≤ C * (Real.pi / 2) := by
      intro C hC hbnd
      have hmain : |∫ θ in a..b, Ψ z θ| ≤ C * |b - a| := by
        have h := intervalIntegral.norm_integral_le_of_norm_le_const
          (f := fun θ => Ψ z θ) (a := a) (b := b) (C := C) (fun θ hθ => by
            rw [Real.norm_eq_abs]
            rw [Set.uIoc_of_le (le_of_lt hb.1)] at hθ
            exact hbnd θ ⟨lt_of_lt_of_le ha_pos (le_of_lt hθ.1), lt_of_le_of_lt hθ.2 hb.2⟩)
        simpa only [Real.norm_eq_abs] using h
      refine le_trans hmain (mul_le_mul_of_nonneg_left ?_ hC)
      rw [abs_of_nonneg (by linarith [hb.1])]
      linarith [hb.2, Real.pi_pos]
    have hZc1 : ∀ C : ℝ, 0 ≤ C → (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |Ψ (z + 1) θ| ≤ C) →
        |∫ θ in a..b, Ψ (z + 1) θ| ≤ C * (Real.pi / 2) := by
      intro C hC hbnd
      have hmain : |∫ θ in a..b, Ψ (z + 1) θ| ≤ C * |b - a| := by
        have h := intervalIntegral.norm_integral_le_of_norm_le_const
          (f := fun θ => Ψ (z + 1) θ) (a := a) (b := b) (C := C) (fun θ hθ => by
            rw [Real.norm_eq_abs]
            rw [Set.uIoc_of_le (le_of_lt hb.1)] at hθ
            exact hbnd θ ⟨lt_of_lt_of_le ha_pos (le_of_lt hθ.1), lt_of_le_of_lt hθ.2 hb.2⟩)
        simpa only [Real.norm_eq_abs] using h
      refine le_trans hmain (mul_le_mul_of_nonneg_left ?_ hC)
      rw [abs_of_nonneg (by linarith [hb.1])]
      linarith [hb.2, Real.pi_pos]
    have hZ1 := hZc1 M₁ hM₁pos.le (fun θ hθ => (hM₁b θ hθ).2)
    have hZ0 := hZc M hMpos.le (fun θ hθ => (hMb θ hθ).2)
    calc |∫ θ in a..b, Work.Spaces.pz Ψ z θ|
        = |((∫ θ in a..b, Ψ (z + 1) θ) - (∫ θ in a..b, Ψ z θ))
            - ∫ t in z..(z + 1), ((∫ θ in a..b, Work.Spaces.pz Ψ t θ)
                - (∫ θ in a..b, Work.Spaces.pz Ψ z θ))| := by
          conv_lhs => rw [h3]
      _ ≤ |(∫ θ in a..b, Ψ (z + 1) θ) - (∫ θ in a..b, Ψ z θ)|
            + |∫ t in z..(z + 1), ((∫ θ in a..b, Work.Spaces.pz Ψ t θ)
                - (∫ θ in a..b, Work.Spaces.pz Ψ z θ))| := by
          have := abs_sub_le ((∫ θ in a..b, Ψ (z + 1) θ) - (∫ θ in a..b, Ψ z θ))
            (0 : ℝ) (∫ t in z..(z + 1), ((∫ θ in a..b, Work.Spaces.pz Ψ t θ)
                - (∫ θ in a..b, Work.Spaces.pz Ψ z θ)))
          simpa using this
      _ ≤ (M₁ * (Real.pi / 2) + M * (Real.pi / 2)) + c := by
          refine add_le_add ?_ ?_
          · calc |(∫ θ in a..b, Ψ (z + 1) θ) - (∫ θ in a..b, Ψ z θ)|
                ≤ |∫ θ in a..b, Ψ (z + 1) θ| + |∫ θ in a..b, Ψ z θ| := by
                  simpa using abs_sub_le (∫ θ in a..b, Ψ (z + 1) θ) (0 : ℝ) (∫ θ in a..b, Ψ z θ)
              _ ≤ M₁ * (Real.pi / 2) + M * (Real.pi / 2) := add_le_add hZ1 hZ0
          · have hmain : |∫ t in z..(z + 1), ((∫ θ in a..b, Work.Spaces.pz Ψ t θ)
                - (∫ θ in a..b, Work.Spaces.pz Ψ z θ))| ≤ c := by
              have h := intervalIntegral.norm_integral_le_of_norm_le_const
                (f := fun t => (∫ θ in a..b, Work.Spaces.pz Ψ t θ)
                  - (∫ θ in a..b, Work.Spaces.pz Ψ z θ)) (a := z) (b := z + 1) (C := c)
                (fun t ht => by
                  rw [Real.norm_eq_abs]
                  rw [Set.uIoc_of_le (by linarith : z ≤ z + 1)] at ht
                  exact hB t ⟨le_of_lt ht.1, ht.2⟩)
              simpa only [Real.norm_eq_abs, show (z + 1) - z = 1 from by ring, abs_one,
                mul_one] using h
            exact hmain
      _ = (Real.pi / 2) * (M + M₁) + c := by ring
  -- the per-`b` bound
  set K : ℝ := |Real.tan a * Ψ z a| + (α * (5 + α) * z) * ((Real.pi / 2) * (M + M₁) + c)
      + (α ^ 2 * z ^ 2) * ((1 / 2) * (QP + Real.pi / 2)) + (1 / 2) * (QF + Real.pi / 2)
      + 2 * M + 6 * (M * (Real.pi / 2)) with hKdef
  have key : ∀ b ∈ Set.Ioo a (Real.pi / 2), |Real.tan b * Ψ z b| ≤ K := by
    intro b hb
    rw [hKdef]
    have hab' : Set.uIcc a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
      intro θ hθ
      rw [Set.uIcc_of_le (le_of_lt hb.1)] at hθ
      exact ⟨lt_of_lt_of_le ha_pos hθ.1, lt_of_le_of_lt hθ.2 hb.2⟩
    have hFint : IntervalIntegrable (fun θ => F z θ) volume a b :=
      (hFcont.mono hab').intervalIntegrable
    have hcontp : ContinuousOn (fun θ => Work.Spaces.pzIter 2 Ψ z θ) (Set.uIcc a b) := by
      have h2 : ContDiffOn ℝ 1 (fun θ => Work.Spaces.pzIter 2 Ψ z θ)
          (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
        contDiffOn_slice (Work.Spaces.pzIter 2 Ψ) hz (n := 1) (hpz2cd.of_le (by norm_num))
      exact h2.continuousOn.mono hab'
    have hpI : IntervalIntegrable (fun θ => Work.Spaces.pzIter 2 Ψ z θ) volume a b :=
      hcontp.intervalIntegrable
    have hcontq : ContinuousOn (fun θ => Work.Spaces.pz Ψ z θ) (Set.uIcc a b) := by
      have h2 : ContDiffOn ℝ 1 (fun θ => Work.Spaces.pz Ψ z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
        contDiffOn_slice (Work.Spaces.pz Ψ) hz (n := 1) hpz1c
      exact h2.continuousOn.mono hab'
    have hqI : IntervalIntegrable (fun θ => Work.Spaces.pz Ψ z θ) volume a b :=
      hcontq.intervalIntegrable
    have hcontψ : ContinuousOn (fun θ => Ψ z θ) (Set.uIcc a b) := by
      have h2 : ContDiffOn ℝ 0 (fun θ => Ψ z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
        contDiffOn_slice Ψ hz (n := 0) (h.sm 0)
      exact h2.continuousOn.mono hab'
    have hψI : IntervalIntegrable (fun θ => Ψ z θ) volume a b := hcontψ.intervalIntegrable
    have hslice1 : ContDiffOn ℝ 1 (fun θ => Ψ z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      contDiffOn_slice Ψ hz (n := 1) (h.sm 1)
    have hslice2 : ContDiffOn ℝ 2 (fun θ => Ψ z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      contDiffOn_slice Ψ hz (n := 2) (h.sm 2)
    have hcontp2 : ContinuousOn (fun θ => deriv (fun t => deriv (fun θ' => Ψ z θ') t) θ)
        (Set.uIcc a b) := by
      have h1 : ContDiffOn ℝ 1 (deriv (fun θ' => Ψ z θ')) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
        hslice2.deriv_of_isOpen isOpen_Ioo (by norm_num)
      have h2 : ContDiffOn ℝ 0 (fun θ => deriv (fun t => deriv (fun θ' => Ψ z θ') t) θ)
          (Set.Ioo (0 : ℝ) (Real.pi / 2)) := h1.deriv_of_isOpen isOpen_Ioo (by norm_num)
      exact h2.continuousOn.mono hab'
    have hp2I : IntervalIntegrable (fun θ => deriv (fun t => deriv (fun θ' => Ψ z θ') t) θ)
        volume a b := hcontp2.intervalIntegrable
    have htansm : ContDiffOn ℝ 2 Real.tan (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
      have h : ContDiffOn ℝ (2 : WithTop ℕ∞) (fun θ => Real.sin θ / Real.cos θ)
          (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
        ContDiffOn.div (Real.contDiff_sin.contDiffOn) (Real.contDiff_cos.contDiffOn)
          (fun θ hθ => ne_of_gt (Real.cos_pos_of_mem_Ioo
            ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩))
      have htanfun : Real.tan = fun θ : ℝ => Real.sin θ / Real.cos θ :=
        funext Real.tan_eq_sin_div_cos
      rw [htanfun]
      exact h
    have htw : ContDiffOn ℝ 2 (fun θ => Real.tan θ * Ψ z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      htansm.mul hslice2
    have hconttw : ContinuousOn (deriv (fun θ => Real.tan θ * Ψ z θ)) (Set.uIcc a b) := by
      have h1 : ContDiffOn ℝ 1 (deriv (fun θ => Real.tan θ * Ψ z θ))
          (Set.Ioo (0 : ℝ) (Real.pi / 2)) := htw.deriv_of_isOpen isOpen_Ioo (by norm_num)
      exact h1.continuousOn.mono hab'
    have htwI : IntervalIntegrable (deriv (fun θ => Real.tan θ * Ψ z θ)) volume a b :=
      hconttw.intervalIntegrable
    -- the derivative facts for the three functions of `TanSliceFTC`
    have hdu : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), DifferentiableAt ℝ (fun θ' => Ψ z θ') θ :=
      fun θ hθ => (hslice1.contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt (by norm_num)
    have hdu1 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        DifferentiableAt ℝ (deriv (fun θ' => Ψ z θ')) θ := by
      intro θ hθ
      have h1 : ContDiffOn ℝ 1 (deriv (fun θ' => Ψ z θ')) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
        hslice2.deriv_of_isOpen isOpen_Ioo (by norm_num)
      exact (h1.contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt (by norm_num)
    have hdtw : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        DifferentiableAt ℝ (fun θ' => Real.tan θ' * Ψ z θ') θ :=
      fun θ hθ => (htw.contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt (by norm_num)
    -- the amplitude `A` of the `tan`-identity, and its `(a,b)`-integral
    set A : ℝ → ℝ := fun θ => α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ
      + α * (5 + α) * z * Work.Spaces.pz Ψ z θ + F z θ with hAdef
    have hAI : IntervalIntegrable A volume a b := by
      rw [hAdef]
      exact ((hpI.const_mul (α ^ 2 * z ^ 2)).add (hqI.const_mul (α * (5 + α) * z))).add hFint
    have hsplit : (∫ θ in a..b, A θ)
        = (α ^ 2 * z ^ 2) * (∫ θ in a..b, Work.Spaces.pzIter 2 Ψ z θ)
          + (α * (5 + α) * z) * (∫ θ in a..b, Work.Spaces.pz Ψ z θ)
          + (∫ θ in a..b, F z θ) := by
      rw [hAdef]
      rw [intervalIntegral.integral_add
        ((hpI.const_mul (α ^ 2 * z ^ 2)).add (hqI.const_mul (α * (5 + α) * z))) hFint]
      rw [intervalIntegral.integral_add (hpI.const_mul (α ^ 2 * z ^ 2))
        (hqI.const_mul (α * (5 + α) * z))]
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    -- the `tan`-identity
    have heq : ∀ θ ∈ Set.Ioo a b, deriv (fun t => Real.tan t * Ψ z t) θ
        = A θ + deriv (fun t => deriv (fun θ' => Ψ z θ') t) θ + 6 * Ψ z θ := by
      intro θ hθ
      have hθo : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
        ⟨by linarith [hθ.1, ha_pos], by linarith [hθ.2, hb.2]⟩
      have hb' := h.eq z hz θ hθo.1 hθo.2
      rw [Work.Elliptic.bslOp_apply, Work.Elliptic.Lzero] at hb'
      rw [hAdef]
      simp only [pthIter_two_eq_fun Ψ, Work.Spaces.pth] at hb' ⊢
      linear_combination (norm := ring_nf) hb'
    have hid := TanSliceFTC (u := fun θ => Ψ z θ) (A := A) (a := a) (b := b) (le_of_lt hb.1)
      (fun θ hθ => (hdu θ (hab' hθ)).hasDerivAt)
      (fun θ hθ => (hdu1 θ (hab' hθ)).hasDerivAt)
      (fun θ hθ => (hdtw θ (hab' hθ)).hasDerivAt)
      hp2I htwI hAI hψI heq
    -- the individual bounds
    have htanb : |(α ^ 2 * z ^ 2) * (∫ θ in a..b, Work.Spaces.pzIter 2 Ψ z θ)|
        ≤ (α ^ 2 * z ^ 2) * ((1 / 2) * (QP + Real.pi / 2)) := by
      rw [abs_mul, abs_of_nonneg (by positivity)]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact le_trans (intervalIntegral.abs_integral_le_integral_abs (le_of_lt hb.1))
        (Ioc_abs_le_half ha_pos hb.2 (le_of_lt hb.1) hp_int)
    have hqbound : |∫ θ in a..b, Work.Spaces.pz Ψ z θ| ≤ (Real.pi / 2) * (M + M₁) + c :=
      hPb b hb
    have htanF : |∫ θ in a..b, F z θ| ≤ (1 / 2) * (QF + Real.pi / 2) :=
      le_trans (intervalIntegral.abs_integral_le_integral_abs (le_of_lt hb.1))
        (Ioc_abs_le_half ha_pos hb.2 (le_of_lt hb.1) hF_int)
    have hψbd : |∫ θ in a..b, Ψ z θ| ≤ M * (Real.pi / 2) := by
      have hmain : |∫ θ in a..b, Ψ z θ| ≤ M * |b - a| := by
        have h := intervalIntegral.norm_integral_le_of_norm_le_const
          (f := fun θ => Ψ z θ) (a := a) (b := b) (C := M) (fun θ hθ => by
            rw [Real.norm_eq_abs]
            rw [Set.uIoc_of_le (le_of_lt hb.1)] at hθ
            exact (hMb θ ⟨lt_of_lt_of_le ha_pos (le_of_lt hθ.1), lt_of_le_of_lt hθ.2 hb.2⟩).2)
        simpa only [Real.norm_eq_abs] using h
      refine le_trans hmain (mul_le_mul_of_nonneg_left ?_ hMpos.le)
      rw [abs_of_nonneg (by linarith [hb.1])]
      linarith [hb.2, Real.pi_pos]
    have hderivbd : |deriv (fun θ => Ψ z θ) b - deriv (fun θ => Ψ z θ) a| ≤ 2 * M := by
      have h1 : |deriv (fun θ => Ψ z θ) b| ≤ M :=
        (hMb b ⟨lt_trans ha_pos hb.1, hb.2⟩).1
      have h2 : |deriv (fun θ => Ψ z θ) a| ≤ M :=
        (hMb a ⟨ha_pos, ha_lt⟩).1
      have htri : |deriv (fun θ => Ψ z θ) b - deriv (fun θ => Ψ z θ) a|
          ≤ |deriv (fun θ => Ψ z θ) b| + |deriv (fun θ => Ψ z θ) a| := by
        have := abs_sub_le (deriv (fun θ => Ψ z θ) b) 0 (deriv (fun θ => Ψ z θ) a)
        simpa using this
      linarith
    -- the `tan`-identity solved for the left-hand side
    have hid' : Real.tan b * Ψ z b
        = Real.tan a * Ψ z a + (∫ θ in a..b, A θ)
          + (deriv (fun θ => Ψ z θ) b - deriv (fun θ => Ψ z θ) a)
          + 6 * ∫ θ in a..b, Ψ z θ := by linarith [hid]
    -- the `(a,b)`-integral of the amplitude
    have hAbound : |∫ θ in a..b, A θ| ≤ (α ^ 2 * z ^ 2) * ((1 / 2) * (QP + Real.pi / 2))
        + (α * (5 + α) * z) * ((Real.pi / 2) * (M + M₁) + c)
        + (1 / 2) * (QF + Real.pi / 2) := by
      rw [hsplit]
      have htri : |(α ^ 2 * z ^ 2) * (∫ θ in a..b, Work.Spaces.pzIter 2 Ψ z θ)
          + (α * (5 + α) * z) * (∫ θ in a..b, Work.Spaces.pz Ψ z θ)
          + (∫ θ in a..b, F z θ)|
          ≤ |(α ^ 2 * z ^ 2) * (∫ θ in a..b, Work.Spaces.pzIter 2 Ψ z θ)|
            + |(α * (5 + α) * z) * (∫ θ in a..b, Work.Spaces.pz Ψ z θ)|
            + |∫ θ in a..b, F z θ| := by
        have h2 := abs_add_le ((α ^ 2 * z ^ 2) * (∫ θ in a..b, Work.Spaces.pzIter 2 Ψ z θ)
          + (α * (5 + α) * z) * (∫ θ in a..b, Work.Spaces.pz Ψ z θ)) (∫ θ in a..b, F z θ)
        have h1 := abs_add_le ((α ^ 2 * z ^ 2) * (∫ θ in a..b, Work.Spaces.pzIter 2 Ψ z θ))
          ((α * (5 + α) * z) * (∫ θ in a..b, Work.Spaces.pz Ψ z θ))
        linarith
      have hbd : |(α ^ 2 * z ^ 2) * (∫ θ in a..b, Work.Spaces.pzIter 2 Ψ z θ)|
            + |(α * (5 + α) * z) * (∫ θ in a..b, Work.Spaces.pz Ψ z θ)|
            + |∫ θ in a..b, F z θ| ≤ (α ^ 2 * z ^ 2) * ((1 / 2) * (QP + Real.pi / 2))
              + (α * (5 + α) * z) * ((Real.pi / 2) * (M + M₁) + c)
              + (1 / 2) * (QF + Real.pi / 2) := by
        have h1 : |(α ^ 2 * z ^ 2) * (∫ θ in a..b, Work.Spaces.pzIter 2 Ψ z θ)|
            ≤ (α ^ 2 * z ^ 2) * ((1 / 2) * (QP + Real.pi / 2)) := by
          rw [abs_mul, abs_of_nonneg (by positivity)]
          exact mul_le_mul_of_nonneg_left (le_trans
            (intervalIntegral.abs_integral_le_integral_abs (le_of_lt hb.1))
            (Ioc_abs_le_half (g := fun θ => Work.Spaces.pzIter 2 Ψ z θ) ha_pos hb.2
              (le_of_lt hb.1) hp_int)) (by positivity)
        have h2 : |(α * (5 + α) * z) * (∫ θ in a..b, Work.Spaces.pz Ψ z θ)|
            ≤ (α * (5 + α) * z) * ((Real.pi / 2) * (M + M₁) + c) := by
          have hc2 : 0 ≤ α * (5 + α) * z :=
            mul_nonneg (mul_nonneg h.hα.le (by linarith [h.hα])) hz.le
          rw [abs_mul, abs_of_nonneg hc2]
          exact mul_le_mul_of_nonneg_left (hPb b hb) hc2
        have h3 : |∫ θ in a..b, F z θ| ≤ (1 / 2) * (QF + Real.pi / 2) :=
          le_trans (intervalIntegral.abs_integral_le_integral_abs (le_of_lt hb.1))
            (Ioc_abs_le_half (g := fun θ => F z θ) ha_pos hb.2 (le_of_lt hb.1) hF_int)
        linarith
      linarith
    rw [hid']
    have htri : |Real.tan a * Ψ z a + (∫ θ in a..b, A θ)
        + (deriv (fun θ => Ψ z θ) b - deriv (fun θ => Ψ z θ) a)
        + 6 * ∫ θ in a..b, Ψ z θ|
        ≤ |Real.tan a * Ψ z a| + |∫ θ in a..b, A θ|
          + |deriv (fun θ => Ψ z θ) b - deriv (fun θ => Ψ z θ) a|
          + |6 * ∫ θ in a..b, Ψ z θ| := by
      have h1 := abs_add_le (Real.tan a * Ψ z a) (∫ θ in a..b, A θ)
      have h2 := abs_add_le (Real.tan a * Ψ z a + (∫ θ in a..b, A θ))
        (deriv (fun θ => Ψ z θ) b - deriv (fun θ => Ψ z θ) a)
      have h3 := abs_add_le (Real.tan a * Ψ z a + (∫ θ in a..b, A θ)
        + (deriv (fun θ => Ψ z θ) b - deriv (fun θ => Ψ z θ) a))
        (6 * ∫ θ in a..b, Ψ z θ)
      exact le_trans h3 (le_trans (add_le_add h2 le_rfl)
        (add_le_add (add_le_add h1 le_rfl) le_rfl))
    have hfin : |Real.tan a * Ψ z a| + |∫ θ in a..b, A θ|
          + |deriv (fun θ => Ψ z θ) b - deriv (fun θ => Ψ z θ) a|
          + |6 * ∫ θ in a..b, Ψ z θ|
        ≤ |Real.tan a * Ψ z a|
          + (α * (5 + α) * z) * ((Real.pi / 2) * (M + M₁) + c)
          + (α ^ 2 * z ^ 2) * ((1 / 2) * (QP + Real.pi / 2))
          + (1 / 2) * (QF + Real.pi / 2) + 2 * M + 6 * (M * (Real.pi / 2)) := by
      have h6 : |6 * ∫ θ in a..b, Ψ z θ| = 6 * |∫ θ in a..b, Ψ z θ| := by
        rw [abs_mul]; norm_num
      have h6b : 6 * |∫ θ in a..b, Ψ z θ| ≤ 6 * (M * (Real.pi / 2)) :=
        mul_le_mul_of_nonneg_left hψbd (by norm_num)
      rw [h6]
      linarith [hAbound, hderivbd, h6b]
    linarith
  -- the squeeze
  have hKlim : Tendsto (fun θ => K / Real.tan θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    have hcos : Tendsto Real.cos (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
      have h := (Real.continuous_cos.continuousAt (x := Real.pi / 2)).tendsto
      have h' : nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) ≤ 𝓝 (Real.pi / 2) := inf_le_left
      simpa [Real.cos_pi_div_two] using h.mono_left h'
    have hsin : Tendsto Real.sin (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 1) := by
      have h := (Real.continuous_sin.continuousAt (x := Real.pi / 2)).tendsto
      have h' : nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) ≤ 𝓝 (Real.pi / 2) := inf_le_left
      simpa [Real.sin_pi_div_two] using h.mono_left h'
    have h2 : Tendsto (fun θ => K * Real.cos θ / Real.sin θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
      have h1 : Tendsto (fun θ => K * Real.cos θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
        simpa using (tendsto_const_nhds.mul hcos)
      have := h1.div hsin one_ne_zero
      rw [show (0 : ℝ) / 1 = 0 from by norm_num] at this
      exact this
    refine Tendsto.congr' ?_ h2
    filter_upwards [Ioo_mem_nhdsLT ha_lt] with θ hθ
    have hs : Real.sin θ ≠ 0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi
      (by linarith [ha_pos, hθ.1]) (by linarith [hθ.2, Real.pi_pos]))
    have hc : Real.cos θ ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [ha_pos, hθ.1], by linarith [hθ.2, Real.pi_pos]⟩)
    rw [Real.tan_eq_sin_div_cos]
    field_simp
  refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
  refine squeeze_zero' (Filter.Eventually.of_forall (fun θ => norm_nonneg _)) ?_ hKlim
  filter_upwards [Ioo_mem_nhdsLT ha_lt] with θ hθ
  have htanpos : 0 < Real.tan θ :=
    Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith [ha_pos, hθ.1]) hθ.2
  rw [le_div_iff₀ htanpos]
  calc ‖Ψ z θ‖ * Real.tan θ = |Real.tan θ * Ψ z θ| := by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos htanpos, mul_comm]
    _ ≤ K := key θ hθ

end Work.FTS.EllipticEst.Honest.Yc
