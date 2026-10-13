/-
Auxiliary lemmas for the compactly supported case `ThetaU.compact_interpol`:

* smoothness (finite orders) of the derived functions `pz G`, `pth G`, `Dz G`, `pth (pth G)`,
  `Dz (pth (pth G))`, ... on the open strip `(0,∞) × (-1, π/2+1)` where `G` is smooth;
* Clairaut identities `pth (Dz G) = Dz (pth G)`, `pth (pth (Dz G)) = Dz (pth (pth G))`;
* integrability of `(z,θ) ↦ w z ² · σ θ · F z θ` for the product measure when `F` is supported
  in `[δ,R]` in `z` and bounded there (the input of the Fubini steps).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.Spaces.mixed_comm
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.FTS.EllipticEst.ThetaU.OpenAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.ThetaU

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The strip of smoothness of the hypothesis of the open interpolation statement. -/
def OStrip : Set (ℝ × ℝ) := Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)

theorem isOpen_OStrip : IsOpen OStrip := isOpen_Ioi.prod isOpen_Ioo

/-! ## Smoothness of the derived functions on the strip -/

theorem contDiffOn_uncurry_pz_fin {G : ℝ → ℝ → ℝ} {n : ℕ}
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) OStrip) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pz G)) OStrip := by
  have hchain : ∀ p ∈ OStrip,
      Work.Spaces.pz G p.1 p.2 = fderiv ℝ (Function.uncurry G) p (1, 0) := fun p hp =>
    Work.Spaces.pz_eq_fderiv
      ((h.differentiableOn (by norm_num : (n + 1 : WithTop ℕ∞) ≠ 0)).differentiableAt
        (isOpen_OStrip.mem_nhds hp))
  have hfd : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) OStrip :=
    h.fderiv_of_isOpen isOpen_OStrip (m := n) (by norm_num)
  have hcomp : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (1, 0)) OStrip :=
    hfd.clm_apply contDiffOn_const
  refine hcomp.congr (fun p hp => ?_)
  exact hchain p hp

theorem contDiffOn_uncurry_pth_fin {G : ℝ → ℝ → ℝ} {n : ℕ}
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) OStrip) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pth G)) OStrip := by
  have hchain : ∀ p ∈ OStrip,
      Work.Spaces.pth G p.1 p.2 = fderiv ℝ (Function.uncurry G) p (0, 1) := fun p hp =>
    Work.Spaces.pth_eq_fderiv
      ((h.differentiableOn (by norm_num : (n + 1 : WithTop ℕ∞) ≠ 0)).differentiableAt
        (isOpen_OStrip.mem_nhds hp))
  have hfd : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) OStrip :=
    h.fderiv_of_isOpen isOpen_OStrip (m := n) (by norm_num)
  have hcomp : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (0, 1)) OStrip :=
    hfd.clm_apply contDiffOn_const
  refine hcomp.congr (fun p hp => ?_)
  exact hchain p hp

theorem contDiffOn_uncurry_Dz_fin {G : ℝ → ℝ → ℝ} {n : ℕ}
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) OStrip) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.Dz G)) OStrip := by
  have hpz := contDiffOn_uncurry_pz_fin h
  have hfun : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => p.1 * Function.uncurry (Work.Spaces.pz G) p) OStrip :=
    contDiff_fst.contDiffOn.mul hpz
  refine hfun.congr (fun p hp => ?_)
  rfl

/-! ## Clairaut identities -/

theorem pth_Dz_eq {G : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ContDiffAt ℝ 2 (Function.uncurry G) (z, θ)) :
    Work.Spaces.pth (Work.Spaces.Dz G) z θ = Work.Spaces.Dz (Work.Spaces.pth G) z θ := by
  have h1 : Work.Spaces.pth (Work.Spaces.Dz G) z θ
      = z * Work.Spaces.pth (Work.Spaces.pz G) z θ := by
    show deriv (fun θ' => z * Work.Spaces.pz G z θ') θ = z * Work.Spaces.pth (Work.Spaces.pz G) z θ
    rw [deriv_const_mul_field]
    rfl
  rw [h1, ← Work.Spaces.pz_pth_comm h]
  rfl

theorem pth_pth_Dz_eq {G : ℝ → ℝ → ℝ} (hG : ContDiffOn ℝ 3 (Function.uncurry G) OStrip)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :
    Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.Dz G)) z θ
      = Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ := by
  have hmem : (z, θ) ∈ OStrip := ⟨hz, hθ⟩
  have hcd : ContDiffAt ℝ 2 (Function.uncurry G) (z, θ) :=
    (hG.contDiffAt (isOpen_OStrip.mem_nhds hmem)).of_le (by norm_num)
  have hev : (fun θ' => Work.Spaces.pth (Work.Spaces.Dz G) z θ')
      =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.Dz (Work.Spaces.pth G) z θ') := by
    have hnb : ∀ᶠ θ' in 𝓝 θ, (z, θ') ∈ OStrip :=
      (isOpen_OStrip.preimage (continuous_const.prodMk continuous_id)).mem_nhds hmem
    filter_upwards [hnb] with θ' hθ'
    exact pth_Dz_eq ((hG.contDiffAt (isOpen_OStrip.mem_nhds hθ')).of_le (by norm_num))
  have h1 : Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.Dz G)) z θ
      = Work.Spaces.pth (Work.Spaces.Dz (Work.Spaces.pth G)) z θ := hev.deriv_eq
  have hcd2 : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.pth G)) (z, θ) :=
    (contDiffOn_uncurry_pth_fin (hG.of_le (by norm_num))).contDiffAt
      (isOpen_OStrip.mem_nhds hmem)
  rw [h1, pth_Dz_eq hcd2]

/-! ## Integrability of `w² σ F` for the product measure -/

/-- If `F` is continuous on the open quadrant of `(z,θ)`, is supported in `z ∈ [δ,R]` and is
bounded by `M` on the box, then `(z,θ) ↦ w z ² σ θ F z θ` is integrable for the product of
the restrictions of Lebesgue measure to `Iz` and `Iθ`. -/
theorem integrable_prod_quad_of_bound {δ R M : ℝ} (hδ : 0 < δ) {F : ℝ → ℝ → ℝ}
    (hFc : ContinuousOn (Function.uncurry F) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hF0 : ∀ z, z ∉ Set.Icc δ R → ∀ θ, F z θ = 0)
    (hFb : ∀ z ∈ Set.Icc δ R, ∀ θ ∈ Work.Spaces.Iθ, |F z θ| ≤ M) :
    MeasureTheory.Integrable
      (Function.uncurry (fun z θ => (Work.Spaces.w z) ^ 2 * thEta θ * F z θ))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  set M' : ℝ := max M 0 with hM'
  have hM'0 : 0 ≤ M' := le_max_right M 0
  have hMM' : M ≤ M' := le_max_left M 0
  -- the dominating function `M' · (w² 1_{[δ,R]}) ⊗ (σ 1_{Iθ})`
  have hAvol : MeasureTheory.Integrable
      ((Set.Icc δ R).indicator (fun z => (Work.Spaces.w z) ^ 2)) MeasureTheory.volume := by
    refine (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr ?_
    refine ContinuousOn.integrableOn_compact isCompact_Icc ?_
    show ContinuousOn (fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2) (Set.Icc δ R)
    refine ContinuousOn.pow ?_ 2
    refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
    intro z hz
    have hz0 : 0 < z := lt_of_lt_of_le hδ hz.1
    positivity
  have hBvol : MeasureTheory.Integrable
      (Work.Spaces.Iθ.indicator thEta) MeasureTheory.volume :=
    (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
      Work.FTS.EllipticEst.integrableOn_thEta.1
  have hg : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => M' * (((Set.Icc δ R).indicator (fun z => (Work.Spaces.w z) ^ 2)) p.1
        * (Work.Spaces.Iθ.indicator thEta) p.2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    ((hAvol.integrableOn).mul_prod (hBvol.integrableOn)).const_mul M'
  -- a.e. strong measurability from continuity on the open quadrant
  have hwcont : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    refine ContinuousOn.pow ?_ 2
    rw [show (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p => (1 + p.1) ^ 2 / p.1 ^ 2 from rfl]
    refine ContinuousOn.div ((continuous_const.add continuous_fst).continuousOn.pow 2)
      (continuous_fst.pow 2).continuousOn ?_
    intro p hp
    have hp0 : 0 < p.1 := hp.1
    positivity
  have hsincont : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
  have hsinnene : ∀ p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2),
      Real.sin (2 * p.2) ≠ 0 := by
    intro p hp
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1]) (by linarith [hp.2.2]))
  have hσcont : ContinuousOn (fun p : ℝ × ℝ => thEta p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    show ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2) ^ (-(Work.Spaces.eta))) _
    exact hsincont.rpow_const (fun p hp => Or.inl (hsinnene p hp))
  have hAE : MeasureTheory.AEStronglyMeasurable
      (Function.uncurry (fun z θ => (Work.Spaces.w z) ^ 2 * thEta θ * F z θ))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    have hcont : ContinuousOn
        (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * thEta p.2 * F p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
      have h1 : ContinuousOn
          (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * (thEta p.2 * F p.1 p.2))
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hwcont.mul (hσcont.mul hFc)
      refine h1.congr (fun p hp => ?_)
      ring
    exact Work.Spaces.aesm_of_continuousOn_Qd
      (Function.uncurry (fun z θ => (Work.Spaces.w z) ^ 2 * thEta θ * F z θ)) hcont
  refine hg.mono' hAE ?_
  -- the pointwise domination, a.e. in the second variable
  have hmem : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)), p.2 ∈ Work.Spaces.Iθ := by
    refine (MeasureTheory.Measure.ae_prod_iff_ae_ae (μ := volume.restrict Work.Spaces.Iz)
      (ν := volume.restrict Work.Spaces.Iθ)
      (p := fun p : ℝ × ℝ => p.2 ∈ Work.Spaces.Iθ)
      (measurableSet_Icc.preimage measurable_snd)).mpr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem (s := Work.Spaces.Iz) measurableSet_Ici]
      with b hb
    filter_upwards [MeasureTheory.ae_restrict_mem (s := Work.Spaces.Iθ) measurableSet_Icc]
      with c hc
    exact hc
  filter_upwards [hmem] with p hp
  have hthEta_nn : 0 ≤ thEta p.2 := thEta_nonneg hp
  have hw_nn : 0 ≤ (Work.Spaces.w p.1) ^ 2 := sq_nonneg _
  have hBnn : 0 ≤ (Work.Spaces.Iθ.indicator thEta) p.2 := by
    by_cases h : p.2 ∈ Work.Spaces.Iθ
    · rw [Set.indicator_of_mem h]; exact hthEta_nn
    · rw [Set.indicator_of_notMem h]
  have hAnn : 0 ≤ ((Set.Icc δ R).indicator (fun z => (Work.Spaces.w z) ^ 2)) p.1 := by
    by_cases h : p.1 ∈ Set.Icc δ R
    · rw [Set.indicator_of_mem h]; exact hw_nn
    · rw [Set.indicator_of_notMem h]
  have hgnn : 0 ≤ M' * (((Set.Icc δ R).indicator (fun z => (Work.Spaces.w z) ^ 2)) p.1
      * (Work.Spaces.Iθ.indicator thEta) p.2) := mul_nonneg hM'0 (mul_nonneg hAnn hBnn)
  rw [Real.norm_eq_abs]
  change |(Work.Spaces.w p.1) ^ 2 * thEta p.2 * F p.1 p.2|
      ≤ M' * (((Set.Icc δ R).indicator (fun z => (Work.Spaces.w z) ^ 2)) p.1
        * (Work.Spaces.Iθ.indicator thEta) p.2)
  by_cases hmem : p.1 ∈ Set.Icc δ R
  · have hFb' : |F p.1 p.2| ≤ M := hFb p.1 hmem p.2 hp
    have h1 : |(Work.Spaces.w p.1) ^ 2 * thEta p.2 * F p.1 p.2|
        = (Work.Spaces.w p.1) ^ 2 * thEta p.2 * |F p.1 p.2| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hw_nn, abs_of_nonneg hthEta_nn]
    rw [h1, Set.indicator_of_mem hmem, Set.indicator_of_mem hp]
    have h2 : (Work.Spaces.w p.1) ^ 2 * thEta p.2 * |F p.1 p.2|
        ≤ (Work.Spaces.w p.1) ^ 2 * thEta p.2 * M' :=
      mul_le_mul_of_nonneg_left (le_trans hFb' hMM') (mul_nonneg hw_nn hthEta_nn)
    calc (Work.Spaces.w p.1) ^ 2 * thEta p.2 * |F p.1 p.2|
        ≤ (Work.Spaces.w p.1) ^ 2 * thEta p.2 * M' := h2
      _ = M' * ((Work.Spaces.w p.1) ^ 2 * thEta p.2) := by ring
  · have hFz : F p.1 p.2 = 0 := hF0 p.1 hmem p.2
    rw [hFz, mul_zero, abs_zero, Set.indicator_of_notMem hmem]
    simp

/-- A bound for a continuous function on the compact box `[δ,R] × Iθ`. -/
theorem exists_bound_box {δ R : ℝ} (hδ : 0 < δ) (hδR : δ < R) {f : ℝ → ℝ → ℝ}
    (hf : ContinuousOn (Function.uncurry f) (Set.Icc δ R ×ˢ Work.Spaces.Iθ)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ Set.Icc δ R, ∀ θ ∈ Work.Spaces.Iθ, |f z θ| ≤ M := by
  have hbox : IsCompact (Set.Icc δ R ×ˢ Work.Spaces.Iθ : Set (ℝ × ℝ)) :=
    isCompact_Icc.prod isCompact_Icc
  have hne : (Set.Icc δ R ×ˢ Work.Spaces.Iθ : Set (ℝ × ℝ)).Nonempty :=
    ⟨(δ, 0), ⟨⟨le_rfl, hδR.le⟩, ⟨le_rfl, by linarith [Real.pi_pos]⟩⟩⟩
  obtain ⟨p₀, -, hmax⟩ := hbox.exists_isMaxOn hne (f := fun p : ℝ × ℝ => |Function.uncurry f p|)
    hf.abs
  refine ⟨|Function.uncurry f p₀|, abs_nonneg _, fun z hz θ hθ => ?_⟩
  exact isMaxOn_iff.mp hmax (z, θ) ⟨hz, hθ⟩

/-- **Fubini for the weighted iterated integrals**: for a function `F` which is continuous on the
open quadrant, vanishes for `z ∉ [δ,R]` and is bounded on the box,
`∫_z w z ² (∫_θ F z θ σ θ) = ∫_θ (∫_z w z ² F z θ) σ θ`, `σ θ = sin(2θ)^{-η}`. -/
theorem fubini_w_thEta {δ R : ℝ} (hδ : 0 < δ) {F : ℝ → ℝ → ℝ}
    (hFc : ContinuousOn (Function.uncurry F) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hF0 : ∀ z, z ∉ Set.Icc δ R → ∀ θ, F z θ = 0)
    (hFb : ∃ Mb : ℝ, ∀ z ∈ Set.Icc δ R, ∀ θ ∈ Work.Spaces.Iθ, |F z θ| ≤ Mb) :
    (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, F z θ * thEta θ))
      = ∫ θ in Work.Spaces.Iθ,
          (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * F z θ) * thEta θ := by
  obtain ⟨Mb, hMb⟩ := hFb
  have hInt := integrable_prod_quad_of_bound (δ := δ) (R := R) (M := Mb) hδ
    (F := F) hFc hF0 hMb
  have hswap := MeasureTheory.integral_integral_swap hInt
  have hL : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
      * (∫ θ in Work.Spaces.Iθ, F z θ * thEta θ))
      = ∫ z, (∫ θ, (Work.Spaces.w z) ^ 2 * thEta θ * F z θ
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    change (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, F z θ * thEta θ)
      = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 * thEta θ * F z θ
    rw [show (∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 * thEta θ * F z θ)
        = ∫ θ in Work.Spaces.Iθ, (F z θ * thEta θ) * (Work.Spaces.w z) ^ 2 from by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
      ring,
      MeasureTheory.integral_mul_const]
    ring
  have hR : (∫ θ in Work.Spaces.Iθ,
        (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * F z θ) * thEta θ)
      = ∫ θ, (∫ z, (Work.Spaces.w z) ^ 2 * thEta θ * F z θ
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    change (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * F z θ) * thEta θ
      = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * thEta θ * F z θ
    rw [show (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * thEta θ * F z θ)
        = ∫ z in Work.Spaces.Iz, ((Work.Spaces.w z) ^ 2 * F z θ) * thEta θ from by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
      ring,
      MeasureTheory.integral_mul_const]
  rw [hL, hR, hswap]

/-- Integrability of the outer (`z`-)slice integral. -/
theorem integrable_outer_of_bound {δ R : ℝ} (hδ : 0 < δ) {F : ℝ → ℝ → ℝ}
    (hFc : ContinuousOn (Function.uncurry F) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hF0 : ∀ z, z ∉ Set.Icc δ R → ∀ θ, F z θ = 0)
    (hFb : ∃ Mb : ℝ, ∀ z ∈ Set.Icc δ R, ∀ θ ∈ Work.Spaces.Iθ, |F z θ| ≤ Mb) :
    MeasureTheory.Integrable
      (fun z => (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, F z θ * thEta θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  obtain ⟨Mb, hMb⟩ := hFb
  have hInt := integrable_prod_quad_of_bound (δ := δ) (R := R) (M := Mb) hδ
    (F := F) hFc hF0 hMb
  have h1 : MeasureTheory.Integrable
      (fun z => ∫ θ, (Work.Spaces.w z) ^ 2 * thEta θ * F z θ
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := hInt.integral_prod_left
  refine h1.congr ?_
  filter_upwards with z
  rw [show (fun θ => (Work.Spaces.w z) ^ 2 * thEta θ * F z θ)
      = (fun θ => (F z θ * thEta θ) * (Work.Spaces.w z) ^ 2) from by funext θ; ring,
    MeasureTheory.integral_mul_const]
  ring

/-- The iterated integral equals the product integral. -/
theorem iterated_eq_prod {δ R : ℝ} (hδ : 0 < δ) {F : ℝ → ℝ → ℝ}
    (hFc : ContinuousOn (Function.uncurry F) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hF0 : ∀ z, z ∉ Set.Icc δ R → ∀ θ, F z θ = 0)
    (hFb : ∃ Mb : ℝ, ∀ z ∈ Set.Icc δ R, ∀ θ ∈ Work.Spaces.Iθ, |F z θ| ≤ Mb) :
    (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, F z θ * thEta θ))
      = ∫ p : ℝ × ℝ, (Work.Spaces.w p.1) ^ 2 * thEta p.2 * F p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  obtain ⟨Mb, hMb⟩ := hFb
  have hInt := integrable_prod_quad_of_bound (δ := δ) (R := R) (M := Mb) hδ
    (F := F) hFc hF0 hMb
  have hprod := MeasureTheory.integral_prod
    (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * thEta p.2 * F p.1 p.2) hInt
  rw [hprod]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  change (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, F z θ * thEta θ)
    = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 * thEta θ * F z θ
  rw [show (∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 * thEta θ * F z θ)
      = ∫ θ in Work.Spaces.Iθ, (F z θ * thEta θ) * (Work.Spaces.w z) ^ 2 from by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
    ring,
    MeasureTheory.integral_mul_const]
  ring

/-- The AM–GM comparison for the product measure. -/
theorem prod_abs_integral_le {f g : ℝ × ℝ → ℝ}
    (hf : MeasureTheory.Integrable f
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hg : MeasureTheory.Integrable g
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (h : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)), |f p| ≤ g p) :
    |∫ p, f p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
      ≤ ∫ p, g p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  refine le_trans (MeasureTheory.abs_integral_le_integral_abs (f := f)) ?_
  refine MeasureTheory.integral_mono_ae hf.norm hg ?_
  filter_upwards [h] with p hp
  simpa only [Real.norm_eq_abs] using hp

/-! ## The derived functions vanish off the support in `z` -/

theorem vanish_off_box_Dz {G : ℝ → ℝ → ℝ} {δ R : ℝ}
    (hsupp : ∀ z, z ∉ Set.Icc δ R → ∀ θ, G z θ = 0) :
    ∀ z, z ∉ Set.Icc δ R → ∀ θ, Work.Spaces.Dz G z θ = 0 := by
  intro z hz θ
  have hnb : ∀ᶠ z' in 𝓝 z, z' ∉ Set.Icc δ R :=
    isClosed_Icc.isOpen_compl.mem_nhds hz
  have hev : (fun z' : ℝ => G z' θ) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
    filter_upwards [hnb] with z' hz'
    exact hsupp z' hz' θ
  show z * deriv (fun z' : ℝ => G z' θ) z = 0
  rw [hev.deriv_eq, deriv_const, mul_zero]

theorem vanish_off_box_pth {G : ℝ → ℝ → ℝ} {δ R : ℝ}
    (hsupp : ∀ z, z ∉ Set.Icc δ R → ∀ θ, G z θ = 0) :
    ∀ z, z ∉ Set.Icc δ R → ∀ θ, Work.Spaces.pth G z θ = 0 := by
  intro z hz θ
  have hfun : (fun θ' : ℝ => G z θ') = fun _ => (0 : ℝ) := funext fun θ' => hsupp z hz θ'
  show deriv (fun θ' : ℝ => G z θ') θ = 0
  rw [hfun, deriv_const]

theorem vanish_off_box_pth_pth {G : ℝ → ℝ → ℝ} {δ R : ℝ}
    (hsupp : ∀ z, z ∉ Set.Icc δ R → ∀ θ, G z θ = 0) :
    ∀ z, z ∉ Set.Icc δ R → ∀ θ, Work.Spaces.pth (Work.Spaces.pth G) z θ = 0 := by
  intro z hz θ
  have hfun : (fun θ' : ℝ => Work.Spaces.pth G z θ') = fun _ => (0 : ℝ) :=
    funext fun θ' => vanish_off_box_pth hsupp z hz θ'
  show deriv (fun θ' : ℝ => Work.Spaces.pth G z θ') θ = 0
  rw [hfun, deriv_const]

theorem vanish_off_box_Dz_Dz {G : ℝ → ℝ → ℝ} {δ R : ℝ}
    (hsupp : ∀ z, z ∉ Set.Icc δ R → ∀ θ, G z θ = 0) :
    ∀ z, z ∉ Set.Icc δ R → ∀ θ, Work.Spaces.Dz (Work.Spaces.Dz G) z θ = 0 := by
  intro z hz θ
  have hnb : ∀ᶠ z' in 𝓝 z, z' ∉ Set.Icc δ R :=
    isClosed_Icc.isOpen_compl.mem_nhds hz
  have hev : (fun z' : ℝ => Work.Spaces.Dz G z' θ) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
    filter_upwards [hnb] with z' hz'
    exact vanish_off_box_Dz hsupp z' hz' θ
  show z * deriv (fun z' : ℝ => Work.Spaces.Dz G z' θ) z = 0
  rw [hev.deriv_eq, deriv_const, mul_zero]

theorem vanish_off_box_Dz_pth {G : ℝ → ℝ → ℝ} {δ R : ℝ}
    (hsupp : ∀ z, z ∉ Set.Icc δ R → ∀ θ, G z θ = 0) :
    ∀ z, z ∉ Set.Icc δ R → ∀ θ, Work.Spaces.Dz (Work.Spaces.pth G) z θ = 0 := by
  intro z hz θ
  have hnb : ∀ᶠ z' in 𝓝 z, z' ∉ Set.Icc δ R :=
    isClosed_Icc.isOpen_compl.mem_nhds hz
  have hev : (fun z' : ℝ => Work.Spaces.pth G z' θ) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
    filter_upwards [hnb] with z' hz'
    exact vanish_off_box_pth hsupp z' hz' θ
  show z * deriv (fun z' : ℝ => Work.Spaces.pth G z' θ) z = 0
  rw [hev.deriv_eq, deriv_const, mul_zero]

theorem vanish_off_box_Dz_pth_pth {G : ℝ → ℝ → ℝ} {δ R : ℝ}
    (hsupp : ∀ z, z ∉ Set.Icc δ R → ∀ θ, G z θ = 0) :
    ∀ z, z ∉ Set.Icc δ R → ∀ θ, Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ = 0 := by
  intro z hz θ
  have hnb : ∀ᶠ z' in 𝓝 z, z' ∉ Set.Icc δ R :=
    isClosed_Icc.isOpen_compl.mem_nhds hz
  have hev : (fun z' : ℝ => Work.Spaces.pth (Work.Spaces.pth G) z' θ)
      =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
    filter_upwards [hnb] with z' hz'
    exact vanish_off_box_pth_pth hsupp z' hz' θ
  show z * deriv (fun z' : ℝ => Work.Spaces.pth (Work.Spaces.pth G) z' θ) z = 0
  rw [hev.deriv_eq, deriv_const, mul_zero]

/-- **The AM–GM comparison in the iterated form.**  If `|F| ≤ J` pointwise and both are
admissible (continuous on the open quadrant, supported in `z ∈ [δ,R]`, bounded on the box) with
`J ≥ 0`, then the weighted iterated integral of `|F|` is bounded by that of `J`. -/
theorem amgm_bound_iterated {δ R : ℝ} (hδ : 0 < δ) {F J : ℝ → ℝ → ℝ}
    (hFc : ContinuousOn (Function.uncurry F) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hF0 : ∀ z, z ∉ Set.Icc δ R → ∀ θ, F z θ = 0)
    (hFb : ∃ Mb : ℝ, ∀ z ∈ Set.Icc δ R, ∀ θ ∈ Work.Spaces.Iθ, |F z θ| ≤ Mb)
    (hJc : ContinuousOn (Function.uncurry J) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hJ0 : ∀ z, z ∉ Set.Icc δ R → ∀ θ, J z θ = 0)
    (hJb : ∃ Mb : ℝ, ∀ z ∈ Set.Icc δ R, ∀ θ ∈ Work.Spaces.Iθ, |J z θ| ≤ Mb)
    (hJnn : ∀ z θ, 0 ≤ J z θ) (h : ∀ z θ, |F z θ| ≤ J z θ) :
    |∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, F z θ * thEta θ)|
      ≤ ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, J z θ * thEta θ) := by
  obtain ⟨MbF, hMbF⟩ := hFb
  obtain ⟨MbJ, hMbJ⟩ := hJb
  have hIntF := integrable_prod_quad_of_bound (M := MbF) hδ (F := F) hFc hF0 hMbF
  have hIntJ := integrable_prod_quad_of_bound (M := MbJ) hδ (F := J) hJc hJ0 hMbJ
  rw [iterated_eq_prod hδ hFc hF0 ⟨MbF, hMbF⟩, iterated_eq_prod hδ hJc hJ0 ⟨MbJ, hMbJ⟩]
  refine prod_abs_integral_le hIntF hIntJ ?_
  have hmem : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)), p.2 ∈ Work.Spaces.Iθ := by
    refine (MeasureTheory.Measure.ae_prod_iff_ae_ae (μ := volume.restrict Work.Spaces.Iz)
      (ν := volume.restrict Work.Spaces.Iθ) (p := fun p : ℝ × ℝ => p.2 ∈ Work.Spaces.Iθ)
      (measurableSet_Icc.preimage measurable_snd)).mpr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem (s := Work.Spaces.Iz) measurableSet_Ici]
      with b hb
    filter_upwards [MeasureTheory.ae_restrict_mem (s := Work.Spaces.Iθ) measurableSet_Icc]
      with c hc
    exact hc
  filter_upwards [hmem] with p hp
  have hthEta_nn : 0 ≤ thEta p.2 := thEta_nonneg hp
  have hw_nn : 0 ≤ (Work.Spaces.w p.1) ^ 2 := sq_nonneg _
  rw [abs_mul, abs_mul, abs_of_nonneg hw_nn, abs_of_nonneg hthEta_nn]
  exact mul_le_mul_of_nonneg_left (h p.1 p.2) (mul_nonneg hw_nn hthEta_nn)

end Work.FTS.EllipticEst.ThetaU
