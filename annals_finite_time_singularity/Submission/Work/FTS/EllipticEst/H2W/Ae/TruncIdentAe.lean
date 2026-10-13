import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.remov.ibpZZ
import Submission.Work.FTS.EllipticEst.remov.ibpZ
import Submission.Work.FTS.EllipticEst.Honest.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp
import Submission.Work.Spaces.aesm_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `truncIdentAe` — the truncated energy identity in the almost-everywhere class

For `AeData α u G`, a weight `W ∈ C²` with compact support, vanishing near `0`, the truncated
`w²`-energy identity holds.  The proof follows the paper's route of
`Work.FTS.EllipticEst.TruncIdentity`, rebuilt in the weak (`AeData`) class:

* `G` is replaced by `bslOp α u` (they agree on the open quadrant, a conull set);
* for each `θ ∈ (0,π/2)` the one-dimensional `z`-integration by parts is applied to the slice
  `z ↦ u z θ` with the radial weight `σ = W w²` (`remov.ibpZZ`, `remov.ibpZ`);
* the resulting identity is integrated in `θ` and the five double integrals are swapped by
  Fubini.  The joint integrability that Fubini needs is the analytic content of the weak class.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.Ae

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-! ## 1. Elementary facts about the weight `w` and the angle -/

private theorem w_sq_eq (z : ℝ) : (Work.Spaces.w z) ^ 2 = (1 + z) ^ 4 / z ^ 4 := by
  rw [Work.Spaces.w, div_pow]
  ring

private theorem w_nonneg (z : ℝ) : 0 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w]
  positivity

private theorem one_le_w {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w, le_div_iff₀ (by positivity)]
  nlinarith

private theorem sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) := by
  obtain ⟨h0, h1⟩ := hθ
  exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])

private theorem sin_two_pos_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- The level-`0` integrand in the `w²σ` form. -/
private theorem HkIntegrand_zero_eq' (α : ℝ) (g : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq,
    Work.FTS.EllipticEst.Honest.sq_profile_eq g z θ (sin_two_nonneg_Iθ hθ)]

private theorem contDiffOn_w_sq :
    ContDiffOn ℝ 2 (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
  have hfun : (fun z : ℝ => (Work.Spaces.w z) ^ 2)
      = fun z : ℝ => ((1 + z) ^ 2) ^ 2 / (z ^ 2) ^ 2 := by
    funext z
    rw [Work.Spaces.w, div_pow]
  rw [hfun]
  exact ContDiffOn.div (((contDiffOn_const.add contDiffOn_id).pow 2).pow 2)
    ((contDiffOn_id.pow 2).pow 2)
    (fun z hz => pow_ne_zero 2 (pow_ne_zero 2 (ne_of_gt hz)))

private theorem contDiffOn_sigma (W : ℝ → ℝ) (hW : ContDiff ℝ 2 W) :
    ContDiffOn ℝ 2 (fun z : ℝ => W z * (Work.Spaces.w z) ^ 2) (Set.Ioi 0) :=
  hW.contDiffOn.mul contDiffOn_w_sq

/-! ## 2. Support facts -/

private theorem W_eq_zero_of_large (W : ℝ → ℝ) (h : HasCompactSupport W) :
    ∃ R : ℝ, 0 < R ∧ ∀ z : ℝ, R < |z| → W z = 0 := by
  obtain ⟨R, hRpos, hR⟩ := h.isCompact.isBounded.exists_pos_norm_le
  refine ⟨R, hRpos, fun z hz => image_eq_zero_of_notMem_tsupport (fun hmem => ?_)⟩
  have h1 := hR z hmem
  rw [Real.norm_eq_abs] at h1
  linarith

private theorem W_bdd (W : ℝ → ℝ) (hW : ContDiff ℝ 2 W) (h : HasCompactSupport W) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℝ, |W z| ≤ M := by
  obtain ⟨R, hRpos, hR⟩ := W_eq_zero_of_large W h
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (-R) R)).exists_bound_of_continuousOn
    (hW.continuous.continuousOn : ContinuousOn W (Set.Icc (-R) R))
  refine ⟨max C 0, le_max_right _ _, fun z => ?_⟩
  by_cases hz : z ∈ Set.Icc (-R) R
  · have h1 := hC z hz
    rw [Real.norm_eq_abs] at h1
    exact le_trans h1 (le_max_left _ _)
  · have hz' : R < |z| := by
      by_cases h : z ≤ 0
      · have h2 : z < -R := by
          by_contra hcon
          exact hz ⟨by linarith [not_lt.mp hcon], by linarith⟩
        rw [abs_of_nonpos h]
        linarith
      · have hzpos : 0 < z := not_le.mp h
        rw [abs_of_pos hzpos]
        by_contra hcon
        exact hz ⟨by linarith, not_lt.mp hcon⟩
    rw [hR z hz']
    exact le_trans (le_of_eq abs_zero) (le_max_right _ _)

/-! ## 3. Two general integration lemmas -/

/-- Extension of an integral from a compact support. -/
private theorem integrableOn_Ioi_of_support {f : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hcont : ContinuousOn f (Set.Ioi 0))
    (h0 : ∀ z : ℝ, z < a → f z = 0) (hb : ∀ z : ℝ, b < z → f z = 0) :
    IntegrableOn f (Set.Ioi 0) := by
  have hsub : Set.Icc a b ⊆ Set.Ioi (0 : ℝ) := fun z hz => lt_of_lt_of_le ha hz.1
  have hint : IntegrableOn f (Set.Icc a b) :=
    (hcont.mono hsub).integrableOn_compact isCompact_Icc
  have hind : Integrable ((Set.Icc a b).indicator f) volume :=
    (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr hint
  have heq : f =ᵐ[volume] (Set.Icc a b).indicator f := by
    filter_upwards with z
    by_cases hz : z ∈ Set.Icc a b
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz]
      by_cases hza : z < a
      · exact h0 z hza
      · have hzb : b < z := by
          have h1 : a ≤ z := not_lt.mp hza
          by_contra hcon
          exact hz ⟨h1, not_lt.mp hcon⟩
        exact hb z hzb
  exact (hind.congr heq.symm).integrableOn

/-- The derivative of a function vanishing off an interval vanishes there as well. -/
private theorem deriv_zero_of_zero {f : ℝ → ℝ} {δ R : ℝ}
    (hfδ : ∀ z : ℝ, z < δ → f z = 0) (hfR : ∀ z : ℝ, R < z → f z = 0) :
    (∀ z : ℝ, z < δ → deriv f z = 0) ∧ (∀ z : ℝ, R < z → deriv f z = 0) := by
  constructor
  · intro z hz
    have hmem : Set.Iio δ ∈ 𝓝 z := Iio_mem_nhds hz
    have hev : f =ᶠ[𝓝 z] (fun _ : ℝ => (0 : ℝ)) := by
      filter_upwards [hmem] with y hy
      show f y = 0
      exact hfδ y hy
    rw [hev.deriv_eq]
    simpa using deriv_const z (0 : ℝ)
  · intro z hz
    have hmem : Set.Ioi R ∈ 𝓝 z := Ioi_mem_nhds hz
    have hev : f =ᶠ[𝓝 z] (fun _ : ℝ => (0 : ℝ)) := by
      filter_upwards [hmem] with y hy
      show f y = 0
      exact hfR y hy
    rw [hev.deriv_eq]
    simpa using deriv_const z (0 : ℝ)

/-- Fubini for `z`-outer/`θ`-inner integrals with a weight depending only on `z`. -/
private theorem fubini_swap (φ : ℝ → ℝ) (f : ℝ → ℝ → ℝ)
    (hI : Integrable (Function.uncurry (fun z θ => φ z * f z θ))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))) :
    (∫ z in Work.Spaces.Iz, φ z * (∫ θ in Work.Spaces.Iθ, f z θ))
      = ∫ θ in Work.Spaces.Iθ, ∫ z in Work.Spaces.Iz, φ z * f z θ := by
  have h1 : (∫ z in Work.Spaces.Iz, φ z * (∫ θ in Work.Spaces.Iθ, f z θ))
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, φ z * f z θ := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
    exact (MeasureTheory.integral_const_mul (φ z) (fun θ => f z θ)).symm
  rw [h1]
  exact MeasureTheory.integral_integral_swap hI

/-! ## 4. A.e. facts about the product measure -/

private theorem ae_restrict_Iz_Ioi :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), z ∈ Set.Ioi (0 : ℝ) := by
  have h : MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
      = MeasureTheory.volume.restrict Work.Spaces.Iz := by
    rw [Work.Spaces.Iz]
    exact MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0))
  have hmem := MeasureTheory.self_mem_ae_restrict (μ := MeasureTheory.volume)
    (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi
  rwa [h] at hmem

private theorem ae_restrict_Iθ_Ioo :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo 0 (Real.pi / 2) := by
  have h : (Set.Ioo (0 : ℝ) (Real.pi / 2)) =ᵐ[MeasureTheory.volume]
      (Set.Icc (0 : ℝ) (Real.pi / 2)) := MeasureTheory.Ioo_ae_eq_Icc
  have hmem := MeasureTheory.self_mem_ae_restrict (μ := MeasureTheory.volume)
    (s := Set.Ioo (0 : ℝ) (Real.pi / 2)) measurableSet_Ioo
  rwa [MeasureTheory.Measure.restrict_congr_set h] at hmem

private theorem ae_prod_fst_pos :
    ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)), 0 < p.1 :=
  (MeasureTheory.Measure.ae_prod_iff_ae_ae
    (measurableSet_Ioi.preimage measurable_fst)).mpr
    (ae_restrict_Iz_Ioi.mono fun x hx => Filter.Eventually.of_forall fun _ => hx)

private theorem ae_prod_snd_Ioo :
    ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)), p.2 ∈ Set.Ioo 0 (Real.pi / 2) :=
  (MeasureTheory.Measure.ae_prod_iff_ae_ae
    (measurableSet_Ioo.preimage measurable_snd)).mpr
    (Filter.Eventually.of_forall fun _ => ae_restrict_Iθ_Ioo)

private theorem ae_prod_snd_Iθ :
    ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)), p.2 ∈ Work.Spaces.Iθ :=
  (MeasureTheory.Measure.ae_prod_iff_ae_ae
    (measurableSet_Icc.preimage measurable_snd)).mpr
    (Filter.Eventually.of_forall fun _ => MeasureTheory.self_mem_ae_restrict measurableSet_Icc)

private theorem one_le_sig_ae :
    ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      1 ≤ (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)) := by
  filter_upwards [ae_prod_snd_Ioo] with p hp
  have hs := sin_two_pos_Ioo hp
  have h1 : (1 : ℝ) ^ (-(Work.Spaces.eta)) ≤ (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)) :=
    Real.rpow_le_rpow_of_nonpos hs (Real.sin_le_one _) (by norm_num [Work.Spaces.eta])
  rwa [Real.one_rpow] at h1

private theorem ae_HkIntegrand_zero (α : ℝ) (g : ℝ → ℝ → ℝ) :
    ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      Work.Spaces.HkIntegrand α 0 g p.1 p.2
        = (g p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2
            * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)) :=
  ae_prod_snd_Iθ.mono fun _ hp => HkIntegrand_zero_eq' α g hp

/-! ## 5. Joint integrability of the level-`0` integrand from `HkMem` -/

private theorem integrable_HkIntegrand_zero {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hmeas : AEStronglyMeasurable (Function.uncurry g)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hmem : Work.Spaces.HkMem α 0 g) :
    Integrable (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 g p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  have haesm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 g p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    have hsinpos : ∀ p ∈ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2) : Set (ℝ × ℝ)),
        0 < Real.sin (2 * p.2) := fun p hp =>
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1]) (by linarith [hp.2.2, Real.pi_pos])
    have hw1 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
      have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
          = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by funext p; rfl
      rw [hfun]
      exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
        (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))
    have hsp : ContinuousOn
        (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
        (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
    have hw : ContinuousOn (fun p : ℝ × ℝ =>
        (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)) ^ 2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      (hw1.div hsp (fun p hp => ne_of_gt (Real.rpow_pos_of_pos (hsinpos p hp) _))).pow 2
    refine (hmeas.pow 2 |>.mul (Work.Spaces.aesm_of_continuousOn_Qd _ hw)).congr ?_
    filter_upwards with p
    simp only [Pi.mul_apply, Pi.pow_apply, Function.uncurry]
    rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq]
    ring
  rw [MeasureTheory.integrable_prod_iff haesm]
  constructor
  · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => ?_)
    exact hmem.1 z hz
  · refine hmem.2.congr (Filter.Eventually.of_forall fun z => ?_)
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    show Work.Spaces.HkIntegrand α 0 g z θ = ‖Work.Spaces.HkIntegrand α 0 g z θ‖
    rw [Real.norm_eq_abs,
      abs_of_nonneg (Work.FTS.EllipticEst.Honest.HkIntegrand_nonneg α 0 g z θ)]

/-! ## 6. Smoothness certificates on the open quadrant -/

private theorem slice_contDiffOn {u : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ContDiffOn ℝ 2 (fun z : ℝ => u z θ) (Set.Ioi 0) := by
  have hmap : Set.MapsTo (fun z : ℝ => (z, θ)) (Set.Ioi (0 : ℝ))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := fun z hz => ⟨hz, hθ⟩
  exact (hsm 2).comp (by fun_prop) hmap

private theorem smoothOpen_Lzero {u : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen u) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.Lzero u) :=
  Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
    (Work.FTS.EllipticEst.Cert.smoothOpen_sub_bsl
      (Work.FTS.EllipticEst.Cert.smoothOpen_add_bsl
        (Work.FTS.EllipticEst.Cert.smoothOpen_neg_bsl
          (Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hso 2))
        (Work.FTS.EllipticEst.SmoothOpen.pth
          (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
            Work.FTS.EllipticEst.Cert.smoothOpen_tan_bsl hso)))
      (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl 6 hso))
    (fun z θ _ _ _ => by simp only [Work.Elliptic.Lzero])

private theorem smoothOpen_bslOp_ae (α : ℝ) {u : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen u) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.bslOp α u) := by
  have hzsq : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z ^ 2) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_zsq_bsl
  have hz : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_z_bsl
  have hA : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => -(α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 u z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
      (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl (-(α ^ 2))
        (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hzsq
          (Work.FTS.EllipticEst.SmoothOpen.pzIter hso 2)))
      (fun z θ _ _ _ => by ring)
  have hB : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (α * (5 + α) * z) * Work.Spaces.pz u z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
      (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl (α * (5 + α))
        (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hz
          (Work.FTS.EllipticEst.SmoothOpen.pz hso)))
      (fun z θ _ _ _ => by ring)
  have hC : Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.Lzero u) := smoothOpen_Lzero hso
  exact Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
    (Work.FTS.EllipticEst.Cert.smoothOpen_add_bsl
      (Work.FTS.EllipticEst.Cert.smoothOpen_sub_bsl hA hB) hC)
    (fun z θ _ _ _ => by simp only [Work.Elliptic.bslOp_apply])

/-! ## 7. Joint integrability of the five integrands -/

private theorem integrable_joint (α : ℝ) (u G : ℝ → ℝ → ℝ) (h : AeData α u G)
    (hu : Work.Spaces.HkMem α 0 u)
    (hgu : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz u z θ))
    (W : ℝ → ℝ) (hW : ContDiff ℝ 2 W) (hsupp : HasCompactSupport W)
    (hvan : ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℝ, z ≤ δ → W z = 0) :
    Integrable (Function.uncurry
        (fun z θ => W z * (Work.Spaces.w z) ^ 2 * (G z θ * u z θ)))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
    Integrable (Function.uncurry
        (fun z θ => W z * (Work.Spaces.w z) ^ 2 * z ^ 2 * (Work.Spaces.pz u z θ) ^ 2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
    Integrable (Function.uncurry
        (fun z θ => W z * (Work.Spaces.w z) ^ 2 * (Work.Elliptic.Lzero u z θ * u z θ)))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
    Integrable (Function.uncurry
        (fun z θ => deriv (deriv (fun z : ℝ => W z * (Work.Spaces.w z) ^ 2 * z ^ 2)) z
          * (u z θ) ^ 2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
    Integrable (Function.uncurry
        (fun z θ => deriv (fun z : ℝ => W z * (Work.Spaces.w z) ^ 2 * z) z * (u z θ) ^ 2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  have hso : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have haesm_u : AEStronglyMeasurable (Function.uncurry u)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hso.continuousOn
  have haesm_pzu : AEStronglyMeasurable (Function.uncurry (Work.Spaces.pz u))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ (Work.FTS.EllipticEst.SmoothOpen.pz hso).continuousOn
  have haesm_rad2 : AEStronglyMeasurable
      (Function.uncurry (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    refine Work.Spaces.aesm_of_continuousOn_Qd _ ?_
    change ContinuousOn (fun p : ℝ × ℝ =>
      p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2) Work.FTS.EllipticEst.Q0
    exact (continuousOn_fst.pow 2).mul
      (Work.FTS.EllipticEst.SmoothOpen.pzIter hso 2).continuousOn
  have haesm_gr : AEStronglyMeasurable
      (Function.uncurry (fun z θ => z * Work.Spaces.pz u z θ))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    refine Work.Spaces.aesm_of_continuousOn_Qd _ ?_
    change ContinuousOn (fun p : ℝ × ℝ => p.1 * Work.Spaces.pz u p.1 p.2)
      Work.FTS.EllipticEst.Q0
    exact continuousOn_fst.mul (Work.FTS.EllipticEst.SmoothOpen.pz hso).continuousOn
  have haesm_L : AEStronglyMeasurable (Function.uncurry (Work.Elliptic.Lzero u))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ (smoothOpen_Lzero hso).continuousOn
  have haesm_bsl : AEStronglyMeasurable (Function.uncurry (Work.Elliptic.bslOp α u))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ (smoothOpen_bslOp_ae α hso).continuousOn
  have haesm_G : AEStronglyMeasurable (Function.uncurry G)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    refine haesm_bsl.congr ?_
    filter_upwards [ae_prod_fst_pos, ae_prod_snd_Ioo] with p hz hθ
    show Work.Elliptic.bslOp α u p.1 p.2 = G p.1 p.2
    exact h.eq p.1 hz p.2 hθ.1 hθ.2
  -- the four `HkIntegrand` integrabilities
  have hIG : Integrable (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 G p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    integrable_HkIntegrand_zero haesm_G h.memG
  have hIu : Integrable (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 u p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    integrable_HkIntegrand_zero haesm_u hu
  have hIgr : Integrable
      (fun p : ℝ × ℝ =>
        Work.Spaces.HkIntegrand α 0 (fun z θ => z * Work.Spaces.pz u z θ) p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    integrable_HkIntegrand_zero haesm_gr hgu
  have hIr2 : Integrable
      (fun p : ℝ × ℝ =>
        Work.Spaces.HkIntegrand α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    integrable_HkIntegrand_zero haesm_rad2 h.memRad2
  -- the weights
  obtain ⟨M, hM0, hM⟩ := W_bdd W hW hsupp
  obtain ⟨δ, hδpos, hδW⟩ := hvan
  obtain ⟨R, hRpos, hRW⟩ := W_eq_zero_of_large W hsupp
  have hσδ : ∀ z : ℝ, z < δ → W z * (Work.Spaces.w z) ^ 2 = 0 := fun z hz => by
    rw [hδW z (le_of_lt hz), zero_mul]
  have hσR : ∀ z : ℝ, R < z → W z * (Work.Spaces.w z) ^ 2 = 0 := fun z hz => by
    have h1 : W z = 0 := hRW z (by rw [abs_of_pos (lt_trans hRpos hz)]; linarith)
    rw [h1, zero_mul]
  have hA2 : ContDiffOn ℝ 2 (fun z : ℝ => W z * (Work.Spaces.w z) ^ 2 * z ^ 2) (Set.Ioi 0) :=
    (contDiffOn_sigma W hW).mul (contDiffOn_id.pow 2)
  have hA1 : ContDiffOn ℝ 1 (deriv (fun z : ℝ => W z * (Work.Spaces.w z) ^ 2 * z ^ 2))
      (Set.Ioi 0) := hA2.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hA0c : ContinuousOn
      (deriv (deriv (fun z : ℝ => W z * (Work.Spaces.w z) ^ 2 * z ^ 2))) (Set.Ioi 0) :=
    hA1.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hid2 : ContDiffOn ℝ 2 (fun z : ℝ => z) (Set.Ioi 0) := contDiffOn_id
  have hB2 : ContDiffOn ℝ 2 (fun z : ℝ => W z * (Work.Spaces.w z) ^ 2 * z) (Set.Ioi 0) :=
    (contDiffOn_sigma W hW).mul hid2
  have hB0c : ContinuousOn (deriv (fun z : ℝ => W z * (Work.Spaces.w z) ^ 2 * z))
      (Set.Ioi 0) :=
    hB2.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hAbd : ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℝ,
      |deriv (deriv (fun z : ℝ => W z * (Work.Spaces.w z) ^ 2 * z ^ 2)) z| ≤ M := by
    have hsub : Set.Icc δ R ⊆ Set.Ioi (0 : ℝ) := fun z hz => lt_of_lt_of_le hδpos hz.1
    obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc δ R)).exists_bound_of_continuousOn
      (hA0c.mono hsub : ContinuousOn
        (deriv (deriv (fun z : ℝ => W z * (Work.Spaces.w z) ^ 2 * z ^ 2))) (Set.Icc δ R))
    have hvanδ : ∀ z : ℝ, z < δ → (fun z : ℝ => W z * (Work.Spaces.w z) ^ 2 * z ^ 2) z = 0 :=
      fun z hz => by
        show W z * (Work.Spaces.w z) ^ 2 * z ^ 2 = 0
        rw [hσδ z hz]; ring
    have hvanR : ∀ z : ℝ, R < z → (fun z : ℝ => W z * (Work.Spaces.w z) ^ 2 * z ^ 2) z = 0 :=
      fun z hz => by
        show W z * (Work.Spaces.w z) ^ 2 * z ^ 2 = 0
        rw [hσR z hz]; ring
    have hd1 := deriv_zero_of_zero hvanδ hvanR
    have hd2 := deriv_zero_of_zero hd1.1 hd1.2
    refine ⟨max C 0, le_max_right _ _, fun z => ?_⟩
    by_cases hz : z ∈ Set.Icc δ R
    · have h1 := hC z hz
      rw [Real.norm_eq_abs] at h1
      exact le_trans h1 (le_max_left _ _)
    · have hz' : z < δ ∨ R < z := by
        by_cases h1 : z < δ
        · exact Or.inl h1
        · refine Or.inr ?_
          by_contra hcon
          exact hz ⟨not_lt.mp h1, not_lt.mp hcon⟩
      rw [hz'.elim (fun h1 => hd2.1 z h1) (fun h2 => hd2.2 z h2), abs_zero]
      exact le_max_right _ _
  have hBbd : ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℝ,
      |deriv (fun z : ℝ => W z * (Work.Spaces.w z) ^ 2 * z) z| ≤ M := by
    have hsub : Set.Icc δ R ⊆ Set.Ioi (0 : ℝ) := fun z hz => lt_of_lt_of_le hδpos hz.1
    obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc δ R)).exists_bound_of_continuousOn
      (hB0c.mono hsub : ContinuousOn
        (deriv (fun z : ℝ => W z * (Work.Spaces.w z) ^ 2 * z)) (Set.Icc δ R))
    have hvanδ : ∀ z : ℝ, z < δ → (fun z : ℝ => W z * (Work.Spaces.w z) ^ 2 * z) z = 0 :=
      fun z hz => by
        show W z * (Work.Spaces.w z) ^ 2 * z = 0
        rw [hσδ z hz]; ring
    have hvanR : ∀ z : ℝ, R < z → (fun z : ℝ => W z * (Work.Spaces.w z) ^ 2 * z) z = 0 :=
      fun z hz => by
        show W z * (Work.Spaces.w z) ^ 2 * z = 0
        rw [hσR z hz]; ring
    have hd1 := deriv_zero_of_zero hvanδ hvanR
    refine ⟨max C 0, le_max_right _ _, fun z => ?_⟩
    by_cases hz : z ∈ Set.Icc δ R
    · have h1 := hC z hz
      rw [Real.norm_eq_abs] at h1
      exact le_trans h1 (le_max_left _ _)
    · have hz' : z < δ ∨ R < z := by
        by_cases h1 : z < δ
        · exact Or.inl h1
        · refine Or.inr ?_
          by_contra hcon
          exact hz ⟨not_lt.mp h1, not_lt.mp hcon⟩
      rw [hz'.elim (fun h1 => hd1.1 z h1) (fun h2 => hd1.2 z h2), abs_zero]
      exact le_max_right _ _
  obtain ⟨M4, hM40, hM4⟩ := hAbd
  obtain ⟨M5, hM50, hM5⟩ := hBbd
  -- a.e. strong measurabilities of the integrands
  have haesm_w : AEStronglyMeasurable
      (fun p : ℝ × ℝ => W p.1 * (Work.Spaces.w p.1) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _
      ((contDiffOn_sigma W hW).continuousOn.comp continuousOn_fst (fun p hp => hp.1))
  have haesm_wA : AEStronglyMeasurable
      (fun p : ℝ × ℝ => W p.1 * (Work.Spaces.w p.1) ^ 2 * p.1 ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _
      (hA2.continuousOn.comp continuousOn_fst (fun p hp => hp.1))
  have haesm_A2 : AEStronglyMeasurable
      (fun p : ℝ × ℝ => deriv (deriv (fun z : ℝ => W z * (Work.Spaces.w z) ^ 2 * z ^ 2)) p.1)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ (hA0c.comp continuousOn_fst (fun p hp => hp.1))
  have haesm_B1 : AEStronglyMeasurable
      (fun p : ℝ × ℝ => deriv (fun z : ℝ => W z * (Work.Spaces.w z) ^ 2 * z) p.1)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ (hB0c.comp continuousOn_fst (fun p hp => hp.1))
  have haesm_f1 : AEStronglyMeasurable
      (Function.uncurry (fun z θ => W z * (Work.Spaces.w z) ^ 2 * (G z θ * u z θ)))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    (haesm_w.mul (haesm_G.mul haesm_u)).congr
      (Filter.Eventually.of_forall fun p => rfl)
  have haesm_f2 : AEStronglyMeasurable
      (Function.uncurry
        (fun z θ => W z * (Work.Spaces.w z) ^ 2 * z ^ 2 * (Work.Spaces.pz u z θ) ^ 2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    (haesm_wA.mul (haesm_pzu.pow 2)).congr
      (Filter.Eventually.of_forall fun p => rfl)
  have haesm_f3 : AEStronglyMeasurable
      (Function.uncurry
        (fun z θ => W z * (Work.Spaces.w z) ^ 2 * (Work.Elliptic.Lzero u z θ * u z θ)))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    (haesm_w.mul (haesm_L.mul haesm_u)).congr
      (Filter.Eventually.of_forall fun p => rfl)
  have haesm_f4 : AEStronglyMeasurable
      (Function.uncurry (fun z θ =>
        deriv (deriv (fun z : ℝ => W z * (Work.Spaces.w z) ^ 2 * z ^ 2)) z * (u z θ) ^ 2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    (haesm_A2.mul (haesm_u.pow 2)).congr
      (Filter.Eventually.of_forall fun p => rfl)
  have haesm_f5 : AEStronglyMeasurable
      (Function.uncurry (fun z θ =>
        deriv (fun z : ℝ => W z * (Work.Spaces.w z) ^ 2 * z) z * (u z θ) ^ 2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    (haesm_B1.mul (haesm_u.pow 2)).congr
      (Filter.Eventually.of_forall fun p => rfl)
  -- the majorants
  have hmaj1 : Integrable (fun p : ℝ × ℝ =>
      (M / 2) * (Work.Spaces.HkIntegrand α 0 G p.1 p.2
        + Work.Spaces.HkIntegrand α 0 u p.1 p.2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    (hIG.add hIu).const_mul _
  have hmaj3 : Integrable (fun p : ℝ × ℝ =>
      (3 * M / 2) * Work.Spaces.HkIntegrand α 0 G p.1 p.2
        + (3 * M / 2) * Work.Spaces.HkIntegrand α 0
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) p.1 p.2
        + (6 * M) * Work.Spaces.HkIntegrand α 0
            (fun z θ => z * Work.Spaces.pz u z θ) p.1 p.2
        + (M / 2) * Work.Spaces.HkIntegrand α 0 u p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    (((hIG.const_mul _).add (hIr2.const_mul _)).add (hIgr.const_mul _)).add
      (hIu.const_mul _)
  have hα1 : α ≤ 1 := le_trans h.hα4 (by norm_num)
  have hα2 : α ^ 2 ≤ 1 / 16 := by nlinarith [h.hα, h.hα4, sq_nonneg α]
  have hα4 : α ^ 4 ≤ 1 := by nlinarith [hα2, sq_nonneg (α ^ 2)]
  have h5s : (5 + α) ^ 2 ≤ 36 := by nlinarith [h.hα, hα1, sq_nonneg (5 + α)]
  have hα5 : α ^ 2 * (5 + α) ^ 2 ≤ 4 := by
    have h1 : α ^ 2 * (5 + α) ^ 2 ≤ (1 / 16) * 36 :=
      mul_le_mul hα2 h5s (sq_nonneg _) (by norm_num)
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine Integrable.mono' hmaj1 haesm_f1 ?_
    filter_upwards [ae_HkIntegrand_zero α G, ae_HkIntegrand_zero α u, one_le_sig_ae]
      with p hGp hup hsig
    have hw2 : (0 : ℝ) ≤ (Work.Spaces.w p.1) ^ 2 := sq_nonneg _
    have hgm : |G p.1 p.2 * u p.1 p.2| ≤ ((G p.1 p.2) ^ 2 + (u p.1 p.2) ^ 2) / 2 := by
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg (G p.1 p.2 + u p.1 p.2),
        sq_nonneg (G p.1 p.2 - u p.1 p.2)]
    have hc0 : (0 : ℝ) ≤ ((G p.1 p.2) ^ 2 + (u p.1 p.2) ^ 2) / 2 := by positivity
    simp only [Function.uncurry]
    rw [Real.norm_eq_abs, hGp, hup, abs_mul, abs_mul, abs_of_nonneg hw2]
    have hstep : |W p.1| * (Work.Spaces.w p.1) ^ 2 * |G p.1 p.2 * u p.1 p.2|
        ≤ M * (Work.Spaces.w p.1) ^ 2 * (((G p.1 p.2) ^ 2 + (u p.1 p.2) ^ 2) / 2)
          * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)) := by
      have h1 : |W p.1| * (Work.Spaces.w p.1) ^ 2 * |G p.1 p.2 * u p.1 p.2|
          ≤ M * (Work.Spaces.w p.1) ^ 2 * |G p.1 p.2 * u p.1 p.2| :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hM p.1) hw2) (abs_nonneg _)
      have h2 : M * (Work.Spaces.w p.1) ^ 2 * |G p.1 p.2 * u p.1 p.2|
          ≤ M * (Work.Spaces.w p.1) ^ 2 * (((G p.1 p.2) ^ 2 + (u p.1 p.2) ^ 2) / 2) :=
        mul_le_mul_of_nonneg_left hgm (mul_nonneg hM0 hw2)
      have h3 : M * (Work.Spaces.w p.1) ^ 2 * (((G p.1 p.2) ^ 2 + (u p.1 p.2) ^ 2) / 2)
          ≤ M * (Work.Spaces.w p.1) ^ 2 * (((G p.1 p.2) ^ 2 + (u p.1 p.2) ^ 2) / 2)
            * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)) :=
        le_mul_of_one_le_right (mul_nonneg (mul_nonneg hM0 hw2) hc0) hsig
      linarith [h1, h2, h3]
    refine le_trans hstep (le_of_eq ?_)
    ring
  · refine Integrable.mono' (hIgr.const_mul M) haesm_f2 ?_
    filter_upwards [ae_HkIntegrand_zero α (fun z θ => z * Work.Spaces.pz u z θ),
      one_le_sig_ae] with p hgrp hsig
    have hw2 : (0 : ℝ) ≤ (Work.Spaces.w p.1) ^ 2 := sq_nonneg _
    have hp0 : (0 : ℝ) ≤ p.1 ^ 2 := sq_nonneg _
    have hz0 : (0 : ℝ) ≤ (Work.Spaces.pz u p.1 p.2) ^ 2 := sq_nonneg _
    simp only [Function.uncurry]
    rw [Real.norm_eq_abs, hgrp, abs_mul, abs_mul, abs_mul, abs_of_nonneg hw2, abs_of_nonneg hp0,
      abs_of_nonneg hz0,
      show (p.1 * Work.Spaces.pz u p.1 p.2) ^ 2
        = p.1 ^ 2 * (Work.Spaces.pz u p.1 p.2) ^ 2 from by ring]
    have hstep : |W p.1| * (Work.Spaces.w p.1) ^ 2 * p.1 ^ 2
          * (Work.Spaces.pz u p.1 p.2) ^ 2
        ≤ M * (p.1 ^ 2 * (Work.Spaces.pz u p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2
          * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) := by
      have h1 : |W p.1| * (Work.Spaces.w p.1) ^ 2 * p.1 ^ 2
            * (Work.Spaces.pz u p.1 p.2) ^ 2
          = |W p.1| * ((Work.Spaces.w p.1) ^ 2 * (p.1 ^ 2
              * (Work.Spaces.pz u p.1 p.2) ^ 2)) := by ring
      have h2 : |W p.1| * ((Work.Spaces.w p.1) ^ 2
            * (p.1 ^ 2 * (Work.Spaces.pz u p.1 p.2) ^ 2))
          ≤ M * ((Work.Spaces.w p.1) ^ 2 * (p.1 ^ 2
              * (Work.Spaces.pz u p.1 p.2) ^ 2)) :=
        mul_le_mul_of_nonneg_right (hM p.1) (mul_nonneg hw2 (mul_nonneg hp0 hz0))
      have h3 : M * ((Work.Spaces.w p.1) ^ 2 * (p.1 ^ 2 * (Work.Spaces.pz u p.1 p.2) ^ 2))
          ≤ M * ((Work.Spaces.w p.1) ^ 2 * (p.1 ^ 2 * (Work.Spaces.pz u p.1 p.2) ^ 2))
            * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)) :=
        le_mul_of_one_le_right (mul_nonneg hM0 (mul_nonneg hw2 (mul_nonneg hp0 hz0))) hsig
      have h4 : M * ((Work.Spaces.w p.1) ^ 2 * (p.1 ^ 2 * (Work.Spaces.pz u p.1 p.2) ^ 2))
            * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))
          = M * (p.1 ^ 2 * (Work.Spaces.pz u p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2
            * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) := by ring
      linarith [h1, h2, h3, h4]
    exact hstep
  · refine Integrable.mono' hmaj3 haesm_f3 ?_
    filter_upwards [ae_prod_fst_pos, ae_prod_snd_Ioo, ae_HkIntegrand_zero α G,
      ae_HkIntegrand_zero α (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ),
      ae_HkIntegrand_zero α (fun z θ => z * Work.Spaces.pz u z θ),
      ae_HkIntegrand_zero α u, one_le_sig_ae] with p hz hp hGp hr2 hgrp hup hsig
    have hw2 : (0 : ℝ) ≤ (Work.Spaces.w p.1) ^ 2 := sq_nonneg _
    have hLz : Work.Elliptic.Lzero u p.1 p.2
        = G p.1 p.2 + α ^ 2 * p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2
          + α * (5 + α) * p.1 * Work.Spaces.pz u p.1 p.2 := by
      have h1 := (h.eq p.1 hz p.2 hp.1 hp.2).symm
      rw [Work.Elliptic.bslOp_apply] at h1
      simp only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero, Work.Spaces.pz] at h1 ⊢
      linarith [h1]
    have hkey : (Work.Elliptic.Lzero u p.1 p.2) ^ 2
        ≤ 3 * ((G p.1 p.2) ^ 2 + (p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2) ^ 2
            + 4 * (p.1 * Work.Spaces.pz u p.1 p.2) ^ 2) := by
      have e1 : (G p.1 p.2 + α ^ 2 * p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2
          + α * (5 + α) * p.1 * Work.Spaces.pz u p.1 p.2) ^ 2
          ≤ 3 * ((G p.1 p.2) ^ 2 + (α ^ 2 * p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2) ^ 2
            + (α * (5 + α) * p.1 * Work.Spaces.pz u p.1 p.2) ^ 2) := by
        nlinarith [sq_nonneg (G p.1 p.2 - α ^ 2 * p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2),
          sq_nonneg (G p.1 p.2 - α * (5 + α) * p.1 * Work.Spaces.pz u p.1 p.2),
          sq_nonneg (α ^ 2 * p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2
            - α * (5 + α) * p.1 * Work.Spaces.pz u p.1 p.2)]
      have e2 : (α ^ 2 * p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2) ^ 2
          = α ^ 4 * (p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2) ^ 2 := by ring
      have e3 : (α * (5 + α) * p.1 * Work.Spaces.pz u p.1 p.2) ^ 2
          = α ^ 2 * (5 + α) ^ 2 * (p.1 * Work.Spaces.pz u p.1 p.2) ^ 2 := by ring
      rw [hLz]
      refine le_trans e1 ?_
      rw [e2, e3]
      nlinarith [hα4, hα5, sq_nonneg (p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2),
        sq_nonneg (p.1 * Work.Spaces.pz u p.1 p.2), sq_nonneg (G p.1 p.2)]
    have hkey' : 3 * ((G p.1 p.2) ^ 2 + (α ^ 2 * p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2) ^ 2
          + (α * (5 + α) * p.1 * Work.Spaces.pz u p.1 p.2) ^ 2)
        ≤ 3 * ((G p.1 p.2) ^ 2 + (p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2) ^ 2
            + 4 * (p.1 * Work.Spaces.pz u p.1 p.2) ^ 2) := by
      have e2 : (α ^ 2 * p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2) ^ 2
          = α ^ 4 * (p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2) ^ 2 := by ring
      have e3 : (α * (5 + α) * p.1 * Work.Spaces.pz u p.1 p.2) ^ 2
          = α ^ 2 * (5 + α) ^ 2 * (p.1 * Work.Spaces.pz u p.1 p.2) ^ 2 := by ring
      rw [e2, e3]
      nlinarith [hα4, hα5, sq_nonneg (p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2),
        sq_nonneg (p.1 * Work.Spaces.pz u p.1 p.2), sq_nonneg (G p.1 p.2)]
    have habs : |Work.Elliptic.Lzero u p.1 p.2 * u p.1 p.2|
        ≤ ((Work.Elliptic.Lzero u p.1 p.2) ^ 2 + (u p.1 p.2) ^ 2) / 2 := by
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg (Work.Elliptic.Lzero u p.1 p.2 + u p.1 p.2),
        sq_nonneg (Work.Elliptic.Lzero u p.1 p.2 - u p.1 p.2)]
    have hc0 : (0 : ℝ) ≤ (3 * ((G p.1 p.2) ^ 2
          + (p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2) ^ 2
          + 4 * (p.1 * Work.Spaces.pz u p.1 p.2) ^ 2) + (u p.1 p.2) ^ 2) / 2 := by positivity
    simp only [Function.uncurry]
    rw [Real.norm_eq_abs, hGp, hr2, hgrp, hup, abs_mul, abs_mul, abs_of_nonneg hw2]
    have hchain : |W p.1| * (Work.Spaces.w p.1) ^ 2
          * |Work.Elliptic.Lzero u p.1 p.2 * u p.1 p.2|
        ≤ (3 * M / 2) * (G p.1 p.2 ^ 2 * (Work.Spaces.w p.1) ^ 2
            * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
          + (3 * M / 2) * ((p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2) ^ 2
              * (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
          + (6 * M) * ((p.1 * Work.Spaces.pz u p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2
              * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
          + (M / 2) * ((u p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2
              * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) := by
      have h1 : |W p.1| * (Work.Spaces.w p.1) ^ 2
            * |Work.Elliptic.Lzero u p.1 p.2 * u p.1 p.2|
          ≤ M * (Work.Spaces.w p.1) ^ 2
            * (((Work.Elliptic.Lzero u p.1 p.2) ^ 2 + (u p.1 p.2) ^ 2) / 2) := by
        have h1a : |W p.1| * (Work.Spaces.w p.1) ^ 2
              * |Work.Elliptic.Lzero u p.1 p.2 * u p.1 p.2|
            ≤ M * (Work.Spaces.w p.1) ^ 2
              * |Work.Elliptic.Lzero u p.1 p.2 * u p.1 p.2| :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hM p.1) hw2) (abs_nonneg _)
        have h1b : M * (Work.Spaces.w p.1) ^ 2
              * |Work.Elliptic.Lzero u p.1 p.2 * u p.1 p.2|
            ≤ M * (Work.Spaces.w p.1) ^ 2
              * (((Work.Elliptic.Lzero u p.1 p.2) ^ 2 + (u p.1 p.2) ^ 2) / 2) :=
          mul_le_mul_of_nonneg_left habs (mul_nonneg hM0 hw2)
        linarith [h1a, h1b]
      have h2 : M * (Work.Spaces.w p.1) ^ 2
            * (((Work.Elliptic.Lzero u p.1 p.2) ^ 2 + (u p.1 p.2) ^ 2) / 2)
          ≤ M * (Work.Spaces.w p.1) ^ 2
            * ((3 * ((G p.1 p.2) ^ 2 + (p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2) ^ 2
                + 4 * (p.1 * Work.Spaces.pz u p.1 p.2) ^ 2) + (u p.1 p.2) ^ 2) / 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hM0 hw2)
        linarith [hkey]
      have h3 : M * (Work.Spaces.w p.1) ^ 2
            * ((3 * ((G p.1 p.2) ^ 2 + (p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2) ^ 2
                + 4 * (p.1 * Work.Spaces.pz u p.1 p.2) ^ 2) + (u p.1 p.2) ^ 2) / 2)
          ≤ M * (Work.Spaces.w p.1) ^ 2
            * ((3 * ((G p.1 p.2) ^ 2 + (p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2) ^ 2
                + 4 * (p.1 * Work.Spaces.pz u p.1 p.2) ^ 2) + (u p.1 p.2) ^ 2) / 2)
            * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)) :=
        le_mul_of_one_le_right (mul_nonneg (mul_nonneg hM0 hw2) hc0) hsig
      have h4 : M * (Work.Spaces.w p.1) ^ 2
            * ((3 * ((G p.1 p.2) ^ 2 + (p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2) ^ 2
                + 4 * (p.1 * Work.Spaces.pz u p.1 p.2) ^ 2) + (u p.1 p.2) ^ 2) / 2)
            * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))
          = (3 * M / 2) * (G p.1 p.2 ^ 2 * (Work.Spaces.w p.1) ^ 2
              * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
            + (3 * M / 2) * ((p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2) ^ 2
                * (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
            + (6 * M) * ((p.1 * Work.Spaces.pz u p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2
                * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
            + (M / 2) * ((u p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2
                * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) := by ring
      nlinarith [h1, h2, h3, h4]
    exact le_trans hchain (le_of_eq (by ring))
  · refine Integrable.mono' (hIu.const_mul M4) haesm_f4 ?_
    filter_upwards [ae_HkIntegrand_zero α u, ae_prod_fst_pos, one_le_sig_ae]
      with p hup hzpos hsig
    have hw1 : 1 ≤ Work.Spaces.w p.1 := one_le_w hzpos
    have hw2 : (0 : ℝ) ≤ (Work.Spaces.w p.1) ^ 2 := sq_nonneg _
    have hw12 : (1 : ℝ) ≤ (Work.Spaces.w p.1) ^ 2 := by nlinarith [hw1]
    have hu0 : (0 : ℝ) ≤ (u p.1 p.2) ^ 2 := sq_nonneg _
    simp only [Function.uncurry]
    rw [Real.norm_eq_abs, hup, abs_mul, abs_of_nonneg (sq_nonneg (u p.1 p.2))]
    have hchain : |deriv (deriv (fun z : ℝ => W z * (Work.Spaces.w z) ^ 2 * z ^ 2)) p.1|
          * (u p.1 p.2) ^ 2
        ≤ M4 * ((u p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2
            * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) := by
      have h1 : |deriv (deriv (fun z : ℝ => W z * (Work.Spaces.w z) ^ 2 * z ^ 2)) p.1|
            * (u p.1 p.2) ^ 2
          ≤ M4 * (u p.1 p.2) ^ 2 := mul_le_mul_of_nonneg_right (hM4 p.1) hu0
      have h2 : M4 * (u p.1 p.2) ^ 2
          ≤ M4 * ((u p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2) :=
        mul_le_mul_of_nonneg_left (by nlinarith [hw12, hu0]) hM40
      have h3 : M4 * ((u p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2)
          ≤ M4 * ((u p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2
              * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) :=
        mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (mul_nonneg hu0 hw2) hsig) hM40
      linarith [h1, h2, h3]
    exact le_trans hchain (le_of_eq (by ring))
  · refine Integrable.mono' (hIu.const_mul M5) haesm_f5 ?_
    filter_upwards [ae_HkIntegrand_zero α u, ae_prod_fst_pos, one_le_sig_ae]
      with p hup hzpos hsig
    have hw1 : 1 ≤ Work.Spaces.w p.1 := one_le_w hzpos
    have hw2 : (0 : ℝ) ≤ (Work.Spaces.w p.1) ^ 2 := sq_nonneg _
    have hw12 : (1 : ℝ) ≤ (Work.Spaces.w p.1) ^ 2 := by nlinarith [hw1]
    have hu0 : (0 : ℝ) ≤ (u p.1 p.2) ^ 2 := sq_nonneg _
    simp only [Function.uncurry]
    rw [Real.norm_eq_abs, hup, abs_mul, abs_of_nonneg (sq_nonneg (u p.1 p.2))]
    have hchain : |deriv (fun z : ℝ => W z * (Work.Spaces.w z) ^ 2 * z) p.1|
          * (u p.1 p.2) ^ 2
        ≤ M5 * ((u p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2
            * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) := by
      have h1 : |deriv (fun z : ℝ => W z * (Work.Spaces.w z) ^ 2 * z) p.1|
            * (u p.1 p.2) ^ 2
          ≤ M5 * (u p.1 p.2) ^ 2 := mul_le_mul_of_nonneg_right (hM5 p.1) hu0
      have h2 : M5 * (u p.1 p.2) ^ 2
          ≤ M5 * ((u p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2) :=
        mul_le_mul_of_nonneg_left (by nlinarith [hw12, hu0]) hM50
      have h3 : M5 * ((u p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2)
          ≤ M5 * ((u p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2
              * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) :=
        mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (mul_nonneg hu0 hw2) hsig) hM50
      linarith [h1, h2, h3]
    exact le_trans hchain (le_of_eq (by ring))

/-! ## 8. The identity on one angular slice -/

private theorem slice_ident (α : ℝ) (u G : ℝ → ℝ → ℝ) (h : AeData α u G)
    (W : ℝ → ℝ) (hW : ContDiff ℝ 2 W) (hsupp : HasCompactSupport W)
    (hvan : ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℝ, z ≤ δ → W z = 0)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (∫ z in Set.Ioi 0, W z * (Work.Spaces.w z) ^ 2 * (G z θ * u z θ))
      = α ^ 2 * (∫ z in Set.Ioi 0,
            W z * (Work.Spaces.w z) ^ 2 * z ^ 2 * (Work.Spaces.pz u z θ) ^ 2)
        + (∫ z in Set.Ioi 0,
            W z * (Work.Spaces.w z) ^ 2 * (Work.Elliptic.Lzero u z θ * u z θ))
        - (α ^ 2 / 2) * (∫ z in Set.Ioi 0,
            deriv (deriv (fun z : ℝ => W z * (Work.Spaces.w z) ^ 2 * z ^ 2)) z
              * (u z θ) ^ 2)
        + (α * (5 + α) / 2) * (∫ z in Set.Ioi 0,
            deriv (fun z : ℝ => W z * (Work.Spaces.w z) ^ 2 * z) z * (u z θ) ^ 2) := by
  obtain ⟨δ, hδpos, hδW⟩ := hvan
  obtain ⟨R, hRpos, hRW⟩ := W_eq_zero_of_large W hsupp
  let φ : ℝ → ℝ := fun z => u z θ
  let σ : ℝ → ℝ := fun z => W z * (Work.Spaces.w z) ^ 2
  have hσ2 : ContDiffOn ℝ 2 σ (Set.Ioi 0) := contDiffOn_sigma W hW
  have hφ2 : ContDiffOn ℝ 2 φ (Set.Ioi 0) := slice_contDiffOn h.smooth hθ
  have hσδ : ∀ z : ℝ, z < δ → σ z = 0 := fun z hz => by
    show W z * (Work.Spaces.w z) ^ 2 = 0
    rw [hδW z (le_of_lt hz), zero_mul]
  have hσR : ∀ z : ℝ, R < z → σ z = 0 := fun z hz => by
    show W z * (Work.Spaces.w z) ^ 2 = 0
    have h1 : W z = 0 := hRW z (by rw [abs_of_pos (lt_trans hRpos hz)]; linarith)
    rw [h1, zero_mul]
  have hσc : ContinuousOn σ (Set.Ioi 0) := hσ2.continuousOn
  have hφc : ContinuousOn φ (Set.Ioi 0) := hφ2.continuousOn
  have hφ1 : ContDiffOn ℝ 1 (deriv φ) (Set.Ioi 0) := hφ2.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hφ1c : ContinuousOn (deriv φ) (Set.Ioi 0) := hφ1.continuousOn
  have hφ2c : ContinuousOn (deriv (deriv φ)) (Set.Ioi 0) :=
    hφ1.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hA2 : ContDiffOn ℝ 2 (fun z : ℝ => z ^ 2 * σ z) (Set.Ioi 0) :=
    ((contDiffOn_id : ContDiffOn ℝ 2 (fun z : ℝ => z) (Set.Ioi 0)).pow 2).mul hσ2
  have hA1 : ContDiffOn ℝ 1 (deriv (fun z : ℝ => z ^ 2 * σ z)) (Set.Ioi 0) :=
    hA2.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hAc : ContinuousOn (fun z : ℝ => z ^ 2 * σ z) (Set.Ioi 0) := hA2.continuousOn
  have hA1c : ContinuousOn (deriv (fun z : ℝ => z ^ 2 * σ z)) (Set.Ioi 0) := hA1.continuousOn
  have hA2c : ContinuousOn (deriv (deriv (fun z : ℝ => z ^ 2 * σ z))) (Set.Ioi 0) :=
    hA1.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hB2 : ContDiffOn ℝ 2 (fun z : ℝ => z * σ z) (Set.Ioi 0) :=
    (contDiffOn_id : ContDiffOn ℝ 2 (fun z : ℝ => z) (Set.Ioi 0)).mul hσ2
  have hBc : ContinuousOn (fun z : ℝ => z * σ z) (Set.Ioi 0) := hB2.continuousOn
  have hB1c : ContinuousOn (deriv (fun z : ℝ => z * σ z)) (Set.Ioi 0) :=
    hB2.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hLc : ContinuousOn (fun z : ℝ => Work.Elliptic.Lzero u z θ) (Set.Ioi 0) :=
    (smoothOpen_Lzero (Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth)).curry_z hθ
      |>.continuousOn
  have hAσδ : ∀ z : ℝ, z < δ → (fun z : ℝ => z ^ 2 * σ z) z = 0 := fun z hz => by
    show z ^ 2 * σ z = 0
    rw [hσδ z hz]; ring
  have hAσR : ∀ z : ℝ, R < z → (fun z : ℝ => z ^ 2 * σ z) z = 0 := fun z hz => by
    show z ^ 2 * σ z = 0
    rw [hσR z hz]; ring
  have hdA := deriv_zero_of_zero hAσδ hAσR
  have hdA2 := deriv_zero_of_zero hdA.1 hdA.2
  have hBσδ : ∀ z : ℝ, z < δ → (fun z : ℝ => z * σ z) z = 0 := fun z hz => by
    show z * σ z = 0
    rw [hσδ z hz]; ring
  have hBσR : ∀ z : ℝ, R < z → (fun z : ℝ => z * σ z) z = 0 := fun z hz => by
    show z * σ z = 0
    rw [hσR z hz]; ring
  have hdB := deriv_zero_of_zero hBσδ hBσR
  -- integrability of the seven pieces (compact support)
  have hi1 : IntegrableOn (fun z : ℝ => z ^ 2 * σ z * φ z * deriv (deriv φ) z) (Set.Ioi 0) :=
    integrableOn_Ioi_of_support (a := δ) (b := max δ R) hδpos (le_max_left _ _)
      (((continuousOn_id.pow 2).mul hσc).mul hφc |>.mul hφ2c)
      (fun z hz => by
        show z ^ 2 * σ z * φ z * deriv (deriv φ) z = 0
        rw [hσδ z hz]; ring)
      (fun z hz => by
        show z ^ 2 * σ z * φ z * deriv (deriv φ) z = 0
        rw [hσR z (lt_of_le_of_lt (le_max_right δ R) hz)]; ring)
  have hi2 : IntegrableOn
      (fun z : ℝ => deriv (fun z : ℝ => z ^ 2 * σ z) z * φ z * deriv φ z) (Set.Ioi 0) :=
    integrableOn_Ioi_of_support (a := δ) (b := max δ R) hδpos (le_max_left _ _)
      ((hA1c.mul hφc).mul hφ1c)
      (fun z hz => by
        show deriv (fun z : ℝ => z ^ 2 * σ z) z * φ z * deriv φ z = 0
        rw [hdA.1 z hz]; ring)
      (fun z hz => by
        show deriv (fun z : ℝ => z ^ 2 * σ z) z * φ z * deriv φ z = 0
        rw [hdA.2 z (lt_of_le_of_lt (le_max_right δ R) hz)]; ring)
  have hi3 : IntegrableOn (fun z : ℝ => σ z * (z * deriv φ z) ^ 2) (Set.Ioi 0) :=
    integrableOn_Ioi_of_support (a := δ) (b := max δ R) hδpos (le_max_left _ _)
      (hσc.mul ((continuousOn_id.mul hφ1c).pow 2))
      (fun z hz => by
        show σ z * (z * deriv φ z) ^ 2 = 0
        rw [hσδ z hz]; ring)
      (fun z hz => by
        show σ z * (z * deriv φ z) ^ 2 = 0
        rw [hσR z (lt_of_le_of_lt (le_max_right δ R) hz)]; ring)
  have hi4 : IntegrableOn
      (fun z : ℝ => deriv (deriv (fun z : ℝ => z ^ 2 * σ z)) z * (φ z) ^ 2) (Set.Ioi 0) :=
    integrableOn_Ioi_of_support (a := δ) (b := max δ R) hδpos (le_max_left _ _)
      (hA2c.mul (hφc.pow 2))
      (fun z hz => by
        show deriv (deriv (fun z : ℝ => z ^ 2 * σ z)) z * (φ z) ^ 2 = 0
        rw [hdA2.1 z hz]; ring)
      (fun z hz => by
        show deriv (deriv (fun z : ℝ => z ^ 2 * σ z)) z * (φ z) ^ 2 = 0
        rw [hdA2.2 z (lt_of_le_of_lt (le_max_right δ R) hz)]; ring)
  have hi5 : IntegrableOn (fun z : ℝ => z * σ z * φ z * deriv φ z) (Set.Ioi 0) :=
    integrableOn_Ioi_of_support (a := δ) (b := max δ R) hδpos (le_max_left _ _)
      (((continuousOn_id.mul hσc).mul hφc).mul hφ1c)
      (fun z hz => by
        show z * σ z * φ z * deriv φ z = 0
        rw [hσδ z hz]; ring)
      (fun z hz => by
        show z * σ z * φ z * deriv φ z = 0
        rw [hσR z (lt_of_le_of_lt (le_max_right δ R) hz)]; ring)
  have hi6 : IntegrableOn
      (fun z : ℝ => deriv (fun z : ℝ => z * σ z) z * (φ z) ^ 2) (Set.Ioi 0) :=
    integrableOn_Ioi_of_support (a := δ) (b := max δ R) hδpos (le_max_left _ _)
      (hB1c.mul (hφc.pow 2))
      (fun z hz => by
        show deriv (fun z : ℝ => z * σ z) z * (φ z) ^ 2 = 0
        rw [hdB.1 z hz]; ring)
      (fun z hz => by
        show deriv (fun z : ℝ => z * σ z) z * (φ z) ^ 2 = 0
        rw [hdB.2 z (lt_of_le_of_lt (le_max_right δ R) hz)]; ring)
  have hi7 : IntegrableOn
      (fun z : ℝ => σ z * (Work.Elliptic.Lzero u z θ * φ z)) (Set.Ioi 0) :=
    integrableOn_Ioi_of_support (a := δ) (b := max δ R) hδpos (le_max_left _ _)
      (hσc.mul (hLc.mul hφc))
      (fun z hz => by
        show σ z * (Work.Elliptic.Lzero u z θ * φ z) = 0
        rw [hσδ z hz]; ring)
      (fun z hz => by
        show σ z * (Work.Elliptic.Lzero u z θ * φ z) = 0
        rw [hσR z (lt_of_le_of_lt (le_max_right δ R) hz)]; ring)
  -- the boundary conditions of the two integrations by parts
  have hb1 : Tendsto (fun z : ℝ => z ^ 2 * σ z * φ z * deriv φ z)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Ioo_mem_nhdsGT hδpos] with z hz
    show (0 : ℝ) = z ^ 2 * σ z * φ z * deriv φ z
    rw [hσδ z hz.2]; ring
  have hb2 : Tendsto (fun z : ℝ => z ^ 2 * σ z * φ z * deriv φ z) atTop (nhds 0) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop (R + 1)] with z hz
    show (0 : ℝ) = z ^ 2 * σ z * φ z * deriv φ z
    rw [hσR z (by linarith)]; ring
  have hb3 : Tendsto (fun z : ℝ => deriv (fun z : ℝ => z ^ 2 * σ z) z * (φ z) ^ 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Ioo_mem_nhdsGT hδpos] with z hz
    show (0 : ℝ) = deriv (fun z : ℝ => z ^ 2 * σ z) z * (φ z) ^ 2
    rw [hdA.1 z hz.2]; ring
  have hb4 : Tendsto (fun z : ℝ => deriv (fun z : ℝ => z ^ 2 * σ z) z * (φ z) ^ 2)
      atTop (nhds 0) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop (R + 1)] with z hz
    show (0 : ℝ) = deriv (fun z : ℝ => z ^ 2 * σ z) z * (φ z) ^ 2
    rw [hdA.2 z (by linarith)]; ring
  have hb5 : Tendsto (fun z : ℝ => z * σ z * (φ z) ^ 2) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Ioo_mem_nhdsGT hδpos] with z hz
    show (0 : ℝ) = z * σ z * (φ z) ^ 2
    rw [hσδ z hz.2]; ring
  have hb6 : Tendsto (fun z : ℝ => z * σ z * (φ z) ^ 2) atTop (nhds 0) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop (R + 1)] with z hz
    show (0 : ℝ) = z * σ z * (φ z) ^ 2
    rw [hσR z (by linarith)]; ring
  -- the equation on the slice
  have hGz : ∀ z ∈ Set.Ioi (0 : ℝ), G z θ
      = -(α ^ 2 * z ^ 2) * deriv (deriv φ) z - (α * (5 + α) * z) * deriv φ z
        + Work.Elliptic.Lzero u z θ := by
    intro z hz
    have h1 := h.eq z hz θ hθ.1 hθ.2
    rw [Work.Elliptic.bslOp_apply] at h1
    have e1 : Work.Spaces.pzIter 2 u z θ = deriv (deriv φ) z := by
      simp only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero, Work.Spaces.pz]
      rfl
    have e2 : Work.Spaces.pz u z θ = deriv φ z := by
      simp only [Work.Spaces.pz]
      rfl
    rw [e1, e2] at h1
    linarith [h1]
  have hstep1 : (∫ z in Set.Ioi 0, σ z * (G z θ * φ z))
      = ∫ z in Set.Ioi 0, σ z * ((-(α ^ 2 * z ^ 2) * deriv (deriv φ) z
          - (α * (5 + α) * z) * deriv φ z + Work.Elliptic.Lzero u z θ) * φ z) := by
    refine MeasureTheory.setIntegral_congr_ae measurableSet_Ioi ?_
    exact Filter.Eventually.of_forall (fun z hz => by rw [hGz z hz])
  have hstep2 : (∫ z in Set.Ioi 0, σ z * ((-(α ^ 2 * z ^ 2) * deriv (deriv φ) z
        - (α * (5 + α) * z) * deriv φ z + Work.Elliptic.Lzero u z θ) * φ z))
      = -(α ^ 2) * (∫ z in Set.Ioi 0, σ z * z ^ 2 * deriv (deriv φ) z * φ z)
        - (α * (5 + α)) * (∫ z in Set.Ioi 0, σ z * (z * deriv φ z) * φ z)
        + (∫ z in Set.Ioi 0, σ z * (Work.Elliptic.Lzero u z θ * φ z)) := by
    have hfun : (fun z : ℝ => σ z * ((-(α ^ 2 * z ^ 2) * deriv (deriv φ) z
          - (α * (5 + α) * z) * deriv φ z + Work.Elliptic.Lzero u z θ) * φ z))
        = fun z : ℝ => (-(α ^ 2)) * (σ z * z ^ 2 * deriv (deriv φ) z * φ z)
          + (-(α * (5 + α))) * (σ z * (z * deriv φ z) * φ z)
          + σ z * (Work.Elliptic.Lzero u z θ * φ z) := by
      funext z; ring
    rw [hfun]
    have hIa : Integrable (fun z : ℝ =>
        (-(α ^ 2)) * (σ z * z ^ 2 * deriv (deriv φ) z * φ z))
        (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
      (hi1.const_mul (-(α ^ 2))).congr (Filter.Eventually.of_forall fun z => by ring)
    have hIb : Integrable (fun z : ℝ =>
        (-(α * (5 + α))) * (σ z * (z * deriv φ z) * φ z))
        (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
      (hi5.const_mul (-(α * (5 + α)))).congr (Filter.Eventually.of_forall fun z => by ring)
    have hIc : Integrable (fun z : ℝ => σ z * (Work.Elliptic.Lzero u z θ * φ z))
        (MeasureTheory.volume.restrict (Set.Ioi 0)) := hi7
    have hIab : Integrable (fun z : ℝ =>
        (-(α ^ 2)) * (σ z * z ^ 2 * deriv (deriv φ) z * φ z)
          + (-(α * (5 + α))) * (σ z * (z * deriv φ z) * φ z))
        (MeasureTheory.volume.restrict (Set.Ioi 0)) := hIa.add hIb
    have e1 : (∫ z in Set.Ioi 0,
          (-(α ^ 2)) * (σ z * z ^ 2 * deriv (deriv φ) z * φ z)
            + (-(α * (5 + α))) * (σ z * (z * deriv φ z) * φ z)
            + σ z * (Work.Elliptic.Lzero u z θ * φ z))
        = (∫ z in Set.Ioi 0,
            (-(α ^ 2)) * (σ z * z ^ 2 * deriv (deriv φ) z * φ z)
              + (-(α * (5 + α))) * (σ z * (z * deriv φ z) * φ z))
          + (∫ z in Set.Ioi 0, σ z * (Work.Elliptic.Lzero u z θ * φ z)) :=
      MeasureTheory.integral_add hIab hIc
    have e2 : (∫ z in Set.Ioi 0,
            (-(α ^ 2)) * (σ z * z ^ 2 * deriv (deriv φ) z * φ z)
              + (-(α * (5 + α))) * (σ z * (z * deriv φ z) * φ z))
        = (∫ z in Set.Ioi 0, (-(α ^ 2)) * (σ z * z ^ 2 * deriv (deriv φ) z * φ z))
          + (∫ z in Set.Ioi 0, (-(α * (5 + α))) * (σ z * (z * deriv φ z) * φ z)) :=
      MeasureTheory.integral_add hIa hIb
    have e3 : (∫ z in Set.Ioi 0, (-(α ^ 2)) * (σ z * z ^ 2 * deriv (deriv φ) z * φ z))
        = (-(α ^ 2)) * (∫ z in Set.Ioi 0, σ z * z ^ 2 * deriv (deriv φ) z * φ z) :=
      MeasureTheory.integral_const_mul (-(α ^ 2))
        (fun z : ℝ => σ z * z ^ 2 * deriv (deriv φ) z * φ z)
    have e4 : (∫ z in Set.Ioi 0, (-(α * (5 + α))) * (σ z * (z * deriv φ z) * φ z))
        = (-(α * (5 + α))) * (∫ z in Set.Ioi 0, σ z * (z * deriv φ z) * φ z) :=
      MeasureTheory.integral_const_mul (-(α * (5 + α)))
        (fun z : ℝ => σ z * (z * deriv φ z) * φ z)
    rw [e1, e2, e3, e4]
    ring
  have hP := Work.FTS.EllipticEst.remov.ibpZZ σ φ hσ2 hφ2 hi1 hi2 hi3 hi4 hb1 hb2 hb3 hb4
  have hQ := Work.FTS.EllipticEst.remov.ibpZ σ φ hσ2 hφ2 hi5 hi6 hb5 hb6
  have eA : (∫ z in Set.Ioi 0, deriv (deriv (fun z : ℝ => z ^ 2 * σ z)) z * (φ z) ^ 2)
      = ∫ z in Set.Ioi 0, deriv (deriv (fun z : ℝ => σ z * z ^ 2)) z * (φ z) ^ 2 := by
    have h1 : (fun z : ℝ => z ^ 2 * σ z) = fun z : ℝ => σ z * z ^ 2 := by
      funext z; ring
    rw [h1]
  have eB : (∫ z in Set.Ioi 0, σ z * (z * deriv φ z) ^ 2)
      = ∫ z in Set.Ioi 0, σ z * z ^ 2 * (deriv φ z) ^ 2 := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
    ring
  have eC : (∫ z in Set.Ioi 0, deriv (fun z : ℝ => z * σ z) z * (φ z) ^ 2)
      = ∫ z in Set.Ioi 0, deriv (fun z : ℝ => σ z * z) z * (φ z) ^ 2 := by
    have h1 : (fun z : ℝ => z * σ z) = fun z : ℝ => σ z * z := by
      funext z; ring
    rw [h1]
  have hmain : (∫ z in Set.Ioi 0, σ z * (G z θ * φ z))
      = α ^ 2 * (∫ z in Set.Ioi 0, σ z * z ^ 2 * (deriv φ z) ^ 2)
        + (∫ z in Set.Ioi 0, σ z * (Work.Elliptic.Lzero u z θ * φ z))
        - (α ^ 2 / 2) * (∫ z in Set.Ioi 0,
            deriv (deriv (fun z : ℝ => σ z * z ^ 2)) z * (φ z) ^ 2)
        + (α * (5 + α) / 2) * (∫ z in Set.Ioi 0,
            deriv (fun z : ℝ => σ z * z) z * (φ z) ^ 2) := by
    rw [hstep1, hstep2, hP, hQ, eA, eC, eB]
    ring
  exact hmain

theorem TruncIdentAe : ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
    Work.Spaces.HkMem α 0 u →
    Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz u z θ) →
    ∀ W : ℝ → ℝ, ContDiff ℝ 2 W → HasCompactSupport W →
      (∃ δ : ℝ, 0 < δ ∧ ∀ z : ℝ, z ≤ δ → W z = 0) →
      (∫ z in Work.Spaces.Iz, W z * (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, G z θ * u z θ))
        = α ^ 2 * (∫ z in Work.Spaces.Iz, W z * (Work.Spaces.w z) ^ 2 * z ^ 2
              * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pz u z θ) ^ 2))
          + (∫ z in Work.Spaces.Iz, W z * (Work.Spaces.w z) ^ 2
              * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Lzero u z θ * u z θ))
          - (α ^ 2 / 2) * (∫ z in Work.Spaces.Iz,
              deriv (deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z ^ 2)) z
                * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2))
          + (α * (5 + α) / 2) * (∫ z in Work.Spaces.Iz,
              deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z) z
                * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2)) := by
  intro α u G h hu hgu W hW hsupp hvan
  obtain ⟨hI1, hI2, hI3, hI4, hI5⟩ :=
    integrable_joint α u G h hu hgu W hW hsupp hvan
  have hmeas : (MeasureTheory.volume.restrict Work.Spaces.Iz : MeasureTheory.Measure ℝ)
      = MeasureTheory.volume.restrict (Set.Ioi 0) := by
    rw [Work.Spaces.Iz]
    exact (MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0))).symm
  -- Fubini: the five `z`-outer integrals in the `θ`-outer form
  have hL : (∫ z in Work.Spaces.Iz, W z * (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, G z θ * u z θ))
      = ∫ θ in Work.Spaces.Iθ, ∫ z in Work.Spaces.Iz, W z * (Work.Spaces.w z) ^ 2
          * (G z θ * u z θ) :=
    fubini_swap (fun z => W z * (Work.Spaces.w z) ^ 2)
      (fun z θ => G z θ * u z θ) hI1
  have hT1 : α ^ 2 * (∫ z in Work.Spaces.Iz, W z * (Work.Spaces.w z) ^ 2 * z ^ 2
            * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pz u z θ) ^ 2))
      = α ^ 2 * (∫ θ in Work.Spaces.Iθ, ∫ z in Work.Spaces.Iz,
          W z * (Work.Spaces.w z) ^ 2 * z ^ 2 * (Work.Spaces.pz u z θ) ^ 2) := by
    congr 1
    exact fubini_swap (fun z => W z * (Work.Spaces.w z) ^ 2 * z ^ 2)
      (fun z θ => (Work.Spaces.pz u z θ) ^ 2) hI2
  have hT2 : (∫ z in Work.Spaces.Iz, W z * (Work.Spaces.w z) ^ 2
            * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Lzero u z θ * u z θ))
      = ∫ θ in Work.Spaces.Iθ, ∫ z in Work.Spaces.Iz, W z * (Work.Spaces.w z) ^ 2
          * (Work.Elliptic.Lzero u z θ * u z θ) :=
    fubini_swap (fun z => W z * (Work.Spaces.w z) ^ 2)
      (fun z θ => Work.Elliptic.Lzero u z θ * u z θ) hI3
  have hT3 : (α ^ 2 / 2) * (∫ z in Work.Spaces.Iz,
            deriv (deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z ^ 2)) z
              * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2))
      = (α ^ 2 / 2) * (∫ θ in Work.Spaces.Iθ, ∫ z in Work.Spaces.Iz,
          deriv (deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z ^ 2)) z
            * (u z θ) ^ 2) := by
    congr 1
    exact fubini_swap
      (fun z => deriv (deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z ^ 2)) z)
      (fun z θ => (u z θ) ^ 2) hI4
  have hT4 : ((α * (5 + α)) / 2) * (∫ z in Work.Spaces.Iz,
            deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z) z
              * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2))
      = ((α * (5 + α)) / 2) * (∫ θ in Work.Spaces.Iθ, ∫ z in Work.Spaces.Iz,
          deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z) z * (u z θ) ^ 2) := by
    congr 1
    exact fubini_swap (fun z => deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z) z)
      (fun z θ => (u z θ) ^ 2) hI5
  -- the identity on almost every angular slice
  have hae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      (∫ z in Work.Spaces.Iz, W z * (Work.Spaces.w z) ^ 2 * (G z θ * u z θ))
        = α ^ 2 * (∫ z in Work.Spaces.Iz, W z * (Work.Spaces.w z) ^ 2 * z ^ 2
              * (Work.Spaces.pz u z θ) ^ 2)
          + (∫ z in Work.Spaces.Iz, W z * (Work.Spaces.w z) ^ 2
              * (Work.Elliptic.Lzero u z θ * u z θ))
          - (α ^ 2 / 2) * (∫ z in Work.Spaces.Iz,
              deriv (deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z ^ 2)) z
                * (u z θ) ^ 2)
          + (α * (5 + α) / 2) * (∫ z in Work.Spaces.Iz,
              deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z) z * (u z θ) ^ 2) := by
    filter_upwards [ae_restrict_Iθ_Ioo] with θ hθ
    rw [hmeas]
    exact slice_ident α u G h W hW hsupp hvan hθ
  have hθeq : (∫ θ in Work.Spaces.Iθ, ∫ z in Work.Spaces.Iz, W z * (Work.Spaces.w z) ^ 2
        * (G z θ * u z θ))
      = ∫ θ in Work.Spaces.Iθ, (α ^ 2 * (∫ z in Work.Spaces.Iz,
              W z * (Work.Spaces.w z) ^ 2 * z ^ 2 * (Work.Spaces.pz u z θ) ^ 2)
          + (∫ z in Work.Spaces.Iz, W z * (Work.Spaces.w z) ^ 2
              * (Work.Elliptic.Lzero u z θ * u z θ))
          - (α ^ 2 / 2) * (∫ z in Work.Spaces.Iz,
              deriv (deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z ^ 2)) z
                * (u z θ) ^ 2)
          + (α * (5 + α) / 2) * (∫ z in Work.Spaces.Iz,
              deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z) z * (u z θ) ^ 2)) :=
    MeasureTheory.integral_congr_ae hae
  have hK1 : Integrable (fun θ : ℝ => ∫ z in Work.Spaces.Iz, W z * (Work.Spaces.w z) ^ 2
        * z ^ 2 * (Work.Spaces.pz u z θ) ^ 2) (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    hI2.integral_prod_right
  have hK2 : Integrable (fun θ : ℝ => ∫ z in Work.Spaces.Iz, W z * (Work.Spaces.w z) ^ 2
        * (Work.Elliptic.Lzero u z θ * u z θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    hI3.integral_prod_right
  have hK3 : Integrable (fun θ : ℝ => ∫ z in Work.Spaces.Iz,
        deriv (deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z ^ 2)) z * (u z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    hI4.integral_prod_right
  have hK4 : Integrable (fun θ : ℝ => ∫ z in Work.Spaces.Iz,
        deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z) z * (u z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    hI5.integral_prod_right
  have hθlin : (∫ θ in Work.Spaces.Iθ, (α ^ 2 * (∫ z in Work.Spaces.Iz,
              W z * (Work.Spaces.w z) ^ 2 * z ^ 2 * (Work.Spaces.pz u z θ) ^ 2)
          + (∫ z in Work.Spaces.Iz, W z * (Work.Spaces.w z) ^ 2
              * (Work.Elliptic.Lzero u z θ * u z θ))
          - (α ^ 2 / 2) * (∫ z in Work.Spaces.Iz,
              deriv (deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z ^ 2)) z
                * (u z θ) ^ 2)
          + (α * (5 + α) / 2) * (∫ z in Work.Spaces.Iz,
              deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z) z * (u z θ) ^ 2)))
      = α ^ 2 * (∫ θ in Work.Spaces.Iθ, ∫ z in Work.Spaces.Iz,
            W z * (Work.Spaces.w z) ^ 2 * z ^ 2 * (Work.Spaces.pz u z θ) ^ 2)
        + (∫ θ in Work.Spaces.Iθ, ∫ z in Work.Spaces.Iz, W z * (Work.Spaces.w z) ^ 2
            * (Work.Elliptic.Lzero u z θ * u z θ))
        - (α ^ 2 / 2) * (∫ θ in Work.Spaces.Iθ, ∫ z in Work.Spaces.Iz,
            deriv (deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z ^ 2)) z
              * (u z θ) ^ 2)
        + ((α * (5 + α)) / 2) * (∫ θ in Work.Spaces.Iθ, ∫ z in Work.Spaces.Iz,
            deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z) z * (u z θ) ^ 2) := by
    have hA : Integrable (fun θ : ℝ => α ^ 2 * (∫ z in Work.Spaces.Iz,
        W z * (Work.Spaces.w z) ^ 2 * z ^ 2 * (Work.Spaces.pz u z θ) ^ 2))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hK1.const_mul _
    have hB : Integrable (fun θ : ℝ => α ^ 2 * (∫ z in Work.Spaces.Iz,
        W z * (Work.Spaces.w z) ^ 2 * z ^ 2 * (Work.Spaces.pz u z θ) ^ 2)
          + (∫ z in Work.Spaces.Iz, W z * (Work.Spaces.w z) ^ 2
              * (Work.Elliptic.Lzero u z θ * u z θ)))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hA.add hK2
    have hC : Integrable (fun θ : ℝ => (α ^ 2 / 2) * (∫ z in Work.Spaces.Iz,
        deriv (deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z ^ 2)) z * (u z θ) ^ 2))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hK3.const_mul _
    have hD : Integrable (fun θ : ℝ => (α * (5 + α) / 2) * (∫ z in Work.Spaces.Iz,
        deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z) z * (u z θ) ^ 2))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hK4.const_mul _
    have hE : Integrable (fun θ : ℝ => α ^ 2 * (∫ z in Work.Spaces.Iz,
        W z * (Work.Spaces.w z) ^ 2 * z ^ 2 * (Work.Spaces.pz u z θ) ^ 2)
          + (∫ z in Work.Spaces.Iz, W z * (Work.Spaces.w z) ^ 2
              * (Work.Elliptic.Lzero u z θ * u z θ))
          - (α ^ 2 / 2) * (∫ z in Work.Spaces.Iz,
              deriv (deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z ^ 2)) z * (u z θ) ^ 2))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hB.sub hC
    rw [MeasureTheory.integral_add hE hD, MeasureTheory.integral_sub hB hC,
      MeasureTheory.integral_add hA hK2,
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul]
  rw [hT1, hT2, hT3, hT4, hL, hθeq, hθlin]

end Work.FTS.EllipticEst.H2W.Ae

