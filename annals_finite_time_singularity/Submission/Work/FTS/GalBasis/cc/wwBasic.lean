import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.GalBasis.cc.ShrinkDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.ThetaU.OpenSliceAux.DthIter_DzIter_eqOn_of_isOpen
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.GalBasis.cc.sin_pow_int_general
import Submission.Work.FTS.GalBasis.cc.layer_pow_int_lt_one
import Submission.Work.FTS.GalBasis.cc.cs_interval

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis.cc

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## 1. Elementary angular facts -/

/-- Jordan's inequality in the shape used below: `4θ/π ≤ sin (2θ)` for `θ ∈ [0,π/4]`. -/
lemma four_div_pi_mul_le_sin_two {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ Real.pi / 4) :
    4 / Real.pi * θ ≤ Real.sin (2 * θ) := by
  have h := Real.mul_le_sin (x := 2 * θ) (by linarith) (by linarith)
  have h2 : 2 / Real.pi * (2 * θ) = 4 / Real.pi * θ := by ring
  linarith [h, h2]

lemma sin_two_pos {θ : ℝ} (h0 : 0 < θ) (h1 : θ < Real.pi / 2) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)

/-- `(s^{-γ/2})^2 = s^{-γ}` for `s > 0`. -/
lemma sq_rpow_neg_half {s γ : ℝ} (hs : 0 < s) : (s ^ (-(γ / 2))) ^ 2 = s ^ (-γ) := by
  rw [← Real.rpow_two, ← Real.rpow_mul (le_of_lt hs)]
  congr 1
  ring

/-- `(s^{(γ-2)/2})^2 = s^{γ-2}` for `s > 0`. -/
lemma sq_rpow_half {s γ : ℝ} (hs : 0 < s) : (s ^ ((γ - 2) / 2)) ^ 2 = s ^ (γ - 2) := by
  rw [← Real.rpow_two, ← Real.rpow_mul (le_of_lt hs)]
  congr 1
  ring

/-- `s^{-γ/2} · s^{(γ-2)/2} = s⁻¹` for `s > 0`. -/
lemma rpow_neg_half_mul {s γ : ℝ} (hs : 0 < s) :
    s ^ (-(γ / 2)) * s ^ ((γ - 2) / 2) = s⁻¹ := by
  rw [← Real.rpow_add hs]
  congr 1
  rw [show -(γ / 2) + (γ - 2) / 2 = -1 by ring, Real.rpow_neg_one]

/-- `∫_t^{2t} sin(2θ)^{-γ} θ^{γ-1} dθ ≤ (π/4)^γ` for `γ ≥ 0` and `2t ≤ π/4`. -/
lemma layer_int_pow_le {γ t : ℝ} (hγ0 : 0 ≤ γ) (ht : 0 < t) (ht2 : 2 * t ≤ Real.pi / 4) :
    ∫ θ in t..(2 * t), (Real.sin (2 * θ)) ^ (-γ) * θ ^ (γ - 1) ≤ (Real.pi / 4) ^ γ := by
  have ht_le : t ≤ 2 * t := by linarith
  have hspos : ∀ θ ∈ Set.Icc t (2 * t), 0 < Real.sin (2 * θ) := fun θ hθ =>
    sin_two_pos (by linarith [hθ.1]) (by linarith [hθ.2, ht2, Real.pi_pos])
  have hpt : ∀ θ ∈ Set.Icc t (2 * t),
      (Real.sin (2 * θ)) ^ (-γ) * θ ^ (γ - 1) ≤ (Real.pi / 4) ^ γ * t⁻¹ := by
    intro θ hθ
    have hθ0 : 0 < θ := by linarith [hθ.1]
    have hθπ : θ ≤ Real.pi / 4 := by linarith [hθ.2, ht2]
    have hs : 0 < Real.sin (2 * θ) := hspos θ hθ
    have hkey : (Real.sin (2 * θ)) ^ (-γ) * θ ^ (γ - 1)
        = (θ / Real.sin (2 * θ)) ^ γ * θ⁻¹ := by
      have e1 : (Real.sin (2 * θ)) ^ (-γ) = ((Real.sin (2 * θ)) ^ γ)⁻¹ :=
        Real.rpow_neg (le_of_lt hs) γ
      have e2 : θ ^ (γ - 1) = θ ^ γ * θ⁻¹ := by
        rw [Real.rpow_sub hθ0 γ 1, Real.rpow_one, div_eq_mul_inv]
      have e3 : (θ / Real.sin (2 * θ)) ^ γ = θ ^ γ * ((Real.sin (2 * θ)) ^ γ)⁻¹ := by
        rw [Real.div_rpow hθ0.le (le_of_lt hs), div_eq_mul_inv]
      rw [e1, e2, e3]; ring
    have hle : θ / Real.sin (2 * θ) ≤ Real.pi / 4 := by
      rw [div_le_iff₀ hs]
      have h4 := mul_le_mul_of_nonneg_left (four_div_pi_mul_le_sin_two hθ0.le hθπ)
        (by positivity : (0 : ℝ) ≤ Real.pi / 4)
      have h5 : Real.pi / 4 * (4 / Real.pi * θ) = θ := by
        field_simp
      rw [h5] at h4
      exact h4
    have hpow : (θ / Real.sin (2 * θ)) ^ γ ≤ (Real.pi / 4) ^ γ :=
      Real.rpow_le_rpow (by positivity) hle hγ0
    have hinv : θ⁻¹ ≤ t⁻¹ := inv_anti₀ ht hθ.1
    rw [hkey]
    exact mul_le_mul hpow hinv (by positivity) (Real.rpow_nonneg (by positivity) γ)
  have hcont1 : ContinuousOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-γ) * θ ^ (γ - 1)) (Set.uIcc t (2 * t)) := by
    rw [Set.uIcc_of_le ht_le]
    refine ContinuousOn.mul ?_ ?_
    · refine ContinuousOn.rpow_const
        ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn) ?_
      intro θ hθ; left; exact ne_of_gt (hspos θ hθ)
    · refine ContinuousOn.rpow_const continuousOn_id ?_
      intro θ hθ; left; exact ne_of_gt (by linarith [hθ.1])
  have hcont2 : ContinuousOn (fun _ : ℝ => (Real.pi / 4) ^ γ * t⁻¹) (Set.uIcc t (2 * t)) :=
    continuousOn_const
  have hmono := intervalIntegral.integral_mono_on ht_le (hcont1.intervalIntegrable)
    (hcont2.intervalIntegrable (μ := volume)) hpt
  have hval : ∫ _θ in t..(2 * t), (Real.pi / 4) ^ γ * t⁻¹ = (Real.pi / 4) ^ γ := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    have h1 : (2 * t - t) * t⁻¹ = 1 := by
      rw [show 2 * t - t = t by ring, mul_inv_cancel₀ (ne_of_gt ht)]
    calc (2 * t - t) * ((Real.pi / 4) ^ γ * t⁻¹)
        = (Real.pi / 4) ^ γ * ((2 * t - t) * t⁻¹) := by ring
      _ = (Real.pi / 4) ^ γ := by rw [h1, mul_one]
  rw [hval] at hmono
  exact hmono

/-! ## 2. The derivative of a `θ`-slice of `D_z^b f` -/

/-- On the open quadrant, `∂_θ (D_z^b f) = mixed b 1 f / sin(2θ)`. -/
lemma pth_dzIter_slice {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen f) {b : ℕ}
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.pth (Work.Spaces.DzIter b f) z θ
      = Work.Spaces.mixed b 1 f z θ / Real.sin (2 * θ) := by
  have hcomm := Work.FTS.EllipticEst.ThetaU.OpenSliceAux.DthIter_DzIter_eqOn_of_isOpen
    Work.FTS.EllipticEst.isOpen_Q0
    ((Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp hsm) b 1
    (show (z, θ) ∈ Work.FTS.EllipticEst.Q0 from ⟨hz, hθ⟩)
  have h2 : Work.Spaces.Dth (Work.Spaces.DzIter b f) z θ = Work.Spaces.mixed b 1 f z θ := by
    have h := hcomm
    simp only [Function.uncurry_def, Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero] at h
    exact h
  have h3 : Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DzIter b f) z θ
      = Work.Spaces.mixed b 1 f z θ := by
    simpa only [Work.Spaces.Dth] using h2
  rw [eq_div_iff (ne_of_gt (sin_two_pos hθ.1 hθ.2))]
  linarith [h3]

/-- The `θ`-slice of `D_z^b f` is differentiable with the expected derivative. -/
lemma hasDerivAt_dzIter_slice {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    {b : ℕ} {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    HasDerivAt (fun θ' => Work.Spaces.DzIter b f z θ')
      (Work.Spaces.mixed b 1 f z θ / Real.sin (2 * θ)) θ := by
  have hC : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.DzIter b f)) Work.FTS.EllipticEst.Q0 :=
    Work.FTS.LocData.contDiffOn_DzIter Work.FTS.EllipticEst.isOpen_Q0 hsm b
  have hslice : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun θ' => Work.Spaces.DzIter b f z θ') (Set.Ioo 0 (π / 2)) :=
    Work.FTS.LocData.contDiffOn_slice_θ hC (show z ∈ Set.Ioi (0 : ℝ) from hz)
  have hdiff : DifferentiableAt ℝ (fun θ' => Work.Spaces.DzIter b f z θ') θ :=
    (hslice.differentiableOn Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
      (isOpen_Ioo.mem_nhds hθ)
  rw [← pth_dzIter_slice hsm hz hθ]
  exact hdiff.hasDerivAt

/-! ## 3. Extracting the slice from its derivative -/

/-- **FTC extraction.**  If `G` is differentiable on `(0,π/2)` with derivative `G'`,
continuous there and tends to `0` at `0⁺`, then `|G θ'| ≤ ∫_0^{θ'} |G'|`. -/
lemma abs_le_integral_abs_deriv {G G' : ℝ → ℝ} {θ' : ℝ}
    (hθ' : θ' ∈ Set.Ioo 0 (π / 2))
    (hderiv : ∀ θ ∈ Set.Ioo 0 (π / 2), HasDerivAt G (G' θ) θ)
    (hcont : ContinuousOn G (Set.Ioo 0 (π / 2)))
    (htend : Tendsto G (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hint : IntervalIntegrable G' volume 0 θ') :
    |G θ'| ≤ ∫ θ in (0 : ℝ)..θ', |G' θ| := by
  set I := ∫ θ in (0 : ℝ)..θ', |G' θ| with hI
  have habs : IntervalIntegrable (fun θ => |G' θ|) volume 0 θ' := hint.abs
  have hkey : |G θ'| - I ≤ 0 := by
    have hge : ∀ᶠ ε in 𝓝[>] (0 : ℝ), -|G ε| ≤ -(|G θ'| - I) := by
      filter_upwards [Ioo_mem_nhdsGT hθ'.1] with ε hε
      obtain ⟨hε0, hεθ⟩ := hε
      have hFTC : ∫ x in ε..θ', G' x = G θ' - G ε := by
        refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (le_of_lt hεθ) ?_ ?_ ?_
        · exact hcont.mono (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2, hθ'.2]⟩)
        · intro x hx
          exact hderiv x ⟨by linarith [hx.1], by linarith [hx.2, hθ'.2]⟩
        · exact hint.mono_set (by
            rw [uIcc_of_le (le_of_lt hεθ), uIcc_of_le hθ'.1.le]
            exact Set.Icc_subset_Icc hε0.le le_rfl)
      have h2 : |G θ' - G ε| ≤ ∫ x in ε..θ', |G' x| := by
        rw [← hFTC]
        exact intervalIntegral.abs_integral_le_integral_abs (le_of_lt hεθ)
      have h3 : ∫ x in ε..θ', |G' x| ≤ I := by
        rw [hI]
        exact intervalIntegral.integral_mono_interval hε0.le (le_of_lt hεθ) le_rfl
          (Filter.Eventually.of_forall fun x => abs_nonneg _) habs
      have h4 : |G θ'| ≤ |G ε| + I := by
        have h5 := abs_sub_abs_le_abs_sub (G θ') (G ε)
        linarith [h2, h3]
      linarith [h4]
    have h1 : Tendsto (fun ε => |G ε|) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using htend.abs
    have hlim : Tendsto (fun ε => -|G ε|) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using h1.neg
    have := le_of_tendsto hlim hge
    linarith
  linarith

/-! ## 4. Integrability of the Hardy weight `sin(2θ)^{γ-2}` -/

/-- `sin(2θ)^{γ-2}` is integrable on `(0,b]` for `γ > 1`, `b ≤ π/4`. -/
lemma integrableOn_sin_pow_sub_two {γ b : ℝ} (h1 : 1 < γ) (hb : b ≤ Real.pi / 4) :
    IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (γ - 2)) (Set.Ioc 0 b) := by
  by_cases h2 : 2 ≤ γ
  · have hcont : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (γ - 2)) (Set.Ioc 0 b) := by
      refine ContinuousOn.rpow_const
        ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn) ?_
      intro θ hθ; right; linarith
    have hbnd : ∀ᵐ θ ∂(volume.restrict (Set.Ioc 0 b)),
        ‖(Real.sin (2 * θ)) ^ (γ - 2)‖ ≤ 1 := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with θ hθ
      have hs0 : 0 < Real.sin (2 * θ) :=
        sin_two_pos hθ.1 (by linarith [hθ.2, hb, Real.pi_pos])
      rw [Real.norm_eq_abs, abs_of_nonneg (le_of_lt (Real.rpow_pos_of_pos hs0 _))]
      exact Real.rpow_le_one hs0.le (Real.sin_le_one _) (by linarith)
    exact IntegrableOn.of_bound (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top)
      (hcont.aestronglyMeasurable measurableSet_Ioc) 1 hbnd
  · have hp1 : -1 < γ - 2 := by linarith
    have hp0 : γ - 2 ≤ 0 := by linarith
    exact (Work.Spaces.sin_two_rpow (γ - 2) hp1 hp0).1.mono_set (by
      intro θ hθ
      exact ⟨le_of_lt hθ.1, by linarith [hθ.2, hb, Real.pi_pos]⟩)

/-! ## 5. The sharp per-slice bound -/

/-- **Sharp slice bound.** -/
theorem slice_sharp {γ : ℝ} (hγ : 1 < γ) {G M : ℝ → ℝ} {θ' : ℝ}
    (hθ'0 : 0 < θ') (hθ'π : θ' ≤ Real.pi / 4)
    (hderiv : ∀ θ ∈ Set.Ioo 0 (π / 2), HasDerivAt G (M θ / Real.sin (2 * θ)) θ)
    (hcont : ContinuousOn G (Set.Ioo 0 (π / 2)))
    (htend : Tendsto G (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hint : IntervalIntegrable (fun θ => M θ / Real.sin (2 * θ)) volume 0 θ')
    (hInt1 : IntegrableOn (fun θ => M θ ^ 2 * (Real.sin (2 * θ)) ^ (-γ)) (Set.Ioc 0 θ'))
    (hInt2 : IntegrableOn (fun θ => (Real.sin (2 * θ)) ^ (γ - 2)) (Set.Ioc 0 θ')) :
    G θ' ^ 2 ≤ (∫ θ in (0 : ℝ)..θ', M θ ^ 2 * (Real.sin (2 * θ)) ^ (-γ))
      * (max 1 (2 ^ (γ - 2)) * θ' ^ (γ - 1) / (γ - 1)) := by
  have hθ'mem : θ' ∈ Set.Ioo 0 (π / 2) := ⟨hθ'0, by linarith [hθ'π, Real.pi_pos]⟩
  have h1 : |G θ'| ≤ ∫ θ in (0 : ℝ)..θ', |M θ / Real.sin (2 * θ)| :=
    abs_le_integral_abs_deriv hθ'mem hderiv hcont htend hint
  have hAnn : 0 ≤ ∫ θ in (0 : ℝ)..θ', |M θ / Real.sin (2 * θ)| :=
    intervalIntegral.integral_nonneg hθ'0.le (fun θ _ => abs_nonneg _)
  have hsin : ∀ x ∈ Set.Ioc (0 : ℝ) θ', 0 < Real.sin (2 * x) := fun x hx =>
    sin_two_pos hx.1 (by linarith [hx.2, hθ'π, Real.pi_pos])
  have hcs : (∫ θ in (0 : ℝ)..θ', |M θ / Real.sin (2 * θ)|) ^ 2
      ≤ (∫ θ in (0 : ℝ)..θ', M θ ^ 2 * (Real.sin (2 * θ)) ^ (-γ))
        * (∫ θ in (0 : ℝ)..θ', (Real.sin (2 * θ)) ^ (γ - 2)) := by
    have hu : IntegrableOn (fun x => (|M x| * (Real.sin (2 * x)) ^ (-(γ / 2))) ^ 2)
        (Set.Ioc 0 θ') := by
      refine IntegrableOn.congr_fun hInt1 (fun x hx => ?_) measurableSet_Ioc
      rw [mul_pow, sq_abs, sq_rpow_neg_half (hsin x hx)]
    have hv : IntegrableOn (fun x => ((Real.sin (2 * x)) ^ ((γ - 2) / 2)) ^ 2)
        (Set.Ioc 0 θ') := by
      refine IntegrableOn.congr_fun hInt2 (fun x hx => ?_) measurableSet_Ioc
      rw [sq_rpow_half (hsin x hx)]
    have hmain := cs_interval hθ'0.le hu hv
    have e1 : (∫ x in (0 : ℝ)..θ', (|M x| * (Real.sin (2 * x)) ^ (-(γ / 2)))
          * ((Real.sin (2 * x)) ^ ((γ - 2) / 2)))
        = ∫ x in (0 : ℝ)..θ', |M x / Real.sin (2 * x)| := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards with x hx
      rw [uIoc_of_le hθ'0.le] at hx
      have hs := hsin x hx
      rw [mul_assoc, rpow_neg_half_mul hs, abs_div, abs_of_pos hs, div_eq_mul_inv]
    have e2 : (∫ x in (0 : ℝ)..θ', (|M x| * (Real.sin (2 * x)) ^ (-(γ / 2))) ^ 2)
        = ∫ x in (0 : ℝ)..θ', M x ^ 2 * (Real.sin (2 * x)) ^ (-γ) := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards with x hx
      rw [uIoc_of_le hθ'0.le] at hx
      rw [mul_pow, sq_abs, sq_rpow_neg_half (hsin x hx)]
    have e3 : (∫ x in (0 : ℝ)..θ', ((Real.sin (2 * x)) ^ ((γ - 2) / 2)) ^ 2)
        = ∫ x in (0 : ℝ)..θ', (Real.sin (2 * x)) ^ (γ - 2) := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards with x hx
      rw [uIoc_of_le hθ'0.le] at hx
      rw [sq_rpow_half (hsin x hx)]
    rw [e1, e2, e3] at hmain
    exact hmain
  have h2 : ∫ θ in (0 : ℝ)..θ', (Real.sin (2 * θ)) ^ (γ - 2)
      ≤ max 1 (2 ^ (γ - 2)) * θ' ^ (γ - 1) / (γ - 1) :=
    sin_pow_int_general hγ hθ'0.le hθ'π
  have h3 : 0 ≤ ∫ θ in (0 : ℝ)..θ', M θ ^ 2 * (Real.sin (2 * θ)) ^ (-γ) :=
    intervalIntegral.integral_nonneg hθ'0.le (fun θ hθ =>
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi
        (by linarith [hθ.1])
        (by linarith [hθ.2, hθ'π, Real.pi_pos])) _))
  calc G θ' ^ 2 = |G θ'| ^ 2 := by rw [sq_abs]
    _ = |G θ'| * |G θ'| := by ring
    _ ≤ (∫ θ in (0 : ℝ)..θ', |M θ / Real.sin (2 * θ)|)
          * (∫ θ in (0 : ℝ)..θ', |M θ / Real.sin (2 * θ)|) :=
        mul_self_le_mul_self (abs_nonneg _) h1
    _ = (∫ θ in (0 : ℝ)..θ', |M θ / Real.sin (2 * θ)|) ^ 2 := by ring
    _ ≤ _ := hcs
    _ ≤ (∫ θ in (0 : ℝ)..θ', M θ ^ 2 * (Real.sin (2 * θ)) ^ (-γ))
          * (max 1 (2 ^ (γ - 2)) * θ' ^ (γ - 1) / (γ - 1)) :=
        mul_le_mul_of_nonneg_left h2 h3

/-- `IntegrableOn` on `Ioc` upgrades to `IntervalIntegrable`. -/
lemma intervalIntegrable_of_integrableOn_Ioc {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : IntegrableOn f (Set.Ioc a b)) : IntervalIntegrable f volume a b := by
  refine ⟨h, ?_⟩
  rw [Set.Ioc_eq_empty (not_lt.mpr hab)]
  exact integrableOn_empty

end Work.FTS.GalBasis.cc
