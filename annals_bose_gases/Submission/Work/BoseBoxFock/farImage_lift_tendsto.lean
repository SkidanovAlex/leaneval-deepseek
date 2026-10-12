import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.aliasImageDefs
import Submission.Work.BoseBoxFock.farImage_convolution_lintegral_le
import Submission.Work.BoseBoxFock.farK0_summable_lattice_inv_fourth
import Submission.Work.BoseBoxFock.lbfDiffKernelComplex
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.farImage_lift_tendsto` — the `ε → 0⁺` limit of the far-image sum

For `g` smooth with `tsupport g ⊆ closedBall 0 (ℓ/2)` and the smooth lift
`L_ε x = √(‖g x‖² + ε²) − ε` of the modulus, the far-image sum

    Σ_{‖latVec m‖ ≥ √2} ∫_u 𝒢_ε(u) · imgW ℓ m u       (𝒢_ε = aliasKernel of the ℂ-lift of `L_ε`)

converges, as `ε → 0⁺`, to the same sum computed with the modulus `x ↦ ‖g x‖`.  (Note
`L_0 = ‖g‖`, so the limit is the `ε = 0` value of the family, and the statement is just the
right-continuity at `0` of the family.)

## Route

Write `h = ‖g‖`, `h_ε = L_ε`, `A u = ∫_x h x h (x−u)`, `A_ε u = ∫_x h_ε x h_ε (x−u)` (the honest
autocorrelations; `aliasKernel` of the ℂ-lift of a real `f` is `∫_x f x f (x−u)`, an
unconditional identity).  Then, for `0 ≤ ε`,

* `0 ≤ h_ε ≤ h`, `h − h_ε ≤ ε`, `h_ε x = 0` wherever `h x = 0`,
* `0 ≤ A_ε ≤ A`, `|A − A_ε| ≤ 2 ε ∫h` (uniformly in `u`), `A u = 0` for `‖u‖ > ℓ`,
  `A u ≤ C ‖g‖_∞ ∫h`,
* `∫⁻_u A u ≤ (∫h)²` (Tonelli + translation invariance: `farImage_convolution_lintegral_le`),
* on `‖latVec m‖ ≥ √2` and `‖u‖ ≤ ℓ`, `imgW ℓ m u ≤ (ℓ⁴(‖latVec m‖−1)⁴)⁻¹`, whose `m`-sum is
  summable (`farK0_summable_lattice_inv_fourth`).

Tannery's theorem (`tendsto_tsum_of_dominated_convergence`) applied to the summands
`term ε m`, with the summable majorant `(ℓ⁴(‖latVec m‖−1)⁴)⁻¹ ∫h²`, reduces the statement to the
per-`m` convergence, which is the dominated-convergence theorem in `u` (the dominating function
being a constant on the ball `‖u‖ ≤ ℓ`, where `imgW` is bounded and `A_ε ≤ A`).
-/

noncomputable section

open MeasureTheory Filter
open scoped Real BigOperators ENNReal

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 8000000

/-! ## 1. The autocorrelation of the ℂ-lift of a real function -/

/-- `aliasKernel` of the ℂ-lift of a real function `f` is the honest autocorrelation
`∫_x f x · f (x − u)`.  No integrability hypothesis is needed (both sides read `0` in the
non-integrable case, by `integral_ofReal`). -/
theorem aliasKernel_lift_eq_integral (f : E3 → ℝ) (u : E3) :
    aliasKernel (fun x : E3 => (f x : ℂ)) u = ∫ x : E3, f x * f (x - u) := by
  rw [aliasKernel, autocorr]
  have hfun : (fun x : E3 => ((f x : ℝ) : ℂ) * (starRingEnd ℂ) (((f (x - u) : ℝ)) : ℂ))
      = fun x : E3 => ((f x * f (x - u) : ℝ) : ℂ) := by
    funext x
    rw [Complex.conj_ofReal, ← Complex.ofReal_mul]
  rw [hfun]
  have h2 : (∫ x : E3, ((f x * f (x - u) : ℝ) : ℂ))
      = (((∫ x : E3, f x * f (x - u)) : ℝ) : ℂ) := integral_ofReal
  rw [h2, Complex.ofReal_re]

/-! ## 2. Measurability of the autocorrelation (Fubini/parametric-integral measurability) -/

/-- `u ↦ aliasKernel f u` is strongly measurable for continuous `f` (the parametrised Bochner
integral of a jointly continuous function). -/
theorem stronglyMeasurable_aliasKernel {f : E3 → ℂ} (hf : Continuous f) :
    StronglyMeasurable (fun u : E3 => aliasKernel f u) := by
  have hjoint : StronglyMeasurable (fun p : E3 × E3 => f p.2 * starRingEnd ℂ (f (p.2 - p.1))) := by
    apply Continuous.stronglyMeasurable
    have h1 : Continuous (fun p : E3 × E3 => f p.2) := hf.comp continuous_snd
    have h2 : Continuous (fun p : E3 × E3 => f (p.2 - p.1)) :=
      hf.comp (continuous_snd.sub continuous_fst)
    exact h1.mul (continuous_star.comp h2)
  have h := hjoint.integral_prod_right' (ν := (volume : Measure E3))
  have h4 : (fun u : E3 => aliasKernel f u)
      = fun u : E3 => Complex.re (∫ x : E3, f x * starRingEnd ℂ (f (x - u))) := by
    funext u
    rw [aliasKernel, autocorr]
  rw [h4]
  exact Complex.continuous_re.comp_stronglyMeasurable h

/-! ## 3. The lattice geometry: the kernel bound and the summability of the decay -/

lemma latVec_zero_norm : ‖latVec (0 : Fin 3 → ℤ)‖ = 0 := by
  rw [EuclideanSpace.norm_eq]
  simp [latVec]

/-- **The pointwise far-image kernel bound.**  For `√2 ≤ ‖latVec m‖` and `‖u‖ ≤ ℓ` the image
weight `imgW ℓ m u = (‖u − ℓ • latVec m‖⁴)⁻¹` is at most `(ℓ⁴(‖latVec m‖−1)⁴)⁻¹`
(reverse triangle inequality; the `m = 0` branch is excluded automatically). -/
lemma imgW_le_of_sqrtTwo_le {ℓ : ℝ} (hℓ : 0 < ℓ) {m : Fin 3 → ℤ}
    (hm : Real.sqrt 2 ≤ ‖latVec m‖) {u : E3} (hu : ‖u‖ ≤ ℓ) :
    imgW ℓ m u ≤ (ℓ ^ 4 * (‖latVec m‖ - 1) ^ 4)⁻¹ := by
  have hmne : m ≠ 0 := by
    intro h
    rw [h, latVec_zero_norm] at hm
    linarith [Real.one_lt_sqrt_two]
  rw [imgW_ne_zero hmne]
  have hbpos : 0 < ‖latVec m‖ - 1 := by linarith [Real.one_lt_sqrt_two]
  have hkey : ℓ * (‖latVec m‖ - 1) ≤ ‖u - ℓ • latVec m‖ := by
    have h2 := norm_sub_le u (u - ℓ • latVec m)
    rw [sub_sub_cancel] at h2
    have h3 : ‖ℓ • latVec m‖ = ℓ * ‖latVec m‖ := by
      rw [norm_smul, Real.norm_of_nonneg hℓ.le]
    rw [h3] at h2
    nlinarith [h2, hu]
  have hpos : (0 : ℝ) < ℓ * (‖latVec m‖ - 1) := by positivity
  have h4 : (ℓ * (‖latVec m‖ - 1)) ^ 4 ≤ ‖u - ℓ • latVec m‖ ^ 4 :=
    pow_le_pow_left₀ hpos.le hkey 4
  have h5 : (‖u - ℓ • latVec m‖ ^ 4)⁻¹ ≤ ((ℓ * (‖latVec m‖ - 1)) ^ 4)⁻¹ :=
    (inv_le_inv₀ (pow_pos (lt_of_lt_of_le hpos hkey) 4) (pow_pos hpos 4)).mpr h4
  rw [mul_pow] at h5
  exact h5

/-- On the region `‖v‖ ≥ √2` one has `‖v‖/4 ≤ ‖v‖ − 1`. -/
lemma quarter_le_sub_one : ∀ v : ℝ, Real.sqrt 2 ≤ v → v / 4 ≤ v - 1 := by
  intro v hv
  have h1 : (1 : ℝ) / Real.sqrt 2 ≤ 3 / 4 := by
    rw [div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num))]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2, hv]
  have h2 : (1 : ℝ) - 1 / Real.sqrt 2 ≥ 1 / 4 := by linarith
  have hv0 : 0 < v := by linarith [Real.one_lt_sqrt_two]
  have h3 : 1 / v ≤ 1 / Real.sqrt 2 := one_div_le_one_div_of_le (by positivity) hv
  have h4 : (1 : ℝ) - 1 / v ≥ 1 - 1 / Real.sqrt 2 := by linarith
  have h5 : v * (1 - 1 / v) = v - 1 := by field_simp
  rw [← h5]
  nlinarith [mul_le_mul_of_nonneg_left h4 hv0.le]

/-- **Summability of the far-image lattice decay**, in the normal form produced by
`imgW_le_of_sqrtTwo_le`. -/
lemma summable_latVec_decay {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Summable (fun m : Fin 3 → ℤ =>
      if Real.sqrt 2 ≤ ‖latVec m‖
        then (ℓ ^ 4 * (‖latVec m‖ - 1) ^ 4)⁻¹ else 0) := by
  have hbase : Summable (fun m : Fin 3 → ℤ =>
      (256 * (ℓ ^ 4)⁻¹) * (‖latVec m‖ ^ 4)⁻¹) :=
    farK0_summable_lattice_inv_fourth.mul_left _
  refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_) hbase
  · split_ifs
    · positivity
    · exact le_refl 0
  · by_cases hm : Real.sqrt 2 ≤ ‖latVec m‖
    · rw [if_pos hm]
      have hv0 : 0 < ‖latVec m‖ := by
        linarith [Real.one_lt_sqrt_two, norm_nonneg (latVec m)]
      have hb0 : (0 : ℝ) < ‖latVec m‖ - 1 := by linarith [Real.one_lt_sqrt_two]
      have h1 : (‖latVec m‖ / 4) ^ 4 ≤ (‖latVec m‖ - 1) ^ 4 :=
        pow_le_pow_left₀ (by positivity) (quarter_le_sub_one _ hm) 4
      have h2 : ((‖latVec m‖ - 1) ^ 4)⁻¹ ≤ ((‖latVec m‖ / 4) ^ 4)⁻¹ :=
        (inv_le_inv₀ (pow_pos hb0 4) (pow_pos (div_pos hv0 (by norm_num)) 4)).mpr h1
      have h3 : ((‖latVec m‖ / 4) ^ 4)⁻¹ = 256 * ((‖latVec m‖ ^ 4))⁻¹ := by
        rw [div_pow, inv_div]
        norm_num
        ring
      calc (ℓ ^ 4 * (‖latVec m‖ - 1) ^ 4)⁻¹
          = (ℓ ^ 4)⁻¹ * ((‖latVec m‖ - 1) ^ 4)⁻¹ := by rw [mul_inv]
        _ ≤ (ℓ ^ 4)⁻¹ * ((‖latVec m‖ / 4) ^ 4)⁻¹ :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = (ℓ ^ 4)⁻¹ * (256 * ((‖latVec m‖ ^ 4))⁻¹) := by rw [h3]
        _ = (256 * (ℓ ^ 4)⁻¹) * (‖latVec m‖ ^ 4)⁻¹ := by ring
    · rw [if_neg hm]
      positivity

/-! ## 4. The `L¹`-Tonelli bound for the autocorrelation -/

/-- The autocorrelation mass: `∫⁻_u ofReal (∫_x f x f (x−u)) ≤ ofReal ((∫ f)²)` for nonnegative
continuous compactly supported `f` (Tonelli + translation invariance). -/
theorem lintegral_autoCorr_le {f : E3 → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hf0 : ∀ x, 0 ≤ f x) :
    (∫⁻ u, ENNReal.ofReal (∫ x, f x * f (x - u)))
      ≤ ENNReal.ofReal ((∫ x, f x) ^ 2) := by
  have hint : Integrable f := hf.integrable_of_hasCompactSupport hfc
  have key : ∀ u : E3, ENNReal.ofReal (∫ x, f x * f (x - u))
      ≤ ∫⁻ x, ENNReal.ofReal (f x) * ENNReal.ofReal (f (x - u)) := by
    intro u
    have hmeas : AEStronglyMeasurable (fun x : E3 => f x * f (x - u)) volume :=
      (hf.mul (hf.comp (continuous_id.sub continuous_const))).aestronglyMeasurable
    have hnn : 0 ≤ᵐ[(volume : Measure E3)] (fun x : E3 => f x * f (x - u)) :=
      Filter.Eventually.of_forall fun x => mul_nonneg (hf0 x) (hf0 (x - u))
    rw [integral_eq_lintegral_of_nonneg_ae hnn hmeas]
    calc ENNReal.ofReal ((∫⁻ x, ENNReal.ofReal (f x * f (x - u))).toReal)
        ≤ ∫⁻ x, ENNReal.ofReal (f x * f (x - u)) := ENNReal.ofReal_toReal_le
      _ = ∫⁻ x, ENNReal.ofReal (f x) * ENNReal.ofReal (f (x - u)) :=
          lintegral_congr fun x => ENNReal.ofReal_mul (hf0 x)
  calc (∫⁻ u, ENNReal.ofReal (∫ x, f x * f (x - u)))
      ≤ ∫⁻ u, ∫⁻ x, ENNReal.ofReal (f x) * ENNReal.ofReal (f (x - u)) := lintegral_mono key
    _ ≤ ENNReal.ofReal (∫ x, f x) * ENNReal.ofReal (∫ x, f x) :=
        farImage_convolution_lintegral_le hf0 hf.measurable hint
    _ = ENNReal.ofReal ((∫ x, f x) ^ 2) := by
        rw [← ENNReal.ofReal_mul (integral_nonneg hf0)]
        ring_nf

/-! ## 5. Elementary facts about the autocorrelation of a compactly supported continuous `f` -/

/-- Integrability of the autocorrelation integrand `x ↦ f x · f (x − u)`. -/
lemma integrable_mul_sub_self {f : E3 → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (u : E3) : Integrable (fun x : E3 => f x * f (x - u)) := by
  have hcs : HasCompactSupport (fun x : E3 => f x * f (x - u)) :=
    HasCompactSupport.of_support_subset_isCompact hfc (by
      intro x hx
      by_contra hx'
      have hzero : f x = 0 := by
        by_contra hfne
        exact hx' (subset_tsupport f hfne)
      simp only [Function.mem_support] at hx
      exact hx (by simp [hzero]))
  exact (hf.mul (hf.comp (continuous_id.sub continuous_const))).integrable_of_hasCompactSupport hcs

/-- Monotonicity of the autocorrelation in the function. -/
lemma autoCorr_mono {f g : E3 → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (hgc : HasCompactSupport g) (hg0 : ∀ x, 0 ≤ g x)
    (hgf : ∀ x, g x ≤ f x) (u : E3) :
    (∫ x : E3, g x * g (x - u)) ≤ ∫ x : E3, f x * f (x - u) := by
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x =>
    mul_nonneg (hg0 x) (hg0 (x - u))) (integrable_mul_sub_self hf hfc u)
    (Filter.Eventually.of_forall fun x => ?_)
  exact mul_le_mul (hgf x) (hgf (x - u)) (hg0 (x - u)) (le_trans (hg0 x) (hgf x))

/-- The uniform Lipschitz estimate `|A_f − A_g| ≤ 2 ε ∫ f` when `0 ≤ g ≤ f` and `f − g ≤ ε`. -/
lemma autoCorr_diff_le {f g : E3 → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (hgc : HasCompactSupport g) (hg0 : ∀ x, 0 ≤ g x)
    (hgf : ∀ x, g x ≤ f x) {ε : ℝ} (hε0 : 0 ≤ ε) (hgap : ∀ x, f x - g x ≤ ε) (u : E3) :
    |(∫ x : E3, f x * f (x - u)) - ∫ x : E3, g x * g (x - u)| ≤ 2 * ε * ∫ x : E3, f x := by
  have hfu : Continuous (fun x : E3 => f (x - u)) :=
    hf.comp (continuous_id.sub continuous_const)
  have hfucs : HasCompactSupport (fun x : E3 => f (x - u)) :=
    hfc.comp_homeomorph (Homeomorph.subRight u)
  have hIf : Integrable (fun x : E3 => f x * f (x - u)) := integrable_mul_sub_self hf hfc u
  have hIg : Integrable (fun x : E3 => g x * g (x - u)) := integrable_mul_sub_self hg hgc u
  have hI1 : Integrable (fun x : E3 => f x * ε) :=
    (hf.mul continuous_const).integrable_of_hasCompactSupport (hfc.mul_right (f' := fun _ => ε))
  have hI2 : Integrable (fun x : E3 => ε * f (x - u)) :=
    (continuous_const.mul hfu).integrable_of_hasCompactSupport (hfucs.mul_left (f := fun _ => ε))
  have hbound : Integrable (fun x : E3 => f x * ε + ε * f (x - u)) := hI1.add hI2
  have hpt : ∀ x : E3, |f x * f (x - u) - g x * g (x - u)| ≤ f x * ε + ε * f (x - u) := by
    intro x
    have hfx : 0 ≤ f x := le_trans (hg0 x) (hgf x)
    have hfxu : 0 ≤ f (x - u) := le_trans (hg0 (x - u)) (hgf (x - u))
    have h1 : f x * f (x - u) - g x * g (x - u)
        = f x * (f (x - u) - g (x - u)) + (f x - g x) * g (x - u) := by ring
    have h2 : |f (x - u) - g (x - u)| ≤ ε := by
      rw [abs_le]
      exact ⟨by linarith [hg0 (x - u), hfxu, hgf (x - u), hε0], hgap (x - u)⟩
    have h3 : |f x - g x| ≤ ε := by
      rw [abs_le]
      exact ⟨by linarith [hg0 x, hfx, hgf x, hε0], hgap x⟩
    rw [h1]
    calc |f x * (f (x - u) - g (x - u)) + (f x - g x) * g (x - u)|
        ≤ |f x * (f (x - u) - g (x - u))| + |(f x - g x) * g (x - u)| := abs_add_le _ _
      _ = f x * |f (x - u) - g (x - u)| + |f x - g x| * g (x - u) := by
          rw [abs_mul, abs_mul, abs_of_nonneg hfx, abs_of_nonneg (hg0 (x - u))]
      _ ≤ f x * ε + ε * g (x - u) := by
          exact add_le_add (mul_le_mul_of_nonneg_left h2 hfx)
            (mul_le_mul_of_nonneg_right h3 (hg0 (x - u)))
      _ ≤ f x * ε + ε * f (x - u) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left (hgf (x - u)) hε0)
  calc |(∫ x : E3, f x * f (x - u)) - ∫ x : E3, g x * g (x - u)|
      = |∫ x : E3, (f x * f (x - u) - g x * g (x - u))| := by
        rw [integral_sub hIf hIg]
    _ ≤ ∫ x : E3, |f x * f (x - u) - g x * g (x - u)| := abs_integral_le_integral_abs
    _ ≤ ∫ x : E3, (f x * ε + ε * f (x - u)) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => abs_nonneg _) hbound
          (Filter.Eventually.of_forall hpt)
    _ = (∫ x : E3, f x * ε) + ∫ x : E3, ε * f (x - u) := by rw [integral_add hI1 hI2]
    _ = ε * (∫ x : E3, f x) + ε * (∫ x : E3, f x) := by
        rw [integral_mul_const, integral_const_mul, integral_sub_right_eq_self]
        ring
    _ = 2 * ε * ∫ x : E3, f x := by ring

/-- The autocorrelation is bounded by `(sup f) · ∫ f`. -/
lemma autoCorr_le_const {f : E3 → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hf0 : ∀ x, 0 ≤ f x) {C : ℝ} (hC : ∀ x, f x ≤ C) (u : E3) :
    (∫ x : E3, f x * f (x - u)) ≤ C * ∫ x : E3, f x := by
  have hfu : Continuous (fun x : E3 => f (x - u)) :=
    hf.comp (continuous_id.sub continuous_const)
  have hfucs : HasCompactSupport (fun x : E3 => f (x - u)) :=
    hfc.comp_homeomorph (Homeomorph.subRight u)
  have hIf : Integrable (fun x : E3 => f x * f (x - u)) := integrable_mul_sub_self hf hfc u
  have hI2 : Integrable (fun x : E3 => C * f (x - u)) :=
    (continuous_const.mul hfu).integrable_of_hasCompactSupport (hfucs.mul_left (f := fun _ => C))
  calc (∫ x : E3, f x * f (x - u))
      ≤ ∫ x : E3, C * f (x - u) :=
        integral_mono hIf hI2 fun x => mul_le_mul_of_nonneg_right (hC x) (hf0 (x - u))
    _ = C * ∫ x : E3, f (x - u) := integral_const_mul C _
    _ = C * ∫ x : E3, f x := by rw [integral_sub_right_eq_self]

/-- Measurability of the image weight. -/
lemma measurable_imgW (ℓ : ℝ) (m : Fin 3 → ℤ) : Measurable (fun u : E3 => imgW ℓ m u) := by
  by_cases hm : m = 0
  · simp only [hm, imgW_zero]
    exact measurable_const
  · simp only [imgW_ne_zero hm]
    have h1 : Measurable (fun u : E3 => ‖u - ℓ • latVec m‖) :=
      continuous_norm.measurable.comp (measurable_id.sub measurable_const)
    exact (h1.pow_const 4).inv

/-- The autocorrelation vanishes for `‖u‖ > ℓ` when `f` is supported in the ball of radius
`ℓ/2`. -/
lemma autoCorr_eq_zero_of_supp {ℓ : ℝ} {f : E3 → ℝ}
    (hfsupp : ∀ x, ℓ / 2 < ‖x‖ → f x = 0) {u : E3} (hu : ℓ < ‖u‖) :
    (∫ x : E3, f x * f (x - u)) = 0 := by
  have h0 : (fun x : E3 => f x * f (x - u)) = fun _ => (0 : ℝ) := by
    funext x
    by_cases hx : ‖x‖ ≤ ℓ / 2
    · by_cases hxu : ‖x - u‖ ≤ ℓ / 2
      · exfalso
        have h1 : ‖u‖ ≤ ‖x - u‖ + ‖x‖ := by
          have h2 : ‖u‖ = ‖(x - u) - x‖ := by
            rw [show (x - u) - x = -u by abel, norm_neg]
          rw [h2]
          exact norm_sub_le _ _
        linarith
      · rw [hfsupp (x - u) (not_le.mp hxu), mul_zero]
    · rw [hfsupp x (not_le.mp hx), zero_mul]
  rw [h0, integral_zero]

theorem farImage_lift_tendsto {ℓ : ℝ} (hℓ : 0 < ℓ)
    {g : EuclideanSpace ℝ (Fin 3) → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgsupp : tsupport g ⊆ Metric.closedBall 0 (ℓ / 2)) :
    Filter.Tendsto
      (fun ε : ℝ => ∑' m : Fin 3 → ℤ,
        (if Real.sqrt 2 ≤ ‖Work.BoseBoxFock.latVec m‖
          then ∫ u : EuclideanSpace ℝ (Fin 3),
                 Work.BoseBoxFock.aliasKernel (fun x : EuclideanSpace ℝ (Fin 3) =>
                     ((Real.sqrt (‖g x‖ ^ 2 + ε ^ 2) - ε : ℝ) : ℂ)) u *
                   Work.BoseBoxFock.imgW ℓ m u
          else 0))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (∑' m : Fin 3 → ℤ,
        (if Real.sqrt 2 ≤ ‖Work.BoseBoxFock.latVec m‖
          then ∫ u : EuclideanSpace ℝ (Fin 3),
                 Work.BoseBoxFock.aliasKernel
                   (fun x : EuclideanSpace ℝ (Fin 3) => ((‖g x‖ : ℝ) : ℂ)) u *
                   Work.BoseBoxFock.imgW ℓ m u
          else 0))) := by
  have hgcont : Continuous g := hg.continuous
  have hgc : HasCompactSupport g :=
    (isCompact_closedBall (0 : E3) (ℓ / 2)).of_isClosed_subset (isClosed_tsupport g) hgsupp
  set h : E3 → ℝ := fun x => ‖g x‖ with hh
  set hε : ℝ → E3 → ℝ := fun ε x => Real.sqrt (h x ^ 2 + ε ^ 2) - ε with hhε
  set A : E3 → ℝ := fun u => ∫ x : E3, h x * h (x - u) with hA
  set Aε : ℝ → E3 → ℝ := fun ε u => ∫ x : E3, hε ε x * hε ε (x - u) with hAε
  set term : ℝ → (Fin 3 → ℤ) → ℝ := fun ε m =>
    if Real.sqrt 2 ≤ ‖latVec m‖ then
      ∫ u : E3, aliasKernel (fun x : E3 => ((hε ε x : ℝ) : ℂ)) u * imgW ℓ m u else 0 with hterm
  set Cm : (Fin 3 → ℤ) → ℝ := fun m =>
    if Real.sqrt 2 ≤ ‖latVec m‖ then (ℓ ^ 4 * (‖latVec m‖ - 1) ^ 4)⁻¹ else 0 with hCm
  set bnd : (Fin 3 → ℤ) → ℝ := fun m => Cm m * (∫ x : E3, h x) ^ 2 with hbnd
  -- ## elementary facts about the modulus and the lift
  have hh_cont : Continuous h := hgcont.norm
  have hh_cs : HasCompactSupport h := hgc.norm
  have hh0 : ∀ x, 0 ≤ h x := fun x => norm_nonneg _
  have hsupp_h : ∀ x : E3, ℓ / 2 < ‖x‖ → h x = 0 := by
    intro x hx
    by_contra hne
    have hmem : x ∈ tsupport g :=
      subset_closure (Function.mem_support.mpr fun hg0 =>
        hne (by rw [hh]; exact norm_eq_zero.mpr hg0))
    have h2 := hgsupp hmem
    rw [Metric.mem_closedBall, dist_zero_right] at h2
    linarith
  have hε_cont : ∀ ε : ℝ, Continuous (hε ε) := by
    intro ε
    simp only [hhε]
    exact (Real.continuous_sqrt.comp ((hh_cont.pow 2).add continuous_const)).sub continuous_const
  have hε_nonneg : ∀ ε : ℝ, 0 ≤ ε → ∀ x : E3, 0 ≤ hε ε x := by
    intro ε hε0 x
    simp only [hhε]
    have h1 : ε ≤ Real.sqrt (h x ^ 2 + ε ^ 2) := by
      rw [Real.le_sqrt (by positivity) (by positivity)]
      nlinarith [sq_nonneg (h x)]
    linarith
  have hε_le : ∀ ε : ℝ, 0 ≤ ε → ∀ x : E3, hε ε x ≤ h x := by
    intro ε hε0 x
    simp only [hhε]
    have h1 : Real.sqrt (h x ^ 2 + ε ^ 2) ≤ h x + ε := by
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith [hh0 x, hε0]
    linarith
  have hε_gap : ∀ ε : ℝ, 0 ≤ ε → ∀ x : E3, h x - hε ε x ≤ ε := by
    intro ε hε0 x
    simp only [hhε]
    have h1 : h x ≤ Real.sqrt (h x ^ 2 + ε ^ 2) := by
      rw [Real.le_sqrt (hh0 x) (by positivity)]
      nlinarith
    linarith
  have hε_zero : ∀ ε : ℝ, 0 ≤ ε → ∀ x : E3, h x = 0 → hε ε x = 0 := by
    intro ε hε0 x hx
    simp only [hhε]
    rw [hx, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add, Real.sqrt_sq_eq_abs,
      abs_of_nonneg hε0, sub_self]
  have hε_cs : ∀ ε : ℝ, 0 ≤ ε → HasCompactSupport (hε ε) := by
    intro ε hε0
    refine HasCompactSupport.of_support_subset_isCompact hh_cs.isCompact fun x hx => ?_
    by_contra hx'
    rw [Function.mem_support] at hx
    exact hx (hε_zero ε hε0 x (by
      by_contra hne
      exact hx' (subset_tsupport h hne)))
  -- ## the autocorrelations
  have hA_eq : ∀ u : E3, A u = aliasKernel (fun x : E3 => ((h x : ℝ) : ℂ)) u := by
    intro u
    simp only [hA]
    rw [aliasKernel_lift_eq_integral]
  have hA_nonneg : ∀ u : E3, 0 ≤ A u := by
    intro u
    simp only [hA]
    exact integral_nonneg fun x => mul_nonneg (hh0 x) (hh0 (x - u))
  have hA_zero : ∀ u : E3, ℓ < ‖u‖ → A u = 0 := by
    intro u hu
    simp only [hA]
    exact autoCorr_eq_zero_of_supp hsupp_h hu
  have hAε_eq : ∀ ε : ℝ, Aε ε = aliasKernel (fun x : E3 => ((hε ε x : ℝ) : ℂ)) := by
    intro ε
    funext u
    simp only [hAε]
    exact (aliasKernel_lift_eq_integral (hε ε) u).symm
  have hAε_nonneg : ∀ ε : ℝ, 0 ≤ ε → ∀ u : E3, 0 ≤ Aε ε u := by
    intro ε hε0 u
    simp only [hAε]
    exact integral_nonneg fun x => mul_nonneg (hε_nonneg ε hε0 x) (hε_nonneg ε hε0 (x - u))
  have hAε_le : ∀ ε : ℝ, 0 ≤ ε → ∀ u : E3, Aε ε u ≤ A u := by
    intro ε hε0 u
    simp only [hAε, hA]
    exact autoCorr_mono hh_cont hh_cs (hε_cont ε) (hε_cs ε hε0) (hε_nonneg ε hε0)
      (hε_le ε hε0) u
  have hAε_diff : ∀ ε : ℝ, 0 ≤ ε → ∀ u : E3, |A u - Aε ε u| ≤ 2 * ε * ∫ x : E3, h x := by
    intro ε hε0 u
    simp only [hAε, hA]
    exact autoCorr_diff_le hh_cont hh_cs (hε_cont ε) (hε_cs ε hε0) (hε_nonneg ε hε0)
      (hε_le ε hε0) hε0 (hε_gap ε hε0) u
  have hAε_zero : ∀ ε : ℝ, 0 ≤ ε → ∀ u : E3, ℓ < ‖u‖ → Aε ε u = 0 := by
    intro ε hε0 u hu
    simp only [hAε]
    exact autoCorr_eq_zero_of_supp (fun x hx => hε_zero ε hε0 x (hsupp_h x hx)) hu
  -- ## a uniform bound for the modulus
  obtain ⟨Cg, hCg⟩ : ∃ Cg : ℝ, ∀ x : E3, h x ≤ Cg := by
    obtain ⟨C₀, hC₀⟩ := hh_cs.isCompact.exists_bound_of_continuousOn hh_cont.continuousOn
    refine ⟨max C₀ 0, fun x => ?_⟩
    by_cases hx : x ∈ tsupport h
    · have h1 := hC₀ x hx
      rw [Real.norm_eq_abs] at h1
      exact le_trans (le_abs_self (h x)) (le_trans h1 (le_max_left _ _))
    · have hz : h x = 0 := by
        by_contra hne
        exact hx (subset_closure (Function.mem_support.mpr hne))
      rw [hz]
      exact le_max_right _ _
  have hA_le : ∀ u : E3, A u ≤ Cg * ∫ x : E3, h x := by
    intro u
    simp only [hA]
    exact autoCorr_le_const hh_cont hh_cs hh0 hCg u
  -- ## the summable majorant
  have hCm_nonneg : ∀ m : Fin 3 → ℤ, 0 ≤ Cm m := by
    intro m
    simp only [hCm]
    split_ifs with hm
    · positivity
    · exact le_refl 0
  have hsumm_Cm : Summable Cm := by
    simpa only [hCm] using summable_latVec_decay hℓ
  have hsumm_bnd : Summable bnd := by
    simpa only [hbnd] using hsumm_Cm.mul_right ((∫ x : E3, h x) ^ 2)
  have hfun0 : (fun x : E3 => hε 0 x) = h := by
    funext x
    simp only [hhε, hh]
    rw [zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (norm_nonneg _), sub_zero]
  -- ## the per-`m` convergence (dominated convergence in `u`)
  have hper : ∀ m : Fin 3 → ℤ, Tendsto (fun ε : ℝ => term ε m)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (term 0 m)) := by
    intro m
    by_cases hm : Real.sqrt 2 ≤ ‖latVec m‖
    · set B : E3 → ℝ := fun u =>
        (Cm m * (Cg * ∫ x : E3, h x)) * (if ‖u‖ ≤ ℓ then 1 else 0) with hB
      have hs_eq : {u : E3 | ‖u‖ ≤ ℓ} = Metric.closedBall (0 : E3) ℓ := by
        ext u
        rw [Set.mem_ofPred_eq, Metric.mem_closedBall, dist_zero_right]
      have hs : MeasurableSet {u : E3 | ‖u‖ ≤ ℓ} := by
        rw [hs_eq]
        exact Metric.isClosed_closedBall.measurableSet
      have hBint : Integrable B := by
        have hfin : (volume : Measure E3) {u : E3 | ‖u‖ ≤ ℓ} ≠ ⊤ := by
          have h0 : (volume : Measure E3) (Metric.closedBall (0 : E3) ℓ) ≠ ⊤ :=
            (measure_closedBall_lt_top (μ := (volume : Measure E3)) (x := (0 : E3))
              (r := ℓ)).ne
          rwa [hs_eq]
        have hconst : IntegrableOn (fun _ : E3 => Cm m * (Cg * ∫ x : E3, h x))
            {u : E3 | ‖u‖ ≤ ℓ} volume :=
          integrableOn_const (C := Cm m * (Cg * ∫ x : E3, h x)) hfin
        have hBeq : B = {u : E3 | ‖u‖ ≤ ℓ}.indicator
            (fun _ => Cm m * (Cg * ∫ x : E3, h x)) := by
          funext u
          simp only [hB]
          by_cases hu : ‖u‖ ≤ ℓ
          · rw [if_pos hu, Set.indicator_of_mem (show u ∈ {u : E3 | ‖u‖ ≤ ℓ} from hu), mul_one]
          · rw [if_neg hu, Set.indicator_of_notMem (show u ∉ {u : E3 | ‖u‖ ≤ ℓ} from hu),
              mul_zero]
        rw [hBeq]
        exact (integrable_indicator_iff hs).mpr hconst
      have hmeas : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          AEStronglyMeasurable (fun u : E3 => Aε ε u * imgW ℓ m u) volume := by
        filter_upwards [self_mem_nhdsWithin] with ε hε
        have h1 : StronglyMeasurable (fun u : E3 => Aε ε u) := by
          rw [hAε_eq ε]
          exact stronglyMeasurable_aliasKernel
            (Complex.ofRealCLM.continuous.comp (hε_cont ε))
        exact (h1.mul (measurable_imgW ℓ m).stronglyMeasurable).aestronglyMeasurable
      have hbound : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          ∀ᵐ u : E3 ∂(volume : Measure E3), ‖Aε ε u * imgW ℓ m u‖ ≤ B u := by
        filter_upwards [self_mem_nhdsWithin] with ε hε
        have hε0 : 0 ≤ ε := le_of_lt hε
        filter_upwards with u
        by_cases hu : ‖u‖ ≤ ℓ
        · have h1 : imgW ℓ m u ≤ Cm m := by
            have h2 := imgW_le_of_sqrtTwo_le hℓ hm hu
            have h3 : Cm m = (ℓ ^ 4 * (‖latVec m‖ - 1) ^ 4)⁻¹ := by
              simp only [hCm]; exact if_pos hm
            rwa [h3]
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hAε_nonneg ε hε0 u),
            abs_of_nonneg (imgW_nonneg ℓ m u)]
          calc Aε ε u * imgW ℓ m u ≤ A u * Cm m :=
                mul_le_mul (hAε_le ε hε0 u) h1 (imgW_nonneg ℓ m u) (hA_nonneg u)
            _ = Cm m * A u := by ring
            _ ≤ Cm m * (Cg * ∫ x : E3, h x) :=
                mul_le_mul_of_nonneg_left (hA_le u) (hCm_nonneg m)
            _ = B u := by simp only [hB]; rw [if_pos hu, mul_one]
        · have h1 : Aε ε u = 0 := hAε_zero ε hε0 u (lt_of_not_ge hu)
          rw [h1, zero_mul, norm_zero]
          simp only [hB]
          rw [if_neg hu, mul_zero]
      have hlim : ∀ᵐ u : E3 ∂(volume : Measure E3),
          Tendsto (fun ε : ℝ => Aε ε u * imgW ℓ m u) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
            (nhds (A u * imgW ℓ m u)) := by
        filter_upwards with u
        have h1 : Tendsto (fun ε : ℝ => A u - Aε ε u) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
            (nhds 0) := by
          refine squeeze_zero' (f := fun ε : ℝ => A u - Aε ε u)
            (g := fun ε : ℝ => 2 * ε * ∫ x : E3, h x) ?_ ?_ ?_
          · filter_upwards [self_mem_nhdsWithin] with ε hε
            exact sub_nonneg.mpr (hAε_le ε (le_of_lt hε) u)
          · filter_upwards [self_mem_nhdsWithin] with ε hε
            have h2 := hAε_diff ε (le_of_lt hε) u
            rw [abs_le] at h2
            exact h2.2
          · have h3 : Tendsto (fun ε : ℝ => 2 * ε * ∫ x : E3, h x) (nhds (0 : ℝ))
                (nhds (2 * 0 * ∫ x : E3, h x)) :=
              (tendsto_const_nhds.mul tendsto_id).mul tendsto_const_nhds
            simpa using h3.mono_left nhdsWithin_le_nhds
        have h2 : Tendsto (fun ε : ℝ => A u - (A u - Aε ε u))
            (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (A u - 0)) :=
          tendsto_const_nhds.sub h1
        have h3 : (fun ε : ℝ => A u - (A u - Aε ε u)) = fun ε : ℝ => Aε ε u := by
          funext ε; ring
        rw [h3] at h2
        simpa using h2.mul tendsto_const_nhds
      have hDCT := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
        (μ := (volume : Measure E3)) (l := nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (F := fun ε u => Aε ε u * imgW ℓ m u) (f := fun u => A u * imgW ℓ m u) B
        hmeas hbound hBint hlim
      simp only [hterm, if_pos hm]
      have e1 : (fun ε : ℝ =>
            ∫ u : E3, aliasKernel (fun x : E3 => ((hε ε x : ℝ) : ℂ)) u * imgW ℓ m u)
          = fun ε : ℝ => ∫ u : E3, Aε ε u * imgW ℓ m u := by
        funext ε
        refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        rw [hAε_eq ε]
      have e2 : (∫ u : E3, aliasKernel (fun x : E3 => ((hε 0 x : ℝ) : ℂ)) u * imgW ℓ m u)
          = ∫ u : E3, A u * imgW ℓ m u := by
        have hf0 : (fun x : E3 => ((hε 0 x : ℝ) : ℂ)) = fun x : E3 => ((h x : ℝ) : ℂ) := by
          simp only [hfun0]
        rw [hf0]
        refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        simp only [hA_eq]
      rw [e1, e2]
      exact hDCT
    · simp only [hterm, if_neg hm]
      exact tendsto_const_nhds
  -- ## the Tannery domination
  have hterm_bound : ∀ m : Fin 3 → ℤ, ∀ ε : ℝ, 0 ≤ ε → ‖term ε m‖ ≤ bnd m := by
    intro m ε hε0
    by_cases hm : Real.sqrt 2 ≤ ‖latVec m‖
    · have hCm_eq : Cm m = (ℓ ^ 4 * (‖latVec m‖ - 1) ^ 4)⁻¹ := by
        simp only [hCm]; exact if_pos hm
      have h1 : (∫ u : E3, aliasKernel (fun x : E3 => ((hε ε x : ℝ) : ℂ)) u * imgW ℓ m u)
          = ∫ u : E3, Aε ε u * imgW ℓ m u := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        rw [hAε_eq ε]
      have hA2 : (∫⁻ u : E3, ENNReal.ofReal (A u * imgW ℓ m u))
          ≤ ENNReal.ofReal (Cm m) * ENNReal.ofReal ((∫ x : E3, h x) ^ 2) := by
        have hpt : ∀ u : E3, ENNReal.ofReal (A u * imgW ℓ m u)
            ≤ ENNReal.ofReal (Cm m) * ENNReal.ofReal (A u) := by
          intro u
          by_cases hAu : A u = 0
          · simp [hAu]
          · have hpos : 0 < A u := lt_of_le_of_ne (hA_nonneg u) (Ne.symm hAu)
            have hu : ‖u‖ ≤ ℓ := by
              by_contra h
              exact hAu (hA_zero u (lt_of_not_ge h))
            have h1 : imgW ℓ m u ≤ Cm m := by
              have h2 := imgW_le_of_sqrtTwo_le hℓ hm hu
              rwa [hCm_eq]
            rw [ENNReal.ofReal_mul (hA_nonneg u), mul_comm (ENNReal.ofReal (Cm m))]
            exact mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal h1) bot_le
        calc (∫⁻ u : E3, ENNReal.ofReal (A u * imgW ℓ m u))
            ≤ ∫⁻ u : E3, ENNReal.ofReal (Cm m) * ENNReal.ofReal (A u) := lintegral_mono hpt
          _ = ENNReal.ofReal (Cm m) * ∫⁻ u : E3, ENNReal.ofReal (A u) :=
              lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
          _ ≤ ENNReal.ofReal (Cm m) * ENNReal.ofReal ((∫ x : E3, h x) ^ 2) := by
              refine mul_le_mul_of_nonneg_left ?_ bot_le
              calc (∫⁻ u : E3, ENNReal.ofReal (A u))
                  = ∫⁻ u : E3, ENNReal.ofReal (∫ x : E3, h x * h (x - u)) := by
                    refine lintegral_congr fun u => ?_
                    simp only [hA]
                _ ≤ ENNReal.ofReal ((∫ x : E3, h x) ^ 2) :=
                    lintegral_autoCorr_le hh_cont hh_cs hh0
      have hfin2 : (∫⁻ u : E3, ENNReal.ofReal (A u * imgW ℓ m u)) ≠ ⊤ :=
        (lt_of_le_of_lt hA2 (by
          rw [lt_top_iff_ne_top]
          exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)).ne
      simp only [hterm, if_pos hm]
      rw [h1]
      calc ‖∫ u : E3, Aε ε u * imgW ℓ m u‖
          ≤ (∫⁻ u : E3, ENNReal.ofReal ‖Aε ε u * imgW ℓ m u‖).toReal :=
            MeasureTheory.norm_integral_le_lintegral_norm _
        _ = (∫⁻ u : E3, ENNReal.ofReal (Aε ε u * imgW ℓ m u)).toReal := by
            congr 1
            refine lintegral_congr fun u => ?_
            rw [Real.norm_eq_abs,
              abs_of_nonneg (mul_nonneg (hAε_nonneg ε hε0 u) (imgW_nonneg ℓ m u))]
        _ ≤ (∫⁻ u : E3, ENNReal.ofReal (A u * imgW ℓ m u)).toReal :=
            ENNReal.toReal_mono hfin2 (lintegral_mono fun u =>
              ENNReal.ofReal_le_ofReal
                (mul_le_mul_of_nonneg_right (hAε_le ε hε0 u) (imgW_nonneg ℓ m u)))
        _ ≤ (ENNReal.ofReal (Cm m) * ENNReal.ofReal ((∫ x : E3, h x) ^ 2)).toReal :=
            ENNReal.toReal_mono
              (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hA2
        _ = Cm m * (∫ x : E3, h x) ^ 2 := by
            rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hCm_nonneg m),
              ENNReal.toReal_ofReal (by positivity)]
        _ = bnd m := by simp only [hbnd]
    · simp only [hterm, if_neg hm, norm_zero, hbnd, hCm]
      simp
  have hdom : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ∀ m : Fin 3 → ℤ, ‖term ε m‖ ≤ bnd m := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact fun m => hterm_bound m ε (le_of_lt hε)
  -- ## Tannery
  have key : Tendsto (fun ε : ℝ => ∑' m : Fin 3 → ℤ, term ε m)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (∑' m : Fin 3 → ℤ, term 0 m)) :=
    tendsto_tsum_of_dominated_convergence (f := fun ε m => term ε m)
      (g := fun m => term 0 m) (bound := bnd) hsumm_bnd hper hdom
  -- ## identify the limit and the source
  have hsum_eq : (∑' m : Fin 3 → ℤ, term 0 m)
      = ∑' m : Fin 3 → ℤ, (if Real.sqrt 2 ≤ ‖latVec m‖ then
          ∫ u : E3, aliasKernel (fun x : E3 => ((‖g x‖ : ℝ) : ℂ)) u * imgW ℓ m u else 0) := by
    refine tsum_congr fun m => ?_
    simp only [hterm]
    by_cases hm : Real.sqrt 2 ≤ ‖latVec m‖
    · rw [if_pos hm, if_pos hm]
      refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      simp only [hfun0, hh]
    · rw [if_neg hm, if_neg hm]
  rw [hsum_eq] at key
  have hsrc : (fun ε : ℝ => ∑' m : Fin 3 → ℤ, term ε m)
      = fun ε : ℝ => ∑' m : Fin 3 → ℤ,
          (if Real.sqrt 2 ≤ ‖latVec m‖ then
            ∫ u : E3, aliasKernel (fun x : E3 =>
                ((Real.sqrt (‖g x‖ ^ 2 + ε ^ 2) - ε : ℝ) : ℂ)) u * imgW ℓ m u else 0) := by
    funext ε
    refine tsum_congr fun m => ?_
    simp only [hterm, hhε, hh]
  rw [hsrc] at key
  exact key

end Work.BoseBoxFock
