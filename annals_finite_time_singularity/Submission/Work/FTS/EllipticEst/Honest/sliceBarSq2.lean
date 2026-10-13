import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.Honest.Basic
import Submission.Work.FTS.EllipticEst.Honest.sliceBarSq2_boundary_tendsto
import Submission.Work.FTS.EllipticEst.remov.interval_integral_mono_limit

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

local notation "σ" => Work.FTS.EllipticEst.AngSecond.sig

/-- `σ = sin(2θ)^{-η}` is continuous on the open angular interval `(0, π/2)`. -/
theorem continuousOn_sig_Ioo :
    ContinuousOn σ (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  refine (Real.continuous_sin.comp_continuousOn (continuousOn_id.const_mul 2)).rpow_const ?_
  intro θ hθ
  have h1 : (0 : ℝ) < 2 * θ := by linarith [hθ.1]
  have h2 : 2 * θ < Real.pi := by linarith [hθ.2]
  exact Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h1 h2))

/-- `ρ θ = sin θ · cos θ · σ θ` is nonnegative on the open angular interval. -/
theorem wrho_nonneg_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 ≤ Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta θ := by
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩
  have h1 : (0 : ℝ) < 2 * θ := by linarith [hθ.1]
  have h2 : 2 * θ < Real.pi := by linarith [hθ.2]
  have hs2 : 0 < Real.sin (2 * θ) := Real.sin_pos_of_pos_of_lt_pi h1 h2
  rw [Work.FTS.EllipticEst.TanTheta.wrho]
  exact mul_nonneg (mul_nonneg hs.le hc.le) (Real.rpow_nonneg hs2.le _)

/-- The integrals over `(0, π/2)` and over `Iθ` agree. -/
theorem integral_Ioo_eq_Iθ' (f : ℝ → ℝ) :
    (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), f θ) = ∫ θ in Work.Spaces.Iθ, f θ := by
  have h : (Set.Ioo (0 : ℝ) (Real.pi / 2)) =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ)]
      (Set.Icc (0 : ℝ) (Real.pi / 2)) := MeasureTheory.Ioo_ae_eq_Icc
  rw [Work.Spaces.Iθ]
  rw [show (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), f θ)
      = ∫ θ, f θ ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict
          (Set.Ioo (0 : ℝ) (Real.pi / 2))) from rfl]
  rw [MeasureTheory.Measure.restrict_congr_set h]

/-- `σ` is nonnegative on the open angular interval. -/
private theorem sig_nonneg_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) : 0 ≤ σ θ :=
  Work.FTS.EllipticEst.AngSecond.sig_nonneg ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩

/-- **The slice integrand is locally integrable.**  If `u²σ` is integrable on `Iθ` then
`(u/cos)²σ` is integrable on every `(0, b)` with `b < π/2`: on `(0,b)` one has
`cos²θ ≥ cos²b > 0`, so the integrand is dominated by the constant multiple
`(1/cos²b)·u²σ`. -/
private theorem local_integrable_local (u : ℝ → ℝ)
    (h0 : MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2 * σ θ) Work.Spaces.Iθ) :
    ∀ b ∈ Set.Ioo 0 (Real.pi / 2),
      MeasureTheory.IntegrableOn (fun θ => (u θ / Real.cos θ) ^ 2 * σ θ) (Set.Ioo 0 b) := by
  intro b hb
  have hbpos : 0 < b := hb.1
  have hbpi : b < Real.pi / 2 := hb.2
  have hcosb : 0 < Real.cos b :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hbpos, Real.pi_pos], hbpi⟩
  have h0b : MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2 * σ θ) (Set.Ioo 0 b) :=
    h0.mono_set (fun x hx => ⟨le_of_lt hx.1, le_of_lt (lt_trans hx.2 hbpi)⟩)
  refine (h0b.const_mul (1 / (Real.cos b) ^ 2)).mono' ?_ ?_
  · have h1 : AEStronglyMeasurable (fun θ : ℝ => (u θ) ^ 2 * σ θ)
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Ioo 0 b)) :=
      h0b.aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun θ : ℝ => (1 : ℝ) / (Real.cos θ) ^ 2)
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Ioo 0 b)) :=
      (ContinuousOn.div continuousOn_const (Real.continuous_cos.continuousOn.pow 2)
        (fun θ hθ => pow_ne_zero 2 (ne_of_gt (Real.cos_pos_of_mem_Ioo
          ⟨by linarith [Real.pi_pos, hθ.1], by linarith [hθ.2, hbpi]⟩)))).aestronglyMeasurable
        measurableSet_Ioo
    have h3 := h1.mul h2
    convert h3 using 1
    ext θ
    simp only [Pi.mul_apply]
    ring
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    have hcθ : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos, hθ.1], by linarith [hθ.2, hbpi]⟩
    have hσ : 0 ≤ σ θ := sig_nonneg_Ioo ⟨hθ.1, lt_trans hθ.2 hbpi⟩
    have hcb_le : Real.cos b ≤ Real.cos θ :=
      Real.cos_le_cos_of_nonneg_of_le_pi (x := θ) (y := b) hθ.1.le
        (by linarith [hbpi, Real.pi_pos]) hθ.2.le
    have hsq : Real.cos b ^ 2 ≤ Real.cos θ ^ 2 := by nlinarith [hcosb, hcθ, hcb_le]
    have hkey : (u θ / Real.cos θ) ^ 2 ≤ (1 / (Real.cos b) ^ 2) * (u θ) ^ 2 := by
      have hdiv : (1 : ℝ) / (Real.cos θ) ^ 2 ≤ 1 / (Real.cos b) ^ 2 :=
        one_div_le_one_div_of_le (pow_pos hcosb 2) hsq
      calc (u θ / Real.cos θ) ^ 2 = (u θ) ^ 2 * (1 / (Real.cos θ) ^ 2) := by
            rw [div_pow]; ring
        _ ≤ (u θ) ^ 2 * (1 / (Real.cos b) ^ 2) := mul_le_mul_of_nonneg_left hdiv (sq_nonneg _)
        _ = (1 / (Real.cos b) ^ 2) * (u θ) ^ 2 := by ring
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hσ)]
    calc (u θ / Real.cos θ) ^ 2 * σ θ
        ≤ ((1 / (Real.cos b) ^ 2) * (u θ) ^ 2) * σ θ := mul_le_mul_of_nonneg_right hkey hσ
      _ = (1 / (Real.cos b) ^ 2) * ((u θ) ^ 2 * σ θ) := by ring

/-- **Monotone limit of set integrals with a moving bound.**  If `F ≥ 0` is integrable on each
member `s n` of an increasing sequence of sets covering `(0, β)`, and `∫_{s n} F ≤ K n` where
`K n → K0`, then `F` is integrable on `(0, β)` and `∫_{(0,β)} F ≤ K0`. -/
private theorem lintegral_le_of_directed_local {F : ℝ → ℝ} {s : ℕ → Set ℝ} {β K0 : ℝ}
    (hβ : 0 < β) (hmeas : ∀ n, MeasurableSet (s n)) (hmono : Monotone s)
    (hsub : ∀ n, s n ⊆ Set.Ioo 0 β) (hcov : Set.Ioo 0 β ⊆ ⋃ n, s n)
    (hint : ∀ n, MeasureTheory.IntegrableOn F (s n))
    (haesm : MeasureTheory.AEStronglyMeasurable F
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Ioo 0 β)))
    (hnn : ∀ x ∈ Set.Ioo 0 β, 0 ≤ F x)
    {K : ℕ → ℝ} (hK : ∀ n, (∫ x in s n, F x) ≤ K n)
    (hKlim : Filter.Tendsto K Filter.atTop (nhds K0)) :
    MeasureTheory.IntegrableOn F (Set.Ioo 0 β) ∧
      (∫ x in Set.Ioo 0 β, F x) ≤ K0 := by
  have hunion : (⋃ n, s n) = Set.Ioo 0 β :=
    Set.Subset.antisymm (Set.iUnion_subset hsub) hcov
  have hdir : Directed (· ⊆ ·) s := fun m n =>
    ⟨max m n, hmono (le_max_left m n), hmono (le_max_right m n)⟩
  have hterm : ∀ n, (∫⁻ x in s n, ENNReal.ofReal (F x)) = ENNReal.ofReal (∫ x in s n, F x) := by
    intro n
    refine (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hint n) ?_).symm
    filter_upwards [MeasureTheory.ae_restrict_mem (hmeas n)] with x hx
    exact hnn x (hsub n hx)
  have hKnn : 0 ≤ K0 := by
    refine ge_of_tendsto hKlim (Eventually.of_forall fun n => ?_)
    exact le_trans (setIntegral_nonneg (hmeas n) (fun x hx => hnn x (hsub n hx))) (hK n)
  have hbound : ∀ ε : NNReal, 0 < ε → (∫⁻ x in Set.Ioo 0 β, ENNReal.ofReal (F x))
      ≤ ENNReal.ofReal K0 + (ε : ENNReal) := by
    intro ε hε
    have hεR : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
    have hev : ∀ᶠ n in Filter.atTop, K n < K0 + (ε : ℝ) :=
      hKlim.eventually (isOpen_Iio.mem_nhds (lt_add_of_pos_right K0 hεR))
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
    have hsup : (∫⁻ x in Set.Ioo 0 β, ENNReal.ofReal (F x))
        = ⨆ n, ∫⁻ x in s n, ENNReal.ofReal (F x) := by
      rw [← hunion]
      exact MeasureTheory.setLIntegral_iUnion_of_directed (fun x => ENNReal.ofReal (F x)) hdir
    rw [hsup]
    refine iSup_le fun n => ?_
    calc (∫⁻ x in s n, ENNReal.ofReal (F x))
        ≤ ∫⁻ x in s (max n N), ENNReal.ofReal (F x) :=
          MeasureTheory.lintegral_mono_set (hmono (le_max_left n N))
      _ = ENNReal.ofReal (∫ x in s (max n N), F x) := hterm (max n N)
      _ ≤ ENNReal.ofReal (K (max n N)) := ENNReal.ofReal_le_ofReal (hK (max n N))
      _ ≤ ENNReal.ofReal (K0 + (ε : ℝ)) :=
          ENNReal.ofReal_le_ofReal (le_of_lt (hN (max n N) (le_max_right n N)))
      _ = ENNReal.ofReal K0 + (ε : ENNReal) := by
          rw [ENNReal.ofReal_add hKnn (le_of_lt hεR), ENNReal.ofReal_coe_nnreal]
  exact Work.FTS.EllipticEst.remov.integrable_of_lintegral_ofReal_le' measurableSet_Ioo hKnn haesm
    hnn (ENNReal.le_of_forall_pos_le_add fun ε hε _ => hbound ε hε)

/-- The pointwise algebra behind `core_local`: with `u = v·cos θ`, `u' = w·cos θ − v·sin θ`,
`ρ = σ·sin θ·cos θ` and `cos²θ + sin²θ = 1`,

`100 (u² + u'²) σ − v² σ = 100 σ (w cos θ)² − 200 ρ v w + 99 v² σ`. -/
private theorem core_pt_identity (u D V W c s sg r : ℝ) (hV : u = V * c)
    (hD : D = W * c - V * s) (hr : r = sg * s * c) (hcs : c ^ 2 + s ^ 2 = 1) :
    100 * (u ^ 2 * sg) + 100 * (D ^ 2 * sg) - V ^ 2 * sg
      = 100 * (W ^ 2 * c ^ 2 * sg) - 200 * (r * V * W) + 99 * (V ^ 2 * sg) := by
  rw [hV, hD, hr]
  linear_combination (100 * sg * V ^ 2) * hcs


/-- **The core identity of `sliceBarSq2`, on a compact sub-interval `(a,b) ⊂ (0, π/2)`.**

With `σ = sin(2θ)^{-η}` and `ρ θ = sin θ · cos θ · σ θ`, for `u` of class `C²` on the open
quadrant,

```
∫_{(a,b)} [100 (u² + u'²) σ − (u/cos)² σ]
  = 100 ∫_{(a,b)} σ (∂_θ(u/cos))² cos²θ
    + ∫_{(a,b)} (u/cos)² σ (99 + cos 2θ)
    − 100 [ρ · (u/cos)²]  at `a` and `b` .
```

Route: with `v = u/cos` the pointwise identity
`100(u²+u'²)σ − v²σ = 100 σ (v'cos θ)² − 200 ρ v v' + 99 v²σ`, then the integration by parts
`∫ ρ v v' = (1/2)[ρ v²] − (1/2)∫ ρ' v²` (the FTC applied to `(1/2)ρv²` on `[a,b]`), and
`ρ' = (1−η) cos 2θ · σ` with `100 (1 − η) = 1` because `η = 99/100`. -/
private theorem core_local (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < Real.pi / 2) :
    (∫ θ in Set.Ioo a b, (100 * ((u θ) ^ 2 * σ θ) + 100 * ((deriv u θ) ^ 2 * σ θ)
        - (u θ / Real.cos θ) ^ 2 * σ θ))
      = 100 * (∫ θ in Set.Ioo a b, (deriv (fun t : ℝ => u t / Real.cos t) θ) ^ 2
              * (Real.cos θ) ^ 2 * σ θ)
        + (∫ θ in Set.Ioo a b, (u θ / Real.cos θ) ^ 2 * σ θ * (99 + Real.cos (2 * θ)))
        - 100 * (Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta b
              * (u b / Real.cos b) ^ 2
            - Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta a
              * (u a / Real.cos a) ^ 2) := by
  have hsub : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun x hx =>
    ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hb⟩
  have hIoo_sub : Set.Ioo a b ⊆ Set.Icc a b := fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  have hcospos : ∀ θ ∈ Set.Icc a b, 0 < Real.cos θ := fun θ hθ =>
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, (hsub hθ).1], (hsub hθ).2⟩
  -- ## notation
  set ρ : ℝ → ℝ := Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta with hρ
  set ρ' : ℝ → ℝ := Work.FTS.EllipticEst.TanTheta.wrhoD Work.Spaces.eta with hρ'
  have hρeq : ∀ θ : ℝ, ρ θ = σ θ * Real.sin θ * Real.cos θ := by
    intro θ
    rw [hρ]
    dsimp only [Work.FTS.EllipticEst.TanTheta.wrho, Work.FTS.EllipticEst.AngSecond.sig]
    ring
  have hρDeq : ∀ θ : ℝ, ρ' θ = (1 - Work.Spaces.eta) * Real.cos (2 * θ) * σ θ := by
    intro θ
    rw [hρ']
    dsimp only [Work.FTS.EllipticEst.TanTheta.wrhoD, Work.FTS.EllipticEst.AngSecond.sig]
  have heta100 : (1 : ℝ) - Work.Spaces.eta = 1 / 100 := by
    rw [Work.Spaces.eta]; norm_num
  -- ## continuity on the compact interval
  have hσcont : ContinuousOn σ (Set.Icc a b) := continuousOn_sig_Ioo.mono hsub
  have hρcont : ContinuousOn ρ (Set.Icc a b) := by
    have hc : ContinuousOn (fun θ : ℝ => σ θ * Real.sin θ * Real.cos θ) (Set.Icc a b) :=
      ((hσcont.mul Real.continuous_sin.continuousOn).mul Real.continuous_cos.continuousOn)
    exact hc.congr (fun x _ => hρeq x)
  have hρ'cont : ContinuousOn ρ' (Set.Icc a b) := by
    have hc : ContinuousOn (fun θ : ℝ => (1 - Work.Spaces.eta) * Real.cos (2 * θ) * σ θ)
        (Set.Icc a b) :=
      ((continuousOn_const.mul
        (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn).mul hσcont)
    exact hc.congr (fun x _ => hρDeq x)
  have hVcont : ContinuousOn (fun t : ℝ => u t / Real.cos t) (Set.Icc a b) :=
    (hu.continuousOn.mono hsub).div Real.continuous_cos.continuousOn
      (fun θ hθ => ne_of_gt (hcospos θ hθ))
  have hVcd : ContDiffOn ℝ 2 (fun t : ℝ => u t / Real.cos t) (Set.Ioo 0 (Real.pi / 2)) :=
    hu.div (Real.contDiff_cos.contDiffOn.of_le le_top)
      (fun θ hθ => ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩))
  have hV'cont : ContinuousOn (deriv (fun t : ℝ => u t / Real.cos t)) (Set.Icc a b) :=
    (hVcd.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)).mono hsub
  -- ## differentiability on the compact interval
  have hVD : ∀ θ ∈ Set.Icc a b,
      HasDerivAt (fun t : ℝ => u t / Real.cos t) (deriv (fun t : ℝ => u t / Real.cos t) θ) θ := by
    intro θ hθ
    exact ((hVcd.contDiffAt (isOpen_Ioo.mem_nhds (hsub hθ))).differentiableAt (by norm_num)).hasDerivAt
  have hrel : ∀ θ ∈ Set.Icc a b, deriv u θ
      = deriv (fun t : ℝ => u t / Real.cos t) θ * Real.cos θ
        - (u θ / Real.cos θ) * Real.sin θ := by
    intro θ hθ
    have hmul : HasDerivAt (fun y : ℝ => (u y / Real.cos y) * Real.cos y)
        (deriv (fun t : ℝ => u t / Real.cos t) θ * Real.cos θ
          - (u θ / Real.cos θ) * Real.sin θ) θ := by
      have h := (hVD θ hθ).mul (Real.hasDerivAt_cos θ)
      convert h using 1
      ring
    have hev : u =ᶠ[𝓝 θ] fun y : ℝ => (u y / Real.cos y) * Real.cos y := by
      filter_upwards [isOpen_Ioo.mem_nhds (hsub hθ)] with y hy
      exact (div_mul_cancel₀ (u y) (ne_of_gt (Real.cos_pos_of_mem_Ioo
        ⟨by linarith [Real.pi_pos, hy.1], hy.2⟩))).symm
    exact (hmul.congr_of_eventuallyEq hev).deriv
  -- ## the pointwise identity
  have hpt : ∀ θ ∈ Set.Icc a b,
      100 * ((u θ) ^ 2 * σ θ) + 100 * ((deriv u θ) ^ 2 * σ θ) - (u θ / Real.cos θ) ^ 2 * σ θ
        = 100 * ((deriv (fun t : ℝ => u t / Real.cos t) θ) ^ 2 * (Real.cos θ) ^ 2 * σ θ)
          - 200 * (ρ θ * (u θ / Real.cos θ) * deriv (fun t : ℝ => u t / Real.cos t) θ)
          + 99 * ((u θ / Real.cos θ) ^ 2 * σ θ) := by
    intro θ hθ
    have hc : Real.cos θ ≠ 0 := ne_of_gt (hcospos θ hθ)
    have hu_eq : u θ = (u θ / Real.cos θ) * Real.cos θ := (div_mul_cancel₀ _ hc).symm
    have hcs : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
    exact core_pt_identity (u θ) (deriv u θ) (u θ / Real.cos θ)
      (deriv (fun t : ℝ => u t / Real.cos t) θ) (Real.cos θ) (Real.sin θ) (σ θ) (ρ θ)
      hu_eq (hrel θ hθ) (hρeq θ) hcs
  -- ## the antiderivative `(1/2) ρ v²`
  have hPD : ∀ x ∈ Set.Icc a b, HasDerivAt (fun y : ℝ => (1 / 2) * (ρ y * (u y / Real.cos y) ^ 2))
      (ρ x * (u x / Real.cos x) * deriv (fun t : ℝ => u t / Real.cos t) x
        + (1 / 2) * (ρ' x * (u x / Real.cos x) ^ 2)) x := by
    intro x hx
    have h1 : HasDerivAt ρ (ρ' x) x := by
      rw [hρ, hρ']
      exact Work.FTS.EllipticEst.TanTheta.wrho_deriv Work.Spaces.eta (hsub hx)
    have h2 : HasDerivAt (fun y : ℝ => (u y / Real.cos y) ^ 2)
        (2 * (u x / Real.cos x) ^ (2 - 1) * deriv (fun t : ℝ => u t / Real.cos t) x) x :=
      (hVD x hx).pow 2
    have h3 := (h1.mul h2).const_mul (1 / 2)
    convert h3 using 1
    ring
  have hdcont : ContinuousOn (fun x : ℝ => ρ x * (u x / Real.cos x)
      * deriv (fun t : ℝ => u t / Real.cos t) x
      + (1 / 2) * (ρ' x * (u x / Real.cos x) ^ 2)) (Set.Icc a b) :=
    ((hρcont.mul hVcont).mul hV'cont).add
      (continuousOn_const.mul (hρ'cont.mul (hVcont.pow 2)))
  have hFTCint : (∫ θ in a..b, (ρ θ * (u θ / Real.cos θ)
        * deriv (fun t : ℝ => u t / Real.cos t) θ
      + (1 / 2) * (ρ' θ * (u θ / Real.cos θ) ^ 2)))
      = (1 / 2) * (ρ b * (u b / Real.cos b) ^ 2)
        - (1 / 2) * (ρ a * (u a / Real.cos a) ^ 2) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hPD x (by rw [Set.uIcc_of_le hab.le] at hx; exact hx))
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).mpr hdcont.integrableOn_Icc)
  have hFTC : (∫ θ in Set.Ioo a b, (ρ θ * (u θ / Real.cos θ)
        * deriv (fun t : ℝ => u t / Real.cos t) θ
      + (1 / 2) * (ρ' θ * (u θ / Real.cos θ) ^ 2)))
      = (1 / 2) * (ρ b * (u b / Real.cos b) ^ 2)
        - (1 / 2) * (ρ a * (u a / Real.cos a) ^ 2) := by
    have h := hFTCint
    rw [intervalIntegral.integral_of_le hab.le, MeasureTheory.integral_Ioc_eq_integral_Ioo] at h
    exact h
  -- ## splitting the FTC identity
  have hint1 : MeasureTheory.IntegrableOn (fun θ : ℝ => ρ θ * (u θ / Real.cos θ)
      * deriv (fun t : ℝ => u t / Real.cos t) θ) (Set.Ioo a b) :=
    (((hρcont.mul hVcont).mul hV'cont).integrableOn_Icc).mono_set hIoo_sub
  have hint2 : MeasureTheory.IntegrableOn (fun θ : ℝ => ρ' θ * (u θ / Real.cos θ) ^ 2)
      (Set.Ioo a b) :=
    ((hρ'cont.mul (hVcont.pow 2)).integrableOn_Icc).mono_set hIoo_sub
  have hsplit : (∫ θ in Set.Ioo a b, ρ θ * (u θ / Real.cos θ)
        * deriv (fun t : ℝ => u t / Real.cos t) θ)
      = (1 / 2) * (ρ b * (u b / Real.cos b) ^ 2) - (1 / 2) * (ρ a * (u a / Real.cos a) ^ 2)
        - (1 / 2) * (∫ θ in Set.Ioo a b, ρ' θ * (u θ / Real.cos θ) ^ 2) := by
    have hsum : (∫ θ in Set.Ioo a b, (ρ θ * (u θ / Real.cos θ)
          * deriv (fun t : ℝ => u t / Real.cos t) θ
        + (1 / 2) * (ρ' θ * (u θ / Real.cos θ) ^ 2)))
        = (∫ θ in Set.Ioo a b, ρ θ * (u θ / Real.cos θ)
            * deriv (fun t : ℝ => u t / Real.cos t) θ)
          + (1 / 2) * (∫ θ in Set.Ioo a b, ρ' θ * (u θ / Real.cos θ) ^ 2) := by
      rw [MeasureTheory.integral_add hint1 (hint2.const_mul (1 / 2)),
        MeasureTheory.integral_const_mul]
    linarith [hFTC, hsum]
  -- ## replacing `ρ'` by `(1/100) cos 2θ σ`
  have hcos2int : MeasureTheory.IntegrableOn (fun θ : ℝ =>
      Real.cos (2 * θ) * σ θ * (u θ / Real.cos θ) ^ 2) (Set.Ioo a b) :=
    ((((Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn.mul hσcont).mul
      (hVcont.pow 2)).integrableOn_Icc).mono_set hIoo_sub
  have hcon2 : (∫ θ in Set.Ioo a b, ρ' θ * (u θ / Real.cos θ) ^ 2)
      = (1 / 100) * (∫ θ in Set.Ioo a b,
          Real.cos (2 * θ) * σ θ * (u θ / Real.cos θ) ^ 2) := by
    rw [show (∫ θ in Set.Ioo a b, ρ' θ * (u θ / Real.cos θ) ^ 2)
        = ∫ θ in Set.Ioo a b,
            (1 / 100) * (Real.cos (2 * θ) * σ θ * (u θ / Real.cos θ) ^ 2) from by
      refine setIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
      rw [hρDeq θ, heta100]
      ring]
    rw [MeasureTheory.integral_const_mul]
  -- ## integrability on the pieces
  have hUUint : MeasureTheory.IntegrableOn (fun θ : ℝ => (u θ) ^ 2 * σ θ) (Set.Ioo a b) :=
    ((((hu.continuousOn.mono hsub).pow 2).mul hσcont).integrableOn_Icc).mono_set hIoo_sub
  have hVVint : MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv u θ) ^ 2 * σ θ) (Set.Ioo a b) :=
    (((((hu.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)).mono hsub).pow 2).mul
      hσcont).integrableOn_Icc).mono_set hIoo_sub
  have hWWint : MeasureTheory.IntegrableOn (fun θ : ℝ => (u θ / Real.cos θ) ^ 2 * σ θ)
      (Set.Ioo a b) :=
    (((hVcont.pow 2).mul hσcont).integrableOn_Icc).mono_set hIoo_sub
  have hW1int : MeasureTheory.IntegrableOn (fun θ : ℝ =>
      (deriv (fun t : ℝ => u t / Real.cos t) θ) ^ 2 * (Real.cos θ) ^ 2 * σ θ) (Set.Ioo a b) :=
    ((((hV'cont.pow 2).mul (Real.continuous_cos.continuousOn.pow 2)).mul hσcont).integrableOn_Icc).mono_set
      hIoo_sub
  have hW2int : MeasureTheory.IntegrableOn (fun θ : ℝ =>
      (u θ / Real.cos θ) ^ 2 * σ θ * (99 + Real.cos (2 * θ))) (Set.Ioo a b) :=
    ((((hVcont.pow 2).mul hσcont).mul (continuousOn_const.add
      (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn)).integrableOn_Icc).mono_set
      hIoo_sub
  -- ## the left-hand side, split
  have hL1 : (∫ θ in Set.Ioo a b, (100 * ((u θ) ^ 2 * σ θ) + 100 * ((deriv u θ) ^ 2 * σ θ)
        - (u θ / Real.cos θ) ^ 2 * σ θ))
      = 100 * (∫ θ in Set.Ioo a b, (u θ) ^ 2 * σ θ)
        + 100 * (∫ θ in Set.Ioo a b, (deriv u θ) ^ 2 * σ θ)
        - (∫ θ in Set.Ioo a b, (u θ / Real.cos θ) ^ 2 * σ θ) := by
    rw [MeasureTheory.integral_sub
      (f := fun θ : ℝ => 100 * ((u θ) ^ 2 * σ θ) + 100 * ((deriv u θ) ^ 2 * σ θ))
      (g := fun θ : ℝ => (u θ / Real.cos θ) ^ 2 * σ θ)
      ((hUUint.const_mul 100).add (hVVint.const_mul 100)) hWWint]
    rw [MeasureTheory.integral_add
      (f := fun θ : ℝ => 100 * ((u θ) ^ 2 * σ θ))
      (g := fun θ : ℝ => 100 * ((deriv u θ) ^ 2 * σ θ))
      (hUUint.const_mul 100) (hVVint.const_mul 100)]
    rw [MeasureTheory.integral_const_mul (100 : ℝ), MeasureTheory.integral_const_mul (100 : ℝ)]
  -- ## the left-hand side, pointwise rewritten
  have hL2 : (∫ θ in Set.Ioo a b, (100 * ((u θ) ^ 2 * σ θ) + 100 * ((deriv u θ) ^ 2 * σ θ)
        - (u θ / Real.cos θ) ^ 2 * σ θ))
      = 100 * (∫ θ in Set.Ioo a b, (deriv (fun t : ℝ => u t / Real.cos t) θ) ^ 2
            * (Real.cos θ) ^ 2 * σ θ)
        - 200 * (∫ θ in Set.Ioo a b, ρ θ * (u θ / Real.cos θ)
            * deriv (fun t : ℝ => u t / Real.cos t) θ)
        + 99 * (∫ θ in Set.Ioo a b, (u θ / Real.cos θ) ^ 2 * σ θ) := by
    rw [setIntegral_congr_fun measurableSet_Ioo (fun θ hθ => hpt θ (hIoo_sub hθ))]
    rw [MeasureTheory.integral_add
      (f := fun θ : ℝ => 100 * ((deriv (fun t : ℝ => u t / Real.cos t) θ) ^ 2
            * (Real.cos θ) ^ 2 * σ θ)
          - 200 * (ρ θ * (u θ / Real.cos θ) * deriv (fun t : ℝ => u t / Real.cos t) θ))
      (g := fun θ : ℝ => 99 * ((u θ / Real.cos θ) ^ 2 * σ θ))
      ((hW1int.const_mul 100).sub (hint1.const_mul 200)) (hWWint.const_mul 99)]
    rw [MeasureTheory.integral_sub
      (f := fun θ : ℝ => 100 * ((deriv (fun t : ℝ => u t / Real.cos t) θ) ^ 2
            * (Real.cos θ) ^ 2 * σ θ))
      (g := fun θ : ℝ => 200 * (ρ θ * (u θ / Real.cos θ)
            * deriv (fun t : ℝ => u t / Real.cos t) θ))
      (hW1int.const_mul 100) (hint1.const_mul 200)]
    rw [MeasureTheory.integral_const_mul (100 : ℝ), MeasureTheory.integral_const_mul (200 : ℝ),
      MeasureTheory.integral_const_mul (99 : ℝ)]
  -- ## the last piece
  have hW2 : (∫ θ in Set.Ioo a b, (u θ / Real.cos θ) ^ 2 * σ θ * (99 + Real.cos (2 * θ)))
      = 99 * (∫ θ in Set.Ioo a b, (u θ / Real.cos θ) ^ 2 * σ θ)
        + (∫ θ in Set.Ioo a b, Real.cos (2 * θ) * σ θ * (u θ / Real.cos θ) ^ 2) := by
    rw [show (∫ θ in Set.Ioo a b, (u θ / Real.cos θ) ^ 2 * σ θ * (99 + Real.cos (2 * θ)))
        = ∫ θ in Set.Ioo a b, (99 * ((u θ / Real.cos θ) ^ 2 * σ θ)
            + Real.cos (2 * θ) * σ θ * (u θ / Real.cos θ) ^ 2) from by
      refine setIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
      ring]
    rw [MeasureTheory.integral_add (hWWint.const_mul 99) hcos2int,
      MeasureTheory.integral_const_mul (99 : ℝ)]
  -- ## assembly
  linarith [hL1, hL2, hsplit, hcon2, hW2]

theorem sliceBarSq2 (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hlim : ∃ c : ℝ, Filter.Tendsto (fun θ => u θ / Real.cos θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds c))
    (h0 : MeasureTheory.IntegrableOn
      (fun θ => (u θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ)
    (h1 : MeasureTheory.IntegrableOn
      (fun θ => (deriv u θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn
      (fun θ => (u θ / Real.cos θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ ∧
    (∫ θ in Work.Spaces.Iθ,
        (u θ / Real.cos θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
      ≤ 100 * ((∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
          + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2
              * Work.FTS.EllipticEst.AngSecond.sig θ)) := by
  have hπ2 : (0 : ℝ) < Real.pi / 2 := Real.pi_div_two_pos
  obtain ⟨c, hc⟩ := hlim
  -- ## abbreviations
  let H : ℝ → ℝ := fun x => (u x) ^ 2 * σ x + (deriv u x) ^ 2 * σ x
  let F : ℝ → ℝ := fun x => (u x / Real.cos x) ^ 2 * σ x
  let q : ℕ → ℝ := fun n => (1 / 2 : ℝ) ^ (n + 2)
  let a_ : ℕ → ℝ := fun n => (Real.pi / 2) * q n
  let b_ : ℕ → ℝ := fun n => (Real.pi / 2) * (1 - q n)
  let s : ℕ → Set ℝ := fun n => Set.Ioo (a_ n) (b_ n)
  -- ## elementary facts about the weight
  have hσnn_Iθ : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ σ θ :=
    fun θ hθ => Work.FTS.EllipticEst.AngSecond.sig_nonneg hθ
  have hσnn_Ioo : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 ≤ σ θ := fun θ hθ =>
    hσnn_Iθ θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hcospos : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 < Real.cos θ := fun θ hθ =>
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩
  -- ## elementary facts about the two sequences
  have hq_pos : ∀ n, 0 < q n := by
    intro n
    simp only [q]
    positivity
  have hq_le : ∀ n, q n ≤ 1 / 4 := by
    intro n
    have h2 : (2 : ℕ) ≤ n + 2 := by omega
    calc q n ≤ (1 / 2 : ℝ) ^ 2 := by
          simp only [q]
          exact pow_le_pow_of_le_one (by norm_num) (by norm_num) h2
      _ = 1 / 4 := by norm_num
  have hq_lt_one : ∀ n, q n < 1 := fun n => lt_of_le_of_lt (hq_le n) (by norm_num)
  have hq_anti : Antitone q := by
    intro m n hmn
    simp only [q]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hq_tend : Filter.Tendsto q Filter.atTop (nhds 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (show (1 / 2 : ℝ) < 1 by norm_num)
    have h2 : Filter.Tendsto (fun n => (1 / 2 : ℝ) ^ n * (1 / 2 : ℝ) ^ 2) Filter.atTop
        (nhds ((0 : ℝ) * (1 / 2 : ℝ) ^ 2)) := h.mul_const _
    rw [zero_mul] at h2
    refine h2.congr' ?_
    filter_upwards with n
    simp only [q]
    rw [pow_add]
  have ha_pos : ∀ n, 0 < a_ n := fun n => by
    simp only [a_]
    exact mul_pos hπ2 (hq_pos n)
  have ha_lt_b : ∀ n, a_ n < b_ n := fun n => by
    have h : q n < 1 - q n := by have := hq_le n; linarith
    have h2 := mul_lt_mul_of_pos_left h hπ2
    simpa only [a_, b_] using h2
  have hb_lt : ∀ n, b_ n < Real.pi / 2 := fun n => by
    have h : 1 - q n < 1 := by have := hq_pos n; linarith
    have h2 := mul_lt_mul_of_pos_left h hπ2
    simpa only [b_, mul_one] using h2
  have hb_pos : ∀ n, 0 < b_ n := fun n => by
    have h : 0 < 1 - q n := by have := hq_lt_one n; linarith
    simp only [b_]
    exact mul_pos hπ2 h
  have ha_lt_pi2 : ∀ n, a_ n < Real.pi / 2 := fun n => by
    have h : q n < 1 := hq_lt_one n
    have h2 := mul_lt_mul_of_pos_left h hπ2
    simpa only [a_, mul_one] using h2
  have hsub : ∀ n, s n ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    intro n x hx
    simp only [s] at hx
    exact ⟨lt_trans (ha_pos n) hx.1, lt_of_lt_of_le hx.2 (le_of_lt (hb_lt n))⟩
  have hs_meas : ∀ n, MeasurableSet (s n) := fun n => by
    simp only [s]
    exact measurableSet_Ioo
  have hs_mono : Monotone s := by
    intro m n hmn
    refine Set.Ioo_subset_Ioo ?_ ?_
    · simp only [a_]
      exact mul_le_mul_of_nonneg_left (hq_anti hmn) hπ2.le
    · have h : q n ≤ q m := hq_anti hmn
      simp only [b_]
      exact mul_le_mul_of_nonneg_left (by linarith) hπ2.le
  have ha_tend : Filter.Tendsto a_ Filter.atTop (nhds 0) := by
    simpa only [a_, mul_zero] using hq_tend.const_mul (Real.pi / 2)
  have hb_tend : Filter.Tendsto b_ Filter.atTop (nhds (Real.pi / 2)) := by
    have h : Filter.Tendsto (fun n => (Real.pi / 2) * (1 - q n)) Filter.atTop
        (nhds ((Real.pi / 2) * (1 - 0))) :=
      (tendsto_const_nhds.sub hq_tend).const_mul (Real.pi / 2)
    simpa only [b_, sub_zero, mul_one] using h
  have hs_cov : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ ⋃ n, s n := by
    intro x hx
    have h1 : ∀ᶠ n in Filter.atTop, a_ n < x := ha_tend.eventually (Iio_mem_nhds hx.1)
    have h2 : ∀ᶠ n in Filter.atTop, x < b_ n := hb_tend.eventually (Ioi_mem_nhds hx.2)
    obtain ⟨n, hn⟩ := (h1.and h2).exists
    exact Set.mem_iUnion.mpr ⟨n, hn.1, hn.2⟩
  have hs_union : (⋃ n, s n) = Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    Set.Subset.antisymm (Set.iUnion_subset hsub) hs_cov
  -- ## integrability on the pieces
  have hs_sub_Iθ : ∀ n, s n ⊆ Work.Spaces.Iθ := by
    intro n x hx
    simp only [s] at hx
    exact ⟨le_of_lt (lt_trans (ha_pos n) hx.1),
      le_of_lt (lt_of_lt_of_le hx.2 (le_of_lt (hb_lt n)))⟩
  have h_UX : ∀ n, MeasureTheory.IntegrableOn (fun x => (u x) ^ 2 * σ x) (s n) :=
    fun n => h0.mono_set (hs_sub_Iθ n)
  have h_VX : ∀ n, MeasureTheory.IntegrableOn (fun x => (deriv u x) ^ 2 * σ x) (s n) :=
    fun n => h1.mono_set (hs_sub_Iθ n)
  have hloc := local_integrable_local u h0
  have h_FX : ∀ n, MeasureTheory.IntegrableOn F (s n) := by
    intro n
    have hmem : s n ⊆ Set.Ioo (0 : ℝ) (b_ n) := by
      intro x hx
      simp only [s] at hx
      exact ⟨lt_trans (ha_pos n) hx.1, hx.2⟩
    have h := (hloc (b_ n) ⟨hb_pos n, hb_lt n⟩).mono_set hmem
    simpa only [F] using h
  have h_FX' : ∀ n, MeasureTheory.IntegrableOn (fun x => (u x / Real.cos x) ^ 2 * σ x) (s n) :=
    fun n => by simpa only [F] using h_FX n
  -- ## the core inequality, piecewise
  have hcore : ∀ n, (∫ x in s n, F x)
      ≤ 100 * (∫ x in s n, H x)
        + 100 * (Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta (b_ n)
            * (u (b_ n) / Real.cos (b_ n)) ^ 2) := by
    intro n
    have hU := h_UX n
    have hV := h_VX n
    have hF := h_FX n
    have hF' := h_FX' n
    -- the core identity, as an identity of set integrals over `s n`
    have hid : (∫ x in s n, (100 * ((u x) ^ 2 * σ x) + 100 * ((deriv u x) ^ 2 * σ x)
          - (u x / Real.cos x) ^ 2 * σ x))
        = 100 * (∫ x in s n, (deriv (fun t : ℝ => u t / Real.cos t) x) ^ 2
              * (Real.cos x) ^ 2 * σ x)
          + (∫ x in s n, (u x / Real.cos x) ^ 2 * σ x * (99 + Real.cos (2 * x)))
          - 100 * (Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta (b_ n)
                * (u (b_ n) / Real.cos (b_ n)) ^ 2
              - Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta (a_ n)
                * (u (a_ n) / Real.cos (a_ n)) ^ 2) := by
      simp only [s]
      exact core_local u hu (ha_pos n) (ha_lt_b n) (hb_lt n)
    -- splitting the left-hand side
    have e1 : (∫ x in s n, (100 * ((u x) ^ 2 * σ x) + 100 * ((deriv u x) ^ 2 * σ x)
          - (u x / Real.cos x) ^ 2 * σ x))
        = (∫ x in s n, (100 * ((u x) ^ 2 * σ x) + 100 * ((deriv u x) ^ 2 * σ x)))
          - ∫ x in s n, (u x / Real.cos x) ^ 2 * σ x :=
      MeasureTheory.integral_sub
        (f := fun x => 100 * ((u x) ^ 2 * σ x) + 100 * ((deriv u x) ^ 2 * σ x))
        (g := fun x => (u x / Real.cos x) ^ 2 * σ x)
        ((hU.const_mul 100).add (hV.const_mul 100)) hF'
    have e2 : (∫ x in s n, (100 * ((u x) ^ 2 * σ x) + 100 * ((deriv u x) ^ 2 * σ x)))
        = 100 * (∫ x in s n, (u x) ^ 2 * σ x)
          + 100 * (∫ x in s n, (deriv u x) ^ 2 * σ x) := by
      rw [MeasureTheory.integral_add
        (f := fun x => 100 * ((u x) ^ 2 * σ x)) (g := fun x => 100 * ((deriv u x) ^ 2 * σ x))
        (hU.const_mul 100) (hV.const_mul 100)]
      rw [MeasureTheory.integral_const_mul (100 : ℝ), MeasureTheory.integral_const_mul (100 : ℝ)]
    have hL : (∫ x in s n, (100 * ((u x) ^ 2 * σ x) + 100 * ((deriv u x) ^ 2 * σ x)
          - (u x / Real.cos x) ^ 2 * σ x))
        = 100 * (∫ x in s n, (u x) ^ 2 * σ x)
          + 100 * (∫ x in s n, (deriv u x) ^ 2 * σ x)
          - ∫ x in s n, (u x / Real.cos x) ^ 2 * σ x := by
      rw [e1, e2]
    have hH : (∫ x in s n, H x)
        = (∫ x in s n, (u x) ^ 2 * σ x) + (∫ x in s n, (deriv u x) ^ 2 * σ x) := by
      rw [show (∫ x in s n, H x)
          = ∫ x in s n, ((u x) ^ 2 * σ x + (deriv u x) ^ 2 * σ x) from by simp only [H]]
      exact MeasureTheory.integral_add (f := fun x => (u x) ^ 2 * σ x)
        (g := fun x => (deriv u x) ^ 2 * σ x) hU hV
    -- nonnegativity of the discarded terms
    have hI1nn : 0 ≤ ∫ x in s n, (deriv (fun t : ℝ => u t / Real.cos t) x) ^ 2
        * (Real.cos x) ^ 2 * σ x := by
      refine setIntegral_nonneg (hs_meas n) (fun x hx => ?_)
      exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (hσnn_Ioo x (hsub n hx))
    have hI2nn : 0 ≤ ∫ x in s n, (u x / Real.cos x) ^ 2 * σ x * (99 + Real.cos (2 * x)) := by
      refine setIntegral_nonneg (hs_meas n) (fun x hx => ?_)
      exact mul_nonneg (mul_nonneg (sq_nonneg _) (hσnn_Ioo x (hsub n hx)))
        (by linarith [Real.neg_one_le_cos (2 * x)])
    have hAnn : 0 ≤ Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta (a_ n)
        * (u (a_ n) / Real.cos (a_ n)) ^ 2 :=
      mul_nonneg (wrho_nonneg_Ioo ⟨ha_pos n, ha_lt_pi2 n⟩) (sq_nonneg _)
    rw [hL] at hid
    rw [hH]
    simp only [F] at hid ⊢
    linarith [hid, hI1nn, hI2nn, hAnn]
  -- ## the monotone-limit step
  have hint : ∀ n, MeasureTheory.IntegrableOn F (s n) := h_FX
  have hnn : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 ≤ F x := by
    intro x hx
    simp only [F]
    exact mul_nonneg (sq_nonneg _) (hσnn_Ioo x hx)
  have hFcont : ContinuousOn F (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have h1c : ContinuousOn (fun x : ℝ => u x / Real.cos x)
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      hu.continuousOn.div Real.continuous_cos.continuousOn
        (fun θ hθ => ne_of_gt (hcospos θ hθ))
    simp only [F]
    exact (h1c.pow 2).mul continuousOn_sig_Ioo
  have haesm : AEStronglyMeasurable F
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict
        (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    hFcont.aestronglyMeasurable measurableSet_Ioo
  have hHint_Ioo : MeasureTheory.IntegrableOn H (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have h : MeasureTheory.IntegrableOn
        (fun x : ℝ => (u x) ^ 2 * σ x + (deriv u x) ^ 2 * σ x)
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      (h0.mono_set (fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩)).add
        (h1.mono_set (fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩))
    simpa only [H] using h
  have hHlim : Filter.Tendsto (fun n => ∫ x in s n, H x) Filter.atTop
      (nhds (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), H x)) := by
    have hHInt : MeasureTheory.IntegrableOn H (⋃ n, s n) := by
      rw [hs_union]
      exact hHint_Ioo
    simpa only [hs_union] using
      MeasureTheory.tendsto_setIntegral_of_monotone hs_meas hs_mono hHInt
  have hb_within : Filter.Tendsto b_ Filter.atTop
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within b_ hb_tend
      (Eventually.of_forall fun n => hb_lt n)
  have hbdlim : Filter.Tendsto (fun n => Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta (b_ n)
      * (u (b_ n) / Real.cos (b_ n)) ^ 2) Filter.atTop (nhds 0) :=
    (sliceBarSq2_boundary_tendsto u ⟨c, hc⟩).comp hb_within
  have hKlim : Filter.Tendsto (fun n => 100 * (∫ x in s n, H x)
      + 100 * (Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta (b_ n)
        * (u (b_ n) / Real.cos (b_ n)) ^ 2)) Filter.atTop
      (nhds (100 * (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), H x))) := by
    have h := (hHlim.const_mul 100).add (hbdlim.const_mul 100)
    simpa using h
  obtain ⟨hFint, hFle⟩ := lintegral_le_of_directed_local (F := F) (s := s)
    (K := fun n => 100 * (∫ x in s n, H x)
      + 100 * (Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta (b_ n)
        * (u (b_ n) / Real.cos (b_ n)) ^ 2))
    hπ2 hs_meas hs_mono hsub hs_cov hint haesm hnn hcore hKlim
  -- ## conclusion
  refine ⟨?_, ?_⟩
  · rw [Work.Spaces.Iθ]
    exact hFint.congr_set_ae MeasureTheory.Ioo_ae_eq_Icc.symm
  · rw [← integral_Ioo_eq_Iθ' (fun x => (u x / Real.cos x) ^ 2 * σ x)]
    have hFle' : (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), (u x / Real.cos x) ^ 2 * σ x)
        ≤ 100 * (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), H x) := by
      simpa only [F] using hFle
    have hHval : (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), H x)
        = (∫ x in Work.Spaces.Iθ, (u x) ^ 2 * σ x)
          + (∫ x in Work.Spaces.Iθ, (deriv u x) ^ 2 * σ x) := by
      rw [show (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), H x)
          = ∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2),
              ((u x) ^ 2 * σ x + (deriv u x) ^ 2 * σ x) from by simp only [H]]
      rw [MeasureTheory.integral_add
        (f := fun x => (u x) ^ 2 * σ x) (g := fun x => (deriv u x) ^ 2 * σ x)
        (h0.mono_set (fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩))
        (h1.mono_set (fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩))]
      rw [integral_Ioo_eq_Iθ' (fun x => (u x) ^ 2 * σ x),
        integral_Ioo_eq_Iθ' (fun x => (deriv u x) ^ 2 * σ x)]
    calc (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), F x)
        ≤ 100 * (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), H x) := hFle
      _ = 100 * ((∫ x in Work.Spaces.Iθ, (u x) ^ 2 * σ x)
            + (∫ x in Work.Spaces.Iθ, (deriv u x) ^ 2 * σ x)) := by rw [hHval]

end Work.FTS.EllipticEst.Honest
