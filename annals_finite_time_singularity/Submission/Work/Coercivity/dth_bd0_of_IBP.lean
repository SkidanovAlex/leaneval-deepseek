/-
# The boundary condition at `z = 0` for `D_θ f`, from `IBP f`

If `f` satisfies the integration-by-parts package `IBP` of `Submission/Work/Coercivity/Defs.lean`
(smoothness on a neighbourhood of the closed quadrant together with the vanishing of the
factor `z (f w)²` at `z = 0` and at `z = ∞`, and the relevant integrabilities), then the
angular derivative `D_θ f = sin(2θ) ∂_θ f` satisfies the *same* vanishing condition at `z = 0`:

  `z (D_θ f(z,θ) w(z))² → 0` as `z → 0⁺`,  for every `θ ∈ [0, π/2]`.

This is the hypothesis needed by the `z`-integration by parts of the `θ`-coercivity estimate
(`Work.Coercivity.thetaDerivative`), applied to `D_θ f` rather than to `f`.

## Proof

`IBP f` gives `z (f w)² → 0`, i.e. `f² (1+z)^4 / z^3 → 0`, hence `|f(z,θ)| = o(z^{3/2})`.
By continuity this forces `f(0,θ) = 0`, and then the difference quotient `f(z,θ)/z = o(z^{1/2})`
forces `∂_z f(0,θ) = 0` (the two-sided derivative exists by smoothness and its value is the
one-sided limit).  Both vanishing statements hold on all of `Iθ`.

Consequently, for `θ` in the interior, the second-order Taylor formula

  `f(z,θ') = ∫_0^z (z-s) ∂_z² f(s,θ') ds`

holds for every `θ'` in a neighbourhood of `θ`; differentiating it in `θ'` at `θ` (via the
mean value theorem for `slope` and the `θ`-regularity of `∂_z² f`) yields

  `∂_θ f(z,θ) = ∫_0^z (z-s) ∂_θ∂_z² f(s,θ) ds`,

whose absolute value is `O(z²)` (the integrand is uniformly bounded on a fixed compact
rectangle).  Hence `(D_θ f)² w² z = O(z) → 0`, and at the endpoints `θ = 0, π/2` the factor
`sin(2θ)` vanishes identically.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.Coercivity.thetaAux
import Submission.Work.Spaces.HardyZ
import Submission.Work.Spaces.CurrySmooth

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-- The open neighbourhood of the closed quadrant on which `SmoothNbhd` requires smoothness. -/
theorem isOpen_box : IsOpen (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π / 2 + 1) : Set (ℝ × ℝ)) :=
  isOpen_Ioi.prod isOpen_Ioo

/-- The `θ`-slice `θ' ↦ q t θ'` of a function smooth on a neighbourhood of the closed quadrant
is differentiable at any interior angle, with derivative `pth q t θ`. -/
theorem hasDerivAt_pth_slice {q : ℝ → ℝ → ℝ} (hq : Spaces.SmoothNbhd q) {t θ : ℝ}
    (ht : t ∈ Set.Ioi (-1)) (hθ : θ ∈ Set.Ioo (-1) (π / 2 + 1)) :
    HasDerivAt (fun θ' => q t θ') (Spaces.pth q t θ) θ := by
  have hmaps : Set.MapsTo (fun θ' : ℝ => (t, θ')) (Set.Ioo (-1) (π / 2 + 1))
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π / 2 + 1)) := fun x hx => ⟨ht, hx⟩
  have hcd : ContDiffOn ℝ ⊤ (fun θ' => q t θ') (Set.Ioo (-1) (π / 2 + 1)) :=
    hq.comp (contDiffOn_const.prodMk contDiffOn_id) hmaps
  exact ((hcd.differentiableOn (by simp)).differentiableAt (isOpen_Ioo.mem_nhds hθ)).hasDerivAt

/-- **Second-order Taylor formula with integral remainder.**  For a function `g` of class `C²`
on `[0,z]`, `g z - z g'(0) - g(0) = ∫_0^z (z - s) g''(s) ds`. -/
theorem integral_zsub_mul_second_deriv (g g' g'' : ℝ → ℝ) {z : ℝ} (hz : 0 ≤ z)
    (hcont : ContinuousOn g (Set.Icc 0 z))
    (hcont' : ContinuousOn g' (Set.Icc 0 z))
    (hcont'' : ContinuousOn g'' (Set.Icc 0 z))
    (hd1 : ∀ x ∈ Set.Ioo 0 z, HasDerivAt g (g' x) x)
    (hd2 : ∀ x ∈ Set.Ioo 0 z, HasDerivAt g' (g'' x) x)
    (h0 : g 0 = 0) (h0' : g' 0 = 0) :
    ∫ x in (0:ℝ)..z, (z - x) * g'' x = g z := by
  have hFcont : ContinuousOn (fun s => g z - g s - (z - s) * g' s) (Set.Icc 0 z) := by
    refine (continuousOn_const.sub hcont).sub ?_
    exact (continuousOn_const.sub continuousOn_id).mul hcont'
  have hFderiv : ∀ x ∈ Set.Ioo 0 z,
      HasDerivAt (fun s => g z - g s - (z - s) * g' s) (-(z - x) * g'' x) x := by
    intro x hx
    have h1 : HasDerivAt (fun s : ℝ => g z - g s) (-(g' x)) x := (hd1 x hx).const_sub (g z)
    have h2 : HasDerivAt (fun s : ℝ => z - s) (-1) x := (hasDerivAt_id x).const_sub z
    have h4 : HasDerivAt (fun s => (z - s) * g' s) ((-1) * g' x + (z - x) * g'' x) x :=
      h2.mul (hd2 x hx)
    have h5 := h1.sub h4
    have heq : -(g' x) - ((-1) * g' x + (z - x) * g'' x) = -(z - x) * g'' x := by ring
    rwa [heq] at h5
  have hint : IntervalIntegrable (fun x => -(z - x) * g'' x) volume 0 z := by
    apply ContinuousOn.intervalIntegrable
    refine ((continuousOn_const.sub continuousOn_id).neg.mul ?_)
    simpa [Set.uIcc_of_le hz] using hcont''
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hz hFcont hFderiv hint
  have hRHS : g z - g z - (z - z) * g' z - (g z - g 0 - (z - 0) * g' 0) = -g z := by
    rw [h0, h0']; ring
  rw [hRHS] at key
  have hneg : (fun y => -(z - y) * g'' y) = fun y => -((z - y) * g'' y) := by
    funext y; ring
  rw [hneg, intervalIntegral.integral_neg] at key
  linarith

/-- **Vanishing of `f` and `∂_z f` at `z = 0`.**  From `IBP f` one gets, for every `θ ∈ Iθ`,
`f(0,θ) = 0` and `∂_z f(0,θ) = 0`. -/
theorem zeros_of_IBP (f : ℝ → ℝ → ℝ) (hf : IBP f) :
    ∀ θ ∈ Spaces.Iθ, f 0 θ = 0 ∧ Spaces.pz f 0 θ = 0 := by
  intro θ hθ
  have bd := hf.bd0 θ hθ
  have hA1 : Tendsto (fun z => (f z θ)^2 * (1 + z)^4 / z^3) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    refine bd.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz0 : z ≠ 0 := ne_of_gt hz
    simp only [Spaces.w]
    field_simp
  have hX3 : Tendsto (fun z : ℝ => z^3/(1+z)^4) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h : ContinuousAt (fun z : ℝ => z^3/(1+z)^4) 0 := by
      have h1 : ContinuousAt (fun z : ℝ => z^3) 0 := by fun_prop
      have h2 : ContinuousAt (fun z : ℝ => (1+z)^4) 0 := by fun_prop
      exact h1.div h2 (by norm_num)
    have hh : Tendsto (fun z : ℝ => z^3/(1+z)^4) (𝓝 (0:ℝ)) (𝓝 (0^3/(1+0)^4)) := h.tendsto
    have h2 : (0:ℝ)^3/(1+0)^4 = 0 := by norm_num
    rw [h2] at hh
    exact hh.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  have hX1 : Tendsto (fun z : ℝ => z/(1+z)^4) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h : ContinuousAt (fun z : ℝ => z/(1+z)^4) 0 := by
      have h1 : ContinuousAt (fun z : ℝ => z) 0 := by fun_prop
      have h2 : ContinuousAt (fun z : ℝ => (1+z)^4) 0 := by fun_prop
      exact h1.div h2 (by norm_num)
    have hh : Tendsto (fun z : ℝ => z/(1+z)^4) (𝓝 (0:ℝ)) (𝓝 (0/(1+0)^4)) := h.tendsto
    have h2 : (0:ℝ)/(1+0)^4 = 0 := by norm_num
    rw [h2] at hh
    exact hh.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  have hflim : Tendsto (fun z => f z θ) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hAsq : Tendsto (fun z => (f z θ)^2) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      have h := hA1.mul hX3
      simp only [mul_zero] at h
      refine h.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with z hz
      have hz0 : z ≠ 0 := ne_of_gt hz
      have h1z : (1:ℝ)+z ≠ 0 := by have hzp : (0:ℝ) < z := hz; linarith
      field_simp
    have habs : Tendsto (fun z => |f z θ|) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      have h := Real.continuous_sqrt.continuousAt.tendsto.comp hAsq
      rw [Real.sqrt_zero] at h
      refine h.congr' ?_
      filter_upwards with z
      simp only [Function.comp_apply, Real.sqrt_sq_eq_abs]
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [Real.norm_eq_abs] using habs
  have hcont0 : Tendsto (fun z => f z θ) (𝓝 (0:ℝ)) (𝓝 (f 0 θ)) :=
    ((Spaces.hardyZ_contDiffOn_slice f hf.smooth hθ).continuousOn.continuousAt
      (isOpen_Ioi.mem_nhds (by simp [Set.mem_Ioi]))).tendsto
  have hf0 : f 0 θ = 0 :=
    tendsto_nhds_unique (hcont0.mono_left nhdsWithin_le_nhds) hflim
  refine ⟨hf0, ?_⟩
  have hdiv0 : Tendsto (fun z => f z θ / z) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hs2 : Tendsto (fun z => (f z θ / z)^2) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      have h := hA1.mul hX1
      simp only [mul_zero] at h
      refine h.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with z hz
      have hz0 : z ≠ 0 := ne_of_gt hz
      have h1z : (1:ℝ)+z ≠ 0 := by have hzp : (0:ℝ) < z := hz; linarith
      field_simp
    have habs : Tendsto (fun z => |f z θ / z|) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      have h := Real.continuous_sqrt.continuousAt.tendsto.comp hs2
      rw [Real.sqrt_zero] at h
      refine h.congr' ?_
      filter_upwards with z
      simp only [Function.comp_apply, Real.sqrt_sq_eq_abs]
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [Real.norm_eq_abs] using habs
  have hslope : Tendsto (fun z => f z θ / z) (𝓝[>] (0:ℝ)) (𝓝 (Spaces.pz f 0 θ)) := by
    have hd := Spaces.hardyZ_hasDerivAt_slice f hf.smooth hθ (z := 0) (by simp [Set.mem_Ioi])
    have hsl := hd.tendsto_slope
    have hle : 𝓝[>] (0:ℝ) ≤ 𝓝[≠] (0:ℝ) := by
      apply nhdsWithin_mono
      intro x hx; exact ne_of_gt hx
    refine (hsl.mono_left hle).congr' ?_
    filter_upwards with z
    rw [slope]
    simp only [sub_zero, hf0, smul_eq_mul]
    rw [vsub_eq_sub, sub_zero, div_eq_inv_mul]
  exact tendsto_nhds_unique hslope hdiv0

/-- **The `O(z²)` bound for the angular derivative.**  If `f` is smooth on a neighbourhood of
the closed quadrant, `θ` is an interior angle and `f(0,·) ≡ 0`, `∂_z f(0,·) ≡ 0` in a
neighbourhood of `θ`, then `∂_θ f(z,θ) = O(z²)` as `z → 0⁺`. -/
theorem pth_le_sq (f : ℝ → ℝ → ℝ) (hf : Spaces.SmoothNbhd f) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π/2))
    (hzero : ∀ᶠ θ' in 𝓝 θ, f 0 θ' = 0 ∧ Spaces.pz f 0 θ' = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ z in 𝓝[>] (0:ℝ), |Spaces.pth f z θ| ≤ C * z ^ 2 := by
  classical
  obtain ⟨s, hs_mem, hs_sub⟩ := Filter.eventually_iff_exists_mem.mp hzero
  obtain ⟨ε, hεpos, hεsub⟩ := Metric.mem_nhds_iff.mp hs_mem
  set X : ℝ := min ε (min θ (π/2 - θ)) with hXdef
  set r : ℝ := X/2 with hrdef
  have hθpos : 0 < θ := hθ.1
  have hθlt : θ < π/2 := hθ.2
  have hπθ : 0 < π/2 - θ := by linarith
  have hXpos : 0 < X := by rw [hXdef]; exact lt_min hεpos (lt_min hθpos hπθ)
  have hrpos : 0 < r := by rw [hrdef]; linarith
  have hXθ : X ≤ θ := le_trans (min_le_right ε (min θ (π/2 - θ))) (min_le_left θ (π/2 - θ))
  have hXπ : X ≤ π/2 - θ := le_trans (min_le_right ε (min θ (π/2 - θ))) (min_le_right θ (π/2 - θ))
  have hrθ : r < θ := by rw [hrdef]; linarith
  have hrπ : r < π/2 - θ := by rw [hrdef]; linarith
  have hrε : r ≤ ε := by rw [hrdef]; linarith [min_le_left ε (min θ (π/2 - θ))]
  have hzero' : ∀ θ' ∈ Set.Ioo (θ-r) (θ+r), f 0 θ' = 0 ∧ Spaces.pz f 0 θ' = 0 := by
    intro θ' hθ'
    refine hs_sub θ' (hεsub ?_)
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith [hθ'.1, hrε], by linarith [hθ'.2, hrε]⟩
  have hIθmem : ∀ θ' ∈ Set.Ioo (θ-r) (θ+r), θ' ∈ Spaces.Iθ := by
    intro θ' hθ'
    exact ⟨by linarith [hθ'.1, hrθ], by linarith [hθ'.2, hrπ]⟩
  have hpz_smooth : Spaces.SmoothNbhd (Spaces.pz f) :=
    Spaces.contDiffOn_uncurry_pz isOpen_box hf
  have hq_smooth : Spaces.SmoothNbhd (Spaces.pz (Spaces.pz f)) :=
    Spaces.contDiffOn_uncurry_pz isOpen_box hpz_smooth
  have hpthq_smooth : Spaces.SmoothNbhd (Spaces.pth (Spaces.pz (Spaces.pz f))) :=
    Spaces.contDiffOn_uncurry_pth isOpen_box hq_smooth
  have hKsub : Set.Icc (0:ℝ) (1/2) ×ˢ Set.Icc (θ-r) (θ+r) ⊆
      Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π/2+1) := by
    intro p hp
    refine ⟨?_, ?_⟩
    · simp only [Set.mem_Ioi]; linarith [hp.1.1]
    · simp only [Set.mem_Ioo]
      exact ⟨by linarith [hp.2.1, hrθ], by linarith [hp.2.2, hrπ]⟩
  have hKcomp : IsCompact (Set.Icc (0:ℝ) (1/2) ×ˢ Set.Icc (θ-r) (θ+r)) :=
    isCompact_Icc.prod isCompact_Icc
  have hKcont : ContinuousOn (Function.uncurry (Spaces.pth (Spaces.pz (Spaces.pz f))))
      (Set.Icc (0:ℝ) (1/2) ×ˢ Set.Icc (θ-r) (θ+r)) :=
    hpthq_smooth.continuousOn.mono hKsub
  obtain ⟨M, hM⟩ := IsCompact.exists_bound_of_continuousOn hKcomp hKcont
  have hMnonneg : 0 ≤ M :=
    le_trans (norm_nonneg _) (hM (0, θ) ⟨⟨le_refl 0, by norm_num⟩, ⟨by linarith, by linarith⟩⟩)
  have hkey : ∀ z ∈ Set.Ioo (0:ℝ) (1/2), |Spaces.pth f z θ| ≤ M * z^2 := by
    intro z hz
    have hz0 : (0:ℝ) < z := hz.1
    have hzle : z ≤ 1/2 := le_of_lt hz.2
    have hz0le : (0:ℝ) ≤ z := le_of_lt hz0
    have hzmem : z ∈ Set.Ioi (-1) := by simp only [Set.mem_Ioi]; linarith
    have hθmemI : θ ∈ Set.Ioo (-1) (π/2+1) := ⟨by linarith, by linarith⟩
    have hθint : θ ∈ Set.Ioo (θ-r) (θ+r) := ⟨by linarith, by linarith⟩
    have hTP : ∀ θ' ∈ Set.Ioo (θ-r) (θ+r),
        f z θ' = ∫ x in (0:ℝ)..z, (z-x)*(Spaces.pz (Spaces.pz f)) x θ' := by
      intro θ' hθ'
      have hθ'Iθ : θ' ∈ Spaces.Iθ := hIθmem θ' hθ'
      have hz' := hzero' θ' hθ'
      have hsubmem : Set.Icc (0:ℝ) z ⊆ Set.Ioi (-1) := fun x hx => by
        simp only [Set.mem_Ioi]; linarith [hx.1]
      have hc1 : ContinuousOn (fun x => f x θ') (Set.Icc (0:ℝ) z) :=
        (Spaces.hardyZ_contDiffOn_slice f hf hθ'Iθ).continuousOn.mono hsubmem
      have hc2 : ContinuousOn (fun x => Spaces.pz f x θ') (Set.Icc (0:ℝ) z) :=
        (Spaces.hardyZ_contDiffOn_slice (Spaces.pz f) hpz_smooth hθ'Iθ).continuousOn.mono hsubmem
      have hc3 : ContinuousOn (fun x => Spaces.pz (Spaces.pz f) x θ') (Set.Icc (0:ℝ) z) :=
        (Spaces.hardyZ_contDiffOn_slice (Spaces.pz (Spaces.pz f)) hq_smooth hθ'Iθ).continuousOn.mono hsubmem
      have hd1 : ∀ x ∈ Set.Ioo (0:ℝ) z, HasDerivAt (fun x => f x θ') (Spaces.pz f x θ') x :=
        fun x hx => Spaces.hardyZ_hasDerivAt_slice f hf hθ'Iθ (by simp only [Set.mem_Ioi]; linarith [hx.1])
      have hd2 : ∀ x ∈ Set.Ioo (0:ℝ) z, HasDerivAt (fun x => Spaces.pz f x θ') (Spaces.pz (Spaces.pz f) x θ') x :=
        fun x hx => Spaces.hardyZ_hasDerivAt_slice (Spaces.pz f) hpz_smooth hθ'Iθ (by simp only [Set.mem_Ioi]; linarith [hx.1])
      exact (integral_zsub_mul_second_deriv (fun x => f x θ') (fun x => Spaces.pz f x θ')
        (fun x => Spaces.pz (Spaces.pz f) x θ') hz0le hc1 hc2 hc3 hd1 hd2 hz'.1 hz'.2).symm
    have heqF : (fun θ' => ∫ x in (0:ℝ)..z, (z-x)*(Spaces.pz (Spaces.pz f)) x θ') =ᶠ[𝓝 θ]
        (fun θ' => f z θ') := by
      filter_upwards [isOpen_Ioo.mem_nhds hθint] with θ' hθ'
      exact (hTP θ' hθ').symm
    have hdF : HasDerivAt (fun θ' => f z θ') (Spaces.pth f z θ) θ :=
      hasDerivAt_pth_slice hf hzmem hθmemI
    have hD : HasDerivAt (fun θ' => ∫ x in (0:ℝ)..z, (z-x)*(Spaces.pz (Spaces.pz f)) x θ')
        (Spaces.pth f z θ) θ := hdF.congr_of_eventuallyEq heqF
    have hMVT : ∀ s' ∈ Set.Icc (0:ℝ) z, ∀ θ' ∈ Set.Icc (θ-r) (θ+r),
        |(Spaces.pz (Spaces.pz f)) s' θ' - (Spaces.pz (Spaces.pz f)) s' θ| ≤ M * |θ' - θ| := by
      intro s' hs' θ' hθ'
      have hs1 : s' ∈ Set.Ioi (-1) := by simp only [Set.mem_Ioi]; linarith [hs'.1]
      have hconv : Convex ℝ (Set.Icc (θ-r) (θ+r)) := convex_Icc _ _
      have hmemθ : θ ∈ Set.Icc (θ-r) (θ+r) := ⟨by linarith, by linarith⟩
      have hdiff : ∀ t ∈ Set.Icc (θ-r) (θ+r),
          DifferentiableAt ℝ (fun t' => (Spaces.pz (Spaces.pz f)) s' t') t := by
        intro t ht
        have ht1 : t ∈ Set.Ioo (-1) (π/2+1) :=
          ⟨by linarith [ht.1, hrθ], by linarith [ht.2, hrπ]⟩
        exact (hasDerivAt_pth_slice hq_smooth hs1 ht1).differentiableAt
      have hdb : ∀ t ∈ Set.Icc (θ-r) (θ+r),
          ‖deriv (fun t' => (Spaces.pz (Spaces.pz f)) s' t') t‖ ≤ M := by
        intro t ht
        have hb := hM (s', t) ⟨⟨hs'.1, by linarith [hs'.2, hzle]⟩, ht⟩
        rw [Real.norm_eq_abs] at hb
        simpa [Spaces.pth] using hb
      have := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hdb hconv hmemθ hθ'
      simpa [Real.norm_eq_abs] using this
    have hcontq : ∀ θ' ∈ Spaces.Iθ,
        ContinuousOn (fun x => (Spaces.pz (Spaces.pz f)) x θ') (Set.Icc (0:ℝ) z) :=
      fun θ' hθ' => (Spaces.hardyZ_contDiffOn_slice (Spaces.pz (Spaces.pz f)) hq_smooth hθ').continuousOn.mono
        (fun x hx => by simp only [Set.mem_Ioi]; linarith [hx.1])
    have hII : ∀ {u : ℝ → ℝ}, ContinuousOn u (Set.Icc (0:ℝ) z) → IntervalIntegrable u volume 0 z := by
      intro u hu
      have : ContinuousOn u (Set.uIcc (0:ℝ) z) := by rwa [Set.uIcc_of_le hz0le]
      exact this.intervalIntegrable
    have hslope_bd : ∀ᶠ hh in 𝓝[≠] θ,
        ‖slope (fun θ' => ∫ x in (0:ℝ)..z, (z-x)*(Spaces.pz (Spaces.pz f)) x θ') θ hh‖ ≤ M * z^2 := by
      filter_upwards [show Set.Ioo (θ-r) (θ+r) ∈ 𝓝[≠] θ from
          nhdsWithin_le_nhds (s := {θ}ᶜ) (isOpen_Ioo.mem_nhds hθint),
        self_mem_nhdsWithin] with hh hhh hne
      have hhIθ : hh ∈ Spaces.Iθ := hIθmem hh hhh
      have hzcont : ∀ θ' ∈ Spaces.Iθ,
          ContinuousOn (fun x => (z-x)*(Spaces.pz (Spaces.pz f)) x θ') (Set.Icc (0:ℝ) z) :=
        fun θ' hθ' => (continuous_const.sub continuous_id).continuousOn.mul (hcontq θ' hθ')
      have hI1 : IntervalIntegrable (fun x => (z-x)*(Spaces.pz (Spaces.pz f)) x hh) volume 0 z :=
        hII (hzcont hh hhIθ)
      have hI2 : IntervalIntegrable (fun x => (z-x)*(Spaces.pz (Spaces.pz f)) x θ) volume 0 z :=
        hII (hzcont θ (hIθmem θ hθint))
      have hIntBd : ‖(∫ x in (0:ℝ)..z, (z-x)*(Spaces.pz (Spaces.pz f)) x hh)
            - (∫ x in (0:ℝ)..z, (z-x)*(Spaces.pz (Spaces.pz f)) x θ)‖ ≤ M * |hh - θ| * z^2 := by
        have hlin : (∫ x in (0:ℝ)..z, (z-x)*(Spaces.pz (Spaces.pz f)) x hh)
              - (∫ x in (0:ℝ)..z, (z-x)*(Spaces.pz (Spaces.pz f)) x θ)
            = ∫ x in (0:ℝ)..z, (z-x)*((Spaces.pz (Spaces.pz f)) x hh - (Spaces.pz (Spaces.pz f)) x θ) := by
          rw [← intervalIntegral.integral_sub hI1 hI2]
          apply intervalIntegral.integral_congr
          intro x hx; ring
        rw [hlin]
        have hcAabs : IntervalIntegrable
            (fun x => (z-x)*|(Spaces.pz (Spaces.pz f)) x hh - (Spaces.pz (Spaces.pz f)) x θ|) volume 0 z :=
          hII ((continuous_const.sub continuous_id).continuousOn.mul
            ((hcontq hh hhIθ).sub (hcontq θ (hIθmem θ hθint))).abs)
        have hcB : IntervalIntegrable (fun x => (z-x)*(M * |hh - θ|)) volume 0 z :=
          hII ((continuous_const.sub continuous_id).continuousOn.mul continuousOn_const)
        have hcC : IntervalIntegrable (fun x => z*(M * |hh - θ|)) volume 0 z :=
          hII (continuousOn_const : ContinuousOn (fun _ : ℝ => z * (M * |hh - θ|)) (Set.Icc (0:ℝ) z))
        calc ‖∫ x in (0:ℝ)..z, (z-x)*((Spaces.pz (Spaces.pz f)) x hh - (Spaces.pz (Spaces.pz f)) x θ)‖
            ≤ ∫ x in (0:ℝ)..z, ‖(z-x)*((Spaces.pz (Spaces.pz f)) x hh - (Spaces.pz (Spaces.pz f)) x θ)‖ :=
              intervalIntegral.norm_integral_le_integral_norm hz0le
          _ = ∫ x in (0:ℝ)..z, (z-x)*|(Spaces.pz (Spaces.pz f)) x hh - (Spaces.pz (Spaces.pz f)) x θ| := by
              apply intervalIntegral.integral_congr
              intro x hx
              rw [Set.uIcc_of_le hz0le] at hx
              simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by linarith [hx.2] : (0:ℝ) ≤ z - x)]
          _ ≤ ∫ x in (0:ℝ)..z, (z-x)*(M * |hh - θ|) := by
              apply intervalIntegral.integral_mono_on hz0le
              · exact hcAabs
              · exact hcB
              · intro x hx
                exact mul_le_mul_of_nonneg_left (hMVT x hx hh ⟨le_of_lt hhh.1, le_of_lt hhh.2⟩) (by linarith [hx.2])
          _ ≤ ∫ x in (0:ℝ)..z, z*(M * |hh - θ|) := by
              apply intervalIntegral.integral_mono_on hz0le
              · exact hcB
              · exact hcC
              · intro x hx
                exact mul_le_mul_of_nonneg_right (by linarith [hx.1]) (mul_nonneg hMnonneg (abs_nonneg _))
          _ = M * |hh - θ| * z^2 := by
              rw [intervalIntegral.integral_const, smul_eq_mul]; ring
      have hsl : slope (fun θ' => ∫ x in (0:ℝ)..z, (z-x)*(Spaces.pz (Spaces.pz f)) x θ') θ hh
          = (hh-θ)⁻¹ * ((∫ x in (0:ℝ)..z, (z-x)*(Spaces.pz (Spaces.pz f)) x hh)
              - (∫ x in (0:ℝ)..z, (z-x)*(Spaces.pz (Spaces.pz f)) x θ)) := by
        rw [slope]
        simp only [smul_eq_mul, vsub_eq_sub]
      rw [hsl, norm_mul, Real.norm_eq_abs, abs_inv]
      calc |hh - θ|⁻¹ * ‖(∫ x in (0:ℝ)..z, (z-x)*(Spaces.pz (Spaces.pz f)) x hh)
              - (∫ x in (0:ℝ)..z, (z-x)*(Spaces.pz (Spaces.pz f)) x θ)‖
            ≤ |hh - θ|⁻¹ * (M * |hh - θ| * z^2) := mul_le_mul_of_nonneg_left hIntBd (by positivity)
        _ = M*z^2 := by
            rw [show M * |hh - θ| * z^2 = |hh - θ| * (M*z^2) by ring,
                ← mul_assoc, inv_mul_cancel₀ (abs_ne_zero.mpr (sub_ne_zero.mpr hne)), one_mul]
    have hlim := hD.tendsto_slope.norm
    have hfin := le_of_tendsto hlim hslope_bd
    simpa [Real.norm_eq_abs] using hfin
  refine ⟨max M 1, by positivity, ?_⟩
  filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1/2 by norm_num)] with z hz
  calc |Spaces.pth f z θ| ≤ M * z^2 := hkey z hz
    _ ≤ max M 1 * z^2 := mul_le_mul_of_nonneg_right (le_max_left M 1) (by positivity)

theorem dth_bd0_of_IBP (f : ℝ → ℝ → ℝ) (hf : IBP f) : ∀ θ ∈ Spaces.Iθ, Filter.Tendsto (fun z => z * (Spaces.Dth f z θ * Spaces.w z) ^ 2) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  intro θ hθ
  rcases eq_or_lt_of_le hθ.1 with h0 | hpos
  · subst h0
    have hz : (fun z => z * (Spaces.Dth f z 0 * Spaces.w z) ^ 2) = fun _ => (0:ℝ) := by
      funext z; simp [Spaces.Dth]
    rw [hz]; exact tendsto_const_nhds
  rcases eq_or_lt_of_le hθ.2 with hπ | hlt
  · subst hπ
    have hsin : Real.sin (2 * (π/2)) = 0 := by
      rw [show (2:ℝ) * (π/2) = π by ring, Real.sin_pi]
    have hz : (fun z => z * (Spaces.Dth f z (π/2) * Spaces.w z) ^ 2) = fun _ => (0:ℝ) := by
      funext z; simp [Spaces.Dth, hsin]
    rw [hz]; exact tendsto_const_nhds
  have hθIoo : θ ∈ Set.Ioo 0 (π/2) := ⟨hpos, hlt⟩
  have hzev : ∀ᶠ θ' in 𝓝 θ, f 0 θ' = 0 ∧ Spaces.pz f 0 θ' = 0 := by
    filter_upwards [isOpen_Ioo.mem_nhds hθIoo] with θ' hθ'
    exact zeros_of_IBP f hf θ' ⟨hθ'.1.le, hθ'.2.le⟩
  obtain ⟨C, hCpos, hCf⟩ := pth_le_sq f hf.smooth hθIoo hzev
  have hsp : ∀ᶠ z in 𝓝[>] (0:ℝ),
      ‖z * (Spaces.Dth f z θ * Spaces.w z)^2‖ ≤ C^2 * (z*(1+z)^4) := by
    filter_upwards [hCf, self_mem_nhdsWithin] with z hzC hzpos
    have hz0le : (0:ℝ) ≤ z := le_of_lt hzpos
    have hp2 : (Spaces.pth f z θ)^2 ≤ (C * z^2)^2 := by
      rw [← sq_abs (Spaces.pth f z θ)]
      exact pow_le_pow_left₀ (abs_nonneg _) hzC 2
    have hsp' : (Real.sin (2*θ) * Spaces.pth f z θ)^2 ≤ (C * z^2)^2 := by
      have h1 : |Real.sin (2*θ) * Spaces.pth f z θ| ≤ C * z^2 := by
        rw [abs_mul]
        calc |Real.sin (2*θ)| * |Spaces.pth f z θ| ≤ 1 * (C*z^2) :=
              mul_le_mul (Real.abs_sin_le_one _) hzC (abs_nonneg _) (by norm_num)
          _ = C*z^2 := by ring
      rw [← sq_abs (Real.sin (2*θ) * Spaces.pth f z θ)]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    have hz0 : z ≠ 0 := ne_of_gt hzpos
    have hw2 : (Spaces.w z)^2 * z^4 = (1+z)^4 := by rw [Spaces.w]; field_simp
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Spaces.Dth]
    calc z * ((Real.sin (2*θ) * Spaces.pth f z θ) * Spaces.w z)^2
        = z * (Real.sin (2*θ) * Spaces.pth f z θ)^2 * (Spaces.w z)^2 := by ring
      _ ≤ z * (C*z^2)^2 * (Spaces.w z)^2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsp' hz0le) (sq_nonneg _)
      _ = C^2 * (z*(1+z)^4) := by
          rw [show z * (C*z^2)^2 * (Spaces.w z)^2 = C^2 * (z * ((Spaces.w z)^2 * z^4)) by ring, hw2]
  have hup : Tendsto (fun z => C^2 * (z*(1+z)^4)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h1 : Tendsto (fun z : ℝ => z*(1+z)^4) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      have hc : Continuous (fun z : ℝ => z*(1+z)^4) := by fun_prop
      have hh := hc.tendsto (0:ℝ)
      rw [show (0:ℝ)*(1+0)^4 = 0 by norm_num] at hh
      exact hh.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa using tendsto_const_nhds.mul h1
  rw [tendsto_zero_iff_norm_tendsto_zero]
  exact squeeze_zero' (Filter.Eventually.of_forall (fun z => norm_nonneg _)) hsp hup

end Work.Coercivity
