import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.H2.HhardZibp
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

/-! ## Auxiliary lemmas for `ZibpLimit`

The primitive `u z = ∫_θ ZG α f g z θ` satisfies the pointwise bound
`|u z| ≤ (M/2) z w(z)² V(z)` with `V(z) = ∫_θ ZU α g z θ` (`abs_ZibpU_le`), and a function
dominated below by `c/z` on a ray `[Z,∞)` or near `0⁺`, with `c > 0`, cannot be integrable on
`[0,∞)` (`not_integrableOn_Ici_of_le_inv_atTop`, `not_integrableOn_Ici_of_le_inv_nearZero`).
Both facts use the divergence of `∫ z⁻¹`: the function `log` is differentiable with
`deriv log = 1/z` and `‖log z‖ → ∞` along the relevant filter, so Mathlib's
`not_integrableOn_of_tendsto_norm_atTop_of_deriv_isBigO_filter` applies as soon as the
dominating lower bound shows `deriv log = O F`. -/

/-- The angular slice of a function smooth on a neighbourhood of the closed quadrant. -/
theorem continuousOn_thetaSlice {h : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd h)
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    ContinuousOn (fun θ => h z θ) Work.Spaces.Iθ := by
  have hz' : (-1 : ℝ) < z := by
    have h1 : 0 ≤ z := hz
    linarith
  have hcomp : ContinuousOn (fun θ : ℝ => (z, θ)) Work.Spaces.Iθ :=
    continuousOn_const.prodMk continuousOn_id
  have hbox : ContinuousOn (Function.uncurry h)
      (Set.Ioi (-1 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (π / 2 + 1)) := hsm.continuousOn
  have h : ContinuousOn (fun θ : ℝ => Function.uncurry h (z, θ)) Work.Spaces.Iθ :=
    hbox.comp hcomp (fun θ hθ =>
      ⟨hz', ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩⟩)
  exact h

/-- The pointwise bound on the integrand of the primitive: on the quadrant, `ZG` is dominated
by `(M/2) z w(z)² ZU`, using `|f| ≤ M`, `z ≥ 0` and `ZU ≥ 0`. -/
theorem abs_ZG_le {α : ℝ} {f g : ℝ → ℝ → ℝ} {M z θ : ℝ} (hM : 0 ≤ M) (hz : 0 < z)
    (hθ : θ ∈ Work.Spaces.Iθ) (hf : |f z θ| ≤ M) :
    |ZG α f g z θ| ≤ (M / 2) * z * (Work.Spaces.w z) ^ 2 * ZU α g z θ := by
  have hU := ZU_nonneg (α := α) (g := g) (z := z) hθ
  have heq : |ZG α f g z θ|
      = ((1 / 2) * |f z θ|) * (z * (Work.Spaces.w z) ^ 2 * ZU α g z θ) := by
    rw [ZG, abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 2),
      abs_of_pos hz, abs_of_nonneg (sq_nonneg (Work.Spaces.w z)), abs_of_nonneg hU]
    ring
  rw [heq]
  have h3 : (1 / 2) * |f z θ| ≤ (1 / 2) * M := by linarith
  calc ((1 / 2) * |f z θ|) * (z * (Work.Spaces.w z) ^ 2 * ZU α g z θ)
      ≤ ((1 / 2) * M) * (z * (Work.Spaces.w z) ^ 2 * ZU α g z θ) :=
        mul_le_mul_of_nonneg_right h3 (mul_nonneg (mul_nonneg hz.le (sq_nonneg _)) hU)
    _ = (M / 2) * z * (Work.Spaces.w z) ^ 2 * ZU α g z θ := by ring

/-- **The pointwise bound on the primitive.**  For `z > 0`,
`|∫_θ ZG α f g z θ| ≤ (M/2) z w(z)² ∫_θ ZU α g z θ`. -/
theorem abs_ZibpU_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f g : ℝ → ℝ → ℝ}
    (hsmf : Work.Spaces.SmoothNbhd f) (hsmg : Work.Spaces.SmoothNbhd g) {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, |f z θ| ≤ M) {z : ℝ} (hz : 0 < z) :
    |∫ θ in Work.Spaces.Iθ, ZG α f g z θ|
      ≤ (M / 2) * z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, ZU α g z θ) := by
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hUint : IntegrableOn (fun θ => ZU α g z θ) Work.Spaces.Iθ :=
    ZU_integrable_theta hsmg hα hα1 hz
  have hCint : IntegrableOn
      (fun θ => (M / 2) * z * (Work.Spaces.w z) ^ 2 * ZU α g z θ) Work.Spaces.Iθ :=
    hUint.const_mul _
  have hbound : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      |ZG α f g z θ| ≤ (M / 2) * z * (Work.Spaces.w z) ^ 2 * ZU α g z θ := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    exact abs_ZG_le hM hz hθ (hf z hzI θ hθ)
  calc |∫ θ in Work.Spaces.Iθ, ZG α f g z θ|
      ≤ ∫ θ in Work.Spaces.Iθ, |ZG α f g z θ| := abs_integral_le_integral_abs
    _ ≤ ∫ θ in Work.Spaces.Iθ, (M / 2) * z * (Work.Spaces.w z) ^ 2 * ZU α g z θ :=
        integral_mono_of_nonneg (ae_of_all _ fun θ => abs_nonneg _) hCint hbound
    _ = (M / 2) * z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, ZU α g z θ) :=
        integral_const_mul _ _

/-- A function that dominates `c/z` (`c > 0`) on a ray `[Z,∞)` with `Z ≥ 0` is not integrable
on `[0,∞)`: the primitive `log` is differentiable there with `deriv log = 1/z` and
`‖log z‖ → ∞`. -/
theorem not_integrableOn_Ici_of_le_inv_atTop {F : ℝ → ℝ} {c Z : ℝ} (hc : 0 < c) (hZ : 0 ≤ Z)
    (hF : ∀ z, Z ≤ z → c / z ≤ F z) :
    ¬ IntegrableOn F (Set.Ici 0) := by
  intro hmem
  have hmem' : IntegrableOn F (Set.Ici Z) := hmem.mono_set (Set.Ici_subset_Ici.2 hZ)
  refine not_integrableOn_of_tendsto_norm_atTop_of_deriv_isBigO_filter (E := ℝ) (F := ℝ)
    (f := Real.log) (g := F) (k := Set.Ici Z) atTop (Filter.Ici_mem_atTop Z) ?_ ?_ ?_ hmem'
  · filter_upwards [Filter.Ioi_mem_atTop (0:ℝ)] with x hx
    exact (Real.hasDerivAt_log (ne_of_gt hx)).differentiableAt
  · have hA : Tendsto (fun x : ℝ => |Real.log x|) atTop atTop :=
      tendsto_abs_atTop_atTop.comp Real.tendsto_log_atTop
    simpa only [Real.norm_eq_abs] using hA
  · have h1 : deriv Real.log =O[atTop] (fun x : ℝ => x⁻¹) :=
      Filter.EventuallyEq.isBigO (by
        filter_upwards [Filter.Ioi_mem_atTop (0:ℝ)] with x hx
        exact (Real.hasDerivAt_log (ne_of_gt hx)).deriv)
    refine h1.trans (Asymptotics.IsBigO.of_bound c⁻¹ ?_)
    filter_upwards [Filter.Ici_mem_atTop (max Z 1)] with x hx
    have hxZ : Z ≤ x := le_trans (le_max_left _ _) hx
    have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx
    have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
    have hFx : 0 ≤ F x := le_trans (div_nonneg hc.le hx0.le) (hF x hxZ)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hFx, abs_of_pos (inv_pos.2 hx0),
      inv_mul_eq_div, le_div_iff₀ hc]
    have hcx : c ≤ F x * x := (div_le_iff₀ hx0).1 (hF x hxZ)
    have hcx' : c * x⁻¹ ≤ F x := by
      have h := mul_le_mul_of_nonneg_right hcx (inv_nonneg.2 hx0.le)
      rwa [mul_assoc, mul_inv_cancel₀ (ne_of_gt hx0), mul_one] at h
    linarith [hcx', mul_comm c x⁻¹]

/-- A function that dominates `c/z` (`c > 0`) near `0⁺`, on some interval `(0,ε)`, is not
integrable on `[0,∞)`. -/
theorem not_integrableOn_Ici_of_le_inv_nearZero {F : ℝ → ℝ} {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε)
    (hF : ∀ z, 0 < z → z < ε → c / z ≤ F z) :
    ¬ IntegrableOn F (Set.Ici 0) := by
  intro hmem
  have hmem' : IntegrableOn F (Set.Ioo 0 ε) := hmem.mono_set (fun x hx => le_of_lt hx.1)
  refine not_integrableOn_of_tendsto_norm_atTop_of_deriv_isBigO_filter (E := ℝ) (F := ℝ)
    (f := Real.log) (g := F) (k := Set.Ioo 0 ε) (𝓝[>] (0:ℝ))
    ((nhdsGT_basis 0).mem_iff.2 ⟨ε, hε, subset_rfl⟩) ?_ ?_ ?_ hmem'
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact (Real.hasDerivAt_log (ne_of_gt hx)).differentiableAt
  · have hA : Tendsto (fun x : ℝ => |Real.log x|) (𝓝[>] (0:ℝ)) atTop :=
      tendsto_abs_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
    simpa only [Real.norm_eq_abs] using hA
  · have h1 : deriv Real.log =O[𝓝[>] (0:ℝ)] (fun x : ℝ => x⁻¹) :=
      Filter.EventuallyEq.isBigO (by
        filter_upwards [self_mem_nhdsWithin] with x hx
        exact (Real.hasDerivAt_log (ne_of_gt hx)).deriv)
    refine h1.trans (Asymptotics.IsBigO.of_bound c⁻¹ ?_)
    filter_upwards [(nhdsGT_basis (0:ℝ)).mem_iff.2 ⟨ε, hε, subset_rfl⟩] with x hx
    have hx0 : 0 < x := hx.1
    have hxε : x < ε := hx.2
    have hFx : 0 ≤ F x := le_trans (div_nonneg hc.le hx0.le) (hF x hx0 hxε)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hFx, abs_of_pos (inv_pos.2 hx0),
      inv_mul_eq_div, le_div_iff₀ hc]
    have hcx : c ≤ F x * x := (div_le_iff₀ hx0).1 (hF x hx0 hxε)
    have hcx' : c * x⁻¹ ≤ F x := by
      have h := mul_le_mul_of_nonneg_right hcx (inv_nonneg.2 hx0.le)
      rwa [mul_assoc, mul_inv_cancel₀ (ne_of_gt hx0), mul_one] at h
    linarith [hcx', mul_comm c x⁻¹]

/-- Vanishing of the primitive in the degenerate case `M = 0`: if `|f| ≤ 0` on the quadrant,
then `∫_θ ZG α f g z θ = 0` for every `z > 0`. -/
theorem ZibpU_eq_zero {α : ℝ} {f g : ℝ → ℝ → ℝ}
    (hf0 : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, |f z θ| ≤ 0) {z : ℝ} (hz : 0 < z) :
    (∫ θ in Work.Spaces.Iθ, ZG α f g z θ) = 0 := by
  have hfun : ∀ θ ∈ Work.Spaces.Iθ, ZG α f g z θ = 0 := by
    intro θ hθ
    have hfz : f z θ = 0 :=
      abs_eq_zero.1 (le_antisymm (hf0 z (le_of_lt hz) θ hθ) (abs_nonneg _))
    rw [ZG, hfz]
    ring
  rw [MeasureTheory.setIntegral_congr_fun (s := Work.Spaces.Iθ) measurableSet_Icc hfun]
  simp

/-- The primitive `u(z) = ∫_θ ZG α f g z θ` can only have the limit `0` at `0+`  and at
`+∞`, given that `∫_z w(z)^2 * (∫_θ ZU α g z θ dθ) dz` is finite.

Route: `|u z| ≤ M/2 * z * w(z)^2 * V(z)` with `V(z) = ∫_θ ZU α g z θ dθ` (from the definition
of `ZG`, `|f| ≤ M` and `ZU ≥ 0`).  A nonzero limit `L` at `+∞` forces `|u z| ≥ |L|/2` for
large `z`, hence `w(z)^2 V(z) ≥ c/z` for all large `z`, so `∫_z w^2V ≥ ∫ c/z = ∞`,
contradicting `hInt` (divergence of `∫ z⁻¹` on `(Z,∞)`: `∫_{(Z,2^n Z)} z⁻¹ = n log 2 → ∞`).
At `0+` a nonzero limit forces `w(z)^2 V(z) ≥ c/z` for small `z`, and `∫_{(0,ε)} z⁻¹ = ∞`. -/
theorem ZibpLimit {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f g : ℝ → ℝ → ℝ}
    (hsmf : Work.Spaces.SmoothNbhd f) (hsmg : Work.Spaces.SmoothNbhd g) {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, |f z θ| ≤ M)
    (hInt : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, Work.FTS.H2.ZU α g z θ)) Work.Spaces.Iz) :
    (∀ L0 : ℝ, Filter.Tendsto
        (fun z => (∫ θ in Work.Spaces.Iθ, Work.FTS.H2.ZG α f g z θ))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds L0) → L0 = 0) ∧
      (∀ Linf : ℝ, Filter.Tendsto
        (fun z => (∫ θ in Work.Spaces.Iθ, Work.FTS.H2.ZG α f g z θ))
        Filter.atTop (nhds Linf) → Linf = 0) := by
  set u : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, ZG α f g z θ with huf
  set F : ℝ → ℝ := fun z => (Work.Spaces.w z) ^ 2
      * (∫ θ in Work.Spaces.Iθ, ZU α g z θ) with hFdef
  have hIntF : IntegrableOn F Work.Spaces.Iz := by rw [hFdef]; exact hInt
  have hbound : ∀ z, 0 < z → |u z| ≤ (M / 2) * z * F z := by
    intro z hz
    have h := abs_ZibpU_le (α := α) hα hα1 hsmf hsmg hM hf hz
    have h2 : (M / 2) * z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, ZU α g z θ)
        = (M / 2) * z * F z := by rw [hFdef]; ring
    calc |u z| = |∫ θ in Work.Spaces.Iθ, ZG α f g z θ| := by rw [huf]
      _ ≤ (M / 2) * z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, ZU α g z θ) := h
      _ = (M / 2) * z * F z := h2
  have hev_of : ∀ {L : ℝ} {l : Filter ℝ}, Tendsto u l (𝓝 L) → L ≠ 0 →
      ∀ᶠ z in l, |L| / 2 ≤ |u z| := by
    intro L l hL hne
    have hpos : 0 < |L| := abs_pos.2 hne
    have hball : Metric.ball L (|L| / 2) ∈ 𝓝 L := Metric.ball_mem_nhds L (by linarith)
    filter_upwards [hL hball] with z hz
    have hz' : |u z - L| < |L| / 2 := by
      have h := Metric.mem_ball.1 hz
      rwa [Real.dist_eq] at h
    have h2 : |L| - |u z| ≤ |L - u z| := abs_sub_abs_le_abs_sub L (u z)
    rw [abs_sub_comm L (u z)] at h2
    linarith
  have hstep : ∀ {L z : ℝ}, 0 < M → 0 < z → |L| / 2 ≤ |u z| → (|L| / M) / z ≤ F z := by
    intro L z hMp hz hb
    have h1 : |L| / 2 ≤ (M / 2) * z * F z := le_trans hb (hbound z hz)
    have h2 : |L| / M ≤ z * F z := by
      rw [div_le_iff₀ hMp]
      nlinarith [h1]
    rw [div_le_iff₀ hz]
    linarith [h2]
  by_cases hM0 : M = 0
  · have hf0 : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, |f z θ| ≤ 0 := by
      intro z hz θ hθ
      have h := hf z hz θ hθ
      rw [hM0] at h
      exact h
    have hzero : ∀ z, 0 < z → u z = 0 := by
      intro z hz
      have h := ZibpU_eq_zero (α := α) (f := f) (g := g) hf0 hz
      simpa only [huf] using h
    constructor
    · intro L0 hL0
      refine tendsto_nhds_unique hL0 ?_
      refine (tendsto_const_nhds (x := (0 : ℝ))).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact (hzero z hz).symm
    · intro Linf hLinf
      refine tendsto_nhds_unique hLinf ?_
      refine (tendsto_const_nhds (x := (0 : ℝ))).congr' ?_
      filter_upwards [Filter.Ioi_mem_atTop (0:ℝ)] with z hz
      exact (hzero z hz).symm
  · have hMpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hM0)
    constructor
    · intro L0 hL0
      by_contra hne
      have hev := hev_of hL0 hne
      obtain ⟨ε, hε, hsub⟩ := (nhdsGT_basis (0:ℝ)).mem_iff.1 hev
      refine (not_integrableOn_Ici_of_le_inv_nearZero (F := F) (c := |L0| / M) (ε := ε)
        (div_pos (abs_pos.2 hne) hMpos) hε ?_) hIntF
      intro z hz0 hzε
      exact hstep hMpos hz0 (hsub ⟨hz0, hzε⟩)
    · intro Linf hLinf
      by_contra hne
      have hev := hev_of hLinf hne
      obtain ⟨Z, hZ⟩ := Filter.eventually_atTop.1 hev
      refine (not_integrableOn_Ici_of_le_inv_atTop (F := F) (c := |Linf| / M) (Z := max Z 1)
        (div_pos (abs_pos.2 hne) hMpos) (by positivity) ?_) hIntF
      intro z hz
      have hz0 : 0 < z := lt_of_lt_of_le zero_lt_one (le_trans (le_max_right _ _) hz)
      exact hstep hMpos hz0 (hZ z (le_trans (le_max_left _ _) hz))

end Work.FTS.H2
