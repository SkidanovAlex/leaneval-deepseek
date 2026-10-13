import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.Honest.SliceSetup
import Submission.Work.FTS.EllipticEst.hasDerivAt_self_antideriv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

/-- `π/4` lies in the open interval `(0, π/2)`. -/
private theorem pi_div_four_mem : Real.pi / 4 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
  ⟨by positivity, by linarith [Real.pi_pos]⟩

/-! ## Auxiliary slice estimates -/

/-- **Boundedness of `u'` on `(0,π/2)` from the integrability of `u''`.**  Newton–Leibniz on the
segment between `θ` and `π/4` bounds `u'` by `|u' (π/4)|` plus the total mass of `|u''|`. -/
private theorem deriv_abs_le_Ioo (u : ℝ → ℝ)
    (hsm : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hint : MeasureTheory.IntegrableOn (fun θ => deriv (fun θ' => deriv u θ') θ)
      (Set.Ioo 0 (Real.pi / 2))) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |deriv u θ| ≤ M := by
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (deriv u) (deriv (fun t : ℝ => deriv u t) x) x := by
    intro x hx
    have h2 : ContDiffAt ℝ 2 u x := hsm.contDiffAt (isOpen_Ioo.mem_nhds hx)
    have hd1 : ContDiffAt ℝ 1 (deriv u) x := h2.derivWithin (by norm_num)
    exact (hd1.differentiableAt (by norm_num)).hasDerivAt
  have hg : MeasureTheory.IntegrableOn (fun θ : ℝ => ‖deriv (fun t : ℝ => deriv u t) θ‖)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hint.norm
  have hC00 : 0 ≤ |deriv u (Real.pi / 4)|
      + ∫ s in Set.Ioo (0 : ℝ) (Real.pi / 2), ‖deriv (fun t : ℝ => deriv u t) s‖ := by
    have := integral_nonneg (μ := volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)))
      (f := fun s => ‖deriv (fun t : ℝ => deriv u t) s‖) (fun s => norm_nonneg _)
    linarith [abs_nonneg (deriv u (Real.pi / 4))]
  refine ⟨|deriv u (Real.pi / 4)|
    + ∫ s in Set.Ioo (0 : ℝ) (Real.pi / 2), ‖deriv (fun t : ℝ => deriv u t) s‖, hC00,
    fun θ hθ => ?_⟩
  have hseg : Set.uIcc (Real.pi / 4) θ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    intro x hx
    rw [Set.mem_uIcc] at hx
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨lt_of_lt_of_le pi_div_four_mem.1 h1, lt_of_le_of_lt h2 hθ.2⟩
    · exact ⟨lt_of_lt_of_le hθ.1 h1, lt_of_le_of_lt h2 pi_div_four_mem.2⟩
  have hFTC : ∫ t in (Real.pi / 4)..θ, deriv (fun t : ℝ => deriv u t) t
      = deriv u θ - deriv u (Real.pi / 4) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hderiv x (hseg hx))
      ((hint.mono_set hseg).intervalIntegrable)
  have key : |deriv u θ - deriv u (Real.pi / 4)|
      ≤ ∫ s in Set.Ioo (0 : ℝ) (Real.pi / 2), ‖deriv (fun t : ℝ => deriv u t) s‖ := by
    rw [← hFTC]
    rcases le_total (Real.pi / 4) θ with hle | hle
    · rw [intervalIntegral.integral_of_le hle]
      calc |∫ t in Set.Ioc (Real.pi / 4) θ, deriv (fun t : ℝ => deriv u t) t|
          = ‖∫ t in Set.Ioc (Real.pi / 4) θ, deriv (fun t : ℝ => deriv u t) t‖ := by
            rw [Real.norm_eq_abs]
        _ ≤ ∫ t in Set.Ioc (Real.pi / 4) θ, ‖deriv (fun t : ℝ => deriv u t) t‖ :=
            MeasureTheory.norm_integral_le_integral_norm _
        _ ≤ ∫ s in Set.Ioo (0 : ℝ) (Real.pi / 2), ‖deriv (fun t : ℝ => deriv u t) s‖ :=
            setIntegral_mono_set hg (Eventually.of_forall fun _ => norm_nonneg _)
              (Eventually.of_forall fun x hx =>
                ⟨lt_of_lt_of_le pi_div_four_mem.1 hx.1.le, lt_of_le_of_lt hx.2 hθ.2⟩)
    · rw [intervalIntegral.integral_of_ge hle]
      calc |(-∫ t in Set.Ioc θ (Real.pi / 4), deriv (fun t : ℝ => deriv u t) t)|
          = ‖∫ t in Set.Ioc θ (Real.pi / 4), deriv (fun t : ℝ => deriv u t) t‖ := by
            rw [Real.norm_eq_abs, abs_neg]
        _ ≤ ∫ t in Set.Ioc θ (Real.pi / 4), ‖deriv (fun t : ℝ => deriv u t) t‖ :=
            MeasureTheory.norm_integral_le_integral_norm _
        _ ≤ ∫ s in Set.Ioo (0 : ℝ) (Real.pi / 2), ‖deriv (fun t : ℝ => deriv u t) s‖ :=
            setIntegral_mono_set hg (Eventually.of_forall fun _ => norm_nonneg _)
              (Eventually.of_forall fun x hx =>
                ⟨lt_of_lt_of_le hθ.1 hx.1.le, lt_of_le_of_lt hx.2 pi_div_four_mem.2⟩)
  calc |deriv u θ| = |deriv u (Real.pi / 4) + (deriv u θ - deriv u (Real.pi / 4))| := by
        ring_nf
    _ ≤ |deriv u (Real.pi / 4)| + |deriv u θ - deriv u (Real.pi / 4)| := abs_add_le _ _
    _ ≤ |deriv u (Real.pi / 4)|
        + ∫ s in Set.Ioo (0 : ℝ) (Real.pi / 2), ‖deriv (fun t : ℝ => deriv u t) s‖ := by
        linarith [key]

/-- **A global bound for `u` on the open interval.** -/
private theorem u_bound_Ioo (u : ℝ → ℝ) (hsm : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    {M : ℝ} (hM : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |deriv u θ| ≤ M) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |u θ| ≤ |u (Real.pi / 4)| + M * (Real.pi / 2) := by
  intro θ hθ
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM (Real.pi / 4) pi_div_four_mem)
  have hseg : Set.uIcc (Real.pi / 4) θ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    intro x hx
    rw [Set.mem_uIcc] at hx
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨lt_of_lt_of_le pi_div_four_mem.1 h1, lt_of_le_of_lt h2 hθ.2⟩
    · exact ⟨lt_of_lt_of_le hθ.1 h1, lt_of_le_of_lt h2 pi_div_four_mem.2⟩
  have hFTC : ∫ t in (Real.pi / 4)..θ, deriv u t = u θ - u (Real.pi / 4) :=
    intervalIntegral.integral_deriv_of_contDiffOn_uIcc ((hsm.of_le (by norm_num)).mono hseg)
  have hbound : ∀ x ∈ Set.uIoc (Real.pi / 4) θ, ‖deriv u x‖ ≤ M := by
    intro x hx
    rw [Real.norm_eq_abs]
    refine hM x ?_
    rw [Set.mem_uIoc] at hx
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨lt_of_lt_of_le pi_div_four_mem.1 (le_of_lt h1), lt_of_le_of_lt h2 hθ.2⟩
    · exact ⟨lt_of_lt_of_le hθ.1 (le_of_lt h1), lt_of_le_of_lt h2 pi_div_four_mem.2⟩
  have h2 : |∫ t in (Real.pi / 4)..θ, deriv u t| ≤ M * |θ - Real.pi / 4| := by
    simpa only [Real.norm_eq_abs] using
      intervalIntegral.norm_integral_le_of_norm_le_const hbound
  have h3 : |θ - Real.pi / 4| ≤ Real.pi / 2 := by
    rw [abs_sub_le_iff]
    constructor <;> linarith [hθ.1, hθ.2, Real.pi_pos]
  calc |u θ| = |u (Real.pi / 4) + (u θ - u (Real.pi / 4))| := by ring_nf
    _ ≤ |u (Real.pi / 4)| + |u θ - u (Real.pi / 4)| := abs_add_le _ _
    _ = |u (Real.pi / 4)| + |∫ t in (Real.pi / 4)..θ, deriv u t| := by rw [hFTC]
    _ ≤ |u (Real.pi / 4)| + M * |θ - Real.pi / 4| := by linarith
    _ ≤ |u (Real.pi / 4)| + M * (Real.pi / 2) := by
        have := mul_le_mul_of_nonneg_left h3 hM0
        linarith

/-- **Linear vanishing of `u` at the right endpoint.** -/
private theorem u_abs_le_mul_sub_right (u : ℝ → ℝ) {M : ℝ}
    (hsm : ContDiffOn ℝ 1 u (Set.Ioo 0 (Real.pi / 2)))
    (hM : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |deriv u θ| ≤ M)
    (hpi : Filter.Tendsto u (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |u θ| ≤ M * (Real.pi / 2 - θ) := by
  intro θ hθ
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM (Real.pi / 4) pi_div_four_mem)
  have hmem : Set.Ioo θ (Real.pi / 2) ∈ 𝓝[<] (Real.pi / 2) := by
    rw [← nhdsWithin_Ioo_eq_nhdsLT hθ.2]
    exact self_mem_nhdsWithin
  have key : ∀ θ' ∈ Set.Ioo θ (Real.pi / 2), |u θ - u θ'| ≤ M * (θ' - θ) := by
    intro θ' hθ'
    have hseg : Set.uIcc θ θ' ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
      intro x hx
      rw [Set.mem_uIcc] at hx
      rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨lt_of_lt_of_le hθ.1 h1, lt_of_le_of_lt h2 hθ'.2⟩
      · exact ⟨lt_of_lt_of_le (lt_trans hθ.1 hθ'.1) h1, lt_of_le_of_lt h2 hθ.2⟩
    have hFTC : ∫ t in θ..θ', deriv u t = u θ' - u θ :=
      intervalIntegral.integral_deriv_of_contDiffOn_uIcc (hsm.mono hseg)
    have hbound : ∀ x ∈ Set.uIoc θ θ', ‖deriv u x‖ ≤ M := by
      intro x hx
      rw [Real.norm_eq_abs]
      refine hM x ?_
      rw [Set.mem_uIoc] at hx
      rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨lt_of_lt_of_le hθ.1 (le_of_lt h1), lt_of_le_of_lt h2 hθ'.2⟩
      · exact ⟨lt_of_lt_of_le (lt_trans hθ.1 hθ'.1) (le_of_lt h1), lt_of_le_of_lt h2 hθ.2⟩
    have h2 := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    rw [Real.norm_eq_abs, hFTC, abs_sub_comm, abs_of_pos (sub_pos.mpr hθ'.1)] at h2
    exact h2
  have hId : Filter.Tendsto (fun θ' : ℝ => θ') (𝓝[<] (Real.pi / 2)) (𝓝 (Real.pi / 2)) :=
    (tendsto_id'.2 le_rfl).mono_right nhdsWithin_le_nhds
  have hsub : Filter.Tendsto (fun θ' : ℝ => θ' - θ) (𝓝[<] (Real.pi / 2))
      (𝓝 (Real.pi / 2 - θ)) := hId.sub tendsto_const_nhds
  have hshift : Filter.Tendsto (fun θ' : ℝ => M * (θ' - θ)) (𝓝[<] (Real.pi / 2))
      (𝓝 (M * (Real.pi / 2 - θ))) := hsub.const_mul M
  have hlim1 : Filter.Tendsto (fun θ' : ℝ => u θ' + M * (θ' - θ)) (𝓝[<] (Real.pi / 2))
      (𝓝 (M * (Real.pi / 2 - θ))) := by
    simpa using hpi.add hshift
  have hlower : u θ ≤ M * (Real.pi / 2 - θ) :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlim1 (by
      filter_upwards [hmem] with θ' hθ'
      have h1 : u θ - u θ' ≤ M * (θ' - θ) := (le_abs_self _).trans (key θ' hθ')
      linarith)
  have hlim2 : Filter.Tendsto (fun θ' : ℝ => u θ' - M * (θ' - θ)) (𝓝[<] (Real.pi / 2))
      (𝓝 (-(M * (Real.pi / 2 - θ)))) := by
    simpa using hpi.sub hshift
  have hupper : -(M * (Real.pi / 2 - θ)) ≤ u θ :=
    le_of_tendsto_of_tendsto hlim2 tendsto_const_nhds (by
      filter_upwards [hmem] with θ' hθ'
      have h1 : -(u θ - u θ') ≤ M * (θ' - θ) :=
        (neg_le_abs (u θ - u θ')).trans (key θ' hθ')
      linarith)
  rw [abs_le]
  exact ⟨hupper, hlower⟩

/-- **`u / cos θ` is bounded on `(0, π/2)`.** -/
private theorem u_div_cos_bdd (u : ℝ → ℝ) {B M : ℝ}
    (hB : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |u θ| ≤ B)
    (hlin : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |u θ| ≤ M * (Real.pi / 2 - θ)) :
    ∃ K : ℝ, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |u θ / Real.cos θ| ≤ K := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB (Real.pi / 4) pi_div_four_mem)
  have hM0 : 0 ≤ M := by
    have h := hlin (Real.pi / 4) pi_div_four_mem
    have h4 : (0 : ℝ) < Real.pi / 4 := by positivity
    nlinarith [abs_nonneg (u (Real.pi / 4)), h, h4]
  refine ⟨max (2 * B) ((Real.pi / 2) * M), fun θ hθ => ?_⟩
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hx : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
  have hsinθ : (2 / Real.pi) * (Real.pi / 2 - θ) ≤ Real.sin (Real.pi / 2 - θ) :=
    Real.mul_le_sin hx.le (by linarith [hθ.1])
  have hsin : (2 / Real.pi) * (Real.pi / 2 - θ) ≤ Real.cos θ := by
    rwa [Real.sin_pi_div_two_sub] at hsinθ
  have hcoef : 0 < (2 / Real.pi) * (Real.pi / 2 - θ) := by positivity
  rcases le_total θ (Real.pi / 4) with h | h
  · have hcos12 : (1 : ℝ) / 2 ≤ Real.cos θ := by
      have h1 : (1 : ℝ) / 2 ≤ (2 / Real.pi) * (Real.pi / 2 - θ) := by
        have hc : (0 : ℝ) < 2 / Real.pi := by positivity
        have h2 : (2 / Real.pi) * (Real.pi / 4) = 1 / 2 := by
          field_simp
          ring
        have h3 := mul_le_mul_of_nonneg_left
          (show Real.pi / 4 ≤ Real.pi / 2 - θ by linarith) hc.le
        linarith [h2, h3]
      exact h1.trans hsin
    calc |u θ / Real.cos θ| = |u θ| / Real.cos θ := by rw [abs_div, abs_of_pos hcos]
      _ ≤ B / (1 / 2) := div_le_div₀ hB0 (hB θ hθ) (by norm_num) hcos12
      _ = 2 * B := by ring
      _ ≤ max (2 * B) ((Real.pi / 2) * M) := le_max_left _ _
  · calc |u θ / Real.cos θ| = |u θ| / Real.cos θ := by rw [abs_div, abs_of_pos hcos]
      _ ≤ (M * (Real.pi / 2 - θ)) / ((2 / Real.pi) * (Real.pi / 2 - θ)) :=
          div_le_div₀ (mul_nonneg hM0 hx.le) (hlin θ hθ) hcoef hsin
      _ = (Real.pi / 2) * M := by
          rw [div_eq_iff (ne_of_gt hcoef)]
          field_simp
          try ring
      _ ≤ max (2 * B) ((Real.pi / 2) * M) := le_max_right _ _

/-- **Pointwise antiderivative identity for the self-pairing of `Lzero1`.** -/
private theorem hasDerivAt_Lzero1_antideriv (u : ℝ → ℝ) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (h2 : ContDiffAt ℝ 2 u θ) :
    HasDerivAt (fun s => -(deriv u s) * u s + (1 / 2) * Real.tan s * (u s) ^ 2)
      (Work.FTS.EllipticEst.Lzero1 u θ * u θ - (deriv u θ) ^ 2
        - (1 / 2) * (u θ / Real.cos θ) ^ 2 + 6 * (u θ) ^ 2) θ := by
  have h := Work.FTS.EllipticEst.hasDerivAt_self_antideriv u θ hθ h2
  have hL : Work.Elliptic.Lzero (fun _ s => u s) 0 θ = Work.FTS.EllipticEst.Lzero1 u θ := by
    rw [Work.FTS.EllipticEst.Lzero1_eq_Lzero u 0]
  exact h.congr_deriv (by rw [hL])

/-- **The antiderivative `F θ = -u'θ·uθ + (1/2)tanθ·uθ²` tends to `0` at both endpoints.** -/
private theorem tendsto_antideriv_zero (u : ℝ → ℝ) {B K M : ℝ}
    (h0 : Filter.Tendsto u (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hpi : Filter.Tendsto u (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0))
    (hM : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |deriv u θ| ≤ M)
    (hB : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |u θ| ≤ B)
    (hK : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |u θ / Real.cos θ| ≤ K) :
    Filter.Tendsto (fun s => -(deriv u s) * u s + (1 / 2) * Real.tan s * (u s) ^ 2)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
    Filter.Tendsto (fun s => -(deriv u s) * u s + (1 / 2) * Real.tan s * (u s) ^ 2)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB (Real.pi / 4) pi_div_four_mem)
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (hK (Real.pi / 4) pi_div_four_mem)
  have hmem0 : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝[>] (0 : ℝ) := by
    rw [← nhdsWithin_Ioo_eq_nhdsGT (by positivity : (0 : ℝ) < Real.pi / 2)]
    exact self_mem_nhdsWithin
  have hmempi : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝[<] (Real.pi / 2) := by
    rw [← nhdsWithin_Ioo_eq_nhdsLT (by positivity : (0 : ℝ) < Real.pi / 2)]
    exact self_mem_nhdsWithin
  -- the `-(u'·u)` part, at any filter along which `u → 0`
  have hmul : ∀ (l : Filter ℝ), Filter.Tendsto u l (𝓝 0) →
      Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ l →
      Filter.Tendsto (fun s => -(deriv u s) * u s) l (𝓝 0) := by
    intro l hu hmem
    have hg : Filter.Tendsto (fun s => M * |u s|) l (𝓝 0) := by
      have h1 : Filter.Tendsto (fun s => |u s|) l (𝓝 0) := by
        simpa using hu.abs
      have h2 := h1.const_mul M
      simpa using h2
    have hle : ∀ᶠ s in l, |-(deriv u s) * u s| ≤ M * |u s| := by
      filter_upwards [hmem] with s hs
      rw [neg_mul, abs_neg, abs_mul]
      exact mul_le_mul_of_nonneg_right (hM s hs) (abs_nonneg _)
    have hf : Filter.Tendsto (fun s => |-(deriv u s) * u s|) l (𝓝 0) :=
      squeeze_zero' (Eventually.of_forall fun s => abs_nonneg _) hle hg
    exact tendsto_zero_iff_norm_tendsto_zero.mpr
      (by simpa only [Real.norm_eq_abs] using hf)
  -- `tan θ · u² → 0` at `0⁺`
  have htanA : Filter.Tendsto (fun s => Real.tan s * (u s) ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have htan0 : Filter.Tendsto (fun s => |Real.tan s|) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hc : ContinuousAt Real.tan (0 : ℝ) :=
        (Real.hasDerivAt_tan (by rw [Real.cos_zero]; norm_num)).continuousAt
      have hle : 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) := nhdsWithin_le_nhds
      have h' : Filter.Tendsto Real.tan (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        have := hc.tendsto.mono_left hle
        simpa [Real.tan_zero] using this
      simpa using h'.abs
    have hg : Filter.Tendsto (fun s => B ^ 2 * |Real.tan s|) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have := htan0.const_mul (B ^ 2)
      simpa using this
    have hle : ∀ᶠ s in 𝓝[>] (0 : ℝ), |Real.tan s * (u s) ^ 2| ≤ B ^ 2 * |Real.tan s| := by
      filter_upwards [hmem0] with s hs
      rw [abs_mul, abs_pow]
      have hu2 : |u s| ^ 2 ≤ B ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) (hB s hs) 2
      calc |Real.tan s| * |u s| ^ 2 ≤ |Real.tan s| * B ^ 2 :=
            mul_le_mul_of_nonneg_left hu2 (abs_nonneg _)
        _ = B ^ 2 * |Real.tan s| := by ring
    have hf : Filter.Tendsto (fun s => |Real.tan s * (u s) ^ 2|) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      squeeze_zero' (Eventually.of_forall fun s => abs_nonneg _) hle hg
    exact tendsto_zero_iff_norm_tendsto_zero.mpr
      (by simpa only [Real.norm_eq_abs] using hf)
  -- `tan θ · u² → 0` at `(π/2)⁻`
  have htanB : Filter.Tendsto (fun s => Real.tan s * (u s) ^ 2)
      (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
    have hg : Filter.Tendsto (fun s => K * |u s|) (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
      have h1 : Filter.Tendsto (fun s => |u s|) (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
        simpa using hpi.abs
      have h2 := h1.const_mul K
      simpa using h2
    have hle : ∀ᶠ s in 𝓝[<] (Real.pi / 2), |Real.tan s * (u s) ^ 2| ≤ K * |u s| := by
      filter_upwards [hmempi] with s hs
      have hcos : Real.cos s ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo
        ⟨by linarith [hs.1, Real.pi_pos], hs.2⟩)
      have h1 : |Real.tan s| * |u s| ^ 2
          = |Real.sin s| * |u s| * (|u s| / |Real.cos s|) := by
        rw [Real.tan_eq_sin_div_cos, abs_div]
        field_simp
        try ring
      have h2 : |u s| / |Real.cos s| ≤ K := by
        rw [← abs_div]
        exact hK s hs
      have hs1 : |Real.sin s| ≤ 1 := Real.abs_sin_le_one s
      calc |Real.tan s * (u s) ^ 2| = |Real.tan s| * |u s| ^ 2 := by rw [abs_mul, abs_pow]
        _ = |Real.sin s| * |u s| * (|u s| / |Real.cos s|) := h1
        _ ≤ 1 * |u s| * K :=
            mul_le_mul (mul_le_mul_of_nonneg_right hs1 (abs_nonneg _)) h2
              (div_nonneg (abs_nonneg _) (abs_nonneg _)) (by positivity)
        _ = K * |u s| := by ring
    have hf : Filter.Tendsto (fun s => |Real.tan s * (u s) ^ 2|) (𝓝[<] (Real.pi / 2)) (𝓝 0) :=
      squeeze_zero' (Eventually.of_forall fun s => abs_nonneg _) hle hg
    exact tendsto_zero_iff_norm_tendsto_zero.mpr
      (by simpa only [Real.norm_eq_abs] using hf)
  constructor
  · have h1 := hmul (𝓝[>] (0 : ℝ)) h0 hmem0
    have h2 := htanA.const_mul (1 / 2 : ℝ)
    have h3 := h1.add h2
    simpa [mul_assoc] using h3
  · have h1 := hmul (𝓝[<] (Real.pi / 2)) hpi hmempi
    have h2 := htanB.const_mul (1 / 2 : ℝ)
    have h3 := h1.add h2
    simpa [mul_assoc] using h3

/-! ## The target -/

/-- **The honest slice self-form of `Lzero1` (inequality form).**  For `u` of class `C²` on the *open* interval `(0,π/2)` whose one-sided endpoint limits both vanish and whose second derivative is integrable on the open interval, the `Lzero1`-pairing dominates the derivative energy minus `6∫u²`; the positive term `(1/2)∫(u/cos)²` is dropped.  With `F θ = -u'θ·u θ + (1/2)tanθ·u θ²` one has `F' = Lzero1 u·u - (u')² - (1/2)(u/cos)² + 6u²` on `(0,π/2)`, `F → 0` at both endpoints, and integrating over `(ε, π/2-ε)` (dropping the positive term) then letting `ε → 0` gives the claim. -/
theorem LzeroSelfFormHon (u : ℝ → ℝ)
    (hsm : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (h0 : Filter.Tendsto u (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hpi : Filter.Tendsto u (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0))
    (hint : MeasureTheory.IntegrableOn (fun θ => deriv (fun θ' => deriv u θ') θ)
      (Set.Ioo 0 (Real.pi / 2)))
    (hint2 : MeasureTheory.IntegrableOn
      (fun θ => Work.FTS.EllipticEst.Lzero1 u θ * u θ) Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
      ≤ (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.Lzero1 u θ * u θ)
        + 6 * (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2) := by
  have hlt : (0 : ℝ) < Real.pi / 2 := by positivity
  obtain ⟨M, hM0, hM⟩ := deriv_abs_le_Ioo u hsm hint
  have hB := u_bound_Ioo u hsm hM
  have hlin := u_abs_le_mul_sub_right u (hsm.of_le (by norm_num)) hM hpi
  obtain ⟨K, hK⟩ := u_div_cos_bdd u hB hlin
  have hderiv : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun s => -(deriv u s) * u s + (1 / 2) * Real.tan s * (u s) ^ 2)
        (Work.FTS.EllipticEst.Lzero1 u θ * u θ - (deriv u θ) ^ 2
          - (1 / 2) * (u θ / Real.cos θ) ^ 2 + 6 * (u θ) ^ 2) θ :=
    fun θ hθ => hasDerivAt_Lzero1_antideriv u hθ (hsm.contDiffAt (isOpen_Ioo.mem_nhds hθ))
  obtain ⟨hl0, hlpi⟩ := tendsto_antideriv_zero u h0 hpi hM hB hK
  have hIoo_sub : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Work.Spaces.Iθ :=
    fun θ hθ => ⟨hθ.1.le, hθ.2.le⟩
  have hcos_ne : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.cos θ ≠ 0 := by
    intro θ hθ
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  have hcont_deriv : ContinuousOn (deriv u) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have hd : ContDiffOn ℝ 1 (deriv u) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      hsm.deriv_of_isOpen isOpen_Ioo (by norm_num)
    exact hd.continuousOn
  have hmeas_sq : AEStronglyMeasurable (fun θ => (deriv u θ) ^ 2)
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    ((hcont_deriv.pow 2).aemeasurable measurableSet_Ioo).aestronglyMeasurable
  have hsq_int : IntegrableOn (fun θ => (deriv u θ) ^ 2) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    refine IntegrableOn.of_bound ?_ hmeas_sq (M ^ 2) ?_
    · rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
    · refine ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      rw [← sq_abs (deriv u θ)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hM θ hθ) 2
  have hu2_int : IntegrableOn (fun θ => (u θ) ^ 2) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have hB0 : 0 ≤ |u (Real.pi / 4)| + M * (Real.pi / 2) := by
      have := mul_nonneg hM0 (by positivity : (0 : ℝ) ≤ Real.pi / 2)
      linarith [abs_nonneg (u (Real.pi / 4))]
    refine IntegrableOn.of_bound ?_
      (((hsm.continuousOn.pow 2).aemeasurable measurableSet_Ioo).aestronglyMeasurable)
      ((|u (Real.pi / 4)| + M * (Real.pi / 2)) ^ 2) ?_
    · rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
    · refine ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      rw [← sq_abs (u θ)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hB θ hθ) 2
  have hdiv2_int : IntegrableOn (fun θ => (u θ / Real.cos θ) ^ 2)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have hdiv_cont : ContinuousOn (fun θ => u θ / Real.cos θ)
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      hsm.continuousOn.div Real.continuous_cos.continuousOn hcos_ne
    refine IntegrableOn.of_bound ?_
      (((hdiv_cont.pow 2).aemeasurable measurableSet_Ioo).aestronglyMeasurable)
      (K ^ 2) ?_
    · rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
    · refine ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      rw [← sq_abs (u θ / Real.cos θ)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hK θ hθ) 2
  have hL_int : IntegrableOn (fun θ => Work.FTS.EllipticEst.Lzero1 u θ * u θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hint2.mono_set hIoo_sub
  have h_ab : IntegrableOn (fun θ => Work.FTS.EllipticEst.Lzero1 u θ * u θ
      - (deriv u θ) ^ 2) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hL_int.sub hsq_int
  have h_abc : IntegrableOn (fun θ => Work.FTS.EllipticEst.Lzero1 u θ * u θ
      - (deriv u θ) ^ 2 - (1 / 2) * (u θ / Real.cos θ) ^ 2)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := h_ab.sub (hdiv2_int.const_mul (1 / 2))
  have hFp_int : IntegrableOn (fun θ => Work.FTS.EllipticEst.Lzero1 u θ * u θ
      - (deriv u θ) ^ 2 - (1 / 2) * (u θ / Real.cos θ) ^ 2 + 6 * (u θ) ^ 2)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := h_abc.add (hu2_int.const_mul 6)
  have hFTC := integral_Ioo_eq_sub_of_tendsto hlt hderiv hFp_int hl0 hlpi
  have hzero : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ * u θ
      - (deriv u θ) ^ 2 - (1 / 2) * (u θ / Real.cos θ) ^ 2 + 6 * (u θ) ^ 2) = 0 := by
    simpa using hFTC
  have hsplit : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ * u θ
      - (deriv u θ) ^ 2 - (1 / 2) * (u θ / Real.cos θ) ^ 2 + 6 * (u θ) ^ 2)
      = (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ * u θ)
        - (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (deriv u θ) ^ 2)
        - (1 / 2) * (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (u θ / Real.cos θ) ^ 2)
        + 6 * (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (u θ) ^ 2) := by
    rw [integral_add h_abc (hu2_int.const_mul 6),
      integral_sub h_ab (hdiv2_int.const_mul (1 / 2)),
      integral_sub hL_int hsq_int, integral_const_mul, integral_const_mul]
  have hC_nonneg : 0 ≤ ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (u θ / Real.cos θ) ^ 2 :=
    integral_nonneg (fun θ => sq_nonneg _)
  have hmain : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (deriv u θ) ^ 2)
      ≤ (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ * u θ)
        + 6 * (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (u θ) ^ 2) := by
    linarith [hzero, hsplit, hC_nonneg]
  have e1 : (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
      = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (deriv u θ) ^ 2 := by
    simp only [Work.Spaces.Iθ]
    rw [MeasureTheory.integral_Icc_eq_integral_Ioo]
  have e2 : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.Lzero1 u θ * u θ)
      = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ * u θ := by
    simp only [Work.Spaces.Iθ]
    rw [MeasureTheory.integral_Icc_eq_integral_Ioo]
  have e3 : (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)
      = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (u θ) ^ 2 := by
    simp only [Work.Spaces.Iθ]
    rw [MeasureTheory.integral_Icc_eq_integral_Ioo]
  rw [e1, e2, e3]
  exact hmain

end Work.FTS.EllipticEst.Honest
