/-
# `St5`: divergence of the BKM integral from a pointwise `1/(T-t)` lower bound

This is the "Beale–Kato–Majda divergence" step (`St5`) of the Stability layer: if the
`L∞`-in-space norm of the vorticity is bounded below by `c/(T-t)` on `[0,T)`, then the
BKM integral `∫₀ᵗ ⨆ₓ‖ω(x,s)‖ ds` diverges as `t → T⁻`.

The mathematical content is one-dimensional.  Writing `f := vortLInf u`, the hypothesis is
`f(t) ≥ c/(T-t)` for `t ∈ [0,T)`, and the conclusion follows from the comparison estimate

  `∫₀ᵗ f ≥ ∫₀ᵗ c/(T-s) ds = c · log (T/(T-t)) → +∞  (t → T⁻)`,

together with the fact that `vortLInf u` is interval-integrable up to `t` (so that the
integral comparison `integral_mono_on` applies).

The exact value of the elementary integral is `intervalIntegral.integral_comp_sub_left`
(substituting `u = T - s`) followed by `integral_one_div_of_pos`.
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.StabilityFar.Defs
import Submission.Work.LWP.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Set Filter Topology MeasureTheory
open scoped Topology

namespace Work.StabilityFar.BKM

/-- `bkm u` is the interval integral of `vortLInf u` — the two definitions in
`Submission/Work/LWP/Defs.lean` unfold to the same expression. -/
theorem bkm_eq_intervalIntegral_vortLInf (u : Work.StabilityFar.R3 → ℝ → Work.StabilityFar.R3) :
    Work.LWP.bkm u = fun t => ∫ s in (0:ℝ)..t, Work.LWP.vortLInf u s := by
  funext t
  rfl

/-- The elementary integral `∫₀ᵗ c/(T-s) ds = c · log (T/(T-t))` for `0 ≤ t < T`, `0 < T`. -/
theorem integral_div_sub_eq (c T t : ℝ) (hT : 0 < T) (ht : t ∈ Set.Ico 0 T) :
    (∫ s in (0:ℝ)..t, c / (T - s)) = c * Real.log (T / (T - t)) := by
  have hTt : 0 < T - t := by linarith [ht.2]
  have hsub : (∫ s in (0:ℝ)..t, (1:ℝ) / (T - s)) = Real.log (T / (T - t)) := by
    rw [intervalIntegral.integral_comp_sub_left (fun u : ℝ => (1:ℝ) / u) T]
    simp only [sub_zero]
    exact integral_one_div_of_pos hTt hT
  have h1 : (∫ s in (0:ℝ)..t, c / (T - s)) = c * ∫ s in (0:ℝ)..t, (1:ℝ) / (T - s) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s _
    show c / (T - s) = c * (1 / (T - s))
    exact div_eq_mul_one_div c (T - s)
  rw [h1, hsub]

/-- The comparison function `t ↦ c · log (T/(T-t))` tends to `+∞` along `t → T⁻` (for
`T > 0`, `c > 0`). -/
theorem tendsto_log_div_sub_atTop (c T : ℝ) (hT : 0 < T) (hc : 0 < c) :
    Filter.Tendsto (fun t : ℝ => c * Real.log (T / (T - t))) (𝓝[<] T) Filter.atTop := by
  have h1 : Filter.Tendsto (fun t : ℝ => T - t) (𝓝[<] T) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h : Filter.Tendsto (fun t : ℝ => T - t) (𝓝 T) (𝓝 (T - T)) :=
        tendsto_const_nhds.sub tendsto_id
      simpa using h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [Set.mem_Ioi, Set.mem_Iio] at ht ⊢
      linarith
  have h3 : Filter.Tendsto (fun t : ℝ => (T - t)⁻¹) (𝓝[<] T) Filter.atTop :=
    tendsto_inv_nhdsGT_zero.comp h1
  have h4 : Filter.Tendsto (fun t : ℝ => T * (T - t)⁻¹) (𝓝[<] T) Filter.atTop := by
    have h := (Filter.Tendsto.const_mul_atTop hT tendsto_id).comp h3
    simpa only [Function.comp_def, id_eq] using h
  have h4' : Filter.Tendsto (fun t : ℝ => T / (T - t)) (𝓝[<] T) Filter.atTop := by
    simpa only [div_eq_mul_inv] using h4
  have h5 : Filter.Tendsto (fun t : ℝ => Real.log (T / (T - t))) (𝓝[<] T) Filter.atTop :=
    Real.tendsto_log_atTop.comp h4'
  exact Filter.Tendsto.const_mul_atTop hc h5

/-- `[0,T) = Ico 0 T` is an eventual condition at `T` from the left, for `T > 0`. -/
theorem eventually_mem_Ico_nhdsLT (T : ℝ) (hT : 0 < T) :
    ∀ᶠ t in 𝓝[<] T, t ∈ Set.Ico 0 T := by
  have hIoo : Set.Ioo (0:ℝ) T ∈ 𝓝[<] T := by
    have h1 : Set.Ioi (0:ℝ) ∈ 𝓝[<] T := nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds hT)
    have h2 : Set.Iio T ∈ 𝓝[<] T := self_mem_nhdsWithin
    have h3 := Filter.inter_mem h1 h2
    rwa [Set.Ioi_inter_Iio] at h3
  exact Filter.mem_of_superset hIoo (fun t ht => ⟨le_of_lt ht.1, ht.2⟩)

theorem bkm_tendsto_atTop_of_linf_lower {u : Work.StabilityFar.R3 → ℝ → Work.StabilityFar.R3}
    {T c : ℝ} (hT : 0 < T) (hc : 0 < c)
    (hlower : ∀ t ∈ Set.Ico 0 T, c / (T - t) ≤ Work.LWP.vortLInf u t)
    (hint : ∀ t ∈ Set.Ico 0 T, IntervalIntegrable (Work.LWP.vortLInf u) volume 0 t) :
    Filter.Tendsto (Work.LWP.bkm u) (nhdsWithin T (Set.Iio T)) Filter.atTop := by
  have hbkm : ∀ t : ℝ, Work.LWP.bkm u t = ∫ s in (0:ℝ)..t, Work.LWP.vortLInf u s :=
    fun t => rfl
  rw [Filter.tendsto_atTop]
  intro a
  have hL : Filter.Tendsto (fun t : ℝ => c * Real.log (T / (T - t))) (𝓝[<] T) Filter.atTop :=
    tendsto_log_div_sub_atTop c T hT hc
  have hevL : ∀ᶠ t in 𝓝[<] T, a ≤ c * Real.log (T / (T - t)) :=
    hL.eventually (eventually_ge_atTop a)
  have hevIco : ∀ᶠ t in 𝓝[<] T, t ∈ Set.Ico 0 T := eventually_mem_Ico_nhdsLT T hT
  filter_upwards [hevL, hevIco] with t haL ht
  rw [hbkm t]
  calc a ≤ c * Real.log (T / (T - t)) := haL
    _ = ∫ s in (0:ℝ)..t, c / (T - s) := (integral_div_sub_eq c T t hT ht).symm
    _ ≤ ∫ s in (0:ℝ)..t, Work.LWP.vortLInf u s := by
        apply intervalIntegral.integral_mono_on ht.1
        · apply ContinuousOn.intervalIntegrable
          apply ContinuousOn.div
          · exact continuousOn_const
          · exact continuousOn_const.sub continuousOn_id
          · intro s hs
            have hsle : s ≤ t := by
              rw [Set.uIcc_of_le ht.1] at hs; exact hs.2
            linarith [ht.2]
        · exact hint t ht
        · intro s hs
          exact hlower s ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩

end Work.StabilityFar.BKM
