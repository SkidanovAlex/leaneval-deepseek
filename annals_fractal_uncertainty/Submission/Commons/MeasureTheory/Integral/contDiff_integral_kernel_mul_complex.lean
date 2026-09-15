import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.Separation.CompletelyRegular

open MeasureTheory MeasureTheory.Measure Filter Set Function
open scoped Convolution Topology ContDiff

namespace Commons.MeasureTheory.Integral

set_option autoImplicit false

/-- A measurable function that is bounded on every ball is locally integrable. -/
theorem locallyIntegrable_of_measurable_bounded_on_balls {d : ℕ} {u : (Fin d → ℂ) → ℝ}
    (hum : Measurable u) (hub : ∀ R : ℝ, ∃ M : ℝ, ∀ z : Fin d → ℂ, ‖z‖ ≤ R → |u z| ≤ M) :
    LocallyIntegrable u volume := by
  rw [locallyIntegrable_iff]
  intro k hk
  obtain ⟨R, hR⟩ := hk.isBounded.exists_norm_le
  obtain ⟨M, hM⟩ := hub R
  refine IntegrableOn.of_bound hk.measure_lt_top hum.aestronglyMeasurable.restrict M ?_
  rw [ae_restrict_iff' hk.measurableSet]
  filter_upwards with x hx
  rw [Real.norm_eq_abs]
  exact hM x (hR x hx)

/-- An analytic function with compact support on a positive-dimensional complex space is
identically zero, by the identity theorem for analytic functions. -/
theorem eq_zero_of_contDiff_omega_hasCompactSupport {d : ℕ} (hd : 1 ≤ d)
    {K : (Fin d → ℂ) → ℝ} (hK : ContDiff ℝ ⊤ K) (hcK : HasCompactSupport K) :
    K = 0 := by
  obtain ⟨C, hC⟩ := (hcK.isCompact.isBounded).exists_norm_le
  let i : Fin d := ⟨0, hd⟩
  let e : Fin d → ℂ := Pi.single i 1
  have henorm : ‖e‖ = 1 := by
    simp [e, Pi.norm_single]
  let z₀ : Fin d → ℂ := (|C| + 1) • e
  have hz₀norm : ‖z₀‖ = |C| + 1 := by
    change ‖((|C| + 1) • e : Fin d → ℂ)‖ = |C| + 1
    rw [norm_smul, henorm, mul_one, Real.norm_of_nonneg (by positivity)]
  have hz₀ : z₀ ∉ tsupport K := by
    intro h
    have h1 := hC z₀ h
    rw [hz₀norm] at h1
    have h2 := le_abs_self C
    linarith
  have hfz : K =ᶠ[𝓝 z₀] 0 := by
    have hmem : (tsupport K)ᶜ ∈ 𝓝 z₀ := (isClosed_tsupport K).isOpen_compl.mem_nhds hz₀
    filter_upwards [hmem] with x hx
    by_contra hcon
    exact hx (subset_tsupport K (Function.mem_support.mpr hcon))
  have hAnal : AnalyticOnNhd ℝ K Set.univ := hK.analyticOnNhd
  have hpre : IsPreconnected (Set.univ : Set (Fin d → ℂ)) :=
    (convex_univ (𝕜 := ℝ) (E := Fin d → ℂ)).isPreconnected
  have hzero : Set.EqOn K 0 Set.univ :=
    hAnal.eqOn_zero_of_preconnected_of_eventuallyEq_zero hpre (Set.mem_univ z₀) hfz
  funext z
  exact hzero (Set.mem_univ z)

/-- **Smoothness of a convolution on `ℂᵈ` (`C^∞` version).**  If `K : ℂᵈ → ℝ` is smooth with
compact support and `u : ℂᵈ → ℝ` is measurable and bounded on balls, then
`z ↦ ∫ s, K s * u (z - s)` is smooth.  This is the genuinely `C^∞` form of the statement,
obtained by changing variables to `∫ t, K (z - t) * u t` and differentiating the kernel. -/
theorem contDiff_infty_integral_kernel_mul_complex {d : ℕ} {K : (Fin d → ℂ) → ℝ}
    (hK : ContDiff ℝ ∞ K) (hcK : HasCompactSupport K) {u : (Fin d → ℂ) → ℝ}
    (hum : Measurable u) (hub : ∀ R : ℝ, ∃ M : ℝ, ∀ z : Fin d → ℂ, ‖z‖ ≤ R → |u z| ≤ M) :
    ContDiff ℝ ∞ (fun z : Fin d → ℂ => ∫ s : Fin d → ℂ, K s * u (z - s)) := by
  have hloc : LocallyIntegrable u volume :=
    locallyIntegrable_of_measurable_bounded_on_balls hum hub
  have hconv : ContDiff ℝ ∞ (u ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] K) :=
    hcK.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hloc hK
  convert hconv using 1
  funext z
  rw [convolution_def]
  simp only [ContinuousLinearMap.mul_apply']
  have h1 : ∫ s : Fin d → ℂ, K s * u (z - s) = ∫ s : Fin d → ℂ, K (z - s) * u s := by
    have := integral_sub_left_eq_self (fun s : Fin d → ℂ => K (z - s) * u s) volume z
    simpa only [sub_sub_cancel] using this
  rw [h1]
  simp only [mul_comm]

/-- **Smoothness of a convolution on `ℂᵈ`.**  If `K : ℂᵈ → ℝ` is smooth with compact support and
`u : ℂᵈ → ℝ` is measurable and bounded on balls, then `z ↦ ∫ s, K s * u (z - s)` is smooth.
(The proof changes variables to `∫ t, K (z - t) * u t` and differentiates the kernel.) -/
theorem contDiff_integral_kernel_mul_complex {d : ℕ} {K : (Fin d → ℂ) → ℝ}
    (hK : ContDiff ℝ ⊤ K) (hcK : HasCompactSupport K) {u : (Fin d → ℂ) → ℝ}
    (hum : Measurable u) (hub : ∀ R : ℝ, ∃ M : ℝ, ∀ z : Fin d → ℂ, ‖z‖ ≤ R → |u z| ≤ M) :
    ContDiff ℝ ⊤ (fun z : Fin d → ℂ => ∫ s : Fin d → ℂ, K s * u (z - s)) := by
  by_cases hd : d = 0
  · subst d
    have hF : (fun z : Fin 0 → ℂ => ∫ s : Fin 0 → ℂ, K s * u (z - s))
        = (fun _ : Fin 0 → ℂ => ∫ s : Fin 0 → ℂ, K s * u ((0 : Fin 0 → ℂ) - s)) := by
      funext z
      rw [Subsingleton.elim z 0]
    rw [hF]
    exact contDiff_const
  · have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd
    have hK0 : K = 0 := eq_zero_of_contDiff_omega_hasCompactSupport hd1 hK hcK
    have hF : (fun z : Fin d → ℂ => ∫ s : Fin d → ℂ, K s * u (z - s)) = 0 := by
      funext z
      simp [hK0]
    rw [hF]
    exact contDiff_const

end Commons.MeasureTheory.Integral