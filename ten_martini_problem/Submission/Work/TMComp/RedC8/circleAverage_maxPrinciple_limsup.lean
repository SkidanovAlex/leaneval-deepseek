import Mathlib
import Submission.Work.TMComp.RedC8.ClampExt
import Submission.Work.TMComp.RealCartan.rcMaxPrinciple

/-!
# The maximum principle with a limsup boundary condition

Let `Ω ⊆ ℂ` be open, bounded and preconnected, let `V : ℂ → ℝ` be continuous on `Ω` and satisfy
the circle sub-mean-value inequality `V z ≤ circleAverage V z r` on `Ω`, and suppose that at every
frontier point `ζ` of `Ω` the values of `V` have limsup at most `C`:

`∀ η > 0, eventually along nhdsWithin ζ Ω, V z ≤ C + η`.

Then `V ≤ C` on `Ω`.

The idea is to reduce to the *pointwise* boundary maximum principle
`Work.TMComp.RealCartan.rcMaxPrinciple` by clamping `V` off at level `C`: define

`clampExt Ω V C z = if z ∈ Ω then max (V z) C else C`.

The boundary limsup condition is exactly what makes `clampExt Ω V C` continuous (the values stay
in `[C, C + η]` near a frontier point), the clamp of a sub-mean-value function with a constant is
again sub-mean-value, and on the frontier `clampExt Ω V C` equals the constant `C`.  Applying
`rcMaxPrinciple` to the clamped function gives `max (V z) C ≤ C`, i.e. `V z ≤ C`, on `Ω`.
-/

set_option linter.unusedVariables false

open Classical Metric Set
open scoped Topology

namespace Work.TMComp.RedC8

/-- The clamped extension `max (V ·) C` inside `Ω` and `C` outside is continuous, provided `V` is
continuous on `Ω` and has limsup at most `C` at every frontier point of `Ω`. -/
theorem clampExt_continuous {Ω : Set ℂ} (hΩ : IsOpen Ω) {V : ℂ → ℝ}
    (hVc : ContinuousOn V Ω) {C : ℝ}
    (hbd : ∀ ζ ∈ frontier Ω, ∀ η : ℝ, 0 < η → ∀ᶠ z in nhdsWithin ζ Ω, V z ≤ C + η) :
    Continuous (clampExt Ω V C) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ Ω
  · -- `x` is an interior point
    have hVx : ContinuousAt V x := hVc.continuousAt (hΩ.mem_nhds hx)
    have hmax : ContinuousAt (fun z => max (V z) C) x := hVx.max tendsto_const_nhds
    refine hmax.congr (Filter.eventuallyEq_of_mem (hΩ.mem_nhds hx) (fun z hz => ?_))
    exact (clampExt_of_mem hz).symm
  · by_cases hxcl : x ∈ closure Ω
    · -- `x` is a frontier point
      have hxf : x ∈ frontier Ω := by
        rw [hΩ.frontier_eq]; exact ⟨hxcl, hx⟩
      have hxval : clampExt Ω V C x = C := clampExt_of_notMem hx
      change Filter.Tendsto (clampExt Ω V C) (𝓝 x) (𝓝 (clampExt Ω V C x))
      rw [hxval, Metric.tendsto_nhds]
      intro ε hε
      have hε2 : (0 : ℝ) < ε / 2 := by linarith
      obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhdsWithin_iff.mp (hbd x hxf (ε / 2) hε2)
      filter_upwards [Metric.ball_mem_nhds x hδpos] with z hz
      rw [Metric.mem_ball] at hz
      by_cases hzΩ : z ∈ Ω
      · rw [clampExt_of_mem hzΩ, Real.dist_eq]
        have hVz : V z ≤ C + ε / 2 := hδ ⟨hz, hzΩ⟩
        have hle : max (V z) C - C ≤ ε / 2 := by
          have : max (V z) C ≤ C + ε / 2 := max_le (by linarith) (by linarith)
          linarith
        have hnn : 0 ≤ max (V z) C - C := by
          have : C ≤ max (V z) C := le_max_right _ _
          linarith
        rw [abs_of_nonneg hnn]; linarith
      · rw [clampExt_of_notMem hzΩ, Real.dist_eq, sub_self, abs_zero]; linarith
    · -- `x` is outside the closure of `Ω`, where the function is locally constant
      have hnc : ∀ᶠ z in nhds x, z ∉ Ω := by
        filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hxcl] with z hz
        exact fun hzΩ => hz (subset_closure hzΩ)
      have heq : (fun _ : ℂ => C) =ᶠ[nhds x] clampExt Ω V C :=
        Filter.eventuallyEq_of_mem hnc (fun z hz => (clampExt_of_notMem hz).symm)
      exact continuousAt_const.congr heq

/-- The clamped extension of a sub-mean-value function is again sub-mean-value. -/
theorem clampExt_meanValue {Ω : Set ℂ} {V : ℂ → ℝ} {C : ℝ}
    (hVc : ContinuousOn V Ω)
    (hWc : Continuous (clampExt Ω V C))
    (hVmean : ∀ z ∈ Ω, ∀ r : ℝ, 0 < r → Metric.closedBall z r ⊆ Ω →
      V z ≤ Real.circleAverage V z r) :
    ∀ z ∈ Ω, ∀ r : ℝ, 0 < r → Metric.closedBall z r ⊆ Ω →
      clampExt Ω V C z ≤ Real.circleAverage (clampExt Ω V C) z r := by
  intro z hz r hr hball
  have hsp : Metric.sphere z r ⊆ Ω := fun x hx => hball (Metric.sphere_subset_closedBall hx)
  have hciV : CircleIntegrable V z r := by
    apply ContinuousOn.circleIntegrable'
    rw [abs_of_pos hr]
    exact hVc.mono hsp
  have hciW : CircleIntegrable (clampExt Ω V C) z r :=
    (hWc.continuousOn.mono (Set.subset_univ _)).circleIntegrable'
  have hmono : Real.circleAverage V z r ≤ Real.circleAverage (clampExt Ω V C) z r := by
    apply Real.circleAverage_mono hciV hciW
    intro x hx
    rw [abs_of_pos hr] at hx
    rw [clampExt_of_mem (hsp hx)]
    exact le_max_left _ _
  have hCle : C ≤ Real.circleAverage (clampExt Ω V C) z r := by
    have h := Real.circleAverage_mono (circleIntegrable_const C z r) hciW
      (fun x hx => by
        rw [abs_of_pos hr] at hx
        rw [clampExt_of_mem (hsp hx)]
        exact le_max_right _ _)
    rwa [Real.circleAverage_const] at h
  rw [clampExt_of_mem hz, max_le_iff]
  exact ⟨le_trans (hVmean z hz r hr hball) hmono, hCle⟩

theorem circleAverage_maxPrinciple_limsup {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hbdd : Bornology.IsBounded Ω) (hpre : IsPreconnected Ω)
    {V : ℂ → ℝ} (hVc : ContinuousOn V Ω)
    (hVmean : ∀ z ∈ Ω, ∀ r : ℝ, 0 < r → Metric.closedBall z r ⊆ Ω →
      V z ≤ Real.circleAverage V z r)
    {C : ℝ}
    (hbd : ∀ ζ ∈ frontier Ω, ∀ η : ℝ, 0 < η → ∀ᶠ z in nhdsWithin ζ Ω, V z ≤ C + η) :
    ∀ z ∈ Ω, V z ≤ C := by
  have hWc : Continuous (clampExt Ω V C) := clampExt_continuous hΩ hVc hbd
  have hWmean := clampExt_meanValue hVc hWc hVmean
  have hWbd : ∀ ζ ∈ frontier Ω, clampExt Ω V C ζ ≤ C := by
    intro ζ hζ
    have hζnot : ζ ∉ Ω := by
      have h := hΩ.frontier_eq
      rw [h] at hζ
      exact hζ.2
    rw [clampExt_of_notMem hζnot]
  have hres := Work.TMComp.RealCartan.rcMaxPrinciple hΩ hbdd hWc hWmean hWbd
  intro z hz
  have h1 := hres z hz
  rw [clampExt_of_mem hz, max_le_iff] at h1
  exact h1.1

end Work.TMComp.RedC8
