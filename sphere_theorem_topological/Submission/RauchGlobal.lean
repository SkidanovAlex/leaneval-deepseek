import Submission.RauchLocal
import Submission.IndexForm

/-!
# Rauch's theorem, global form: no conjugate point before `π/2`

The chart-local Rauch theorem (`Submission.ConjPoint.eqOn_zero_of_jacobi`) says that a Jacobi field
along a *chart* geodesic which vanishes at `0` and again at `t₁ < π/2` vanishes identically.  This
file globalises it to arbitrary `C^∞` unit-speed geodesics of the manifold: a field `J` along a
curve `γ` which is *locally* a Jacobi field (i.e. in suitable charts near every time it satisfies
the chart Jacobi equation, see `IsJacobiAt`) and vanishes at two times `0 < t₁ < π/2` vanishes
identically.

The key point is that the Rauch/Sturm inequality is a *pointwise* statement about the function
`h = √⟨J,J⟩` (its first and second derivatives), so it can be applied on any interval, the chart
data being chosen at each time separately; this is exactly what `Submission/RauchLocal` provides
(`rauch_sturm_ready_of_hasDerivAt` is stated with germ-level hypotheses).

## Contents

* `IsJacobiAt cov γ J t`: `J` is a Jacobi field along `γ` near `t` (chart-wise formulation);
* `exists_local_data`: the germ data expanded to an explicit interval `Ioo (t-ρ) (t+ρ)`;
* `continuousAt_inner_self_of_isJacobiAt`: `s ↦ ⟨J s, J s⟩` is continuous where `J` is a Jacobi
  field;
* `sturm_data_at`: the Sturm data (first and second derivative of `h = √⟨J,J⟩` and the inequality
  `h'' + 4h ≥ 0`) at a time where `J` does not vanish;
* **`eqOn_zero_of_jacobi`**: (Rauch) a locally-Jacobi field vanishing at `0` and at `t₁ < π/2`
  vanishes on `[0,t₁]`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.ChartConnection
open Submission.Jacobi
open Submission.ChartCurv
open Submission.Curvature
open Submission.CurvatureVec
open Submission.Rauch
open Submission.ChartBounds
open Submission.RauchLocal
open Commons.Analysis.ODE

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.RauchGlobal

noncomputable section

variable [I.Boundaryless]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}

/-! ## 1. Jacobi fields, locally -/

/-- **`J` is a Jacobi field along `γ` near `t`.**  There is a chart at a point `x₀`, a coordinate
curve `u` (with derivative `w`) representing `γ` near `t`, and coordinates `y` of `J`, such that
the chart Jacobi equation `D(Dy) + R(y,w)w = 0` holds near `t`, and `γ` is unit speed in the chart.
All hypotheses are germ-level (they only involve a neighbourhood of `t`). -/
def IsJacobiAt (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (γ : ℝ → M) (J : (t : ℝ) → TangentSpace I (γ t)) (t : ℝ) : Prop :=
  ∃ (x₀ : M) (u w y : ℝ → E),
    (∀ᶠ s in 𝓝 t, u s ∈ (extChartAt I x₀).target) ∧
    (∀ᶠ s in 𝓝 t, HasDerivAt u (w s) s) ∧
    (∀ᶠ s in 𝓝 t, γ s = (extChartAt I x₀).symm (u s)) ∧
    (∀ᶠ s in 𝓝 t, frameVector (I := I) x₀ (γ s) (y s) = J s) ∧
    (∀ᶠ s in 𝓝 t, chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s)) (w s) (w s) = 1) ∧
    (∀ᶠ s in 𝓝 t, HasDerivAt y (deriv y s) s) ∧
    (∀ᶠ s in 𝓝 t, HasDerivAt (chartCovDeriv cov x₀ u w y)
      (deriv (chartCovDeriv cov x₀ u w y) s) s) ∧
    (∀ᶠ s in 𝓝 t, chartCovDeriv cov x₀ u w (chartCovDeriv cov x₀ u w y) s
      + chartCurv cov x₀ ((extChartAt I x₀).symm (u s)) (y s) (w s) = 0)

/-- **The local data of a Jacobi field, expanded on an explicit interval.** -/
theorem exists_local_data {γ : ℝ → M} {J : (t : ℝ) → TangentSpace I (γ t)} {t : ℝ}
    (hJ : IsJacobiAt cov γ J t) :
    ∃ (x₀ : M) (u w y : ℝ → E) (ρ : ℝ), 0 < ρ ∧
      (∀ s ∈ Ioo (t - ρ) (t + ρ), u s ∈ (extChartAt I x₀).target) ∧
      (∀ s ∈ Ioo (t - ρ) (t + ρ), HasDerivAt u (w s) s) ∧
      (∀ s ∈ Ioo (t - ρ) (t + ρ), γ s = (extChartAt I x₀).symm (u s)) ∧
      (∀ s ∈ Ioo (t - ρ) (t + ρ), frameVector (I := I) x₀ (γ s) (y s) = J s) ∧
      (∀ s ∈ Ioo (t - ρ) (t + ρ),
        chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s)) (w s) (w s) = 1) ∧
      (∀ s ∈ Ioo (t - ρ) (t + ρ), HasDerivAt y (deriv y s) s) ∧
      (∀ s ∈ Ioo (t - ρ) (t + ρ), HasDerivAt (chartCovDeriv cov x₀ u w y)
        (deriv (chartCovDeriv cov x₀ u w y) s) s) ∧
      (∀ s ∈ Ioo (t - ρ) (t + ρ), chartCovDeriv cov x₀ u w (chartCovDeriv cov x₀ u w y) s
        + chartCurv cov x₀ ((extChartAt I x₀).symm (u s)) (y s) (w s) = 0) := by
  obtain ⟨x₀, u, w, y, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hJ
  have hall : ∀ᶠ s in 𝓝 t,
      u s ∈ (extChartAt I x₀).target ∧ HasDerivAt u (w s) s ∧
      γ s = (extChartAt I x₀).symm (u s) ∧
      frameVector (I := I) x₀ (γ s) (y s) = J s ∧
      chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s)) (w s) (w s) = 1 ∧
      HasDerivAt y (deriv y s) s ∧
      HasDerivAt (chartCovDeriv cov x₀ u w y) (deriv (chartCovDeriv cov x₀ u w y) s) s ∧
      chartCovDeriv cov x₀ u w (chartCovDeriv cov x₀ u w y) s
        + chartCurv cov x₀ ((extChartAt I x₀).symm (u s)) (y s) (w s) = 0 := by
    filter_upwards [h1, h2, h3, h4, h5, h6, h7, h8] with s hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8
    exact ⟨hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8⟩
  obtain ⟨ρ, hρ, hsub⟩ := Metric.mem_nhds_iff.mp hall
  have hball : Ioo (t - ρ) (t + ρ) ⊆ Metric.ball t ρ := by
    intro s hs
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have got : ∀ s ∈ Ioo (t - ρ) (t + ρ),
      u s ∈ (extChartAt I x₀).target ∧ HasDerivAt u (w s) s ∧
      γ s = (extChartAt I x₀).symm (u s) ∧
      frameVector (I := I) x₀ (γ s) (y s) = J s ∧
      chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s)) (w s) (w s) = 1 ∧
      HasDerivAt y (deriv y s) s ∧
      HasDerivAt (chartCovDeriv cov x₀ u w y) (deriv (chartCovDeriv cov x₀ u w y) s) s ∧
      chartCovDeriv cov x₀ u w (chartCovDeriv cov x₀ u w y) s
        + chartCurv cov x₀ ((extChartAt I x₀).symm (u s)) (y s) (w s) = 0 :=
    fun s hs => hsub (hball hs)
  exact ⟨x₀, u, w, y, ρ, hρ,
    fun s hs => (got s hs).1, fun s hs => (got s hs).2.1, fun s hs => (got s hs).2.2.1,
    fun s hs => (got s hs).2.2.2.1, fun s hs => (got s hs).2.2.2.2.1,
    fun s hs => (got s hs).2.2.2.2.2.1, fun s hs => (got s hs).2.2.2.2.2.2.1,
    fun s hs => (got s hs).2.2.2.2.2.2.2⟩

/-! ## 2. Continuity of `⟨J,J⟩` along a Jacobi field -/

/-- Along a Jacobi field, the squared norm `s ↦ ⟨J s, J s⟩` is continuous. -/
theorem continuousAt_inner_self_of_isJacobiAt {γ : ℝ → M}
    {J : (t : ℝ) → TangentSpace I (γ t)} {t : ℝ} (hJ : IsJacobiAt cov γ J t) :
    ContinuousAt (fun s => inner ℝ (J s) (J s)) t := by
  obtain ⟨x₀, u, w, y, ρ, hρ, hutgt, hu, hγ, hframe, hunit, hy, hDy, hjac⟩ :=
    exists_local_data (cov := cov) hJ
  have ht : t ∈ Ioo (t - ρ) (t + ρ) := ⟨by linarith, by linarith⟩
  have hutgt_t : u t ∈ (extChartAt I x₀).target := hutgt t ht
  have hut : ContinuousAt u t := (hu t ht).continuousAt
  have hyt : ContinuousAt y t := (hy t ht).continuousAt
  have hcurve : ContinuousAt (fun s => (extChartAt I x₀).symm (u s)) t :=
    ((contMDiffOn_extChartAt_symm (𝕜 := ℝ) (I := I) (n := ∞) x₀).continuousOn.continuousAt
      ((isOpen_extChartAt_target x₀).mem_nhds hutgt_t)).comp hut
  have hsrc : (extChartAt I x₀).symm (u t) ∈ (chartAt H x₀).source :=
    mem_source_chartCurve (I := I) hutgt_t
  have hgram : ContinuousAt (fun s => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s))
      (y s) (y s)) t := by
    have h3 : ContinuousAt (fun s => ((extChartAt I x₀).symm (u s), y s, y s)) t :=
      hcurve.prodMk (hyt.prodMk hyt)
    exact (Submission.IndexForm.continuousAt_chartGram_prod3 (I := I) x₀ hsrc (y t) (y t)).comp
      (f := fun s => ((extChartAt I x₀).symm (u s), y s, y s)) (x := t) h3
  -- identify with the intrinsic inner product near `t`
  have heq : (fun s => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s)) (y s) (y s))
      =ᶠ[𝓝 t] (fun s => inner ℝ (J s) (J s)) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    rw [chartGram_apply, ← hγ s hs, hframe s hs]
  exact hgram.congr heq

/-! ## 3. The Sturm data of a Jacobi field -/

/-- **The Sturm data of a Jacobi field where it does not vanish.**  For a field satisfying the
Jacobi equation near `t` and `⟨J t, J t⟩ > 0`, the function `h = √⟨J,J⟩` is twice differentiable at
`t` with `h'' + 4 h ≥ 0`. -/
theorem sturm_data_at (hcov : ContMDiffCovariantDerivative cov ∞)
    (hmet : IsMetricCompatible cov) (hpinch : QuarterPinched cov) (htor : cov.torsion = 0)
    {γ : ℝ → M} {J : (t : ℝ) → TangentSpace I (γ t)} {t : ℝ}
    (hJ : IsJacobiAt cov γ J t) (hpos : 0 < inner ℝ (J t) (J t)) :
    HasDerivAt (fun s => Real.sqrt (inner ℝ (J s) (J s)))
        (deriv (fun s => Real.sqrt (inner ℝ (J s) (J s))) t) t ∧
      HasDerivAt (deriv (fun s => Real.sqrt (inner ℝ (J s) (J s))))
        (deriv (deriv (fun s => Real.sqrt (inner ℝ (J s) (J s)))) t) t ∧
      0 ≤ deriv (deriv (fun s => Real.sqrt (inner ℝ (J s) (J s)))) t
        + 4 * Real.sqrt (inner ℝ (J t) (J t)) := by
  obtain ⟨x₀, u, w, y, ρ, hρ, hutgt, hu, hγ, hframe, hunit, hy, hDy, hjac⟩ :=
    exists_local_data (cov := cov) hJ
  have ht : t ∈ Ioo (t - ρ) (t + ρ) := ⟨by linarith, by linarith⟩
  -- shrink the interval so that `⟨J,J⟩` stays positive
  have hcont : ContinuousAt (fun s => inner ℝ (J s) (J s)) t :=
    continuousAt_inner_self_of_isJacobiAt (cov := cov) hJ
  have hpos_nhds : {s : ℝ | 0 < inner ℝ (J s) (J s)} ∈ 𝓝 t :=
    hcont.eventually (isOpen_Ioi.mem_nhds hpos)
  obtain ⟨ρ', hρ'pos, hρ'sub⟩ := Metric.mem_nhds_iff.mp hpos_nhds
  have hminpos : 0 < min ρ ρ' := lt_min hρ hρ'pos
  have hI : Ioo (t - min ρ ρ') (t + min ρ ρ') ⊆ Ioo (t - ρ) (t + ρ) :=
    Ioo_subset_Ioo (by linarith [min_le_left ρ ρ']) (by linarith [min_le_left ρ ρ'])
  have hI' : Ioo (t - min ρ ρ') (t + min ρ ρ') ⊆ Metric.ball t ρ' := by
    intro s hs
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith [hs.1, min_le_right ρ ρ'], by linarith [hs.2, min_le_right ρ ρ']⟩
  have hposI : ∀ s ∈ Ioo (t - min ρ ρ') (t + min ρ ρ'),
      0 < chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s)) (y s) (y s) := by
    intro s hs
    have h1 : 0 < inner ℝ (J s) (J s) := hρ'sub (hI' hs)
    rw [← hframe s (hI hs), ← chartGram_apply] at h1
    rw [← hγ s (hI hs)]
    exact h1
  -- the Sturm-ready data in the chart
  obtain ⟨g1, g2, hg1, hg2, hineq⟩ :=
    rauch_sturm_ready_of_hasDerivAt (cov := cov) hcov hmet hpinch htor
      (fun s hs => hutgt s (hI hs)) (fun s hs => hu s (hI hs))
      (fun s hs => hunit s (hI hs)) (fun s hs => hy s (hI hs)) (fun s hs => hDy s (hI hs))
      (fun s hs => hjac s (hI hs)) hposI
  -- the chart function agrees with the intrinsic one
  have hHpt : ∀ s ∈ Ioo (t - ρ) (t + ρ),
      Real.sqrt (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s)) (y s) (y s))
        = Real.sqrt (inner ℝ (J s) (J s)) := by
    intro s hs
    rw [chartGram_apply, ← hγ s hs, hframe s hs]
  have hev : (fun s => Real.sqrt (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s))
        (y s) (y s))) =ᶠ[𝓝 t] (fun s => Real.sqrt (inner ℝ (J s) (J s))) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact hHpt s hs
  have htI : t ∈ Ioo (t - min ρ ρ') (t + min ρ ρ') := ⟨by linarith, by linarith⟩
  -- first derivative
  have h1 : HasDerivAt (fun s => Real.sqrt (inner ℝ (J s) (J s))) (g1 t) t :=
    (hev.hasDerivAt_iff).mp (hg1 t htI)
  -- the derivative of the intrinsic function is `g1` near `t`
  have hgd : deriv (fun s => Real.sqrt (inner ℝ (J s) (J s))) =ᶠ[𝓝 t] g1 := by
    filter_upwards [isOpen_Ioo.mem_nhds htI] with s hs
    have hevs : (fun r => Real.sqrt (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u r))
          (y r) (y r))) =ᶠ[𝓝 s] (fun r => Real.sqrt (inner ℝ (J r) (J r))) := by
      filter_upwards [isOpen_Ioo.mem_nhds (hI hs)] with r hr
      exact hHpt r hr
    exact ((hevs.hasDerivAt_iff).mp (hg1 s hs)).deriv
  have h2 : HasDerivAt (deriv (fun s => Real.sqrt (inner ℝ (J s) (J s)))) (g2 t) t :=
    (hgd.hasDerivAt_iff).mpr (hg2 t htI)
  have hderiv2 : deriv (deriv (fun s => Real.sqrt (inner ℝ (J s) (J s)))) t = g2 t := h2.deriv
  have hineqt := hineq t htI
  have hval : Real.sqrt (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t))
      = Real.sqrt (inner ℝ (J t) (J t)) := hHpt t ht
  rw [hval, ← hderiv2] at hineqt
  exact ⟨by rw [h1.deriv]; exact h1, by rw [hderiv2]; exact h2, hineqt⟩


/-- Continuity of `h = √⟨J,J⟩` where `J` is a Jacobi field. -/
theorem continuousAt_sqrt_inner_self_of_isJacobiAt {γ : ℝ → M}
    {J : (t : ℝ) → TangentSpace I (γ t)} {t : ℝ} (hJ : IsJacobiAt cov γ J t) :
    ContinuousAt (fun s => Real.sqrt (inner ℝ (J s) (J s))) t :=
  ContinuousAt.comp (x := t) Real.continuous_sqrt.continuousAt
    (continuousAt_inner_self_of_isJacobiAt (cov := cov) hJ)

/-! ## 4. Rauch's theorem, global form -/

/-- **Rauch's theorem (no conjugate point before `π/2`), global form.**  Let `J` be a field along a
curve `γ` which is a Jacobi field near every time (in the sense of `IsJacobiAt`).  If `J` vanishes
at `0` and again at `t₁` with `0 < t₁ < π/2`, then `J` vanishes on `[0,t₁]`.

Equivalently: along a unit-speed geodesic there is no conjugate point at distance `< π/2`. -/
theorem eqOn_zero_of_jacobi (hcov : ContMDiffCovariantDerivative cov ∞)
    (hmet : IsMetricCompatible cov) (hpinch : QuarterPinched cov) (htor : cov.torsion = 0)
    {γ : ℝ → M} {J : (t : ℝ) → TangentSpace I (γ t)} {t₁ a b : ℝ}
    (ha : a < 0) (hb : t₁ < b) (hJ : ∀ t ∈ Ioo a b, IsJacobiAt cov γ J t)
    (ht₁pos : 0 < t₁) (ht₁π : t₁ < Real.pi / 2)
    (h0 : J 0 = 0) (h1 : J t₁ = 0) :
    ∀ t ∈ Icc 0 t₁, J t = 0 := by
  set h : ℝ → ℝ := fun s => Real.sqrt (inner ℝ (J s) (J s)) with hdef
  set g : ℝ → ℝ := deriv h with hgdef
  set G : ℝ → ℝ := deriv g with hGdef
  -- membership of the interval `[0,t₁]` in `(a,b)`
  have hmem : ∀ t ∈ Icc (0:ℝ) t₁, t ∈ Ioo a b := fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  -- continuity of `h` on `[0,t₁]`
  have hcont : ContinuousOn h (Icc (0:ℝ) t₁) := by
    intro t ht
    have hc := continuousAt_sqrt_inner_self_of_isJacobiAt (cov := cov) (hJ t (hmem t ht))
    exact hc.continuousWithinAt
  intro t ht
  by_contra hJt
  -- `h t > 0`
  have hh0 : h 0 = 0 := by simp [hdef, h0]
  have hh1 : h t₁ = 0 := by simp [hdef, h1]
  have hhne : h t ≠ 0 := by
    intro hz
    have h2 : inner ℝ (J t) (J t) = 0 :=
      le_antisymm (Real.sqrt_eq_zero'.mp hz) (real_inner_self_nonneg)
    exact hJt ((inner_self_eq_zero).mp h2)
  have hhpos : 0 < h t := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hhne)
  have ht0 : 0 < t := by
    rcases eq_or_lt_of_le ht.1 with hh | hh
    · exact absurd (by rw [← hh]; exact hh0) hhne
    · exact hh
  have htt₁ : t < t₁ := by
    rcases eq_or_lt_of_le ht.2 with hh | hh
    · exact absurd (by rw [hh]; exact hh1) hhne
    · exact hh
  -- the consecutive zeros around `t`
  set A : Set ℝ := {s | s ∈ Icc (0:ℝ) t₁ ∧ h s = 0 ∧ s < t} with hAdef
  set B : Set ℝ := {s | s ∈ Icc (0:ℝ) t₁ ∧ h s = 0 ∧ t < s} with hBdef
  have hAne : A.Nonempty := ⟨0, ⟨⟨le_refl 0, ht₁pos.le⟩, by simp [hdef, h0], ht0⟩⟩
  have hBne : B.Nonempty := ⟨t₁, ⟨⟨ht₁pos.le, le_refl t₁⟩, by simp [hdef, h1], htt₁⟩⟩
  have hAbdd : BddAbove A := ⟨t, fun s hs => le_of_lt hs.2.2⟩
  have hBbdd : BddBelow B := ⟨t, fun s hs => le_of_lt hs.2.2⟩
  set a' : ℝ := sSup A with ha'def
  set b' : ℝ := sInf B with hb'def
  have ha'_le : a' ≤ t := csSup_le hAne (fun s hs => le_of_lt hs.2.2)
  have hb'_le : t ≤ b' := le_csInf hBne (fun s hs => le_of_lt hs.2.2)
  have h0A : (0:ℝ) ∈ A := ⟨⟨le_refl 0, ht₁pos.le⟩, by simp [hdef, h0], ht0⟩
  have ha'0 : 0 ≤ a' := le_csSup hAbdd h0A
  have hb'1 : b' ≤ t₁ := csInf_le (⟨t, fun s hs => le_of_lt hs.2.2⟩)
    (by refine ⟨⟨ht₁pos.le, le_refl t₁⟩, ?_, htt₁⟩; simp [hdef, h1])
  -- `a'` and `b'` are zeros of `h`
  have hcont_a : ContinuousAt h a' := by
    have ha_mem : a' ∈ Ioo a b := ⟨by linarith [ha, ha'0], by linarith [hb, hb'1, htt₁]⟩
    exact continuousAt_sqrt_inner_self_of_isJacobiAt (cov := cov) (hJ a' ha_mem)
  have hcont_b : ContinuousAt h b' := by
    have hb_mem : b' ∈ Ioo a b := ⟨by linarith [ha, ha'0, ha'_le, ht0],
      by linarith [hb, hb'1]⟩
    exact continuousAt_sqrt_inner_self_of_isJacobiAt (cov := cov) (hJ b' hb_mem)
  have ha'_mem : h a' = 0 := by
    rcases eq_or_lt_of_le ha'0 with hh | hh
    · rw [← hh]; simp [hdef, h0]
    · have hclosure : a' ∈ closure A := by
        rw [Metric.mem_closure_iff]
        intro ε hε
        obtain ⟨s, hsA, hsa⟩ := exists_lt_of_lt_csSup hAne (show a' - ε < a' by linarith)
        have hsa' : s ≤ a' := le_csSup hAbdd hsA
        exact ⟨s, hsA, by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hsa, hsA.2.2]⟩
      by_contra hne
      have hnbhd : {x : ℝ | h x ≠ 0} ∈ 𝓝 a' := hcont_a (isOpen_ne.mem_nhds hne)
      obtain ⟨s, hst, hsA⟩ := mem_closure_iff_nhds.mp hclosure {x : ℝ | h x ≠ 0} hnbhd
      exact hst hsA.2.1
  have hb'_mem : h b' = 0 := by
    rcases eq_or_lt_of_le hb'1 with hh | hh
    · rw [hh]; simp [hdef, h1]
    · have hclosure : b' ∈ closure B := by
        rw [Metric.mem_closure_iff]
        intro ε hε
        obtain ⟨s, hsB, hbs⟩ := exists_lt_of_csInf_lt hBne (show b' < b' + ε by linarith)
        have hbs' : b' ≤ s := csInf_le hBbdd hsB
        exact ⟨s, hsB, by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hbs, hsB.2.2]⟩
      by_contra hne
      have hnbhd : {x : ℝ | h x ≠ 0} ∈ 𝓝 b' := hcont_b (isOpen_ne.mem_nhds hne)
      obtain ⟨s, hst, hsB⟩ := mem_closure_iff_nhds.mp hclosure {x : ℝ | h x ≠ 0} hnbhd
      exact hst hsB.2.1
  have ha'_lt : a' < t := lt_of_le_of_ne ha'_le (fun hh => hhne (hh ▸ ha'_mem))
  have hlt_b' : t < b' := lt_of_le_of_ne hb'_le (Ne.symm (fun hh => hhne (hh ▸ hb'_mem)))
  have hIab : Ioo a' b' ⊆ Ioo (0:ℝ) t₁ := fun s hs => ⟨by linarith [hs.1, ha'0], by linarith [hs.2, hb'1]⟩
  -- `h > 0` strictly between the consecutive zeros
  have hposab : ∀ s ∈ Ioo a' b', 0 < h s := by
    intro s hs
    have hsne : h s ≠ 0 := by
      intro hsy
      rcases lt_trichotomy s t with hst | hst | hst
      · have hsA : s ∈ A := ⟨⟨le_trans ha'0 hs.1.le, (lt_trans hst htt₁).le⟩, hsy, hst⟩
        have := le_csSup hAbdd hsA
        linarith [this, hs.1]
      · exact hhne (hst ▸ hsy)
      · have hsB : s ∈ B := ⟨⟨(lt_trans ht0 hst).le, le_trans hs.2.le hb'1⟩, hsy, hst⟩
        have := csInf_le hBbdd hsB
        linarith [this, hs.2]
    exact lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hsne)
  -- the Sturm hypotheses
  have hd1 : ∀ s ∈ Ioo a' b', HasDerivAt h (g s) s := by
    intro s hs
    have hsab : s ∈ Ioo a b := ⟨by linarith [hs.1, ha, ha'0],
      by linarith [hs.2, hb, hb'1, htt₁]⟩
    have hspos : 0 < inner ℝ (J s) (J s) := by
      have h1 := hposab s hs
      simp only [hdef] at h1
      exact Real.sqrt_pos.mp h1
    have hsd := sturm_data_at (cov := cov) hcov hmet hpinch htor (hJ s hsab) hspos
    have := hsd.1
    simpa only [hdef, hgdef] using this
  have hd2 : ∀ s ∈ Ioo a' b', HasDerivAt g (G s) s := by
    intro s hs
    have hsab : s ∈ Ioo a b := ⟨by linarith [hs.1, ha, ha'0],
      by linarith [hs.2, hb, hb'1, htt₁]⟩
    have hspos : 0 < inner ℝ (J s) (J s) := by
      have h1 := hposab s hs
      simp only [hdef] at h1
      exact Real.sqrt_pos.mp h1
    have hsd := sturm_data_at (cov := cov) hcov hmet hpinch htor (hJ s hsab) hspos
    have := hsd.2.1
    simpa only [hdef, hgdef, hGdef] using this
  have hineq : ∀ s ∈ Ioo a' b', 0 ≤ G s + 4 * h s := by
    intro s hs
    have hsab : s ∈ Ioo a b := ⟨by linarith [hs.1, ha, ha'0],
      by linarith [hs.2, hb, hb'1, htt₁]⟩
    have hspos : 0 < inner ℝ (J s) (J s) := by
      have h1 := hposab s hs
      simp only [hdef] at h1
      exact Real.sqrt_pos.mp h1
    have hsd := sturm_data_at (cov := cov) hcov hmet hpinch htor (hJ s hsab) hspos
    have := hsd.2.2
    simpa only [hdef, hgdef, hGdef] using this
  have hcont_ab : ContinuousOn h (Icc a' b') :=
    hcont.mono (Icc_subset_Icc ha'0 hb'1)
  have hbπ : b' - a' < Real.pi / 2 := by
    have : b' - a' ≤ t₁ := by linarith
    linarith
  have hnn : ∀ s ∈ Icc a' b', 0 ≤ h s := fun s _ => Real.sqrt_nonneg _
  have hsqrt4 : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  have hzero := sturm_eqOn_zero_Icc (lam := 4) (by norm_num) (by linarith) (by rw [hsqrt4]; exact hbπ)
    hcont_ab ha'_mem hnn hd1 hd2 hineq hb'_mem
  have := hzero ⟨ha'_lt.le, hlt_b'.le⟩
  rw [this] at hhpos
  exact lt_irrefl _ hhpos

end

end Submission.RauchGlobal
