import Mathlib
import Submission.Lib.Unif2.Work.CriticalSet.Defs
import Submission.Lib.Unif2.Work.CriticalSet.criticalPoint_iff_companion
import Submission.Lib.Unif2.Work.CriticalSet.frontier_superlevel_subset_levelSet

/-!
# The boundary of a superlevel set at a regular value

Two calculus facts are proved here and then combined into the stated equality
`Work.CriticalSet.frontier_superlevel_eq_levelSet_of_regularValue`.

* `Work.CriticalSet.eventually_lt_and_gt_of_hasDerivAt` — a real function with strictly positive
  derivative at `0` is `> φ 0` for `t > 0` small and `< φ 0` for `t < 0` small.  This is the
  one-dimensional mean-value/derivative-sign fact, proved from
  `HasDerivAt.tendsto_slope_zero_right`/`_left`.

* `Work.CriticalSet.exists_mem_gt_and_lt_of_not_criticalPoint` — the chart-level transport: if `E`
  is not critical at `x` (so that the real derivative of the chart pullback of `E` at
  `(chartAt ℂ x) x` does not vanish) and `E x = ε`, then every neighbourhood of `x` contains a
  point with `E > ε` and a point with `E < ε`.  The strict positivity of the derivative gives a
  direction `v : ℂ` in which the pullback increases; the straight line `t ↦ (chartAt ℂ x) x + t v`
  is transported back along the chart.

Neither statement uses harmonicity: only the non-vanishing of the (real) derivative of the chart
pullback of `E` at `x` enters, and only via its *definition* `IsCriticalPointAt`.
-/

open Filter Set
open scoped Topology Manifold ContDiff

noncomputable section

namespace Work.CriticalSet

/-- **A function with strictly positive derivative at `0` crosses its value at `0`.**

If `φ : ℝ → ℝ` has derivative `a > 0` at `0`, then `φ t > φ 0` for all sufficiently small `t > 0`
and `φ t < φ 0` for all sufficiently small `t < 0`.

This is the sign information contained in `HasDerivAt`: the slope `t ↦ (φ t - φ 0) / t` tends to
`a > 0`, hence is positive near `0`; for `t > 0` this says `φ t > φ 0`, and for `t < 0` it says
`φ t < φ 0`. -/
theorem eventually_lt_and_gt_of_hasDerivAt {φ : ℝ → ℝ} {a : ℝ} (h : HasDerivAt φ a 0)
    (ha : 0 < a) :
    (∀ᶠ t in 𝓝[>] (0:ℝ), φ 0 < φ t) ∧ (∀ᶠ t in 𝓝[<] (0:ℝ), φ t < φ 0) := by
  have hmem : Set.Ioi (0:ℝ) ∈ 𝓝 a := Ioi_mem_nhds ha
  have hright : ∀ᶠ t in 𝓝[>] (0:ℝ), 0 < t⁻¹ • (φ (0 + t) - φ 0) :=
    h.tendsto_slope_zero_right hmem
  have hleft : ∀ᶠ t in 𝓝[<] (0:ℝ), 0 < t⁻¹ • (φ (0 + t) - φ 0) :=
    h.tendsto_slope_zero_left hmem
  constructor
  · filter_upwards [hright, self_mem_nhdsWithin] with t ht1 ht2
    have ht2' : (0:ℝ) < t := ht2
    have hmul : 0 < t * (t⁻¹ * (φ (0 + t) - φ 0)) := mul_pos ht2' ht1
    have heq : t * (t⁻¹ * (φ (0 + t) - φ 0)) = φ (0 + t) - φ 0 := by
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt ht2'), one_mul]
    rw [heq, zero_add, sub_pos] at hmul
    exact hmul
  · filter_upwards [hleft, self_mem_nhdsWithin] with t ht1 ht2
    have ht2' : t < (0:ℝ) := ht2
    have hmul : t * (t⁻¹ * (φ (0 + t) - φ 0)) < 0 := mul_neg_of_neg_of_pos ht2' ht1
    have heq : t * (t⁻¹ * (φ (0 + t) - φ 0)) = φ (0 + t) - φ 0 := by
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_lt ht2'), one_mul]
    rw [heq, zero_add, sub_neg] at hmul
    exact hmul

/-- **A non-critical point is a crossing point of its level set.**

Let `E : X → ℝ` be defined on a complex charted space, `x : X` with `E x = ε`, and suppose that `x`
is *not* a critical point of `E`, i.e. (by definition of `IsCriticalPointAt`) the real derivative of
the chart pullback `E ∘ (chartAt ℂ x).symm` at `(chartAt ℂ x) x` is non-zero.  Then every
neighbourhood of `x` contains a point with `E > ε` and a point with `E < ε`.

Proof.  Write `g := E ∘ (chartAt ℂ x).symm`, `z := (chartAt ℂ x) x`.  Since `fderiv ℝ g z ≠ 0` there
is `v : ℂ` with `(fderiv ℝ g z) v ≠ 0`; replacing `v` by `-v` we may assume this number is positive,
so `g` is differentiable at `z` and `t ↦ g (z + t • v)` has strictly positive derivative at `0`.
By `eventually_lt_and_gt_of_hasDerivAt` it is `> ε = g z` for small `t > 0` and `< ε` for small
`t < 0`.  Finally `(chartAt ℂ x).symm` is continuous at `z` with value `x`, so the points
`(chartAt ℂ x).symm (z + t • v)` for small `t` of the appropriate sign lie in any prescribed
neighbourhood of `x`.  No harmonicity, and no continuity of `E` at `z₀`, is used. -/
theorem exists_mem_gt_and_lt_of_not_criticalPoint {X : Type*} [TopologicalSpace X]
    [ChartedSpace ℂ X] {E : X → ℝ} {x : X} {ε : ℝ} (hE : E x = ε)
    (hcrit : ¬ IsCriticalPointAt E x) :
    (∀ U ∈ 𝓝 x, ∃ y ∈ U, ε < E y) ∧ (∀ U ∈ 𝓝 x, ∃ y ∈ U, E y < ε) := by
  classical
  have hL : fderiv ℝ (E ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) ≠ 0 := hcrit
  have hgz : (E ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) = ε := by
    simp only [Function.comp_apply]
    rw [(chartAt ℂ x).left_inv (mem_chart_source ℂ x), hE]
  have hdiff : DifferentiableAt ℝ (E ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) := by
    by_contra h
    exact hL (fderiv_zero_of_not_differentiableAt h)
  have hfd : HasFDerivAt (E ∘ (chartAt ℂ x).symm)
      (fderiv ℝ (E ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)) ((chartAt ℂ x) x) :=
    hdiff.hasFDerivAt
  -- a direction of strictly positive derivative
  obtain ⟨v, hv⟩ : ∃ v : ℂ, 0 < fderiv ℝ (E ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) v := by
    have hne : ∃ v : ℂ, fderiv ℝ (E ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) v ≠ 0 := by
      by_contra h
      rw [not_exists] at h
      refine hL (ContinuousLinearMap.ext fun v => ?_)
      simpa using not_not.mp (h v)
    obtain ⟨v, hv⟩ := hne
    rcases lt_or_gt_of_ne hv with h | h
    · exact ⟨-v, by simpa using neg_pos.mpr h⟩
    · exact ⟨v, h⟩
  -- the curve `t ↦ z + t • v` and the pullback along it
  have hcurve : HasDerivAt (fun t : ℝ => (chartAt ℂ x) x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add ((chartAt ℂ x) x)
  have hfd' : HasFDerivAt (E ∘ (chartAt ℂ x).symm)
      (fderiv ℝ (E ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x))
      ((fun t : ℝ => (chartAt ℂ x) x + t • v) 0) := by simpa using hfd
  have hφ : HasDerivAt (fun t : ℝ => (E ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x + t • v))
      (fderiv ℝ (E ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) v) 0 := by
    change HasDerivAt ((E ∘ (chartAt ℂ x).symm) ∘ fun t : ℝ => (chartAt ℂ x) x + t • v)
      (fderiv ℝ (E ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) v) 0
    exact hfd'.comp_hasDerivAt 0 hcurve
  have hφ0 : (E ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x + (0:ℝ) • v) = ε := by
    simpa only [zero_smul, add_zero] using hgz
  have hcross := eventually_lt_and_gt_of_hasDerivAt hφ hv
  have hcp : ∀ᶠ t in 𝓝[>] (0:ℝ), ε < (E ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x + t • v) := by
    filter_upwards [hcross.1] with t ht
    exact lt_of_eq_of_lt hφ0.symm ht
  have hcn : ∀ᶠ t in 𝓝[<] (0:ℝ), (E ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x + t • v) < ε := by
    filter_upwards [hcross.2] with t ht
    exact lt_of_lt_of_eq ht hφ0
  -- transporting back along the chart
  have hct : ContinuousAt (fun t : ℝ => (chartAt ℂ x) x + t • v) 0 := hcurve.continuousAt
  have hcurve_tendsto : Tendsto (fun t : ℝ => (chartAt ℂ x) x + t • v) (𝓝[>] (0:ℝ))
      (𝓝 ((chartAt ℂ x) x)) := by
    have h1 : Tendsto (fun t : ℝ => (chartAt ℂ x) x + t • v) (𝓝 (0:ℝ))
        (𝓝 ((chartAt ℂ x) x)) := by
      simpa using hct.tendsto
    exact h1.mono_left nhdsWithin_le_nhds
  have hcurve_tendsto' : Tendsto (fun t : ℝ => (chartAt ℂ x) x + t • v) (𝓝[<] (0:ℝ))
      (𝓝 ((chartAt ℂ x) x)) := by
    have h1 : Tendsto (fun t : ℝ => (chartAt ℂ x) x + t • v) (𝓝 (0:ℝ))
        (𝓝 ((chartAt ℂ x) x)) := by
      simpa using hct.tendsto
    exact h1.mono_left nhdsWithin_le_nhds
  have htend : Tendsto (fun t : ℝ => (chartAt ℂ x).symm ((chartAt ℂ x) x + t • v))
      (𝓝[>] (0:ℝ)) (𝓝 x) := (tendsto_symm_chartAt_companion x).comp hcurve_tendsto
  have htend' : Tendsto (fun t : ℝ => (chartAt ℂ x).symm ((chartAt ℂ x) x + t • v))
      (𝓝[<] (0:ℝ)) (𝓝 x) := (tendsto_symm_chartAt_companion x).comp hcurve_tendsto'
  constructor
  · intro U hU
    have h1 : ∀ᶠ t in 𝓝[>] (0:ℝ), (chartAt ℂ x).symm ((chartAt ℂ x) x + t • v) ∈ U := htend hU
    have h3 : ∀ᶠ t in 𝓝[>] (0:ℝ),
        (chartAt ℂ x).symm ((chartAt ℂ x) x + t • v) ∈ U ∧
          ε < E ((chartAt ℂ x).symm ((chartAt ℂ x) x + t • v)) := h1.and hcp
    obtain ⟨t, ht⟩ := h3.exists
    exact ⟨_, ht.1, ht.2⟩
  · intro U hU
    have h1 : ∀ᶠ t in 𝓝[<] (0:ℝ), (chartAt ℂ x).symm ((chartAt ℂ x) x + t • v) ∈ U := htend' hU
    have h3 : ∀ᶠ t in 𝓝[<] (0:ℝ),
        (chartAt ℂ x).symm ((chartAt ℂ x) x + t • v) ∈ U ∧
          E ((chartAt ℂ x).symm ((chartAt ℂ x) x + t • v)) < ε := h1.and hcn
    obtain ⟨t, ht⟩ := h3.exists
    exact ⟨_, ht.1, ht.2⟩

/-- **At a regular value, the boundary of the superlevel set is exactly the level set.**

For `E` with the weak Green function data at `z₀`, `ε > 0` a *regular* value of `E` on
`X ∖ {z₀}`: the part of the frontier of `{x | ε ≤ E x}` inside `X ∖ {z₀}` is exactly the level set
`{x | E x = ε} ∩ (X ∖ {z₀})`.  Together with `Work.CriticalSet.frontier_superlevel_subset_levelSet`
and `Work.CriticalSet.IsRegularLevel` this says that `{E ≥ ε}` is a compact sub-surface whose
boundary is the `C¹` curve `{E = ε}`.

Proof strategy.  `⊆` is `Work.CriticalSet.frontier_superlevel_subset_levelSet` (continuity of `E` off
`z₀`).  For `⊇`, let `x ∈ punctured z₀` with `E x = ε`.  Since `x` is not critical, in the preferred
chart at `x` the pullback `g := E ∘ (chartAt ℂ x).symm` satisfies `fderiv ℝ g ((chartAt ℂ x) x) ≠ 0`.
Hence there is `v : ℂ` with `(fderiv ℝ g ((chartAt ℂ x) x)) v ≠ 0`; replacing `v` by `-v` if necessary
we may suppose this number is positive, and then `t ↦ g ((chartAt ℂ x) x + t v)` is `> ε` for `t > 0`
small and `< ε` for `t < 0` small (derivative at `0` is non-zero, e.g. via
`HasFDerivAt.eventually_lt`/`eventually_gt` or the mean value inequality).  Transporting back along the
chart (which maps a neighbourhood of `x` onto a neighbourhood of `(chartAt ℂ x) x`) shows that every
neighbourhood of `x` contains a point with `E > ε` and a point with `E < ε`.  Therefore
`x ∈ closure {x | ε ≤ E x}` and `x ∉ interior {x | ε ≤ E x}`, i.e. `x ∈ frontier {x | ε ≤ E x}`. -/
theorem frontier_superlevel_eq_levelSet_of_regularValue {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {z₀ : X} {E : X → ℝ}
    (hE : Submission.HasGreenFunctionWeak z₀ E) {ε : ℝ} (hε : 0 < ε)
    (hreg : IsRegularValueOn E (punctured z₀) ε) :
    frontier {x : X | ε ≤ E x} ∩ punctured z₀ = {x : X | E x = ε} ∩ punctured z₀ := by
  apply Set.Subset.antisymm
  · intro x hx
    exact ⟨frontier_superlevel_subset_levelSet hE hε hx, hx.2⟩
  · rintro x ⟨hxE, hxp⟩
    have hxne : x ≠ z₀ := mem_punctured.mp hxp
    have hcrit : ¬ IsCriticalPointAt E x := hreg x (mem_punctured.mpr hxne) hxE
    obtain ⟨hgt, hlt⟩ := exists_mem_gt_and_lt_of_not_criticalPoint hxE hcrit
    refine ⟨?_, hxp⟩
    rw [frontier]
    refine ⟨?_, ?_⟩
    · rw [mem_closure_iff_nhds]
      intro U hU
      obtain ⟨y, hyU, hyE⟩ := hgt U hU
      exact ⟨y, hyU, le_of_lt hyE⟩
    · intro hint
      rw [mem_interior_iff_mem_nhds] at hint
      obtain ⟨y, hyU, hyE⟩ := hlt _ hint
      exact absurd hyU (not_le.mpr hyE)

end Work.CriticalSet
