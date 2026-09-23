import Mathlib
import Submission.Work.OddBound.LiftKit

open scoped ContDiff Manifold
open Bundle

namespace Work.OddBound.polygon

open scoped Bundle Topology
open ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.ChartConnection
open Submission.Jacobi
open Submission.ChartCurv
open Submission.CurvatureVec
open Submission.Curvature
open Submission.Rauch
open Submission.RauchGlobal
open Submission.JacobiVec

set_option linter.unusedSectionVars false

/-!
# Reversing the time parameter preserves the Jacobi equation

A Jacobi field along a geodesic, read backwards in time, is again a Jacobi field: the chart Jacobi
equation `D(Dy) + R(y,w)w = 0` is invariant under the substitution `s ↦ t - s`, because the velocity
flips sign *twice* (once in the covariant derivative, once in the curvature term, which is quadratic
in the velocity).  Consequently a conjugate time of `γ` is a conjugate time of `s ↦ γ (t - s)`, which
is the statement `Work.OddBound.polygon.isConjugateTime_comp_sub` below.

## Contents

* `dB_smul_mid`: `dB`, the derivative of the Christoffel symbol in the base point, is linear in its
  middle argument (this is *not* the symmetry `dB_comm_snd`, which needs torsion-freeness — it is
  plain linearity of `chrB` in its first slot);
* `chartCurv_smul_snd`, `chartCurv_neg_snd`: `chartCurv` is quadratic, hence *even*, in its last
  (velocity) argument — with no torsion-freeness hypothesis;
* `christoffelLM_neg_apply`: `christoffelLM` is odd in its velocity argument;
* `chartCovDeriv_neg_field`, `chartCovDeriv_congr_field`: elementary invariance of `chartCovDeriv`;
* `chartCovDeriv_comp_sub_point`, `chartCovDeriv_comp_sub₂`: `chartCovDeriv` of a time-reversed
  field is minus the time-reversed `chartCovDeriv`;
* `isJacobiAt_comp_sub`: `IsJacobiAt` is preserved by `s ↦ t - s`.
-/

section Aux

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
  [I.Boundaryless]
  {cov : CovariantDerivative I E (TangentSpace I (M := M))}
  [ContMDiffCovariantDerivative cov ∞]

/-! ## 1. Algebraic preliminaries -/

/-- The Christoffel symbol as a continuous linear map is **odd** in its velocity argument. -/
lemma christoffelLM_neg_apply (x₀ p : M) (X : TangentSpace I p) (v : E) :
    christoffelLM cov x₀ p (-X) v = -(christoffelLM cov x₀ p X v) := by
  rw [← neg_one_smul ℝ X, Submission.ExpBound2.christoffelLM_smul_mid]
  simp

/-- `dB` (the derivative of the Christoffel symbol in the base point) is linear in its **middle**
argument.  Unlike `dB_comm_snd` this needs no torsion-freeness: it is the linearity of `chrB` in its
first slot. -/
lemma dB_smul_mid (x₀ p : M) (hp : p ∈ (chartAt H x₀).source) (v : E) (c : ℝ) (a b : E) :
    dB cov x₀ p v (c • a) b = c • dB cov x₀ p v a b := by
  rw [dB, dB,
    mvfderiv_chrB_apply (cov := cov) x₀ p (c • a) b v hp,
    mvfderiv_chrB_apply (cov := cov) x₀ p a b v hp]
  simp only [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hcoord : (Module.finBasis ℝ E).coord i (c • a) = c * (Module.finBasis ℝ E).coord i a := by
    rw [map_smul, smul_eq_mul]
  rw [hcoord, smul_smul]
  congr 1
  ring

/-- The coordinate curvature term is **quadratic** in its last (velocity) argument.  No
torsion-freeness hypothesis: each of the four terms of `chartCurv` is a product of two factors
linear in the velocity. -/
lemma chartCurv_smul_snd (x₀ : M) {p : M} (hp : p ∈ (chartAt H x₀).source)
    (X : E) (r : ℝ) (Y : E) :
    chartCurv cov x₀ p X (r • Y) = r ^ 2 • chartCurv cov x₀ p X Y := by
  have h1 : dB cov x₀ p X (r • Y) (r • Y) = r ^ 2 • dB cov x₀ p X Y Y := by
    calc dB cov x₀ p X (r • Y) (r • Y)
        = r • dB cov x₀ p X (r • Y) Y :=
          dB_smul_last (x₀ := x₀) (p := p) hp X (r • Y) r Y
      _ = r • (r • dB cov x₀ p X Y Y) := by
          rw [dB_smul_mid (cov := cov) (x₀ := x₀) (p := p) hp X r Y Y]
      _ = r ^ 2 • dB cov x₀ p X Y Y := by rw [smul_smul, pow_two]
  have h2 : dB cov x₀ p (r • Y) (r • Y) X = r ^ 2 • dB cov x₀ p Y Y X := by
    calc dB cov x₀ p (r • Y) (r • Y) X
        = r • dB cov x₀ p Y (r • Y) X := dB_smul_fst (x₀ := x₀) (p := p) r Y (r • Y) X
      _ = r • (r • dB cov x₀ p Y Y X) := by
          rw [dB_smul_mid (cov := cov) (x₀ := x₀) (p := p) hp Y r Y X]
      _ = r ^ 2 • dB cov x₀ p Y Y X := by rw [smul_smul, pow_two]
  have h3 : chrB cov x₀ p (chrB cov x₀ p (r • Y) (r • Y)) X
      = r ^ 2 • chrB cov x₀ p (chrB cov x₀ p Y Y) X := by
    calc chrB cov x₀ p (chrB cov x₀ p (r • Y) (r • Y)) X
        = chrB cov x₀ p (r • chrB cov x₀ p (r • Y) Y) X := by
          rw [chrB_smul_snd (x₀ := x₀) (p := p) (c := r) (a := r • Y) (b := Y)]
      _ = r • chrB cov x₀ p (chrB cov x₀ p (r • Y) Y) X := by
          rw [chrB_smul_fst (x₀ := x₀) (p := p) (c := r)
            (a := chrB cov x₀ p (r • Y) Y) (b := X) hp]
      _ = r • chrB cov x₀ p (r • chrB cov x₀ p Y Y) X := by
          rw [chrB_smul_fst (x₀ := x₀) (p := p) (c := r) (a := Y) (b := Y) hp]
      _ = r • (r • chrB cov x₀ p (chrB cov x₀ p Y Y) X) := by
          rw [chrB_smul_fst (x₀ := x₀) (p := p) (c := r)
            (a := chrB cov x₀ p Y Y) (b := X) hp]
      _ = r ^ 2 • chrB cov x₀ p (chrB cov x₀ p Y Y) X := by rw [smul_smul, pow_two]
  have h4 : chrB cov x₀ p (chrB cov x₀ p (r • Y) X) (r • Y)
      = r ^ 2 • chrB cov x₀ p (chrB cov x₀ p Y X) Y := by
    calc chrB cov x₀ p (chrB cov x₀ p (r • Y) X) (r • Y)
        = r • chrB cov x₀ p (chrB cov x₀ p (r • Y) X) Y := by
          rw [chrB_smul_snd (x₀ := x₀) (p := p) (c := r)
            (a := chrB cov x₀ p (r • Y) X) (b := Y)]
      _ = r • chrB cov x₀ p (r • chrB cov x₀ p Y X) Y := by
          rw [chrB_smul_fst (x₀ := x₀) (p := p) (c := r) (a := Y) (b := X) hp]
      _ = r • (r • chrB cov x₀ p (chrB cov x₀ p Y X) Y) := by
          rw [chrB_smul_fst (x₀ := x₀) (p := p) (c := r)
            (a := chrB cov x₀ p Y X) (b := Y) hp]
      _ = r ^ 2 • chrB cov x₀ p (chrB cov x₀ p Y X) Y := by rw [smul_smul, pow_two]
  rw [chartCurv, chartCurv, h1, h2, h3, h4]
  simp only [smul_sub, smul_add]

/-- The coordinate curvature term is **even** in its last (velocity) argument. -/
lemma chartCurv_neg_snd (x₀ : M) {p : M} (hp : p ∈ (chartAt H x₀).source) (X Y : E) :
    chartCurv cov x₀ p X (-Y) = chartCurv cov x₀ p X Y := by
  simpa using chartCurv_smul_snd (cov := cov) x₀ hp X (-1 : ℝ) Y

/-! ## 2. `chartCovDeriv` under the time reversal -/

/-- `chartCovDeriv` is additive-negative in the field. -/
lemma chartCovDeriv_neg_field (x₀ : M) (u w y : ℝ → E) (s : ℝ) :
    chartCovDeriv cov x₀ u w (fun σ => -y σ) s = -(chartCovDeriv cov x₀ u w y s) := by
  have hd : deriv (fun σ : ℝ => -y σ) s = -deriv y s := deriv.neg
  simp only [chartCovDeriv, hd, map_neg, neg_add]

/-- `chartCovDeriv` only depends on the germ of the field. -/
lemma chartCovDeriv_congr_field {x₀ : M} {u w y₁ y₂ : ℝ → E} {s : ℝ}
    (h : y₁ =ᶠ[𝓝 s] y₂) :
    chartCovDeriv cov x₀ u w y₁ s = chartCovDeriv cov x₀ u w y₂ s := by
  simp only [chartCovDeriv, h.deriv_eq, h.eq_of_nhds]

/-- **The key computation.**  If `γ = e.symm ∘ u` has velocity `w` (in the chart at `x₀`) and `y`
satisfies the Jacobi equation at time `t - s`, then time reversal sends the covariant derivative of
`y` to minus the time reversal of the covariant derivative: the derivative `deriv y` flips sign
(chain rule) and the Christoffel term `Γ(w) y` flips sign because `christoffelLM` is odd in the
velocity. -/
lemma chartCovDeriv_comp_sub_point (x₀ : M) {u w y : ℝ → E} {t s : ℝ}
    (hy : HasDerivAt y (deriv y (t - s)) (t - s)) :
    chartCovDeriv cov x₀ (fun σ => u (t - σ)) (fun σ => -(w (t - σ))) (fun σ => y (t - σ)) s
      = -(chartCovDeriv cov x₀ u w y (t - s)) := by
  have hdy : deriv (fun σ : ℝ => y (t - σ)) s = -(deriv y (t - s)) := by
    let f : ℝ → ℝ := fun σ => t - σ
    have hσ : HasDerivAt f (-1) s := (hasDerivAt_id s).const_sub t
    have h := (hy.scomp s hσ).deriv
    rw [neg_one_smul] at h
    exact h
  rw [chartCovDeriv, chartCovDeriv, hdy, frameVector_neg, christoffelLM_neg_apply, neg_add]

/-- The same computation, once more: the *second* covariant derivative along the reversed geodesic
is the time reversal of the second covariant derivative along `γ`.  The two sign flips of
`chartCovDeriv_comp_sub_point` cancel. -/
lemma chartCovDeriv_comp_sub₂ (x₀ : M) {u w y : ℝ → E} {t s : ℝ} {U : Set ℝ}
    (hU : U ∈ 𝓝 s) (hy : ∀ σ ∈ U, HasDerivAt y (deriv y (t - σ)) (t - σ))
    (hz : ∀ σ ∈ U, HasDerivAt (chartCovDeriv cov x₀ u w y)
      (deriv (chartCovDeriv cov x₀ u w y) (t - σ)) (t - σ)) :
    chartCovDeriv cov x₀ (fun σ => u (t - σ)) (fun σ => -(w (t - σ)))
        (chartCovDeriv cov x₀ (fun σ => u (t - σ)) (fun σ => -(w (t - σ)))
          (fun σ => y (t - σ))) s
      = chartCovDeriv cov x₀ u w (chartCovDeriv cov x₀ u w y) (t - s) := by
  have hid : chartCovDeriv cov x₀ (fun σ => u (t - σ)) (fun σ => -(w (t - σ)))
        (fun σ => y (t - σ))
      =ᶠ[𝓝 s] (fun σ => -(chartCovDeriv cov x₀ u w y (t - σ))) :=
    Filter.eventually_of_mem hU
      (fun σ hσ => chartCovDeriv_comp_sub_point (cov := cov) x₀ (hy σ hσ))
  rw [chartCovDeriv_congr_field (cov := cov) hid]
  rw [chartCovDeriv_comp_sub_point (cov := cov) x₀
    (y := fun σ => -(chartCovDeriv cov x₀ u w y σ)) ?_]
  · rw [chartCovDeriv_neg_field (cov := cov) x₀ u w (chartCovDeriv cov x₀ u w y), neg_neg]
  · have h := (hz s (mem_of_mem_nhds hU)).neg
    exact h.congr_deriv (deriv.neg (f := chartCovDeriv cov x₀ u w y) (x := t - s)).symm

/-! ## 3. The Jacobi equation is invariant under time reversal -/

/-- **`IsJacobiAt` is invariant under the substitution `s ↦ t - s`.**  The chart data
`(x₀, u, w, y)` become `(x₀, u ∘ σ, -w ∘ σ, y ∘ σ)` where `σ s = t - s`; the unit-speed condition
`chartGram = 1` and the curvature term are unchanged because both are *even* in the velocity. -/
lemma isJacobiAt_comp_sub {γ : ℝ → M} {J : (s : ℝ) → TangentSpace I (γ s)} {t s : ℝ}
    (hJ : IsJacobiAt cov γ J (t - s)) :
    IsJacobiAt cov (fun r => γ (t - r)) (fun r => J (t - r)) s := by
  obtain ⟨x₀, u, w, y, ρ, hρ, htgt, hu, hγ, hframe, hunit, hy, hDy, hjac⟩ :=
    exists_local_data (cov := cov) hJ
  have hmem : ∀ σ ∈ Ioo (s - ρ) (s + ρ), t - σ ∈ Ioo ((t - s) - ρ) ((t - s) + ρ) := by
    intro σ hσ
    obtain ⟨h1, h2⟩ := hσ
    exact ⟨by linarith, by linarith⟩
  have hsub : Ioo (s - ρ) (s + ρ) ∈ 𝓝 s :=
    isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
  have hZeq : ∀ σ ∈ Ioo (s - ρ) (s + ρ),
      chartCovDeriv cov x₀ (fun r => u (t - r)) (fun r => -(w (t - r))) (fun r => y (t - r)) σ
        = -(chartCovDeriv cov x₀ u w y (t - σ)) :=
    fun σ hσ => chartCovDeriv_comp_sub_point (cov := cov) x₀ (hy (t - σ) (hmem σ hσ))
  have hZZ : ∀ σ ∈ Ioo (s - ρ) (s + ρ),
      chartCovDeriv cov x₀ (fun r => u (t - r)) (fun r => -(w (t - r)))
          (chartCovDeriv cov x₀ (fun r => u (t - r)) (fun r => -(w (t - r)))
            (fun r => y (t - r))) σ
        = chartCovDeriv cov x₀ u w (chartCovDeriv cov x₀ u w y) (t - σ) :=
    fun σ hσ => chartCovDeriv_comp_sub₂ (cov := cov) x₀ (U := Ioo (s - ρ) (s + ρ))
      (isOpen_Ioo.mem_nhds hσ)
      (fun σ' hσ' => hy (t - σ') (hmem σ' hσ'))
      (fun σ' hσ' => hDy (t - σ') (hmem σ' hσ'))
  refine ⟨x₀, (fun r => u (t - r)), (fun r => -(w (t - r))), (fun r => y (t - r)),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hsub] with σ hσ
    exact htgt (t - σ) (hmem σ hσ)
  · filter_upwards [hsub] with σ hσ
    let f : ℝ → ℝ := fun r => t - r
    have hσd : HasDerivAt f (-1) σ := (hasDerivAt_id σ).const_sub t
    have h := (hu (t - σ) (hmem σ hσ)).scomp σ hσd
    rw [neg_one_smul] at h
    exact h
  · filter_upwards [hsub] with σ hσ
    exact hγ (t - σ) (hmem σ hσ)
  · filter_upwards [hsub] with σ hσ
    exact hframe (t - σ) (hmem σ hσ)
  · filter_upwards [hsub] with σ hσ
    have h := hunit (t - σ) (hmem σ hσ)
    rw [← h, chartGram_neg_fst, Submission.ExpBound2.chartGram_neg_snd', neg_neg]
  · filter_upwards [hsub] with σ hσ
    let f : ℝ → ℝ := fun r => t - r
    have hσd : HasDerivAt f (-1) σ := (hasDerivAt_id σ).const_sub t
    exact ((hy (t - σ) (hmem σ hσ)).scomp σ hσd).differentiableAt.hasDerivAt
  · filter_upwards [hsub] with σ hσ
    have hid : chartCovDeriv cov x₀ (fun r => u (t - r)) (fun r => -(w (t - r)))
          (fun r => y (t - r))
        =ᶠ[𝓝 σ] (fun r => -(chartCovDeriv cov x₀ u w y (t - r))) :=
      Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hσ) (fun σ' hσ' => hZeq σ' hσ')
    have hg : HasDerivAt (fun r => -(chartCovDeriv cov x₀ u w y (t - r)))
        (deriv (chartCovDeriv cov x₀ u w y) (t - σ)) σ := by
      let f : ℝ → ℝ := fun r => t - r
      have hσd : HasDerivAt f (-1) σ := (hasDerivAt_id σ).const_sub t
      have h := ((hDy (t - σ) (hmem σ hσ)).scomp σ hσd).neg
      refine h.congr_deriv ?_
      rw [neg_one_smul, neg_neg]
    rw [Filter.EventuallyEq.hasDerivAt_iff hid, Filter.EventuallyEq.deriv_eq hid]
    exact hg.differentiableAt.hasDerivAt
  · filter_upwards [hsub] with σ hσ
    have hσ' := hmem σ hσ
    have hsrc : (extChartAt I x₀).symm (u (t - σ)) ∈ (chartAt H x₀).source :=
      mem_source_chartCurve (I := I) (htgt (t - σ) hσ')
    rw [hZZ σ hσ, chartCurv_neg_snd (cov := cov) x₀ hsrc]
    exact hjac (t - σ) hσ'

end Aux

theorem isConjugateTime_comp_sub
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    {γ : ℝ → M} {t : ℝ}
    (h : Submission.ConjRadius.IsConjugateTime cov γ t) :
    Submission.ConjRadius.IsConjugateTime cov (fun s => γ (t - s)) t := by
  obtain ⟨ht, J, hJ, h0, ht0, a, ha, hane⟩ := h
  refine ⟨ht, fun r => J (t - r), ?_, ?_, ?_, t - a, ⟨?_, ?_⟩, ?_⟩
  · intro r
    exact isJacobiAt_comp_sub (cov := cov) (γ := γ) (J := J) (t := t) (s := r) (hJ (t - r))
  · show J (t - 0) = 0
    rw [sub_zero]
    exact ht0
  · show J (t - t) = 0
    rw [sub_self]
    exact h0
  · linarith [ha.2]
  · linarith [ha.1]
  · show J (t - (t - a)) ≠ 0
    rw [sub_sub_cancel]
    exact hane

end Work.OddBound.polygon
