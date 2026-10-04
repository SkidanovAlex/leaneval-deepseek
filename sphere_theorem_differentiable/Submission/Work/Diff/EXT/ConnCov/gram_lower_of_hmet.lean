import Mathlib
import Submission.Work.Diff.EXT.ChartCoreDefs
import Submission.Work.Diff.EXT.sum_chartMatFun_eq_inner
import Submission.Work.Diff.EXT.chartMatFun_centre_posDef_tfree
import Submission.Work.Diff.EXT.basis_coeff_norm_equiv
import Submission.Work.Diff.EXT.chartRic_partial_jet
import Submission.Work.Diff.EXT.ConnCov.quadForm_uniform_lower_compact

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A uniform lower bound (`hell`) for the chart Gram matrix from a two-sided metric comparison

`Work.Diff.EXT.ConnCov.gram_lower_of_hmet` is the "uniform ellipticity" input of the
connection-comparison (`ConnCov`) area: along a family of smooth metrics `G` on `[0,T)` whose
time-`t` quadratic form is two-sided comparable with the initial one,

`⟨u,u⟩_{G t} ≤ e^{2 n C t} ⟨u,u⟩_{G 0}`  and  `⟨u,u⟩_{G 0} ≤ e^{2 n C t} ⟨u,u⟩_{G t}`
(`n = finrank ℝ E`),

there is `c > 0` such that, uniformly over `t ∈ [T/2, T)`, over `y` in a compact subset `K'` of the
chart target of `x₀` and over `a : E`,

`c ‖a‖² ≤ (G t)(v, v)`,  `v = frameVector I x₀ ((extChartAt I x₀).symm y) a`.

## Method

* The two-sided comparison is *monotone in time*: for `t ∈ [T/2,T)` the second half gives
  `e^{-2nCT} ⟨u,u⟩_{G 0} ≤ ⟨u,u⟩_{G t}` for **every** tangent vector `u` (the exponential factor is
  `≤ e^{2nCt}` and `⟨u,u⟩_{G 0} ≥ 0`).  So it is enough to bound `(G 0)` in the chart frame.
* For a fixed metric `g = G 0` the chart matrix
  `chartMatFun g x₀ y i j = g(vᵢ, vⱼ)`, `vᵢ = frameVector I x₀ p (bB i)`, `p = (extChartAt I x₀).symm y`,
  is a *positive definite* quadratic form at every point `y` of the chart target (the frame vectors
  span, and the frame vector of a nonzero coordinate vector is nonzero:
  `Work.Diff.EXT.frameVector_eq_zero_iff_tfree`), and its entries are continuous there
  (`Work.Diff.EXT.contDiffAt_chartMatFun`).  Compactness of `K'` therefore gives `δ > 0` with
  `δ ∑ vᵢ² ≤ ∑ᵢⱼ vᵢvⱼ (chartMatFun (G 0) x₀ y)ᵢⱼ` for all `y ∈ K'`
  (`Work.Diff.EXT.ConnCov.uniform_posDef_of_compact`).
* Evaluating at the coefficients `v = bB.repr a` of a vector `a : E` and rewriting the quadratic
  form as the metric of the frame vector (`Work.Diff.EXT.sum_chartMatFun_eq_inner` together with
  `frameVector_sum_tfree` and `Module.Basis.sum_repr`) turns this into
  `δ ∑ᵢ (bB.repr a)ᵢ² ≤ (G 0)(v_a, v_a)`; the coefficient norm equivalence
  (`Work.Diff.EXT.basis_coeff_norm_equiv`) upgrades `∑ᵢ (bB.repr a)ᵢ²` to `‖a‖²`.
-/

set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set

namespace Work.Diff.EXT.ConnCov

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-! ## The quadratic form of the chart matrix of a frame vector -/

/-- **The quadratic form of the chart matrix of a vector is the metric of its frame vector.**
For `a : E` with coefficients `bB.repr a` in the canonical basis of the model space, the quadratic
form of the chart matrix of `g` at the chart coordinate `y` is the `g`-square of the frame vector of
`a` at `p = (extChartAt I x₀).symm y`. -/
theorem chartMatFun_qform_repr (g : Submission.Diff.SMet I M) (x₀ : M) (y : E) (a : E) :
    (∑ i, ∑ j, (Work.Diff.EXT.bB (E := E)).repr a i * (Work.Diff.EXT.bB (E := E)).repr a j
        * Work.Diff.EXT.chartMatFun g x₀ y i j)
      = g.inner ((extChartAt I x₀).symm y)
          (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y) a)
          (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y) a) := by
  rw [Work.Diff.EXT.sum_chartMatFun_eq_inner (I := I) (M := M) g x₀ y]
  rw [← Work.Diff.EXT.frameVector_sum_tfree, Module.Basis.sum_repr]

/-! ## Positive definiteness of the chart matrix on the chart target -/

/-- **The chart matrix of a smooth metric is positive definite as a quadratic form at every point
of the chart target.**  For `v ≠ 0` the combination `∑ᵢ vᵢ σᵢ` of coordinate frame vectors is
nonzero (`Work.Diff.EXT.frameVector_eq_zero_iff_tfree` and linear independence of the basis), so the
quadratic form is the squared `g`-length of a nonzero tangent vector. -/
theorem chartMatFun_qform_pos_of_target (g : Submission.Diff.SMet I M) (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) {v : Fin (Module.finrank ℝ E) → ℝ} (hv : v ≠ 0) :
    0 < ∑ i, ∑ j, v i * v j * Work.Diff.EXT.chartMatFun g x₀ y i j := by
  have hp : (extChartAt I x₀).symm y ∈ (chartAt H x₀).source := by
    have h1 : (extChartAt I x₀).symm y ∈ (extChartAt I x₀).source :=
      (extChartAt I x₀).map_target hy
    rwa [extChartAt_source] at h1
  have hsum : (∑ i, v i • Submission.Geodesic.frameVector (I := I) x₀
        ((extChartAt I x₀).symm y) (Work.Diff.EXT.bB (E := E) i))
      = Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
          (∑ i, v i • Work.Diff.EXT.bB (E := E) i) := by
    rw [Work.Diff.EXT.frameVector_sum_tfree]
  rw [Work.Diff.EXT.sum_chartMatFun_eq_inner (I := I) (M := M) g x₀ y v]
  simp only [hsum]
  refine g.pos _ _ ?_
  intro h0
  have h1 : (∑ i, v i • Work.Diff.EXT.bB (E := E) i) = 0 :=
    (Work.Diff.EXT.frameVector_eq_zero_iff_tfree (I := I) (x₀ := x₀)
      (p := (extChartAt I x₀).symm y) hp _).mp h0
  have h2 : ∀ i, v i = 0 :=
    (Fintype.linearIndependent_iff.mp (Work.Diff.EXT.bB (E := E)).linearIndependent) v h1
  exact hv (funext h2)

/-! ## The uniform lower bound for the initial metric -/

/-- **Uniform lower bound for a fixed metric in the chart frame of a compact set.**  For a compact
`K'` inside the target of the chart at `x₀` there is `c > 0` with
`c ‖a‖² ≤ g(v_a, v_a)` for all `y ∈ K'` and all `a : E`, where `v_a` is the frame vector of `a` at
`p = (extChartAt I x₀).symm y`. -/
theorem gram_lower_of_compact_metric [I.Boundaryless] [T2Space M]
    (g : Submission.Diff.SMet I M) (x₀ : M) (K' : Set E)
    (hK'c : IsCompact K') (hK't : K' ⊆ (extChartAt I x₀).target) :
    ∃ c : ℝ, 0 < c ∧ ∀ y ∈ K', ∀ a : E,
      c * ‖a‖ ^ 2 ≤ g.inner ((extChartAt I x₀).symm y)
        (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y) a)
        (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y) a) := by
  have hcont : ∀ y ∈ K', ∀ i j : Fin (Module.finrank ℝ E),
      ContinuousAt (fun y' : E => Work.Diff.EXT.chartMatFun g x₀ y' i j) y := by
    intro y hy i j
    exact (((continuous_apply j).comp (continuous_apply i)).continuousAt.comp
      (Work.Diff.EXT.contDiffAt_chartMatFun (I := I) (M := M) g x₀ (hK't hy)).continuousAt)
  have hpos : ∀ y ∈ K', ∀ v : Fin (Module.finrank ℝ E) → ℝ, v ≠ 0 →
      0 < ∑ i, ∑ j, v i * v j * Work.Diff.EXT.chartMatFun g x₀ y i j :=
    fun y hy v hv => chartMatFun_qform_pos_of_target (I := I) (M := M) g x₀ (hK't hy) hv
  obtain ⟨δ, hδpos, hδ⟩ := quadForm_uniform_lower_compact (X := E) (n := Module.finrank ℝ E)
    (A := fun y : E => Work.Diff.EXT.chartMatFun g x₀ y) (C := K') hK'c hcont hpos
  obtain ⟨K1, K2, _hK1, hK2, hbb⟩ :=
    Work.Diff.EXT.basis_coeff_norm_equiv (E := E) (Work.Diff.EXT.bB (E := E))
  refine ⟨δ / K2, div_pos hδpos hK2, fun y hy a => ?_⟩
  have hcoef : ‖a‖ ^ 2 ≤ K2 * ∑ i, ((Work.Diff.EXT.bB (E := E)).repr a i) ^ 2 := by
    have h := (hbb ((Work.Diff.EXT.bB (E := E)).repr a)).2
    rwa [Module.Basis.sum_repr] at h
  have hquad : (∑ i, ∑ j, (Work.Diff.EXT.bB (E := E)).repr a i
        * (Work.Diff.EXT.bB (E := E)).repr a j * Work.Diff.EXT.chartMatFun g x₀ y i j)
      = g.inner ((extChartAt I x₀).symm y)
          (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y) a)
          (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y) a) :=
    chartMatFun_qform_repr (I := I) (M := M) g x₀ y a
  have hstep : (δ / K2) * ‖a‖ ^ 2
      ≤ ∑ i, ∑ j, (Work.Diff.EXT.bB (E := E)).repr a i
          * (Work.Diff.EXT.bB (E := E)).repr a j * Work.Diff.EXT.chartMatFun g x₀ y i j := by
    calc (δ / K2) * ‖a‖ ^ 2
        ≤ (δ / K2) * (K2 * ∑ i, ((Work.Diff.EXT.bB (E := E)).repr a i) ^ 2) :=
          mul_le_mul_of_nonneg_left hcoef (div_nonneg hδpos.le hK2.le)
      _ = δ * ∑ i, ((Work.Diff.EXT.bB (E := E)).repr a i) ^ 2 := by
          field_simp
      _ ≤ ∑ i, ∑ j, (Work.Diff.EXT.bB (E := E)).repr a i
            * (Work.Diff.EXT.bB (E := E)).repr a j * Work.Diff.EXT.chartMatFun g x₀ y i j :=
          hδ y hy ((Work.Diff.EXT.bB (E := E)).repr a)
  rw [← hquad]
  exact hstep

/-! ## The target -/

theorem gram_lower_of_hmet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (G : ℝ → Submission.Diff.SMet I M) (T C : ℝ) (hT : 0 < T) (hC : 0 ≤ C)
    (hmet : ∀ t ∈ Set.Ico 0 T, ∀ x : M, ∀ u : TangentSpace I x,
      (G t).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G 0).inner x u u ∧
      (G 0).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G t).inner x u u)
    (x₀ : M) (K' : Set E) (hK'c : IsCompact K') (hK't : K' ⊆ (extChartAt I x₀).target)
    (hK'ne : K'.Nonempty) :
    ∃ c : ℝ, 0 < c ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ y ∈ K', ∀ a : E,
      c * ‖a‖ ^ 2 ≤ (G t).inner (Work.Diff.EXT.pt (I := I) x₀ y)
        (Submission.Geodesic.frameVector (I := I) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) a)
        (Submission.Geodesic.frameVector (I := I) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) a) := by
  obtain ⟨c₀, hc₀pos, hc₀⟩ :=
    gram_lower_of_compact_metric (I := I) (M := M) (G 0) x₀ K' hK'c hK't
  refine ⟨Real.exp (-(2 * ((Module.finrank ℝ E : ℝ) * C) * T)) * c₀,
    mul_pos (Real.exp_pos _) hc₀pos, ?_⟩
  intro t ht y hy a
  have ht0 : t ∈ Set.Ico 0 T := ⟨by linarith [ht.1, hT], ht.2⟩
  have hA0 : (0 : ℝ) ≤ 2 * ((Module.finrank ℝ E : ℝ) * C) :=
    mul_nonneg (by norm_num) (mul_nonneg (Nat.cast_nonneg _) hC)
  have hG0 : c₀ * ‖a‖ ^ 2 ≤ (G 0).inner (Work.Diff.EXT.pt (I := I) x₀ y)
      (Submission.Geodesic.frameVector (I := I) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) a)
      (Submission.Geodesic.frameVector (I := I) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) a) :=
    hc₀ y hy a
  have hnn : 0 ≤ (G 0).inner (Work.Diff.EXT.pt (I := I) x₀ y)
      (Submission.Geodesic.frameVector (I := I) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) a)
      (Submission.Geodesic.frameVector (I := I) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) a) := by
    rcases eq_or_ne (Submission.Geodesic.frameVector (I := I) x₀
      (Work.Diff.EXT.pt (I := I) x₀ y) a) 0 with h0 | h0
    · rw [h0]
      simp
    · exact (G 0).pos _ _ h0 |>.le
  have hcmp := (hmet t ht0 (Work.Diff.EXT.pt (I := I) x₀ y)
    (Submission.Geodesic.frameVector (I := I) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) a)).2
  have hexpmono : Real.exp (-(2 * ((Module.finrank ℝ E : ℝ) * C) * T))
      ≤ Real.exp (-(2 * ((Module.finrank ℝ E : ℝ) * C) * t)) := by
    rw [Real.exp_le_exp]
    have h := mul_le_mul_of_nonneg_left ht.2.le hA0
    linarith
  have hexp1 : Real.exp (-(2 * ((Module.finrank ℝ E : ℝ) * C) * t))
      * Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  calc (Real.exp (-(2 * ((Module.finrank ℝ E : ℝ) * C) * T)) * c₀) * ‖a‖ ^ 2
      = Real.exp (-(2 * ((Module.finrank ℝ E : ℝ) * C) * T)) * (c₀ * ‖a‖ ^ 2) := by ring
    _ ≤ Real.exp (-(2 * ((Module.finrank ℝ E : ℝ) * C) * T))
          * ((G 0).inner (Work.Diff.EXT.pt (I := I) x₀ y)
            (Submission.Geodesic.frameVector (I := I) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) a)
            (Submission.Geodesic.frameVector (I := I) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) a)) :=
        mul_le_mul_of_nonneg_left hG0 (Real.exp_pos _).le
    _ ≤ Real.exp (-(2 * ((Module.finrank ℝ E : ℝ) * C) * t))
          * ((G 0).inner (Work.Diff.EXT.pt (I := I) x₀ y)
            (Submission.Geodesic.frameVector (I := I) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) a)
            (Submission.Geodesic.frameVector (I := I) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) a)) :=
        mul_le_mul_of_nonneg_right hexpmono hnn
    _ ≤ (G t).inner (Work.Diff.EXT.pt (I := I) x₀ y)
          (Submission.Geodesic.frameVector (I := I) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) a)
          (Submission.Geodesic.frameVector (I := I) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) a) := by
        calc Real.exp (-(2 * ((Module.finrank ℝ E : ℝ) * C) * t))
              * ((G 0).inner (Work.Diff.EXT.pt (I := I) x₀ y)
                (Submission.Geodesic.frameVector (I := I) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) a)
                (Submission.Geodesic.frameVector (I := I) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) a))
            ≤ Real.exp (-(2 * ((Module.finrank ℝ E : ℝ) * C) * t))
              * (Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t)
                * ((G t).inner (Work.Diff.EXT.pt (I := I) x₀ y)
                  (Submission.Geodesic.frameVector (I := I) x₀
                    (Work.Diff.EXT.pt (I := I) x₀ y) a)
                  (Submission.Geodesic.frameVector (I := I) x₀
                    (Work.Diff.EXT.pt (I := I) x₀ y) a))) :=
              mul_le_mul_of_nonneg_left hcmp (Real.exp_pos _).le
          _ = (Real.exp (-(2 * ((Module.finrank ℝ E : ℝ) * C) * t))
                * Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t))
              * ((G t).inner (Work.Diff.EXT.pt (I := I) x₀ y)
                (Submission.Geodesic.frameVector (I := I) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) a)
                (Submission.Geodesic.frameVector (I := I) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) a)) :=
              by ring
          _ = (G t).inner (Work.Diff.EXT.pt (I := I) x₀ y)
                (Submission.Geodesic.frameVector (I := I) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) a)
                (Submission.Geodesic.frameVector (I := I) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) a) := by
              rw [hexp1, one_mul]

end Work.Diff.EXT.ConnCov
