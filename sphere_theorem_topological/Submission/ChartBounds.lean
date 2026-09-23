import Submission.Distance

/-!
# Bounds for the Riemannian metric in a chart

This module compares the Riemannian metric, expressed in the chart at `x₀` as the quadratic form
`chartGram x₀ p a a` on the coordinate vectors `a : E`, with the norm of the model space `E`.

## Main results

* `chartGram_eq_sum_repr`: the expansion of the chart metric in a basis of `E`;
* `continuousAt_chartGram_prod`: `(p, a) ↦ chartGram x₀ p a a` is continuous at `(p₀, a₀)` whenever
  `p₀` lies in the chart at `x₀` (joint continuity — used both for the comparison with the norm and
  for the integrability of the speed);
* `frameVector_eq_zero_iff`, `chartGram_self_pos`: the chart metric is positive definite at points
  of the chart;
* `exists_chartGram_bounds`: **the chart metric is comparable to the model norm on a compact subset
  of the chart**: there are `0 < λ ≤ Λ` with `λ‖a‖² ≤ chartGram x₀ p a a ≤ Λ‖a‖²` for all `p ∈ K`
  and all `a : E`.

## Method

The comparison on a compact set `K` is obtained by minimising and maximising the *continuous*
function `(p, c) ↦ ∑ᵢ ∑ⱼ cᵢ cⱼ ⟪σᵢ, σⱼ⟫_p` on the compact set `K × {c : ‖c‖ = 1}`, where
`σᵢ = frameVector x₀ p (bb i)` and `bb` is a basis of `E`.  Positivity on that set follows from the
positive definiteness of the metrics `chartGram x₀ p · ·` together with the linear independence of
the frame (`frameVector_eq_zero_iff`).  Homogeneity of degree two in `a` upgrades the bound on the
unit sphere to all `a : E`.  Working in coefficients of a basis is what makes the joint continuity
immediate (the metric is only known to be smooth in the base point for *fixed* coordinate vectors).

## Gotchas

* `E` must be nontrivial for the unit sphere of the coefficient space to be nonempty; the bounds
  lemma therefore carries `[Nontrivial E]`.  In the application `2 ≤ finrank ℝ E`.
-/
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Submission.Geodesic
open Submission.ChartConnection
open Submission.Length
open Submission.Distance
open Submission.Gauss

namespace Submission.ChartBounds

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

noncomputable section

/-! ## Expansion in a basis -/

/-- Expansion of the chart metric in a basis, in both arguments. -/
lemma chartGram_eq_sum_repr {ι : Type*} [Fintype ι] (bb : Module.Basis ι ℝ E)
    (x₀ p : M) (a b : E) :
    chartGram (I := I) x₀ p a b
      = ∑ i, ∑ j, (bb.repr a i) * (bb.repr b j) * chartGram (I := I) x₀ p (bb i) (bb j) := by
  rw [chartGram_eq_sum_fst_repr (I := I) bb x₀ p a b]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [chartGram_eq_sum_snd_repr (I := I) bb x₀ p (bb i) b, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-! ## Joint continuity -/

/-- The coefficient functionals of a basis are continuous. -/
lemma continuous_basis_repr {ι : Type*} [Fintype ι] (bb : Module.Basis ι ℝ E) (i : ι) :
    Continuous (fun v : E => bb.repr v i) := by
  have h : (fun v : E => bb.repr v i) = fun v : E => bb.equivFun v i := by
    funext v
    exact (congrFun (Module.Basis.equivFun_apply bb v) i).symm
  rw [h]
  exact (continuous_apply i).comp (LinearMap.continuous_of_finiteDimensional bb.equivFun.toLinearMap)

/-- **Joint continuity of the chart metric (quadratic form).**  For `p₀` in the chart at `x₀`, the
function `(p, a) ↦ chartGram x₀ p a a` is continuous at `(p₀, a₀)`. -/
lemma continuousAt_chartGram_prod (x₀ : M) {p₀ : M} (hp₀ : p₀ ∈ (chartAt H x₀).source)
    (a₀ : E) :
    ContinuousAt (fun q : M × E => chartGram (I := I) x₀ q.1 q.2 q.2) (p₀, a₀) := by
  obtain bb : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := Module.finBasis ℝ E
  have hfun : (fun q : M × E => chartGram (I := I) x₀ q.1 q.2 q.2)
      = fun q : M × E => ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          (bb.repr q.2 i) * (bb.repr q.2 j) * chartGram (I := I) x₀ q.1 (bb i) (bb j) := by
    funext q
    exact chartGram_eq_sum_repr (I := I) bb x₀ q.1 q.2 q.2
  rw [hfun]
  refine tendsto_finsetSum Finset.univ fun i _ => ?_
  refine tendsto_finsetSum Finset.univ fun j _ => ?_
  have h1 : ContinuousAt (fun q : M × E => bb.repr q.2 i) (p₀, a₀) := by
    show ContinuousAt ((fun v : E => bb.repr v i) ∘ Prod.snd) (p₀, a₀)
    exact (continuous_basis_repr bb i).continuousAt.comp continuousAt_snd
  have h2 : ContinuousAt (fun q : M × E => bb.repr q.2 j) (p₀, a₀) := by
    show ContinuousAt ((fun v : E => bb.repr v j) ∘ Prod.snd) (p₀, a₀)
    exact (continuous_basis_repr bb j).continuousAt.comp continuousAt_snd
  have h3 : ContinuousAt (fun q : M × E => chartGram (I := I) x₀ q.1 (bb i) (bb j)) (p₀, a₀) := by
    show ContinuousAt ((fun p : M => chartGram (I := I) x₀ p (bb i) (bb j)) ∘ Prod.fst) (p₀, a₀)
    exact (continuousAt_chartGram (I := I) x₀ (bb i) (bb j) hp₀).comp continuousAt_fst
  have H1 : Filter.Tendsto (fun q : M × E => bb.repr q.2 i) (𝓝 (p₀, a₀)) (𝓝 (bb.repr a₀ i)) :=
    h1.tendsto
  have H2 : Filter.Tendsto (fun q : M × E => bb.repr q.2 j) (𝓝 (p₀, a₀)) (𝓝 (bb.repr a₀ j)) :=
    h2.tendsto
  have H3 : Filter.Tendsto (fun q : M × E => chartGram (I := I) x₀ q.1 (bb i) (bb j))
      (𝓝 (p₀, a₀)) (𝓝 (chartGram (I := I) x₀ p₀ (bb i) (bb j))) := h3.tendsto
  exact (H1.mul H2).mul H3

/-! ## Positive definiteness -/

/-- The coordinate frame at a point of the chart is injective: the frame vector associated with a
nonzero coordinate vector is nonzero. -/
lemma frameVector_eq_zero_iff {x₀ p : M} (hp : p ∈ (chartAt H x₀).source) (a : E) :
    frameVector (I := I) x₀ p a = 0 ↔ a = 0 := by
  constructor
  · intro h
    have hb : p ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := hp
    have h2 := Trivialization.continuousLinearMapAt_symmL
      (e := trivializationAt E (TangentSpace I) x₀) (R := ℝ) hb a
    have hsymm : (trivializationAt E (TangentSpace I) x₀).symmL ℝ p a = 0 := by
      rw [← (show frameVector (I := I) x₀ p a
        = (trivializationAt E (TangentSpace I) x₀).symmL ℝ p a from rfl)]
      exact h
    rw [hsymm, map_zero] at h2
    exact h2.symm
  · intro h
    rw [h]
    show (trivializationAt E (TangentSpace I) x₀).symmL ℝ p (0 : E) = 0
    exact map_zero _

/-- **The chart metric is positive definite** at points of the chart. -/
lemma chartGram_self_pos {x₀ p : M} (hp : p ∈ (chartAt H x₀).source) {a : E} (ha : a ≠ 0) :
    0 < chartGram (I := I) x₀ p a a := by
  have hne : frameVector (I := I) x₀ p a ≠ 0 := fun h => ha ((frameVector_eq_zero_iff hp a).mp h)
  have h0 : inner ℝ (frameVector (I := I) x₀ p a) (frameVector (I := I) x₀ p a) ≠ 0 :=
    fun h => hne ((inner_self_eq_zero).mp h)
  have hnn : (0:ℝ) ≤ inner ℝ (frameVector (I := I) x₀ p a) (frameVector (I := I) x₀ p a) :=
    inner_self_nonneg (𝕜 := ℝ) (x := frameVector (I := I) x₀ p a)
  rw [chartGram_apply]
  exact lt_of_le_of_ne hnn (Ne.symm h0)

/-! ## Homogeneity and evaluation in a basis -/

/-- The chart metric is homogeneous of degree two. -/
lemma chartGram_smul_smul (x₀ p : M) (c : ℝ) (a : E) :
    chartGram (I := I) x₀ p (c • a) (c • a) = c ^ 2 * chartGram (I := I) x₀ p a a := by
  rw [chartGram_smul_fst, chartGram_smul_snd]
  ring

/-- The frame vector of the zero coordinate vector vanishes. -/
lemma frameVector_zero' (x₀ p : M) : frameVector (I := I) x₀ p (0 : E) = 0 :=
  show (trivializationAt E (TangentSpace I) x₀).symmL ℝ p (0 : E) = 0 from map_zero _

/-- Homogeneity of degree two, in the form in which it is applied: if `a = c • b` then
`chartGram x₀ p a a = c² * chartGram x₀ p b b`. -/
lemma chartGram_smul_smul_of_eq (x₀ p : M) {a b : E} {c : ℝ} (h : a = c • b) :
    chartGram (I := I) x₀ p a a = c ^ 2 * chartGram (I := I) x₀ p b b := by
  subst h
  rw [chartGram_smul_smul]

/-- The chart metric vanishes on the zero coordinate vector. -/
lemma chartGram_zero (x₀ p : M) : chartGram (I := I) x₀ p (0 : E) (0 : E) = 0 := by
  rw [chartGram_apply, frameVector_zero']
  simp

/-- Reconstruction of a vector from its coordinates in a basis. -/
lemma sum_equivFun_basis {ι : Type*} [Fintype ι] (bb : Module.Basis ι ℝ E) (a : E) :
    ∑ i, bb.equivFun a i • bb i = a := by
  rw [← Module.Basis.equivFun_symm_apply, LinearEquiv.symm_apply_apply]

/-- The coordinates of a vector reconstructed in a basis are the original coefficients. -/
lemma repr_sum_basis {ι : Type*} [Fintype ι] (bb : Module.Basis ι ℝ E) (c : ι → ℝ) :
    bb.repr (∑ i, c i • bb i) = c := by
  funext i
  simp only [map_sum, map_smul, Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    rw [Finsupp.single_eq_of_ne (Ne.symm hb)]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- The value of the chart metric on a vector expanded in a basis, as an explicit quadratic form
in the coefficients. -/
lemma chartGram_sum_basis {ι : Type*} [Fintype ι] (bb : Module.Basis ι ℝ E)
    (x₀ p : M) (c : ι → ℝ) :
    chartGram (I := I) x₀ p (∑ i, c i • bb i) (∑ i, c i • bb i)
      = ∑ i, ∑ j, c i * c j * chartGram (I := I) x₀ p (bb i) (bb j) := by
  rw [chartGram_eq_sum_repr (I := I) bb x₀ p]
  rw [repr_sum_basis bb c]

/-! ## The chart metric is comparable to the model norm on a compact set -/

/-- **The chart metric is comparable to the norm of the model space on a compact subset of the
chart.**  There are constants `0 < lam` and `0 < Lam` with
`lam * ‖a‖² ≤ chartGram x₀ p a a ≤ Lam * ‖a‖²` for all `p ∈ K` and all `a : E`. -/
theorem exists_chartGram_bounds [Nontrivial E] (x₀ : M) {K : Set M} (hK : IsCompact K)
    (hKne : K.Nonempty) (hKs : K ⊆ (chartAt H x₀).source) :
    ∃ lam : ℝ, 0 < lam ∧ ∃ Lam : ℝ, 0 < Lam ∧ ∀ p ∈ K, ∀ a : E,
      lam * ‖a‖ ^ 2 ≤ chartGram (I := I) x₀ p a a ∧
        chartGram (I := I) x₀ p a a ≤ Lam * ‖a‖ ^ 2 := by
  obtain bb : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := Module.finBasis ℝ E
  set S : Set E := Metric.sphere (0 : E) 1 with hS
  have hSne : S.Nonempty := by
    obtain ⟨e₀, he₀⟩ : ∃ e : E, e ≠ 0 := exists_ne 0
    refine ⟨‖e₀‖⁻¹ • e₀, ?_⟩
    rw [hS, Metric.mem_sphere, dist_eq_norm, sub_zero, norm_smul, norm_inv,
      Real.norm_of_nonneg (norm_nonneg e₀), inv_mul_cancel₀ (norm_ne_zero_iff.mpr he₀)]
  have hScomp : IsCompact S := isCompact_sphere 0 1
  have hKc : IsCompact (K ×ˢ S) := hK.prod hScomp
  have hKcne : (K ×ˢ S).Nonempty := hKne.prod hSne
  -- the quadratic form in the coordinates of a basis
  set Ψ : M × E → ℝ := fun q =>
    ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
      bb.equivFun q.2 i * bb.equivFun q.2 j * chartGram (I := I) x₀ q.1 (bb i) (bb j)
    with hΨdef
  -- evaluation of `Ψ` is the chart metric
  have hΨeval : ∀ (p : M) (a : E), Ψ (p, a) = chartGram (I := I) x₀ p a a := by
    intro p a
    simp only [hΨdef]
    rw [← chartGram_sum_basis (I := I) bb x₀ p (bb.equivFun a), sum_equivFun_basis bb a]
  -- `Ψ` is continuous on the compact set
  have hΨcont : ContinuousOn Ψ (K ×ˢ S) := by
    intro q hq
    have hqsrc : q.1 ∈ (chartAt H x₀).source := hKs hq.1
    refine tendsto_finsetSum Finset.univ fun i _ => ?_
    refine tendsto_finsetSum Finset.univ fun j _ => ?_
    have h1 : ContinuousWithinAt (fun q' : M × E => bb.equivFun q'.2 i) (K ×ˢ S) q :=
      (show ContinuousAt ((fun v : E => bb.equivFun v i) ∘ Prod.snd) q from
        (continuous_basis_repr bb i).continuousAt.comp continuousAt_snd).continuousWithinAt
    have h2 : ContinuousWithinAt (fun q' : M × E => bb.equivFun q'.2 j) (K ×ˢ S) q :=
      (show ContinuousAt ((fun v : E => bb.equivFun v j) ∘ Prod.snd) q from
        (continuous_basis_repr bb j).continuousAt.comp continuousAt_snd).continuousWithinAt
    have h3 : ContinuousWithinAt
        (fun q' : M × E => chartGram (I := I) x₀ q'.1 (bb i) (bb j)) (K ×ˢ S) q :=
      (show ContinuousAt ((fun p : M => chartGram (I := I) x₀ p (bb i) (bb j)) ∘ Prod.fst) q from
        (continuousAt_chartGram (I := I) x₀ (bb i) (bb j) hqsrc).comp
          continuousAt_fst).continuousWithinAt
    exact ((h1.tendsto.mul h2.tendsto).mul h3.tendsto)
  -- `Ψ` is positive on the compact set
  have hΨpos : ∀ q ∈ K ×ˢ S, 0 < Ψ q := by
    rintro ⟨p, a⟩ ⟨hp, ha⟩
    have hpsrc : p ∈ (chartAt H x₀).source := hKs hp
    have hnorm : ‖a‖ = 1 := by
      rw [hS, Metric.mem_sphere, dist_eq_norm, sub_zero] at ha
      exact ha
    rw [hΨeval p a]
    exact chartGram_self_pos hpsrc (norm_ne_zero_iff.mp (by rw [hnorm]; norm_num))
  obtain ⟨qm, hqm, hm⟩ := hKc.exists_isMinOn hKcne hΨcont
  obtain ⟨qM, hqM, hM⟩ := hKc.exists_isMaxOn hKcne hΨcont
  refine ⟨Ψ qm, hΨpos qm hqm, Ψ qM, hΨpos qM hqM, ?_⟩
  intro p hp a
  rcases eq_or_ne a 0 with rfl | ha
  · rw [chartGram_zero, norm_zero]
    constructor <;> simp
  · set â : E := ‖a‖⁻¹ • a with hâ
    have hânorm : ‖â‖ = 1 := by
      rw [hâ, norm_smul, norm_inv, Real.norm_of_nonneg (norm_nonneg a),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr ha)]
    have hmem : (p, â) ∈ K ×ˢ S :=
      ⟨hp, by rw [hS, Metric.mem_sphere, dist_eq_norm, sub_zero]; exact hânorm⟩
    have hval : chartGram (I := I) x₀ p â â = Ψ (p, â) := (hΨeval p â).symm
    have hsplit : a = ‖a‖ • â := by
      rw [hâ, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr ha), one_smul]
    have haq := chartGram_smul_smul_of_eq (I := I) x₀ p hsplit
    have hlow : Ψ qm ≤ chartGram (I := I) x₀ p â â := by
      rw [hval]; exact hm hmem
    have hhigh : chartGram (I := I) x₀ p â â ≤ Ψ qM := by
      rw [hval]; exact hM hmem
    have hsq : (0:ℝ) ≤ ‖a‖ ^ 2 := sq_nonneg _
    constructor
    · rw [haq, mul_comm (‖a‖ ^ 2) (chartGram (I := I) x₀ p â â)]
      exact mul_le_mul_of_nonneg_right hlow hsq
    · rw [haq, mul_comm (‖a‖ ^ 2) (chartGram (I := I) x₀ p â â)]
      exact mul_le_mul_of_nonneg_right hhigh hsq

end

end Submission.ChartBounds