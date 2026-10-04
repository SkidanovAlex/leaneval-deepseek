import Mathlib
import Submission.Work.Diff.EXT.splice_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Positive definiteness of the chart matrix at the chart centre, `T2Space`-free

`Work.Diff.EXT.chartMatFun_centre_posDef_tfree` is the pointwise positivity input of the uniform
positive definiteness of the chart matrix of a smooth metric.  It is stated with **no** `T2Space M`
and **no** `I.Boundaryless` hypothesis, which is what working with an explicit metric family
`G : ℝ → SMet I M` (rather than with a Riemannian-bundle instance) requires: the seeded library
statements `Submission.ChartBounds.frameVector_eq_zero_iff` and `Submission.Geodesic.frameVector_sum`
carry `[T2Space M]` (spuriously), so the `T2Space`-free restatements of the two frame-vector facts
used here are proved in this file as well.
-/

set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- The coordinate frame vector is additive and homogeneous in its coordinate vector.  (`T2Space`-free
version of `Submission.Geodesic.frameVector_sum`, which is stated over an instance metric and `T2Space`.) -/
theorem frameVector_sum_tfree {ι : Type*} (s : Finset ι) (x₀ p : M) (c : ι → ℝ) (w : ι → E) :
    Submission.Geodesic.frameVector (I := I) x₀ p (∑ i ∈ s, c i • w i)
      = ∑ i ∈ s, c i • Submission.Geodesic.frameVector (I := I) x₀ p (w i) := by
  show (trivializationAt E (TangentSpace I) x₀).symmL ℝ p (∑ i ∈ s, c i • w i)
      = ∑ i ∈ s, c i • (trivializationAt E (TangentSpace I) x₀).symmL ℝ p (w i)
  rw [map_sum]
  simp_rw [map_smul]

/-- The coordinate frame vector vanishes only on the zero coordinate vector.  (`T2Space`-free,
`Boundaryless`-free version of `Submission.ChartBounds.frameVector_eq_zero_iff`.) -/
theorem frameVector_eq_zero_iff_tfree {x₀ p : M} (hp : p ∈ (chartAt H x₀).source) (a : E) :
    Submission.Geodesic.frameVector (I := I) x₀ p a = 0 ↔ a = 0 := by
  constructor
  · intro h
    have hb : p ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := hp
    have h2 := Trivialization.continuousLinearMapAt_symmL
      (e := trivializationAt E (TangentSpace I) x₀) (R := ℝ) hb a
    have hsymm : (trivializationAt E (TangentSpace I) x₀).symmL ℝ p a = 0 := h
    rw [hsymm, map_zero] at h2
    exact h2.symm
  · intro h
    rw [h]
    show (trivializationAt E (TangentSpace I) x₀).symmL ℝ p (0 : E) = 0
    exact map_zero _

/-- Bilinearity of a continuous linear form `T →L[ℝ] T →L[ℝ] ℝ` in both slots: the quadratic form of
the matrix `(f (σ i) (σ j))ᵢⱼ` is the value of `f` on the combination `∑ i, v i • σ i`. -/
private lemma sum_sum_mul_mul_inner {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T]
    {n : ℕ} (f : T →L[ℝ] T →L[ℝ] ℝ) (σ : Fin n → T) (v : Fin n → ℝ) :
    (∑ i, ∑ j, v i * v j * f (σ i) (σ j)) = f (∑ i, v i • σ i) (∑ i, v i • σ i) := by
  simp only [map_sum, sum_apply, map_smul, smul_apply, smul_eq_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- **The chart matrix of a smooth metric is positive definite at the chart centre.**
For `x₀ : M`, `y₀ = (extChartAt I x₀) x₀` and any nonzero coefficient vector `v`,
`0 < ∑ i, ∑ j, v i * v j * chartMatFun g x₀ y₀ i j`.

No `T2Space M` and no `I.Boundaryless`: `(extChartAt I x₀).symm y₀ = x₀` (`PartialEquiv.left_inv`),
bilinearity of the continuous linear map `g.inner x₀`, the `T2Space`-free frame facts above, and the
`pos` field of the Riemannian metric. -/
theorem chartMatFun_centre_posDef_tfree (g : Submission.Diff.SMet I M) (x₀ : M)
    (v : Fin (Module.finrank ℝ E) → ℝ) (hv : v ≠ 0) :
    0 < ∑ i, ∑ j, v i * v j * chartMatFun g x₀ ((extChartAt I x₀) x₀) i j := by
  classical
  -- register `g` as the Riemannian-bundle structure on the tangent bundle, so that the tangent
  -- spaces carry a normed group / inner product structure (this needs neither `T2Space M` nor
  -- `I.Boundaryless`)
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  -- unfold the chart matrix at the chart centre, where the inverse chart returns `x₀`
  have hc : (∑ i, ∑ j, v i * v j * chartMatFun g x₀ ((extChartAt I x₀) x₀) i j)
      = ∑ i, ∑ j, v i * v j *
          g.inner x₀ (Submission.Geodesic.frameVector (I := I) x₀ x₀ (bB (E := E) i))
            (Submission.Geodesic.frameVector (I := I) x₀ x₀ (bB (E := E) j)) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [chartMatFun, extChartAt_to_inv]
  rw [hc, sum_sum_mul_mul_inner (f := g.inner x₀)
    (σ := fun i => Submission.Geodesic.frameVector (I := I) x₀ x₀ (bB (E := E) i)) v]
  -- linearity of the frame vector in its coordinate vector
  have hlin : (∑ i, v i • Submission.Geodesic.frameVector (I := I) x₀ x₀ (bB (E := E) i))
      = Submission.Geodesic.frameVector (I := I) x₀ x₀ (∑ i, v i • bB (E := E) i) := by
    have h := frameVector_sum_tfree (I := I) (s := Finset.univ) (x₀ := x₀) (p := x₀) (c := v)
      (w := fun i => bB (E := E) i)
    simpa using h.symm
  rw [hlin]
  -- the combination is nonzero because `bB` is a basis and `v ≠ 0`
  refine g.pos x₀ _ ?_
  intro hzero
  have ha : (∑ i, v i • bB (E := E) i) = 0 :=
    (frameVector_eq_zero_iff_tfree (I := I) (x₀ := x₀) (p := x₀)
      (mem_chart_source H x₀) (∑ i, v i • bB (E := E) i)).mp hzero
  have hli : ∀ i, v i = 0 :=
    (Fintype.linearIndependent_iff.mp (bB (E := E)).linearIndependent) v ha
  exact hv (funext fun i => hli i)

end Work.Diff.EXT
