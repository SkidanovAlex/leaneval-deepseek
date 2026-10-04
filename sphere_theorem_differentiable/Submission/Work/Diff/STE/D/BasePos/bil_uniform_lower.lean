import Mathlib
import Submission.Work.Diff.STE.D.Base.Defs
import Submission.Work.Diff.STE.D.Setup
import Submission.Work.Diff.EXT.ConnCov.gram_lower_of_hmet

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.D.BasePos

/-- **Uniform positive lower bound for a positive definite section, in a chart frame, on a compact
set.**  Let `a₀` be a section of bilinear forms which is smooth in charts (`ChartData`, i.e. its
chart matrices are `C^∞` on every chart target) and positive definite pointwise.  Then on a compact
subset `K'` of the *target* of the chart at `x₀` there is `δ > 0` with `δ ‖a‖² ≤ a₀(p)(v_a, v_a)`
for every `y ∈ K'` and every `a : E`, where `p = (extChartAt I x₀).symm y` and
`v_a = frameVector I x₀ p a` (the tangent vector whose coordinates in the chart trivialisation are
`a`).

This is the base-generalisation of `Work.Diff.EXT.ConnCov.gram_lower_of_compact_metric` (which needs
an honest `SMet`).  Suggested route: symmetrise
`symmOf a₀ x u v = (a₀ x u v + a₀ x v u) / 2` (same quadratic form: `symmOf a₀ x v v = a₀ x v v`),
deduce `ChartData (symmOf a₀)` from `ha₀` (the chart matrix of `symmOf a₀` is
`(A i j + A j i)/2` for `A = chartMat a₀ x₀`), build the honest metric
`Work.Diff.STE.D.smetOf (symmOf a₀) … : SMet I M` and apply
`Work.Diff.EXT.ConnCov.gram_lower_of_compact_metric` to it (using
`Work.Diff.STE.D.smetOf_inner` to identify the metric with `symmOf a₀`).

The proof below takes the more direct route (no symmetrisation, no `SMet`): the chart matrix
`y ↦ (i j ↦ a₀(p)(σᵢ,σⱼ))` of `a₀` is `C^∞` on the target of the chart (this is `ha₀` read at the
chart centre `x₀`), hence continuous; its quadratic form is positive definite pointwise, by `hpos`
and the bilinearity of `a₀ p : TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ` in both slots
(`map_sum`, `map_smul`).  The compactness theorem
`Work.Diff.EXT.ConnCov.quadForm_uniform_lower_compact` therefore produces a uniform `δ > 0`; finally
the coefficient norm of `a : E` in the canonical basis `Work.Diff.EXT.bB` is comparable to the
Euclidean norm of its coefficients (`Work.Diff.EXT.basis_coeff_norm_equiv`).  Nothing about the
*symmetry* of `a₀` is used.

Note on the two inlined bilinearity steps: they are written directly in the goal's own context
(inside `have … : <the goal's expression> := by simp only [...]`) rather than through a helper lemma
`∀ f : T →L[ℝ] T →L[ℝ] ℝ, …` as in the `SMet` case.  The reason is that without a
`RiemannianBundle`-type class on the tangent bundle the *fibre* instances
`NormedAddCommGroup (TangentSpace I p)` / `NormedSpace ℝ (TangentSpace I p)` are not synthesizable;
one can still pass them explicitly, but `rw`/`exact` matching against a separately stated lemma then
fails, because the instance arguments of the `ContinuousLinearMap` type in the lemma and in the goal
are different terms (both instances are `TangentSpace I p`-instances, and these are not
definitionally equal to each other even though the types are). -/
theorem bil_uniform_lower
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    (a₀ : Work.Diff.STE.Bil (I := I) (M := M))
    (ha₀ : Work.Diff.STE.D.ChartData (I := I) (M := M) a₀)
    (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < a₀ x v v)
    (x₀ : M) (K' : Set E) (hK'c : IsCompact K')
    (hK't : K' ⊆ (extChartAt I x₀).target) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ K', ∀ a : E,
      δ * ‖a‖ ^ 2 ≤ a₀ ((extChartAt I x₀).symm y)
        (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y) a)
        (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y) a) := by
  classical
  -- The chart matrix of `a₀` is continuous on the target of the chart (it is `C^∞` there).
  have hcont : ∀ y ∈ K', ∀ i j : Fin (Module.finrank ℝ E),
      ContinuousAt (fun y' : E => a₀ ((extChartAt I x₀).symm y')
        (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y')
          (Work.Diff.EXT.bB (E := E) i))
        (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y')
          (Work.Diff.EXT.bB (E := E) j))) y := by
    intro y hy i j
    have hcd : ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => fun i j : Fin (Module.finrank ℝ E) =>
        a₀ ((extChartAt I x₀).symm y')
          (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y')
            (Work.Diff.EXT.bB (E := E) i))
          (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y')
            (Work.Diff.EXT.bB (E := E) j))) y :=
      (ha₀ x₀).contDiffAt ((isOpen_extChartAt_target (I := I) x₀).mem_nhds (hK't hy))
    exact (((continuous_apply j).comp (continuous_apply i)).continuousAt.comp hcd.continuousAt)
  -- The quadratic form of the chart matrix is positive definite at every `y ∈ K'`.
  have hposA : ∀ y ∈ K', ∀ v : Fin (Module.finrank ℝ E) → ℝ, v ≠ 0 →
      0 < ∑ i, ∑ j, v i * v j * (a₀ ((extChartAt I x₀).symm y)
        (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
          (Work.Diff.EXT.bB (E := E) i))
        (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
          (Work.Diff.EXT.bB (E := E) j))) := by
    intro y hy v hv
    have hp : (extChartAt I x₀).symm y ∈ (chartAt H x₀).source := by
      have h1 : (extChartAt I x₀).symm y ∈ (extChartAt I x₀).source :=
        (extChartAt I x₀).map_target (hK't hy)
      rwa [extChartAt_source] at h1
    -- linearity of the frame vector in its coordinate vector
    have hlin : (∑ i, v i • Submission.Geodesic.frameVector (I := I) x₀
          ((extChartAt I x₀).symm y) (Work.Diff.EXT.bB (E := E) i))
        = Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
            (∑ i, v i • Work.Diff.EXT.bB (E := E) i) :=
      (Work.Diff.EXT.frameVector_sum_tfree (I := I) (s := Finset.univ) (x₀ := x₀)
        (p := (extChartAt I x₀).symm y) (c := v)
        (w := fun i => Work.Diff.EXT.bB (E := E) i)).symm
    -- bilinearity of `a₀ p` in both slots
    have hbil : (∑ i, ∑ j, v i * v j * (a₀ ((extChartAt I x₀).symm y)
          (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
            (Work.Diff.EXT.bB (E := E) i))
          (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
            (Work.Diff.EXT.bB (E := E) j))))
        = a₀ ((extChartAt I x₀).symm y)
            (∑ i, v i • Submission.Geodesic.frameVector (I := I) x₀
              ((extChartAt I x₀).symm y) (Work.Diff.EXT.bB (E := E) i))
            (∑ i, v i • Submission.Geodesic.frameVector (I := I) x₀
              ((extChartAt I x₀).symm y) (Work.Diff.EXT.bB (E := E) i)) := by
      simp only [map_sum, sum_apply, map_smul, smul_apply, smul_eq_mul, Finset.mul_sum]
      conv_rhs => rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [hbil, hlin]
    refine hpos ((extChartAt I x₀).symm y) _ ?_
    intro h0
    have ha : (∑ i, v i • Work.Diff.EXT.bB (E := E) i) = 0 :=
      (Work.Diff.EXT.frameVector_eq_zero_iff_tfree (I := I) (x₀ := x₀)
        (p := (extChartAt I x₀).symm y) hp _).mp h0
    exact hv (funext fun i =>
      (Fintype.linearIndependent_iff.mp (Work.Diff.EXT.bB (E := E)).linearIndependent) v ha i)
  -- Uniform positive definiteness on the compact set.
  obtain ⟨δ, hδpos, hδ⟩ := Work.Diff.EXT.ConnCov.quadForm_uniform_lower_compact
    (n := Module.finrank ℝ E) (X := E)
    (A := fun y i j => a₀ ((extChartAt I x₀).symm y)
      (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
        (Work.Diff.EXT.bB (E := E) i))
      (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
        (Work.Diff.EXT.bB (E := E) j)))
    hK'c hcont hposA
  obtain ⟨K1, K2, _hK1, hK2, hbb⟩ :=
    Work.Diff.EXT.basis_coeff_norm_equiv (E := E) (Work.Diff.EXT.bB (E := E))
  refine ⟨δ / K2, div_pos hδpos hK2, fun y hy a => ?_⟩
  -- The coefficient norm of `a` is controlled by the Euclidean norm of its coordinates.
  have hcoef : ‖a‖ ^ 2 ≤ K2 * ∑ i, ((Work.Diff.EXT.bB (E := E)).repr a i) ^ 2 := by
    have h := (hbb ((Work.Diff.EXT.bB (E := E)).repr a)).2
    rwa [Module.Basis.sum_repr] at h
  -- The quadratic form of the chart matrix is the value of `a₀` on the frame vector of `a`.
  have hquad : (∑ i, ∑ j, (Work.Diff.EXT.bB (E := E)).repr a i
        * (Work.Diff.EXT.bB (E := E)).repr a j
        * (a₀ ((extChartAt I x₀).symm y)
          (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
            (Work.Diff.EXT.bB (E := E) i))
          (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
            (Work.Diff.EXT.bB (E := E) j))))
      = a₀ ((extChartAt I x₀).symm y)
          (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y) a)
          (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y) a) := by
    have hbil : (∑ i, ∑ j, (Work.Diff.EXT.bB (E := E)).repr a i
          * (Work.Diff.EXT.bB (E := E)).repr a j
          * (a₀ ((extChartAt I x₀).symm y)
            (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
              (Work.Diff.EXT.bB (E := E) i))
            (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
              (Work.Diff.EXT.bB (E := E) j))))
        = a₀ ((extChartAt I x₀).symm y)
            (∑ i, (Work.Diff.EXT.bB (E := E)).repr a i •
              Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
                (Work.Diff.EXT.bB (E := E) i))
            (∑ i, (Work.Diff.EXT.bB (E := E)).repr a i •
              Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
                (Work.Diff.EXT.bB (E := E) i)) := by
      simp only [map_sum, sum_apply, map_smul, smul_apply, smul_eq_mul, Finset.mul_sum]
      conv_rhs => rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [hbil, ← Work.Diff.EXT.frameVector_sum_tfree (I := I) (s := Finset.univ) (x₀ := x₀)
      (p := (extChartAt I x₀).symm y) (c := (Work.Diff.EXT.bB (E := E)).repr a)
      (w := fun i => Work.Diff.EXT.bB (E := E) i), Module.Basis.sum_repr]
  have hstep : (δ / K2) * ‖a‖ ^ 2
      ≤ ∑ i, ∑ j, (Work.Diff.EXT.bB (E := E)).repr a i
          * (Work.Diff.EXT.bB (E := E)).repr a j
          * (a₀ ((extChartAt I x₀).symm y)
            (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
              (Work.Diff.EXT.bB (E := E) i))
            (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
              (Work.Diff.EXT.bB (E := E) j))) := by
    calc (δ / K2) * ‖a‖ ^ 2
        ≤ (δ / K2) * (K2 * ∑ i, ((Work.Diff.EXT.bB (E := E)).repr a i) ^ 2) :=
          mul_le_mul_of_nonneg_left hcoef (div_nonneg hδpos.le hK2.le)
      _ = δ * ∑ i, ((Work.Diff.EXT.bB (E := E)).repr a i) ^ 2 := by
          field_simp
      _ ≤ ∑ i, ∑ j, (Work.Diff.EXT.bB (E := E)).repr a i
            * (Work.Diff.EXT.bB (E := E)).repr a j
            * (a₀ ((extChartAt I x₀).symm y)
              (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
                (Work.Diff.EXT.bB (E := E) i))
              (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
                (Work.Diff.EXT.bB (E := E) j))) :=
          hδ y hy ((Work.Diff.EXT.bB (E := E)).repr a)
  rw [← hquad]
  exact hstep

end Work.Diff.STE.D.BasePos
