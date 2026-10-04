import Mathlib
import Submission.Work.Diff.EXT.ConnCov.gram_lower_of_hmet
import Submission.Work.Diff.EXT.ConnCov.frameCoord_bound
import Submission.Work.Diff.EXT.basis_coeff_norm_equiv
import Submission.Work.Diff.EXT.ChartCoreDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT.ConnCov

theorem coeff_l1_le_of_hmet
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
    ∃ K : ℝ, 0 < K ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ y ∈ K',
      ∀ v : TangentSpace I (Work.Diff.EXT.pt (I := I) x₀ y),
        Finset.sum Finset.univ (fun p => |(Module.finBasis ℝ E).repr
            ((FiberBundle.trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ
              (Work.Diff.EXT.pt (I := I) x₀ y) v) p|)
          ≤ K * Real.sqrt ((G t).inner (Work.Diff.EXT.pt (I := I) x₀ y) v v) := by
  -- ### The two ingredients
  -- (i) a uniform lower ellipticity bound for the *initial* metric in the chart frame of `x₀`,
  --     upgraded to `G t` for `t ∈ [T/2,T)` by the two-sided comparison `hmet`;
  obtain ⟨c, hcpos, hc⟩ :=
    Work.Diff.EXT.ConnCov.gram_lower_of_hmet (I := I) (M := M) G T C hT hC hmet x₀ K'
      hK'c hK't hK'ne
  -- (ii) the equivalence of the coordinate norm on `E` with the norm (the basis `bB` is
  --      `Module.finBasis ℝ E`, so this is a pure change of coordinates on the model space).
  obtain ⟨K1, K2, hK1, hK2, hbb⟩ :=
    Work.Diff.EXT.basis_coeff_norm_equiv (E := E) (Work.Diff.EXT.bB (E := E))
  refine ⟨Real.sqrt ((Module.finrank ℝ E : ℝ) / (c / K1)) + 1, by positivity, ?_⟩
  intro t ht y hy v
  have hyT : y ∈ (extChartAt I x₀).target := hK't hy
  have hδ : 0 < c / K1 := div_pos hcpos hK1
  -- ### The chart matrix of `G t` dominates `(c/K1) · 1` as a quadratic form
  have hell : ∀ w : Fin (Module.finrank ℝ E) → ℝ,
      (c / K1) * ∑ i, (w i) ^ 2
        ≤ ∑ i, ∑ j, w i * w j * Work.Diff.EXT.chartMatFun (G t) x₀ y i j := by
    intro w
    have h1 : ∑ i, (w i) ^ 2 ≤ K1 * ‖∑ i, w i • Work.Diff.EXT.bB (E := E) i‖ ^ 2 :=
      (hbb w).1
    -- the quadratic form of the chart matrix is the metric of the frame vector of the
    -- coordinate vector `∑ i, w i • bB i`
    have hq := Work.Diff.EXT.sum_chartMatFun_eq_inner (I := I) (M := M) (G t) x₀ y w
    have hsum := Work.Diff.EXT.frameVector_sum_tfree (I := I)
      (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
      x₀ ((extChartAt I x₀).symm y) w (Work.Diff.EXT.bB (E := E))
    have hmetric := hc t ht y hy (∑ i, w i • Work.Diff.EXT.bB (E := E) i)
    have hpt : Work.Diff.EXT.pt (I := I) x₀ y = (extChartAt I x₀).symm y := rfl
    rw [hpt] at hmetric
    calc (c / K1) * ∑ i, (w i) ^ 2
        ≤ (c / K1) * (K1 * ‖∑ i, w i • Work.Diff.EXT.bB (E := E) i‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h1 hδ.le
      _ = c * ‖∑ i, w i • Work.Diff.EXT.bB (E := E) i‖ ^ 2 := by field_simp
      _ ≤ (G t).inner ((extChartAt I x₀).symm y)
            (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
              (∑ i, w i • Work.Diff.EXT.bB (E := E) i))
            (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
              (∑ i, w i • Work.Diff.EXT.bB (E := E) i)) := hmetric
      _ = ∑ i, ∑ j, w i * w j * Work.Diff.EXT.chartMatFun (G t) x₀ y i j := by
          rw [hq, hsum]
  -- ### The trivialization coordinates of `v` are the components of the chart matrix
  have hb := Work.Diff.EXT.ConnCov.frameCoord_bound (I := I) (M := M) (G t) x₀ y hyT hδ hell v
  -- rewrite `pt x₀ y = (extChartAt I x₀).symm y` and `bB = Module.finBasis ℝ E` in the bound
  change Finset.sum Finset.univ (fun p => |(Module.finBasis ℝ E).repr
            ((FiberBundle.trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ
              ((extChartAt I x₀).symm y) v) p|)
          ≤ (Real.sqrt ((Module.finrank ℝ E : ℝ) / (c / K1)) + 1) *
              Real.sqrt ((G t).inner ((extChartAt I x₀).symm y) v v)
  have hb' : Finset.sum Finset.univ (fun p => |(Module.finBasis ℝ E).repr
            ((FiberBundle.trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ
              ((extChartAt I x₀).symm y) v) p|)
          ≤ Real.sqrt ((Module.finrank ℝ E : ℝ) / (c / K1)) *
              Real.sqrt ((G t).inner ((extChartAt I x₀).symm y) v v) := hb
  refine le_trans hb' ?_
  exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (zero_le_one))
    (Real.sqrt_nonneg _)

end Work.Diff.EXT.ConnCov
