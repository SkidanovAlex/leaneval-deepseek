import Mathlib
import Submission.Work.Projective.Atlas
import Submission.Work.Projective.nonempty_continuousLinearEquiv
import Submission.Work.Model.prod_transfer

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `ℂPⁿ` as a smooth manifold modelled on `EuclideanSpace ℝ (Fin (2*n))`

`Work.Projective.Atlas` charts `ℂPⁿ` over the model space `Fin n → ℂ` (complex `n`-space).  This
module re-charts it over the Euclidean model `EuclideanSpace ℝ (Fin (2*n)) = ℝ^{2n}`, using a
linear isomorphism `euclidEquiv n : (Fin n → ℂ) ≃L[ℝ] EuclideanSpace ℝ (Fin (2*n))`
(`Work.Projective.nonempty_continuousLinearEquiv`):

* `Work.Projective.instChartedSpaceEuclidean` — `ChartedSpace (EuclideanSpace ℝ (Fin (2*n))) (CP n)`;
* `Work.Projective.instIsManifoldEuclidean` — `IsManifold (𝓡 (2*n)) ∞ (CP n)`, i.e. `ℂPⁿ` is a
  smooth `2n`-manifold in the usual sense (`𝓡 (2*n) = 𝓘(ℝ, EuclideanSpace ℝ (Fin (2*n)))`).

The transition maps of the re-charted atlas are the conjugates `Φ ∘ g ∘ Φ⁻¹` of the transition maps
`g` of the `Fin n → ℂ` atlas (which are smooth by `Work.Projective.chart_symm_trans_chart_mem`) by
the diffeomorphism `Φ = euclidEquiv n`, so smoothness is
`Work.Model.conj_mem` (the model-transfer lemma of `Submission/Work/Model/prod_transfer.lean`).
-/

open scoped Manifold ContDiff Topology

namespace Work.Projective

noncomputable section

/-- A chosen linear isomorphism between the model space `Fin n → ℂ` of the affine charts of `ℂPⁿ`
and the Euclidean model space `ℝ^{2n}`. -/
def euclidEquiv (n : ℕ) : (Fin n → ℂ) ≃L[ℝ] EuclideanSpace ℝ (Fin (2 * n)) :=
  Classical.choice (nonempty_continuousLinearEquiv n)

/-- The re-charted atlas of `ℂPⁿ`, over the Euclidean model. -/
def euclidAtlas (n : ℕ) :
    Set (OpenPartialHomeomorph (CP n) (EuclideanSpace ℝ (Fin (2 * n)))) :=
  Set.range (fun i : Fin (n + 1) =>
    (chart i).trans ((euclidEquiv n).toHomeomorph.toOpenPartialHomeomorph :
      OpenPartialHomeomorph (Fin n → ℂ) (EuclideanSpace ℝ (Fin (2 * n)))))

/-- A chart of `ℂPⁿ` over the Euclidean model: the affine chart at `i`, followed by the linear
isomorphism to `ℝ^{2n}`. -/
def euclidChart (n : ℕ) (i : Fin (n + 1)) :
    OpenPartialHomeomorph (CP n) (EuclideanSpace ℝ (Fin (2 * n))) :=
  (chart i).trans ((euclidEquiv n).toHomeomorph.toOpenPartialHomeomorph :
    OpenPartialHomeomorph (Fin n → ℂ) (EuclideanSpace ℝ (Fin (2 * n))))

theorem euclidChart_mem_atlas {n : ℕ} (i : Fin (n + 1)) : euclidChart n i ∈ euclidAtlas n :=
  ⟨i, rfl⟩

instance instChartedSpaceEuclidean (n : ℕ) :
    ChartedSpace (EuclideanSpace ℝ (Fin (2 * n))) (CP n) where
  atlas := euclidAtlas n
  chartAt p := euclidChart n (Classical.choose (exists_mem_chartSet p))
  mem_chart_source p := by
    have h := Classical.choose_spec (exists_mem_chartSet p)
    rw [euclidChart, OpenPartialHomeomorph.trans_source]
    exact ⟨h, Set.mem_univ _⟩
  chart_mem_atlas p := euclidChart_mem_atlas _

theorem euclid_symm_trans_mem {n : ℕ} (i j : Fin (n + 1)) :
    (euclidChart n i).symm ≫ₕ (euclidChart n j) ∈
      contDiffGroupoid ∞ (𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * n)))) := by
  have h := Work.Model.conj_mem (euclidEquiv n).toHomeomorph
    ((euclidEquiv n).contDiff) ((euclidEquiv n).symm.contDiff)
    (chart_symm_trans_chart_mem i j)
  convert h using 2
  · rw [euclidChart, euclidChart, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]
    simp only [OpenPartialHomeomorph.trans_assoc]

/-- **`ℂPⁿ` is a smooth manifold modelled on the Euclidean space `ℝ^{2n}`.** -/
instance instIsManifoldEuclidean (n : ℕ) :
    IsManifold (𝓡 (2 * n)) ∞ (CP n) where
  compatible := by
    intro e e' he he'
    obtain ⟨i, rfl⟩ := he
    obtain ⟨j, rfl⟩ := he'
    exact euclid_symm_trans_mem i j

end

end Work.Projective
