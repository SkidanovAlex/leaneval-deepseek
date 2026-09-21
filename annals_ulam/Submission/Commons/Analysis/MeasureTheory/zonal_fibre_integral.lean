import Mathlib
import Submission.Commons.Analysis.MeasureTheory.sphere_coordinate_marginal
import Submission.Commons.Analysis.MeasureTheory.sphere_isometry_measurableEquiv_measurePreserving
import Submission.Commons.Analysis.InnerProductSpace.fin_split_coord_isometry

/-!
# Zonal fibre integration (Funk–Hecke reduction)

The sphere integral of a function of a single coordinate splits as an integral over the
coordinate `t ∈ (-1, 1)` of the fibre integral over the unit sphere of the orthogonal
complement, with the classical weight `(1 - t ^ 2) ^ ((n - 3) / 2)`.

The proof transports the statement along the linear isometric equivalence
`fin_split_coord_isometry` splitting off the coordinate `i`, and then applies the product
form of the marginal identity `sphere_coordinate_marginal`.
-/

noncomputable section
open Set Function MeasureTheory Metric
open scoped Classical ENNReal NNReal Pointwise

namespace Commons.Analysis.MeasureTheory

set_option linter.style.haveILetI false

/-- The dimension of the fibre `EuclideanSpace ℝ {j // j ≠ i}` is the cardinality of its
index type. -/
private lemma finrank_fibre_eq_card {n : ℕ} (i : Fin n) :
    Module.finrank ℝ (EuclideanSpace ℝ {j : Fin n // j ≠ i}) =
      Fintype.card {j : Fin n // j ≠ i} := by
  classical
  exact finrank_euclideanSpace (𝕜 := ℝ) (ι := {j : Fin n // j ≠ i})

theorem zonal_fibre_integral
    {n : ℕ} (i : Fin n) (hn : 2 ≤ n)
    (F : ℝ → ℝ) :
    (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        F ((θ : EuclideanSpace ℝ (Fin n)) i)
      ∂MeasureTheory.volume.toSphere) =
    ∫ t : ℝ in Set.Ioo (-1) 1,
      (∫ ω : Metric.sphere (0 : EuclideanSpace ℝ {j : Fin n // j ≠ i}) 1,
          F t * (1 - t ^ 2) ^ (((Fintype.card {j : Fin n // j ≠ i} : ℝ) - 2) / 2)
        ∂MeasureTheory.volume.toSphere) := by
  classical
  let J : Type := {j : Fin n // j ≠ i}
  let W : Type := EuclideanSpace ℝ J
  -- the fibre type is nonempty, hence nontrivial
  have h1lt : 1 < Fintype.card (Fin n) := by
    rw [Fintype.card_fin]
    omega
  have hJ : Nonempty J := by
    rcases Fintype.exists_ne_of_one_lt_card h1lt i with ⟨j, hj⟩
    exact ⟨⟨j, hj⟩⟩
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  haveI : Nonempty J := hJ
  -- split off the coordinate `i` by a linear isometry
  obtain ⟨L, hL1, hL2⟩ :=
    Commons.Analysis.InnerProductSpace.fin_split_coord_isometry (n := n) (i := i)
  -- the induced measure-preserving equivalence of unit spheres
  obtain ⟨e, hmp, hpe⟩ :=
    sphere_isometry_measurableEquiv_measurePreserving
      (V₁ := EuclideanSpace ℝ (Fin n)) (V₂ := WithLp 2 (ℝ × W)) (L := L)
  let g : Metric.sphere (0 : WithLp 2 (ℝ × W)) 1 → ℝ :=
    fun θ => F ((θ : WithLp 2 (ℝ × W)).ofLp.1)
  -- the transported integrand agrees with `F` evaluated at the `i`-th coordinate
  have hpoint : ∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      F ((θ : EuclideanSpace ℝ (Fin n)) i) = g (e θ) := by
    intro θ
    congr 1
    rw [hpe θ]
    exact (hL1 (θ : EuclideanSpace ℝ (Fin n))).symm
  have htrans : (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        F ((θ : EuclideanSpace ℝ (Fin n)) i) ∂volume.toSphere) =
      ∫ θ' : Metric.sphere (0 : WithLp 2 (ℝ × W)) 1,
        F ((θ' : WithLp 2 (ℝ × W)).ofLp.1) ∂volume.toSphere := by
    calc
      (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          F ((θ : EuclideanSpace ℝ (Fin n)) i) ∂volume.toSphere)
          = ∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1, g (e θ) ∂volume.toSphere := by
              apply integral_congr_ae
              filter_upwards with θ
              exact hpoint θ
      _ = ∫ θ' : Metric.sphere (0 : WithLp 2 (ℝ × W)) 1, g θ' ∂volume.toSphere := by
              simpa [g] using
                (MeasureTheory.MeasurePreserving.integral_comp' (f := e) hmp g)
  calc
    (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        F ((θ : EuclideanSpace ℝ (Fin n)) i) ∂volume.toSphere)
        = ∫ θ' : Metric.sphere (0 : WithLp 2 (ℝ × W)) 1,
            F ((θ' : WithLp 2 (ℝ × W)).ofLp.1) ∂volume.toSphere := htrans
    _ = ∫ t : ℝ in Set.Ioo (-1) 1,
          (∫ ω : Metric.sphere (0 : W) 1,
              F t * (1 - t ^ 2) ^ (((Module.finrank ℝ W : ℝ) - 2) / 2)
            ∂volume.toSphere) := by
          simpa [W] using (sphere_coordinate_marginal (W := W) F)
    _ = ∫ t : ℝ in Set.Ioo (-1) 1,
          (∫ ω : Metric.sphere (0 : EuclideanSpace ℝ {j : Fin n // j ≠ i}) 1,
              F t * (1 - t ^ 2) ^ (((Fintype.card {j : Fin n // j ≠ i} : ℝ) - 2) / 2)
            ∂volume.toSphere) := by
          simp [W, J, finrank_fibre_eq_card i]

end Commons.Analysis.MeasureTheory
