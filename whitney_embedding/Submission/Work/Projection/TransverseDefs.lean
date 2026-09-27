import Mathlib
import Submission.Work.Projection.immersion

/-!
# The parametrisation of the double points of a projection of an embedded `n`-manifold

Let `e : M → ℝ^{2n+1}` be a smooth embedding of a smooth `n`-manifold.  For a direction
`u : ℝ^{2n}` the projection `projVec u : ℝ^{2n+1} → ℝ^{2n}` has kernel spanned by `(u, 1)`; so
`projVec u (e x) = projVec u (e y)` for `x ≠ y` if and only if `e y - e x = c • (u, 1)` with
`c ≠ 0`, i.e. if and only if `u = extract (e y - e x)`.

This file sets up the chartwise parametrisation of this relation: for a chart at `p` (for `x`)
and a chart at `q` (for `y`), the *pair parametrisation*
`pairParam e p q (a, b) = pairEquiv (extract (chartRep e q b - chartRep e p a))`
sends the pair of chart coordinates to the (split) direction for which `x` and `y` are a double
point of the projection.  Its critical points are exactly the pairs at which the double point
fails to be transverse.

## Contents

* `pairEquiv`: the linear equivalence splitting `ℝ^{2n}` into two blocks `ℝ^n × ℝ^n` (so that the
  target of the pair parametrisation can be the same space as its source, the model of `M × M`).
* `pairZ`, `pairDom`, `pairParam`, `pairCrit`: the chartwise difference of the two embedded
  points, the domain where it is defined, the parametrisation and its critical set.
* `immBadCoord`, `transBadCoord`: the immersion-bad and transversality-bad sets of directions,
  in the `ℝ^n × ℝ^n` coordinates.
-/

namespace Work.Projection

open scoped Manifold ContDiff
open Topology MeasureTheory

/-- The canonical linear map splitting `ℝ^{2n}` into its first `n` and its last `n` coordinates. -/
noncomputable def pairMap (n : ℕ) :
    EuclideanSpace ℝ (Fin (2 * n)) →ₗ[ℝ]
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
  (LinearMap.prodMap (EuclideanSpace.equiv (Fin n) ℝ).symm.toLinearMap
    (EuclideanSpace.equiv (Fin n) ℝ).symm.toLinearMap).comp
    ((LinearMap.pi (fun i : Fin n =>
        (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin (2 * n)) ⟨i.1, by omega⟩).toLinearMap)).prod
      (LinearMap.pi (fun i : Fin n =>
        (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin (2 * n)) ⟨n + i.1, by omega⟩).toLinearMap)))

lemma pairMap_fst (n : ℕ) (u : EuclideanSpace ℝ (Fin (2 * n))) (i : Fin n) :
    (pairMap n u).1 i = u ⟨i.1, by omega⟩ := by
  simp [pairMap, LinearMap.prodMap, WithLp.ofLp_toLp]

lemma pairMap_snd (n : ℕ) (u : EuclideanSpace ℝ (Fin (2 * n))) (i : Fin n) :
    (pairMap n u).2 i = u ⟨n + i.1, by omega⟩ := by
  simp [pairMap, LinearMap.prodMap, WithLp.ofLp_toLp]

lemma pairMap_injective (n : ℕ) : Function.Injective (pairMap n) := by
  intro u v huv
  ext j
  by_cases hj : j.1 < n
  · have h1 : (pairMap n u).1 = (pairMap n v).1 := congrArg Prod.fst huv
    have := congrFun (congrArg WithLp.ofLp h1) (⟨j.1, hj⟩ : Fin n)
    rw [pairMap_fst, pairMap_fst] at this
    simpa using this
  · have h2 : (pairMap n u).2 = (pairMap n v).2 := congrArg Prod.snd huv
    have := congrFun (congrArg WithLp.ofLp h2) (⟨j.1 - n, by omega⟩ : Fin n)
    rw [pairMap_snd, pairMap_snd] at this
    simpa [show n + (j.1 - n) = j.1 by omega] using this

/-- **The splitting of `ℝ^{2n}` into two blocks of `n` coordinates**, as a linear equivalence. -/
theorem exists_pairEquiv (n : ℕ) :
    ∃ L : EuclideanSpace ℝ (Fin (2 * n)) ≃ₗ[ℝ]
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)),
      (∀ (u : EuclideanSpace ℝ (Fin (2 * n))) (i : Fin n), (L u).1 i = u ⟨i.1, by omega⟩) ∧
      (∀ (u : EuclideanSpace ℝ (Fin (2 * n))) (i : Fin n), (L u).2 i = u ⟨n + i.1, by omega⟩) := by
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin (2 * n))) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) := by
    rw [Module.finrank_prod, finrank_euclideanSpace, finrank_euclideanSpace, Fintype.card_fin,
      Fintype.card_fin]
    exact Nat.two_mul n
  have hsurj : Function.Surjective (pairMap n) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp (pairMap_injective n)
  refine ⟨LinearEquiv.ofBijective (pairMap n) ⟨pairMap_injective n, hsurj⟩, ?_, ?_⟩
  · intro u i
    exact pairMap_fst n u i
  · intro u i
    exact pairMap_snd n u i

/-- The canonical linear equivalence splitting `ℝ^{2n}` into two blocks of `n` coordinates. -/
noncomputable def pairEquiv (n : ℕ) :
    EuclideanSpace ℝ (Fin (2 * n)) ≃ₗ[ℝ]
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
  Classical.choose (exists_pairEquiv n)

@[simp] theorem pairEquiv_apply_fst (n : ℕ) (u : EuclideanSpace ℝ (Fin (2 * n))) (i : Fin n) :
    (pairEquiv n u).1 i = u ⟨i.1, by omega⟩ :=
  (Classical.choose_spec (exists_pairEquiv n)).1 u i

@[simp] theorem pairEquiv_apply_snd (n : ℕ) (u : EuclideanSpace ℝ (Fin (2 * n))) (i : Fin n) :
    (pairEquiv n u).2 i = u ⟨n + i.1, by omega⟩ :=
  (Classical.choose_spec (exists_pairEquiv n)).2 u i


section Param

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- The chartwise difference `e y - e x`: the first component of the pair is the coordinate of
`x` in the chart at `p`, the second that of `y` in the chart at `q`. -/
noncomputable def pairZ (e : M → EuclideanSpace ℝ (Fin (2 * n + 1))) (p q : M) :
    (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) → EuclideanSpace ℝ (Fin (2 * n + 1)) :=
  fun ab => chartRep e q ab.2 - chartRep e p ab.1

/-- The domain of the pair parametrisation: the two parameters lie in the chart targets and the
last coordinate of the difference does not vanish (so that `extract` is defined). -/
noncomputable def pairDom (e : M → EuclideanSpace ℝ (Fin (2 * n + 1))) (p q : M) :
    Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
  {ab | ab.1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).target ∧
        ab.2 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) q).target ∧
        (pairZ e p q ab) (Fin.last (2 * n)) ≠ 0}

/-- The projection direction determined by a pair of chart coordinates. -/
noncomputable def pairDir (e : M → EuclideanSpace ℝ (Fin (2 * n + 1))) (p q : M) :
    (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) → EuclideanSpace ℝ (Fin (2 * n)) :=
  fun ab => extract (pairZ e p q ab)

/-- The pair parametrisation, with values in the `ℝ^n × ℝ^n` coordinates of the direction
space (so that its source and target are the same space). -/
noncomputable def pairParam (e : M → EuclideanSpace ℝ (Fin (2 * n + 1))) (p q : M) :
    (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) →
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
  fun ab => pairEquiv n (pairDir e p q ab)

/-- The critical set of the pair parametrisation. -/
noncomputable def pairCrit (e : M → EuclideanSpace ℝ (Fin (2 * n + 1))) (p q : M) :
    Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
  {ab | ab ∈ pairDom e p q ∧ (fderiv ℝ (pairParam e p q) ab).det = 0}

/-- The immersion-bad directions (of a single chart) in the `ℝ^n × ℝ^n` coordinates. -/
noncomputable def immBadCoord (e : M → EuclideanSpace ℝ (Fin (2 * n + 1))) (p : M) :
    Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
  pairEquiv n '' (immParam (n := n) (k := 2 * n) e p '' immDom (n := n) (k := 2 * n) e p)

/-- The projection direction determined by a pair of points `x`, `y` (relative to the charts at
`p` and `q`): this is the unique direction `u` for which `projVec u (e y) = projVec u (e x)`. -/
noncomputable def pairDirPt (e : M → EuclideanSpace ℝ (Fin (2 * n + 1))) (p q : M) (x y : M) :
    EuclideanSpace ℝ (Fin (2 * n)) :=
  pairDir e p q ((chartAt (EuclideanSpace ℝ (Fin n)) p) x,
    (chartAt (EuclideanSpace ℝ (Fin n)) q) y)

/-- The transversality-bad directions of a pair of charts, in the `ℝ^n × ℝ^n` coordinates. -/
noncomputable def transBadCoord (e : M → EuclideanSpace ℝ (Fin (2 * n + 1))) (p q : M) :
    Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
  pairParam e p q '' pairCrit e p q

end Param

end Work.Projection
