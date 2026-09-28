import Mathlib
import Submission.Work.Stems.CollapseDefs
import Submission.Work.Stems.cubeToOnePoint_continuous
import Submission.Work.Stems.cubeToOnePoint_surjective
import Submission.Work.Stems.cubeToOnePoint_fibers

set_option synthInstance.maxHeartbeats 400000

/-!
# The collapse `Iⁿ / ∂Iⁿ ≅ Sⁿ`

For `n ≥ 1` there is a continuous surjection `φ : Iⁿ → Sⁿ` which sends the boundary `∂Iⁿ` of the
cube to the single point `φ 0` and which is injective off the boundary.  Equivalently, `φ` is the
quotient map `Iⁿ → Iⁿ/∂Iⁿ` composed with a homeomorphism `Iⁿ/∂Iⁿ ≅ Sⁿ`.

The construction (definitions in `Submission.Work.Stems.CollapseDefs`) goes through the one-point
compactification `OnePoint ℝⁿ ≃ₜ Sⁿ` of `ℝⁿ`:

* `cubeCoords : Iⁿ → ℝⁿ`, `q ↦ (y_i/√(1-y_i²))_i` with `y_i = 2q_i - 1`, is a homeomorphism from
  the interior of the cube onto `ℝⁿ` and blows up at the boundary;
* `cubeToOnePoint : Iⁿ → OnePoint ℝⁿ` sends `∂Iⁿ` to `∞` and agrees with `cubeCoords` elsewhere.
  It is continuous (`cubeToOnePoint_continuous`), surjective for `n ≥ 1`
  (`cubeToOnePoint_surjective`), and its fibres are the boundary and the singletons of the
  interior (`cubeToOnePoint_fibers`);
* a continuous surjection from the compact space `Iⁿ` to the Hausdorff space `OnePoint ℝⁿ` is
  closed, hence a quotient map (`IsClosedMap.isQuotientMap`);
* composing with the homeomorphism `onePointSphereHomeo : OnePoint ℝⁿ ≃ₜ Sⁿ` (which is a quotient
  map) yields the required collapse to the sphere.
-/

open scoped Topology unitInterval

namespace Work.Stems

noncomputable section

/-- The basepoint `0` of the cube lies on the boundary (for `n ≥ 1`). -/
theorem zero_mem_cubeBoundary (n : ℕ) (hn : 1 ≤ n) : (0 : CubeI n) ∈ Cube.boundary (Fin n) := by
  obtain ⟨i⟩ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact ⟨i, Or.inl (by simp)⟩

/-- On the boundary, the collapse is the point at infinity. -/
theorem cubeToOnePoint_eq_infty_of_mem_boundary {n : ℕ} {q : CubeI n}
    (hq : q ∈ Cube.boundary (Fin n)) : cubeToOnePoint n q = OnePoint.infty := by
  simp only [cubeToOnePoint]
  rw [if_pos hq]

/-- Off the boundary, the collapse is the coordinate map. -/
theorem cubeToOnePoint_eq_coe_of_not_mem_boundary {n : ℕ} {q : CubeI n}
    (hq : q ∉ Cube.boundary (Fin n)) :
    cubeToOnePoint n q = (cubeCoords n q : OnePoint (EuclideanSpace ℝ (Fin n))) := by
  simp only [cubeToOnePoint]
  rw [if_neg hq]

/-- The collapse map is closed (its domain is compact and its codomain is Hausdorff). -/
theorem isClosedMap_cubeToOnePoint (n : ℕ) : IsClosedMap (cubeToOnePoint n) :=
  fun _s hs => (hs.isCompact.image (cubeToOnePoint_continuous n)).isClosed

/-- The collapse map is a quotient map for `n ≥ 1`. -/
theorem isQuotientMap_cubeToOnePoint (n : ℕ) (hn : 1 ≤ n) :
    Topology.IsQuotientMap (cubeToOnePoint n) :=
  (isClosedMap_cubeToOnePoint n).isQuotientMap (cubeToOnePoint_continuous n)
    (cubeToOnePoint_surjective n hn)

theorem exists_collapsingMap (n : ℕ) (hn : 1 ≤ n) :
    ∃ φ : C(Fin n → Set.Icc (0:ℝ) 1, Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1),
      Topology.IsQuotientMap φ ∧
        (∀ q ∈ _root_.Cube.boundary (Fin n), φ q = φ 0) ∧
        (∀ q q' : Fin n → Set.Icc (0:ℝ) 1, φ q = φ q' →
          q = q' ∨ (q ∈ _root_.Cube.boundary (Fin n) ∧
            q' ∈ _root_.Cube.boundary (Fin n))) := by
  refine ⟨⟨fun q => onePointSphereHomeo n (cubeToOnePoint n q),
    (onePointSphereHomeo n).continuous.comp (cubeToOnePoint_continuous n)⟩, ?_, ?_, ?_⟩
  · exact (Homeomorph.isQuotientMap (onePointSphereHomeo n)).comp
      (isQuotientMap_cubeToOnePoint n hn)
  · intro q hq
    simp only [ContinuousMap.coe_mk]
    rw [cubeToOnePoint_eq_infty_of_mem_boundary hq,
      cubeToOnePoint_eq_infty_of_mem_boundary (zero_mem_cubeBoundary n hn)]
  · intro q q' h
    simp only [ContinuousMap.coe_mk] at h
    exact cubeToOnePoint_fibers n ((onePointSphereHomeo n).injective h)

end

end Work.Stems
