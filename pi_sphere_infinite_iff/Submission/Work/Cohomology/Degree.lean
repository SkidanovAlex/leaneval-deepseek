import Mathlib
import Submission.Work.Cohomology.Pullback
import Submission.Work.Cohomology.sphereHomologyTop

set_option synthInstance.maxHeartbeats 400000

/-!
# The degree of a self-map of a sphere

For `n ≥ 1` the top homology `H_n(Sⁿ; ℤ)` is infinite cyclic
(`Work.Cohomology.sphereHomologyTop`).  Choosing a generator `[Sⁿ]` once and for all, the **degree**
of a continuous self-map `f : Sⁿ → Sⁿ` is the integer `d` with `f_* [Sⁿ] = d • [Sⁿ]`.

This is the computational tool needed for the clutching construction of bundles over spheres: the
Euler class of an oriented rank-`n` bundle over `Sⁿ` with clutching function `f` is the degree of the
composite of `f` with the evaluation `SO(n) → Sⁿ⁻¹`, and for the quaternionic bundle `ξ_k` of
`Submission.Work.Milnor.Clutch` this reduces to the degree of a power map on `S³`.

## Main definitions and results

* `Work.Cohomology.sphereHomologyGen` — a chosen generator `[Sⁿ]` of `H_n(Sⁿ;ℤ)`;
* `Work.Cohomology.sphereSelfDegree` — the degree `deg f ∈ ℤ`.

The functoriality of the degree (`deg id = 1`, `deg (g ∘ f) = deg g · deg f`) and its homotopy
invariance are the next facts to prove about this definition; see `Submission/NOTES.md` §8.3.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Cohomology

noncomputable section

open CategoryTheory

/-- A chosen generator of `H_n(Sⁿ; ℤ) ≅ ℤ`, for the sphere `Sⁿ ⊆ ℝⁿ⁺¹`. -/
def sphereHomologyGen (n : ℕ) (hn : 1 ≤ n) :
    (singularChains ℤ (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))).homology n :=
  ((sphereHomologyTop n hn).some.inv.hom) (1 : ℤ)

/-- The degree of a self-map of the sphere `Sⁿ ⊆ ℝⁿ⁺¹`. -/
def sphereSelfDegree (n : ℕ) (hn : 1 ≤ n)
    (f : TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) ⟶
      TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) : ℤ :=
  ((sphereHomologyTop n hn).some.hom)
    (HomologicalComplex.homologyMap
      (chainMap ℤ (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))
        (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) f) n
      (sphereHomologyGen n hn))

end

end Work.Cohomology
