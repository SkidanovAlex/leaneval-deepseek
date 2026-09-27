import Mathlib
import Submission.Work.Projection.TransverseDefs

/-!
# The triple-point locus of a projection of an embedded manifold

Let `e : M → ℝ^{2n+1}` be a smooth embedding of a smooth `n`-manifold.  For a direction
`u : ℝ^{2n}` the projection `projVec u : ℝ^{2n+1} → ℝ^{2n}` (whose kernel is spanned by
`(u,1) = vVec u`) has a *triple point* at `(x,y,z)` if the three images coincide.  Since
`projVec u (e y) = projVec u (e x)` means `e y - e x ∈ span (vVec u)`, and the last coordinate of
`e y - e x` is non-zero whenever `x ≠ y` (as `e` is injective), the direction is *determined* by
the pair: `u = extract (e y - e x)`.

In the charts at `p, q, r` the whole configuration is captured by the parametrisation

`tripleParam e p q r ((v 0, v 1, v 2), u) = (projVec u (e y - e x), projVec u (e z - e x))`

(where `v 0, v 1, v 2` are the chart coordinates of `x, y, z`).  The directions which give triple
points through these charts are exactly the `u` for which this map vanishes for some triple of
chart parameters in the relevant domain, and this is how the bad set is defined below
(`tripleBad`).  The map is *not* a submersion everywhere (it fails to be one exactly when the
double point `(x,y)` is non-transverse, i.e. when the two tangent images do not span `ℝ^{2n}`);
the open subset where it is a submersion is recorded as `tripleDomTrans` and the corresponding
set of directions as `tripleBadTrans`.
-/

namespace Work.Projection

open scoped Manifold ContDiff
open Topology

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-- The parametrisation of the triple-point locus: to a triple of chart parameters `(v 0, v 1, v 2)`
(in the charts at `p`, `q`, `r`) and a direction `u` it associates the pair of projected
differences `(projVec u (e y - e x), projVec u (e z - e x))`. -/
noncomputable def tripleParam (e : M → EuclideanSpace ℝ (Fin (2 * n + 1))) (p q r : M) :
    ((Fin 3 → EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin (2 * n))) →
      EuclideanSpace ℝ (Fin (2 * n)) × EuclideanSpace ℝ (Fin (2 * n)) :=
  fun x => (projVec x.2 (pairZ e p q (x.1 0, x.1 1)),
            projVec x.2 (pairZ e p r (x.1 0, x.1 2)))

/-- The domain of the triple parametrisation: the three chart parameters lie in the chart targets,
the last coordinates of the two relevant differences do not vanish (so that the direction is
determined by either of them), and those two last coordinates are *different*.

The last condition is the non-degeneracy of the triple: at a point of the level set
`tripleParam e p q r x = 0` the differences `pairZ e p q (x.1 0, x.1 1) = e y - e x` and
`pairZ e p r (x.1 0, x.1 2) = e z - e x` are both non-zero multiples of `(u,1)`, so the equality
of their last coordinates is equivalent to `e y = e z`; for a genuine triple point (three distinct
points collapsed to one) it therefore holds automatically, while for `z = y` it fails and must be
excluded (the triple parametrisation is not a submersion there). -/
noncomputable def tripleDom (e : M → EuclideanSpace ℝ (Fin (2 * n + 1))) (p q r : M) :
    Set ((Fin 3 → EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin (2 * n))) :=
  {x | x.1 0 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).target ∧
       x.1 1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) q).target ∧
       x.1 2 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) r).target ∧
       (pairZ e p q (x.1 0, x.1 1)) (Fin.last (2 * n)) ≠ 0 ∧
       (pairZ e p r (x.1 0, x.1 2)) (Fin.last (2 * n)) ≠ 0 ∧
       (pairZ e p q (x.1 0, x.1 1)) (Fin.last (2 * n)) ≠
         (pairZ e p r (x.1 0, x.1 2)) (Fin.last (2 * n))}

/-- The part of the domain on which the pair `(x,y)` is a *transverse* double point, certified by
the non-vanishing of the determinant of the pair parametrisation `pairParam e p q`.  On this open
set the triple parametrisation is a submersion (see `fderiv_tripleParam_range_top`). -/
noncomputable def tripleDomTrans (e : M → EuclideanSpace ℝ (Fin (2 * n + 1))) (p q r : M) :
    Set ((Fin 3 → EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin (2 * n))) :=
  {x | x ∈ tripleDom e p q r ∧ (fderiv ℝ (pairParam e p q) (x.1 0, x.1 1)).det ≠ 0}

/-- The set of *bad triple directions* of the projection through the charts at `p`, `q`, `r`: the
directions `u` for which three points of the three chart targets are collapsed to a single point
by `projVec u ∘ e`. -/
noncomputable def tripleBad (e : M → EuclideanSpace ℝ (Fin (2 * n + 1))) (p q r : M) :
    Set (EuclideanSpace ℝ (Fin (2 * n))) :=
  {u | ∃ x : (Fin 3 → EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin (2 * n)),
        x ∈ tripleDom e p q r ∧ tripleParam e p q r x = 0 ∧ x.2 = u}

/-- The bad triple directions for which additionally the pair `(x,y)` is a transverse double
point.  This set has Hausdorff dimension at most `n` (see `dimH_tripleBadTrans_le`). -/
noncomputable def tripleBadTrans (e : M → EuclideanSpace ℝ (Fin (2 * n + 1))) (p q r : M) :
    Set (EuclideanSpace ℝ (Fin (2 * n))) :=
  {u | ∃ x : (Fin 3 → EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin (2 * n)),
        x ∈ tripleDomTrans e p q r ∧ tripleParam e p q r x = 0 ∧ x.2 = u}

@[simp] lemma mem_tripleBad {e : M → EuclideanSpace ℝ (Fin (2 * n + 1))} {p q r : M}
    {u : EuclideanSpace ℝ (Fin (2 * n))} :
    u ∈ tripleBad e p q r ↔
      ∃ x : (Fin 3 → EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin (2 * n)),
        x ∈ tripleDom e p q r ∧ tripleParam e p q r x = 0 ∧ x.2 = u := Iff.rfl

@[simp] lemma mem_tripleDom {e : M → EuclideanSpace ℝ (Fin (2 * n + 1))} {p q r : M}
    {x : (Fin 3 → EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin (2 * n))} :
    x ∈ tripleDom e p q r ↔
      x.1 0 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).target ∧
      x.1 1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) q).target ∧
      x.1 2 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) r).target ∧
      (pairZ e p q (x.1 0, x.1 1)) (Fin.last (2 * n)) ≠ 0 ∧
      (pairZ e p r (x.1 0, x.1 2)) (Fin.last (2 * n)) ≠ 0 ∧
      (pairZ e p q (x.1 0, x.1 1)) (Fin.last (2 * n)) ≠
        (pairZ e p r (x.1 0, x.1 2)) (Fin.last (2 * n)) := Iff.rfl

@[simp] lemma mem_tripleDomTrans {e : M → EuclideanSpace ℝ (Fin (2 * n + 1))} {p q r : M}
    {x : (Fin 3 → EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin (2 * n))} :
    x ∈ tripleDomTrans e p q r ↔
      x ∈ tripleDom e p q r ∧ (fderiv ℝ (pairParam e p q) (x.1 0, x.1 1)).det ≠ 0 := Iff.rfl

/-- The scalar equations of the triple condition, expanded. -/
lemma tripleParam_eq_zero_iff {e : M → EuclideanSpace ℝ (Fin (2 * n + 1))} {p q r : M}
    {x : (Fin 3 → EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin (2 * n))} :
    tripleParam e p q r x = 0 ↔
      projVec x.2 (pairZ e p q (x.1 0, x.1 1)) = 0 ∧
      projVec x.2 (pairZ e p r (x.1 0, x.1 2)) = 0 := by
  constructor
  · intro h
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  · rintro ⟨h1, h2⟩
    exact Prod.ext h1 h2

end Work.Projection
