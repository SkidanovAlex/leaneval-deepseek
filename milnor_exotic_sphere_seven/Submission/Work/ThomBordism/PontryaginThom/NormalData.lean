import Submission.Work.ThomBordism.PontryaginThom.Orthogonal
import Submission.Work.ThomBordism.PontryaginThom.Frames

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# The normal bundle of an immersion, over the finite chart cover

This file fixes the *shape* of the output of the assembly of item 1: the normal bundle of an
immersion `f : V → ℝ^{8+k}`, as gluing data (`ComplementData`) over the finite cover
`Work.Thom.chartCover × ChartIdx 8 k`, together with the two facts that tie it to the geometry:

* the base set of the index `(i,S)` lies in the source of the chart `chartCover i` and the `S`-th
  coordinate projection of the frame `frame f (chartCover i)` is invertible there (so that
  `planeProj (frame f (chartCover i)) S h` and its right inverse `complInj S` are available);
* the kernel of the projection is the plane of the frame, i.e. `im (d f_x)`
  (`ker (P (i,S) x) = range (coeffMap (frame f (chartCover i) x))`).

With `P` and `I` built from the *orthogonal* complement (`Orthogonal.lean`: `orthProj`, `orthInj`)
the chart-independence hypothesis `ker_agree` of `ComplementData` is a consequence of
`range_coeffMap_frame_agree`, and `P ∘ I = id` is `planeProj_orthInj_complInj`.
-/

open scoped Manifold ContDiff Topology

namespace Work.ThomBordism.PontryaginThom

open Work.ThomBordism.Grassmann Work.TangentClasses

noncomputable section

variable {V : Man8} {k : ℕ}

/-- The index type of the cover of the assembly: the finite chart cover of `V` (`Work.Thom`) crossed
with the chart indices `S` of the oriented Grassmannian `G̃r_8(ℝ^{8+k})`. -/
abbrev CoverIdx (V : Man8) (k : ℕ) : Type :=
  Fin (Work.Thom.chartCoverSize (H := Euc 8) (M := V.pt)) × ChartIdx 8 k

/-- **The normal bundle of an immersion `f : V → ℝ^{8+k}`**, as gluing data over the finite cover
`CoverIdx V k`, with the plane of the frame as the kernel of every projection. -/
structure NormalData (V : Man8) (k : ℕ) (f : V.pt → Euc (8 + k)) where
  /-- the complement data (the normal bundle as gluing data) -/
  D : ComplementData V.pt k (CoverIdx V k)
  /-- the base set of `(i,S)` lies in the source of the chart `chartCover i` -/
  baseSet_sub : ∀ (i : Fin (Work.Thom.chartCoverSize (H := Euc 8) (M := V.pt)))
    (S : ChartIdx 8 k) (x : V.pt), x ∈ D.baseSet (i, S) →
      x ∈ (Work.Thom.chartCover (H := Euc 8) (M := V.pt) i).1.source
  /-- on the base set, the `S`-th coordinate projection of the frame is invertible -/
  baseSet_det : ∀ (i : Fin (Work.Thom.chartCoverSize (H := Euc 8) (M := V.pt)))
    (S : ChartIdx 8 k) (x : V.pt), x ∈ D.baseSet (i, S) →
      (frameMatrix S (frame f (Work.Thom.chartCover (H := Euc 8) (M := V.pt) i) x)).det ≠ 0
  /-- the kernel of the projection is the plane of the frame (`im (d f_x)`) -/
  ker_eq_range : ∀ (i : Fin (Work.Thom.chartCoverSize (H := Euc 8) (M := V.pt)))
    (S : ChartIdx 8 k) (x : V.pt), x ∈ D.baseSet (i, S) →
      LinearMap.ker ((D.P (i, S) x : (Fin (8 + k) → ℝ) →ₗ[ℝ] (Fin k → ℝ)))
        = LinearMap.range (coeffMap (frame f (Work.Thom.chartCover (H := Euc 8)
            (M := V.pt) i) x))

end

end Work.ThomBordism.PontryaginThom
