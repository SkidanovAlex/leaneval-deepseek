import Mathlib
import Submission.Work.Thom.Pair
import Submission.Work.Thom.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-!
# Pulling a real bundle back along a map of bases

`Submission/Work/TangentClasses/Bundle.lean` provides `Work.TangentClasses.RealBundle.pullback`
together with `pullback_baseSet`, `pullback_indexAt`, `pullback_coordChange`, `pullback_id`,
`pullback_comp`, `pullback_trivial`.  This module records the *Thom-chapter* face of that
construction: the Euclidean structure and the zero complement are pulled back too.

These are the compatibility lemmas that any Mayer–Vietoris induction over a trivialising cover of
the base (the classical proof of the Thom isomorphism theorem for a general oriented bundle) starts
from.  They are stated for the chapter's `RealBundle`; note that the pullback of the
*trivial* bundle is again trivial (`RealBundle.pullback_trivial`, `rfl`), which is what makes the
rank-`n` trivial bundle over an arbitrary base the pullback of the rank-`n` trivial bundle over a
point.
-/

open Work.TangentClasses

namespace Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type}

/-- **The pullback of a Euclidean bundle is Euclidean**: the transition functions of `Z.pullback f`
are the transition functions of `Z` composed with `f`, so they preserve the norm whenever those of
`Z` do. -/
theorem isEuclidean_pullback {B' : Type} [TopologicalSpace B'] (Z : RealBundle B F ι)
    (f : C(B', B)) (hZ : IsEuclidean Z) : IsEuclidean (Z.pullback f) := by
  intro i j x hx v
  exact hZ i j (f x) hx v

/-- The vector of a point of the total space of a pulled-back bundle, read in a chart: the fibre
coordinate of a pulled-back bundle is the original fibre coordinate. -/
theorem pullback_fiber_eq (Z : RealBundle B F ι) {B' : Type} [TopologicalSpace B'] (f : C(B', B))
    (x : B') : (Z.pullback f).Fiber x = Z.Fiber (f x) := rfl

/-- **The zero complement is pulled back**: the points of the total space of `Z.pullback f` that lie
in the zero complement are exactly those whose image under the bundle map lies in the zero
complement of `Z`.  (Both sides are defined by the fibrewise condition `v ≠ 0`, so this is
`rfl`.) -/
theorem mem_zeroComplement_pullback (Z : RealBundle B F ι) {B' : Type} [TopologicalSpace B']
    (f : C(B', B)) (p : (Z.pullback f).TotalSpace) :
    p ∈ zeroComplement (Z.pullback f) ↔
      (⟨f p.1, (show F from p.2)⟩ : Z.TotalSpace) ∈ zeroComplement Z :=
  Iff.rfl

/-- The projection of a pulled-back bundle: `(Z.pullback f)` is a bundle over `B'`, so its
projection is the base projection of `B'`. -/
theorem pullback_proj_eq (Z : RealBundle B F ι) {B' : Type} [TopologicalSpace B'] (f : C(B', B))
    (p : (Z.pullback f).TotalSpace) : (Z.pullback f).proj p = p.1 := rfl

/-- The **bundle map** out of a pulled-back bundle: a point of `(Z.pullback f).TotalSpace` maps to
the point of `Z.TotalSpace` with the same fibre coordinate, over `f` of its base point. -/
def pullbackTotalMap (Z : RealBundle B F ι) {B' : Type} [TopologicalSpace B']
    (f : C(B', B)) (p : (Z.pullback f).TotalSpace) : Z.TotalSpace :=
  ⟨f p.1, (show F from p.2)⟩

@[simp] theorem pullbackTotalMap_proj (Z : RealBundle B F ι) {B' : Type} [TopologicalSpace B']
    (f : C(B', B)) (p : (Z.pullback f).TotalSpace) :
    (pullbackTotalMap Z f p).1 = f p.1 := rfl

/-- **`IsEuclidean` for the trivial bundle is preserved under pullback, from
`RealBundle.pullback_trivial`**: the trivial bundle over `B'` of the same rank. -/
theorem isEuclidean_pullback_trivial {B' : Type} [TopologicalSpace B'] {ι₀ : Type} [Inhabited ι₀]
    (f : C(B', B)) : IsEuclidean ((RealBundle.trivial B ℝ ι₀).pullback f) :=
  isEuclidean_pullback _ f (isEuclidean_trivial B ℝ ι₀)

end

end Work.Thom
