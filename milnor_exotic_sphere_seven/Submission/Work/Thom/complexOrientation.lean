import Mathlib
import Submission.Work.Thom.complexDet
import Submission.Work.Thom.complexBundleAux
import Submission.Work.Thom.isOrientedOver_of_det_pos
import Submission.Work.Thom.nonempty_thomClass_of_oriented_genFibre
import Submission.Work.Thom.realification

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# The complex orientation: the realification of a complex bundle is canonically oriented

A complex vector bundle is canonically oriented: its transition functions are `ℂ`-linear, hence
have *positive real determinant* (`Work.Thom.det_restrictScalars_pos`), hence preserve the
orientation of the fibre, hence induce the identity on the relative top cohomology of the Thom pair
`(V, V∖0)`.

In the workspace's model the bridge is `Work.Thom.IsOrientedOver`, and
`Work.Thom.isOrientedOver_of_det_pos` is the classical criterion
"`det coordChange i j > 0` pointwise over `U ∩ V` ⟹ the two chart-trivialisations of the model Thom
class agree over the overlap".  Feeding the determinant computation into it gives

* `Work.Thom.isOrientedOver_of_complex` — `IsOrientedOver (realification Z) (2*m) U V` for **any**
  two-chart cover, with **no** hypothesis whatsoever on the overlap (not contractible, not
  null-homotopic gauge);
* `Work.Thom.nonempty_thomClass_of_complex_cover` — **the Thom class of the realification of a
  complex bundle of rank `m` over a two-piece open cover**, and hence (via
  `Work.Thom.ThomClass.eulerClass`) the **top Chern class** `c_m(V) = e(V_ℝ)`.

For `m = 1` this is the **first Chern class** `c₁(L) = e(L_ℝ)` of a complex line bundle — the first
Chern class produced by the workspace.

(The weaker route through a homotopy of gauges lives in
`Submission/Work/Thom/isOrientedOver_of_gauge_homotopy.lean` and
`Submission/Work/Thom/exists_gauge_homotopy_of_complex.lean`; it is the form that works for a
*general* real bundle over a cover with contractible overlap.)
-/

open Work.TangentClasses

namespace Work.Thom

open CategoryTheory

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type}

/-- **The realification of a complex vector bundle is canonically oriented over any two-chart
cover.**  The gauge `Z.coordChange i j x` is `ℂ`-linear and bijective, so its real determinant is
`|det_ℂ|² > 0` (`Work.Thom.det_restrictScalars_pos`), and
`Work.Thom.isOrientedOver_of_det_pos` applies. -/
theorem isOrientedOver_of_complex (m : ℕ) (hm : 1 ≤ m)
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    {U V : Set B} {i j : ι} (hUi : U ⊆ Z.baseSet i) (hVj : V ⊆ Z.baseSet j) :
    IsOrientedOver (realification Z) (2 * m) U V := by
  haveI : NeZero (2 * m) := ⟨by omega⟩
  refine isOrientedOver_of_det_pos (n := 2 * m) (by omega) (finrank_real_euclidean_complex m)
    (Z := realification Z) (i := i) (j := j) ?_ ?_ ?_
  · intro x hx
    rw [realification_baseSet]
    exact hUi hx
  · intro x hx
    rw [realification_baseSet]
    exact hVj hx
  · intro x
    have hcoord : (realification Z).coordChange i j (x : B)
        = (Z.coordChange i j (x : B)).restrictScalars ℝ := by
      ext v
      rw [realification_coordChange]
      rfl
    rw [hcoord]
    exact det_restrictScalars_pos (coordChange_bijective Z i j ⟨hUi x.2.1, hVj x.2.2⟩)

/-- **The Thom class of the realification of a complex bundle over a two-piece open cover.**
No hypothesis on the geometry of the overlap is needed: complex bundles are canonically oriented. -/
theorem nonempty_thomClass_of_complex_cover (m : ℕ) (hm : 1 ≤ m)
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    {U V : Set B} (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ)
    {i j : ι} (hUi : U ⊆ Z.baseSet i) (hVj : V ⊆ Z.baseSet j) :
    Nonempty (ThomClass (realification Z) (2 * m)) := by
  haveI : Inhabited ι := ⟨i⟩
  refine nonempty_thomClass_of_oriented_genFibre (n := 2 * m) (by omega)
    (finrank_real_euclidean_complex m) (Z := realification Z) hU hV hcov
    (isOrientedOver_of_complex m hm Z hUi hVj) (k := i) ?_
  intro y hy
  rw [realification_baseSet]
  exact hUi hy.1

end

end Work.Thom
