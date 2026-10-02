import Mathlib
import Submission.Work.Thom.smooth8
import Submission.Work.Projective.CP4Concrete
import Submission.Work.Projective.Model
import Submission.Work.Projective.CPn

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `ℂP⁴` is a closed oriented smooth `8`-manifold

The repaired interface `Work.Thom.ClosedOrientedSmooth8` (`Submission/Work/Thom/smooth8.lean`)
packages a closed oriented smooth `8`-manifold as

* a type `pt` with a `TopologicalSpace`, a `ChartedSpace (EuclideanSpace ℝ (Fin 8))` and an
  `IsManifold 𝓘(ℝ,ℝ⁸) 1` structure (`C¹` suffices for the interface),
* `CompactSpace` and `ConnectedSpace` instances, and
* a **generating** fundamental class `c ∈ H₈(pt;ℤ)`.

This module inhabits it, so that the global statements
`Work.Thom.HirzebruchIdentity8` / `Work.Thom.HirzebruchCongruence8` are *not vacuous*.

## The witness

The witness is `ℂP⁴ = Work.Projective.CP 4`:

* `Work.Projective.Model` charts `ℂPⁿ` over the Euclidean model `EuclideanSpace ℝ (Fin (2*n))` and
  provides `Work.Projective.instIsManifoldEuclidean 4`, an `IsManifold (𝓡 8) ∞ (ℂP⁴)` structure —
  a `C^∞` structure, hence in particular `C¹`, which is the regularity the interface asks for;
* `Work.Projective.CP4Concrete` provides the chosen generator `Work.Projective.cp4C` of
  `H₈(ℂP⁴;ℤ) ≅ ℤ` together with the spanning statement `Work.Projective.cp4C_span`;
* `Work.Projective.compactSpace_CP`, `Work.Projective.connectedSpace_CP` (from
  `Work.Projective.Atlas`) give compactness and connectedness.

## A formal remark on the instance arguments

The interface's `IsManifold` field carries an implicit `[ChartedSpace (EuclideanSpace ℝ (Fin 8))]`
argument, and `Work.Projective`'s smooth structure is stated for the *defeq but syntactically
different* model `EuclideanSpace ℝ (Fin (2*4))`.  Type class search cannot unify these on the nose
(it would have to solve `2 * ?n = 8` with `?n` a metavariable), so the two instances
`instChartedSpaceCPSpace4` and `instIsManifoldCPSpace4` below state the `ℂP⁴` structures in
exactly the form the interface uses.  They are `abbrev`s (`attribute [instance]`), so they remain
definitionally equal to the `Work.Projective` instances.
-/

namespace Work.Thom

open Work.Projective

open scoped Manifold ContDiff

noncomputable section

/-! ## The `ℂP⁴` instances in the exact form of the interface -/

/-- The Euclidean charted space structure on `ℂP⁴`, stated over the model
`EuclideanSpace ℝ (Fin 8)` (definitionally the `Fin (2*4)` of `Work.Projective`). -/
abbrev instChartedSpaceCPSpace4 : ChartedSpace (EuclideanSpace ℝ (Fin 8)) (CP 4) :=
  instChartedSpaceEuclidean 4

attribute [instance] instChartedSpaceCPSpace4

/-- The `C^∞` smooth structure on `ℂP⁴`, stated over the model `EuclideanSpace ℝ (Fin 8)`. -/
abbrev instIsManifoldCPSpace4 : IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin 8))) ∞ (CP 4) :=
  Work.Projective.instIsManifoldEuclidean 4

attribute [instance] instIsManifoldCPSpace4

/-! ## The witness of `Work.Thom.ClosedOrientedSmooth8` -/

/-- **`ℂP⁴` as a closed oriented smooth `8`-manifold**, in the repaired interface
`Work.Thom.ClosedOrientedSmooth8`.  The underlying type is `Work.Projective.CP 4`, the smooth
structure is the Euclidean one of `Work.Projective.Model` used at regularity `1`, and the
fundamental class is the chosen generator `Work.Projective.cp4C` of `H₈(ℂP⁴;ℤ) ≅ ℤ`. -/
def cp4ClosedOrientedSmooth8 : Work.Thom.ClosedOrientedSmooth8 where
  pt := CP 4
  topologicalSpace := inferInstance
  chartedSpace := instChartedSpaceCPSpace4
  isManifold := inferInstance
  compactSpace := compactSpace_CP 4
  connectedSpace := connectedSpace_CP 4
  c := cp4C
  c_generates := cp4C_span

/-- **There exists a closed oriented smooth `8`-manifold** (namely `ℂP⁴`): the structure
`Work.Thom.ClosedOrientedSmooth8` is inhabited, so the global statements
`Work.Thom.HirzebruchIdentity8` and `Work.Thom.HirzebruchCongruence8` are not vacuous. -/
theorem nonempty_closedOrientedSmooth8 : Nonempty Work.Thom.ClosedOrientedSmooth8 :=
  ⟨cp4ClosedOrientedSmooth8⟩

end

end Work.Thom
