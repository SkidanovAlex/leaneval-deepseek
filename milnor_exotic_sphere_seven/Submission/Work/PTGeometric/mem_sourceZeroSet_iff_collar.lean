import Mathlib
import Submission.Work.PTGeometric.SourceZero

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: the zero set of the flat source homotopy on the collar

On the collar `x 0 ≤ 1 / 2` of the source (where the flat source homotopy *is* the collapse map,
`Work.PTGeometric.flatSourceHomotopy8_eq_collapse`), membership of a point in the null-bordism
`Work.PTGeometric.sourceZeroSet` is read off the cube coordinates.

This lemma lived in `exists_sourceRegionPhi.lean` (the file of the **refuted** interface
`Work.PTGeometric.SourceRegionPhiProp`, deleted by its prover); it is the only part of that file
that is used elsewhere, so it is kept here.

## Main results

* `Work.PTGeometric.mem_sourceZeroSet_iff_collar`
-/

set_option autoImplicit false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter
open Work.ThomBordism Work.ThomBordism.PontryaginThom

namespace Work.PTGeometric

noncomputable section

variable {k : ℕ} {D : ThomTarget k} {ι : Type} [Fintype ι] {Fam : ι → Man8}

/-- **The collar identity for the zero set**: on `x.1 0 ≤ 1 / 2` the flat source homotopy is the
explicit concatenation `alphaFamily`, so `x` is in the null-bordism iff its cube coordinate is in the
core preimage. -/
theorem mem_sourceZeroSet_iff_collar (G : GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1)
    {x : EuclideanHalfSpace ((8 + k) + 1)} (hx : x.1 0 ≤ 1 / 2) :
    x ∈ sourceZeroSet G m hpow ↔
      alphaFamily G m (cubeCoord (k + 8) (tail (k + 8) (srcCast k x.1))) ∈ G.core := by
  rw [sourceZeroSet, Set.mem_ofPred_eq, flatSourceHomotopy8_eq_collapse (k := k)
    (familySource G m hpow).H (familySource G m hpow).φ (alphaFamily G m)
    (familySource G m hpow).collar (x := x.1) hx]

end

end Work.PTGeometric
