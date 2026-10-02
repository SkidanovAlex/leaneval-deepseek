import Mathlib
import Submission.Work.PTGeometric.SourceZero
import Submission.Work.PTGeometric.SourceFamily

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: the zero set is a union of collar rays

The flat source homotopy of a family is constant along the *time* coordinate `x 0` as long as
`x 0 ≤ 1 / 2`: on that collar it equals the explicit concatenation `alphaFamily G m` read at the
cube coordinates `cubeCoord (k + 8) (tail (k + 8) (srcCast x))`, which do not involve the coordinate
`0` at all (`Work.PTGeometric.flatSourceHomotopy8_eq_collapse`).

Consequently the zero set `Z = sourceZeroSet G m hpow` is *saturated* in the collar
`{x | x 0 ≤ 1 / 2}` in the direction of the `0`-axis: two points of the half-space which agree off
the coordinate `0` and both lie in the collar are either both in `Z` or both outside it.  This is the
statement `Work.PTGeometric.mem_sourceZeroSet_of_collarRay`: it is what makes `Z ∩ {x 0 = 0}` the
full radial picture of `Z` in the collar (the input of `SOURCE_PLAN.md` §2, where the defining
function of the region is built from the boundary picture alone).

## Main results

* `Work.PTGeometric.mem_sourceZeroSet_of_collarRay`
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped Manifold ContDiff Topology unitInterval
open Function Set Topology Manifold Filter

namespace Work.PTGeometric

noncomputable section

open Work.ThomBordism
open Work.ThomBordism.PontryaginThom

variable {k : ℕ} {D : ThomTarget k} {ι : Type} [Fintype ι] {Fam : ι → Man8}

/-- **The zero set is saturated along the collar rays.**  If `x` lies in the zero set of the flat
source homotopy of a family and `x 0 ≤ 1 / 2`, then any `y` which agrees with `x` off the coordinate
`0` and still satisfies `y 0 ≤ 1 / 2` lies in the zero set as well: in the collar the homotopy only
sees the cube coordinates `coordinate 1, …, coordinate (8+k)`. -/
theorem mem_sourceZeroSet_of_collarRay {k : ℕ} {D : Work.ThomBordism.PontryaginThom.ThomTarget k}
    {ι : Type} [Fintype ι] {Fam : ι → Work.ThomBordism.Man8}
    (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, Work.PTGeometric.tubeAlpha (G.rep i)) ^ m = 1)
    {x y : EuclideanHalfSpace ((8 + k) + 1)}
    (hx : x ∈ Work.PTGeometric.sourceZeroSet G m hpow) (hx0 : x.1 0 ≤ 1 / 2)
    (hy : ∀ i : Fin ((8 + k) + 1), i ≠ 0 → y.1 i = x.1 i) (hy0 : y.1 0 ≤ 1 / 2) :
    y ∈ Work.PTGeometric.sourceZeroSet G m hpow := by
  -- the collar identity of the flat source homotopy only reads the coordinates `≠ 0`,
  -- and `y` and `x` have the same ones.
  have htail : tail (k + 8) (srcCast k y.1) = tail (k + 8) (srcCast k x.1) := by
    ext i
    rw [tail_apply, tail_apply, srcCast_apply, srcCast_apply]
    exact hy _ (fun h0 => Fin.succ_ne_zero i ((Fin.cast_eq_zero _ (Fin.succ i)).mp h0))
  simp only [sourceZeroSet, Set.mem_ofPred_eq] at hx ⊢
  rw [flatSourceHomotopy8_eq_collapse (k := k) (D := D) (familySource G m hpow).H
        (familySource G m hpow).φ (alphaFamily G m) (familySource G m hpow).collar
        (x := x.1) hx0] at hx
  rw [flatSourceHomotopy8_eq_collapse (k := k) (D := D) (familySource G m hpow).H
        (familySource G m hpow).φ (alphaFamily G m) (familySource G m hpow).collar
        (x := y.1) hy0]
  rw [← htail] at hx
  exact hx

end

end Work.PTGeometric
