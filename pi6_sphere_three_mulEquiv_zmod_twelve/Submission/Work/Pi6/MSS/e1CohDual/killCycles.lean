import Mathlib
import Submission.Work.Pi6.MSS.e1CohDualDefs
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The comparison map kills the cycles of a vanishing page element

`Work.Pi6.MSS.e1cEvZ 𝕜 p s n x` is the functional induced by a cocycle `x ∈ Z_1^{s,n}` on the
homology of the `s`-th graded piece `C(A_{s+1})/C(A_s)` of the Serre filtration.  Here we show
that if that functional vanishes, then evaluating `x` on any lift (through the linear section
`e1cSec`) of a cycle `u` of the graded piece gives zero.

The point is that `u`, being a cycle, has a homology class, and the evaluation of `e1cEvZ x` on
that class is *by definition* the evaluation of `x` on the chosen lift of `u`
(`e1cEv_π` + `e1cEvCyc_apply`).  The only content is producing an honest cycle `z` of the complex
`e1cKg 𝕜 p s` with `iCycles z = u` out of the hypothesis `d u = 0`, which is
`HomologicalComplex.cyclesMk` (there is no issue in degree `0`, since then `next 0 = 0 = 0 - 1`
and the differential `d 0 0` is zero).
-/

set_option maxHeartbeats 1000000

namespace Work.Pi6.MSS.e1CohDual

open CategoryTheory CategoryTheory.Limits HomologicalComplex

theorem killCycles (𝕜 : Type) [Field 𝕜] {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (s n : ℕ)
    (x : ↥(Work.Pi6.MSS.pZ 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) 1 s n))
    (hx : Work.Pi6.MSS.e1cEvZ 𝕜 p s n x = 0)
    (u : (Work.Pi6.MSS.e1cKg 𝕜 p s).X n)
    (hu : ((Work.Pi6.MSS.e1cKg 𝕜 p s).d n (n-1)).hom u = 0) :
    (Work.Pi6.MSS.e1cCochFun 𝕜 p n x.1)
      (((Work.Pi6.MSS.e1cIncl 𝕜 p (s+1)).f n).hom (Work.Pi6.MSS.e1cSec 𝕜 p s n u)) = 0 := by
  -- The index of the differential out of degree `n` in the `down ℕ` shape.
  have hnext : (ComplexShape.down ℕ).next n = n - 1 := Work.Cohomology.down_next n
  -- `u` is a cycle, so it has a lift in `K.cycles n` whose underlying element is `u`.
  let hu' : (CategoryTheory.ConcreteCategory.hom ((CategoryTheory.forget₂ (ModuleCat 𝕜) Ab).map
      ((Work.Pi6.MSS.e1cKg 𝕜 p s).d n (n-1)))) u = 0 := by simpa using hu
  let z : (Work.Pi6.MSS.e1cKg 𝕜 p s).cycles n :=
    (Work.Pi6.MSS.e1cKg 𝕜 p s).cyclesMk u (n-1) hnext hu'
  have hz : ((Work.Pi6.MSS.e1cKg 𝕜 p s).iCycles n).hom z = u := by
    have h := HomologicalComplex.i_cyclesMk (K := Work.Pi6.MSS.e1cKg 𝕜 p s) (x := u)
      (j := n-1) hnext hu'
    simpa using h
  -- The vanishing of the functional on homology.
  have hx' : Work.Pi6.MSS.e1cEv 𝕜 p s n x = 0 := hx
  have h0 : Work.Pi6.MSS.e1cEv 𝕜 p s n x
      (((Work.Pi6.MSS.e1cKg 𝕜 p s).homologyπ n).hom z) = 0 := by
    rw [hx', LinearMap.zero_apply]
  -- Evaluate the definition of the comparison map on the homology class of the cycle `z`.
  rw [Work.Pi6.MSS.e1cEv_π 𝕜 p s n x z] at h0
  rw [Work.Pi6.MSS.e1cEvCyc_apply] at h0
  rw [hz] at h0
  simpa only [Work.Pi6.MSS.e1cPageCoch, Work.Pi6.MSS.e1cCochFun] using h0

end Work.Pi6.MSS.e1CohDual
