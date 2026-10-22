import Mathlib
import Submission.Work.ANALYTIC.RealSide
import Submission.Work.ANALYTIC.prodReal_rounding

namespace Work.ANALYTIC

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open Opposite
open _root_.LightCondensed _root_.LightCondensed.Solid

/-! ## `∏ℤ ⟶ ∏ℝ/∏^bnd ℝ` is an epimorphism

`zToRealQuot = prodZRealIncl ≫ cokernel.π boundedRealIncl : prodZModel ⟶ realQuot` is an
epimorphism of light condensed abelian groups (`LightCondAb` is `LightCondMod ℤ` definitionally).

Proof route: use the epimorphism criterion
`LightCondMod.epi_iff_locallySurjective_on_lightProfinite ℤ` (in the `←` direction).  Given
`S : LightProfinite` and `y` in the `S`-sections of `realQuot = coker boundedRealIncl`, apply the
same criterion in the `→` direction to the epimorphism `cokernel.π boundedRealIncl`: it produces a
surjection `φ : S' ⟶ S` and `z ∈ prodReal(S')` (that is, `z : ℕ → C(S',ℝ)`) with
`cokernel.π boundedRealIncl (z) = realQuot(φ) y`.  Now
`Work.ANALYTIC.prodReal_rounding S' z` gives `w : ℕ → C(S',ℤ)` and `N : ℕ` with
`|z n s - w n s| ≤ N`, so `z = prodZRealIncl w + boundedRealIncl b` where
`b n s = z n s - w n s` is uniformly bounded (hence `b ∈ boundedRealSet S'`) and is killed by
`cokernel.π boundedRealIncl`.  Therefore `zToRealQuot(w) = realQuot(φ) y`, which is exactly the
local-surjectivity datum required for `Epi zToRealQuot`. -/
theorem epi_zToRealQuot : CategoryTheory.Epi Work.ANALYTIC.zToRealQuot := by
  rw [LightCondMod.epi_iff_locallySurjective_on_lightProfinite (R := ℤ)]
  intro S y
  -- `cokernel.π boundedRealIncl` is an epimorphism, so `y` lifts locally to `∏ℝ`
  obtain ⟨S', φ, hφ, z, hz⟩ :=
    (LightCondMod.epi_iff_locallySurjective_on_lightProfinite (R := ℤ)
      (cokernel.π (boundedRealIncl))).mp (inferInstance) S y
  -- round the `ℕ`-indexed family `z` of continuous real functions uniformly
  obtain ⟨w, N, hN⟩ := prodReal_rounding S' z
  -- the rounding error, a uniformly bounded family of continuous real functions
  let bfun : ℕ → C(S', ℝ) := fun n =>
    ⟨fun s => z n s - (w n s : ℝ),
      (z n).continuous.sub
        ((continuous_of_discreteTopology (f := fun k : ℤ => (k : ℝ))).comp (w n).continuous)⟩
  have hbfun : ∀ n s, bfun n s = z n s - (w n s : ℝ) := fun n s => rfl
  let b : ↥(boundedRealSet S') := ⟨bfun, ⟨(N : ℝ), fun n s => by rw [hbfun]; exact hN n s⟩⟩
  -- the rounded error is killed by the quotient map
  have hzero : ((cokernel.π (boundedRealIncl)).hom.app (op S'))
      ((boundedRealIncl.hom.app (op S')) b) = 0 :=
    congrArg (fun (m : boundedReal ⟶ realQuot) =>
      (ConcreteCategory.hom (m.hom.app (op S'))) b) (cokernel.condition (boundedRealIncl))
  -- `z` is the sum of an integer family and a bounded real family
  have hdecomp : (prodZRealIncl.hom.app (op S')) w + (boundedRealIncl.hom.app (op S')) b = z := by
    change (fun n : ℕ => (prodZRealIncl.hom.app (op S')) w n
      + (boundedRealIncl.hom.app (op S')) b n) = z
    funext n
    refine ContinuousMap.ext fun s => ?_
    rw [ContinuousMap.add_apply, prodZRealIncl_apply, boundedRealIncl_apply, hbfun]
    ring
  -- hence the two sides have the same image in the quotient
  have hπ : ((cokernel.π (boundedRealIncl)).hom.app (op S')) ((prodZRealIncl.hom.app (op S')) w)
      = (realQuot.obj.map (op φ)) y := by
    rw [← hz, ← hdecomp]
    simp only [map_add, hzero, add_zero]
  exact ⟨S', φ, hφ, w, hπ⟩

end Work.ANALYTIC
