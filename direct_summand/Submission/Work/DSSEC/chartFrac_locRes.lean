import Mathlib
import Submission.Work.DSSEC.Basic

namespace Work.DSSEC

attribute [local instance] MvPolynomial.gradedAlgebra
open CategoryTheory AlgebraicGeometry
universe u

/-- The chart coordinates `t_k/t_l` are compatible with the restriction maps
`W_{t_S} → W_{t_T}` for `S ⊆ T`.  Both sides of the goal are elements of `W_{t_T}` whose product
with `t_l` is `t_k` (`Work.DSSEC.chartFrac_mul`), and `t_l` is a unit of `W_{t_T}` because
`l ∈ S ⊆ T`. -/
theorem chartFrac_locRes {W : Type u} [CommRing W] {ι : Type u} [DecidableEq ι] (t : ι → W)
    {S T : Finset ι} (h : S ⊆ T) (l : ι) (hl : l ∈ S) (k : ι) :
    DSMap.Mix2.locRes t h (Work.DSSEC.chartFrac t S l hl k) =
      Work.DSSEC.chartFrac t T l (h hl) k := by
  -- both sides are the unique solution `x` of `x · (t_l) = t_k` in `W_{t_T}`, and `t_l` is a
  -- unit there because `l ∈ S ⊆ T`
  have h1 : DSMap.Mix2.locRes t h (Work.DSSEC.chartFrac t S l hl k) *
      algebraMap W (Localization.Away (DSMap.Mix2.tS t T)) (t l) =
      algebraMap W (Localization.Away (DSMap.Mix2.tS t T)) (t k) := by
    simpa using congrArg (DSMap.Mix2.locRes t h) (Work.DSSEC.chartFrac_mul t S l hl k)
  refine (Work.DSSEC.isUnit_algebraMap_t t (h hl)).mul_right_cancel ?_
  rw [h1, Work.DSSEC.chartFrac_mul t T l (h hl) k]

end Work.DSSEC
