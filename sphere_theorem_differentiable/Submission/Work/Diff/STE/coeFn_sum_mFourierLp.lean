import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE

theorem coeFn_sum_mFourierLp {ι : Type*} [Fintype ι] [DecidableEq ι] (p : (ι → ℤ) →₀ ℂ) :
    (∑ k ∈ p.support, p k • UnitAddTorus.mFourierLp (d := ι) (p := 2) k)
      =ᵐ[MeasureTheory.Measure.pi (fun _ : ι => AddCircle.haarAddCircle)]
    (fun t : UnitAddTorus ι => ∑ k ∈ p.support, p k * UnitAddTorus.mFourier k t) := by
  classical
  -- The `Lp` space of `mFourierLp` is the product measure of the normalised Haar measures on
  -- the circle factors, exactly the measure appearing in the statement.
  set ν : MeasureTheory.Measure (UnitAddTorus ι) :=
    MeasureTheory.Measure.pi (fun _ : ι => AddCircle.haarAddCircle)
  -- `ContinuousMap.toLp` is linear, so it turns the finite linear combination of continuous
  -- monomials into the corresponding finite linear combination in `Lp`.
  have htoLp : ContinuousMap.toLp (E := ℂ) 2 ν ℂ
        (∑ k ∈ p.support, p k • UnitAddTorus.mFourier k)
      = ∑ k ∈ p.support, p k • UnitAddTorus.mFourierLp (d := ι) (p := 2) k := by
    rw [map_sum]
    exact Finset.sum_congr rfl (fun k _ => (map_smul _ _ _).trans rfl)
  -- `toLp` agrees with the original continuous function almost everywhere.
  have hcoe := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (E := ℂ) ν
    (∑ k ∈ p.support, p k • UnitAddTorus.mFourier k)
  rw [← htoLp] at *
  filter_upwards [hcoe] with t ht
  rw [ht]
  simp [ContinuousMap.sum_apply, ContinuousMap.smul_apply]

end Work.Diff.STE
