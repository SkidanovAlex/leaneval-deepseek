import Mathlib
import Submission.Work.PlanarSC.HullDefs

namespace Work.PlanarSC

/-- If `U` has no bounded complementary component and a polyomino lies in `U`, then so does its
hull (a bounded component of the complement of the polyomino cannot meet `Uᶜ`, since the component
in `Uᶜ` of such a point is unbounded and lies in it). -/
theorem compHull_subset_of_no_bounded_complement {U : Set ℂ}
    (hnb : ∀ z : ℂ, z ∉ U → ¬ Bornology.IsBounded (connectedComponentIn Uᶜ z))
    {n : ℕ} {S : Finset (ℤ × ℤ)} (hSU : dyadicPolyomino n S ⊆ U) :
    compHull (dyadicPolyomino n S) ⊆ U := by
  intro z hz
  by_contra hzU
  -- `z ∈ compHull A` means the component of `z` in `Aᶜ` is bounded.
  rw [mem_compHull] at hz
  have hzUc : z ∈ Uᶜ := hzU
  -- the complement of the polyomino contains the complement of `U`
  have hsub : Uᶜ ⊆ (dyadicPolyomino n S)ᶜ := fun w hw hwA => hw (hSU hwA)
  -- so the *unbounded* `Uᶜ`-component of `z` sits inside the *bounded* `Aᶜ`-component of `z`
  have hcomp : connectedComponentIn Uᶜ z ⊆ connectedComponentIn (dyadicPolyomino n S)ᶜ z :=
    isPreconnected_connectedComponentIn.subset_connectedComponentIn (mem_connectedComponentIn hzUc)
      (fun w hw => hsub (connectedComponentIn_subset Uᶜ z hw))
  exact hnb z hzU (hz.subset hcomp)

end Work.PlanarSC
