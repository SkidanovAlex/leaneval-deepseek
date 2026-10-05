import Mathlib
import Submission.Work.SubBigon.region_subset_of_boundary_subset

namespace Work.RPB1a

/-- If `ins ⊆ ℝ × ℝ` is open with `closure ins = ins ∪ range γ` and `ins` disjoint from `range γ`,
then the frontier of `ins` is `range γ`; transporting along the linear homeomorphism
`Complex.equivRealProdCLM.symm` turns this into `frontier (e.symm '' ins) = range v` whenever
`range v = e.symm '' range γ`. -/
theorem frontier_image_of_open_closure (ins : Set (ℝ × ℝ)) (γ : Circle → ℝ × ℝ) (v : ℝ → ℂ)
    (hinsopen : IsOpen ins) (hcl : closure ins = ins ∪ Set.range γ)
    (hdisj : Disjoint ins (Set.range γ))
    (hrange : Set.range v = Complex.equivRealProdCLM.symm '' Set.range γ) :
    frontier (Complex.equivRealProdCLM.symm '' ins) = Set.range v := by
  -- The frontier of `ins` is exactly `range γ`.
  have hfront : frontier ins = Set.range γ :=
    Work.SubBigon.frontier_eq_of_closure_eq_union hinsopen hcl hdisj
  -- A homeomorphism maps the frontier of a set onto the frontier of its image.
  have himg : frontier (Complex.equivRealProdCLM.symm '' ins)
      = Complex.equivRealProdCLM.symm '' frontier ins := by
    have h := Homeomorph.image_frontier (Complex.equivRealProdCLM.symm.toHomeomorph) ins
    rw [ContinuousLinearEquiv.coe_toHomeomorph] at h
    exact h.symm
  rw [himg, hfront, hrange]

end Work.RPB1a
