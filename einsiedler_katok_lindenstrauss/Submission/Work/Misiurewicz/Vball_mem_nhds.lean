import Mathlib
import Submission.Work.EKLComp.Misiurewicz.Defs
import Submission.Work.EKLNonExc.VFacts

namespace Work.Misiurewicz

open Work.EKLContract

/-- The translate `V δ • z` of a point `z ∈ X₃` is a neighbourhood of `z`: `V δ` is an open
neighbourhood of the identity (`V_open_one`), and the orbit map `g ↦ g • z` is an open map,
since it factors as right multiplication by a representative (a homeomorphism of `SL₃(ℝ)`)
followed by the open quotient map `mkX : SL₃(ℝ) → X₃` (`orbitImage_isOpen` in `EKLNonExc`). -/
theorem Vball_mem_nhds (δ : ℝ) (hδ : 0 < δ) (z : Work.EKLContract.X3) : Work.EKLComp.Vball δ z ∈ nhds z := by
  have hopen : IsOpen {y : Work.EKLContract.X3 | ∃ g ∈ V δ, y = g • z} :=
    Work.EKLNonExc.orbitImage_isOpen z δ hδ
  have hz : z ∈ {y : Work.EKLContract.X3 | ∃ g ∈ V δ, y = g • z} :=
    ⟨1, (Work.EKLContract.Lemmas.V_open_one δ hδ).2, (one_smul _ z).symm⟩
  refine Filter.mem_of_superset (hopen.mem_nhds hz) ?_
  rintro y ⟨g, hg, rfl⟩
  exact Work.EKLComp.mem_Vball.mpr ⟨g, hg, rfl⟩

end Work.Misiurewicz
