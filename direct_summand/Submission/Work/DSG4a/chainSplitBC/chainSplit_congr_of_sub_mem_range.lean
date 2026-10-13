import Mathlib
import Submission.Work.DSG4a.Data

namespace Work.DSG4a.chainSplitBC

open CategoryTheory

set_option backward.isDefEq.respectTransparency false
universe u

theorem chainSplit_congr_of_sub_mem_range {A : Type u} [CommRing A]
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (cc cc' : Work.DSG4a.singleZ A ⟶ P)
    (h : Work.DSG4a.Criterion.coaugElem P cc - Work.DSG4a.Criterion.coaugElem P cc' ∈
      LinearMap.range (P.d (-1) 0).hom) :
    Work.DSG4a.Criterion.ChainSplit P cc ↔ Work.DSG4a.Criterion.ChainSplit P cc' := by
  -- The two coaugmentation elements differ by an element `d y` of the image of the
  -- differential `d⁻¹ : P.X (-1) ⟶ P.X 0`.
  obtain ⟨y, hy⟩ := h
  -- Any functional killing `d⁻¹` takes the same value on the two elements.
  have key : ∀ s : P.X 0 →ₗ[A] A, s.comp (P.d (-1) 0).hom = 0 →
      s (Work.DSG4a.Criterion.coaugElem P cc') = s (Work.DSG4a.Criterion.coaugElem P cc) := by
    intro s hs
    have hd : s ((P.d (-1) 0).hom y) = 0 := by
      rw [← LinearMap.comp_apply, hs, LinearMap.zero_apply]
    have hcc' : Work.DSG4a.Criterion.coaugElem P cc' =
        Work.DSG4a.Criterion.coaugElem P cc - (P.d (-1) 0).hom y := by
      rw [hy]; abel
    rw [hcc', map_sub, hd, sub_zero]
  constructor
  · rintro ⟨s, hs, hs1⟩
    exact ⟨s, hs, by rw [key s hs, hs1]⟩
  · rintro ⟨s, hs, hs1⟩
    exact ⟨s, hs, by rw [← key s hs, hs1]⟩

end Work.DSG4a.chainSplitBC
