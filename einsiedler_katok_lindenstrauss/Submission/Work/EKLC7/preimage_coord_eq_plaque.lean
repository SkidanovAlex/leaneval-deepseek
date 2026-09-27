import Mathlib
import Submission.Work.EKLC7.OrbitCoord

namespace Work.EKLC7

/-- If `coord x ·` is a section of the orbit map `u ↦ u • x` over the `U`-orbit of `x`
(and the action of `U` at `x` is free), then pulling back a set `D` of group elements
along `coord x` and intersecting with the orbit is the same as taking the orbit of
`D ∩ U`. -/
theorem preimage_coord_eq_plaque {U : Subgroup Work.EKLContract.SL3} {x : Work.EKLContract.X3}
    (hfree : ∀ u₁ ∈ U, ∀ u₂ ∈ U, u₁ • x = u₂ • x → u₁ = u₂)
    (coord : Work.EKLContract.X3 → Work.EKLContract.X3 → Work.EKLContract.SL3)
    (hcoord : ∀ y, y ∈ (fun u : Work.EKLContract.SL3 => u • x) '' (U : Set Work.EKLContract.SL3) →
      coord x y ∈ U ∧ coord x y • x = y)
    {D : Set Work.EKLContract.SL3} :
    {y : Work.EKLContract.X3 | coord x y ∈ D}
        ∩ (fun u : Work.EKLContract.SL3 => u • x) '' (U : Set Work.EKLContract.SL3)
      = (fun u : Work.EKLContract.SL3 => u • x) '' (D ∩ (U : Set Work.EKLContract.SL3)) := by
  ext y
  constructor
  · rintro ⟨hyD, u, hu, rfl⟩
    have himg : u • x ∈ (fun u : Work.EKLContract.SL3 => u • x) ''
        (U : Set Work.EKLContract.SL3) := ⟨u, hu, rfl⟩
    exact ⟨coord x (u • x), ⟨hyD, (hcoord (u • x) himg).1⟩, (hcoord (u • x) himg).2⟩
  · rintro ⟨v, ⟨hvD, hvU⟩, rfl⟩
    have himg : v • x ∈ (fun u : Work.EKLContract.SL3 => u • x) ''
        (U : Set Work.EKLContract.SL3) := ⟨v, hvU, rfl⟩
    have h1 := hcoord (v • x) himg
    refine ⟨?_, v, hvU, rfl⟩
    change coord x (v • x) ∈ D
    rw [hfree (coord x (v • x)) h1.1 v hvU h1.2]
    exact hvD

end Work.EKLC7
