import Mathlib
import Submission.Work.EKLComp.LeafDefs

/-!
# The atom of a pullback σ-algebra

`Work.EKLContract.atom (MeasurableSpace.comap f m) x` is the preimage under `f` of the atom
`Work.EKLContract.atom m (f x)`.

This is a formal consequence of the way Mathlib *defines* `MeasurableSpace.comap f m`: a set is
comap-measurable exactly when it is the preimage of an `m`-measurable set
(`MeasurableSpace.measurableSet_comap`, `Iff.rfl`).  Hence the comap-measurable sets containing
`x` are exactly the preimages of the `m`-measurable sets containing `f x`, and intersecting gives
the claim.  In particular no hypothesis whatsoever on `f` is needed (not even measurability).
-/

open scoped MeasureTheory

namespace Work.EKLComp

open Work.EKLContract

/-- The atom of `MeasurableSpace.comap f m` at `x` is the preimage under `f` of the atom of `m`
at `f x`. -/
theorem atom_comap (f : Work.EKLContract.X3 → Work.EKLContract.X3)
    (m : MeasurableSpace Work.EKLContract.X3) (x : Work.EKLContract.X3) :
    Work.EKLContract.atom (MeasurableSpace.comap f m) x = f ⁻¹' Work.EKLContract.atom m (f x) := by
  ext y
  rw [Set.mem_preimage]
  constructor
  · -- `y ∈ [x]_{comap f m}`: every `m`-measurable `t ∋ f x` has `f ⁻¹' t` comap-measurable
    -- and containing `x`, so `y ∈ f ⁻¹' t`, i.e. `f y ∈ t`.
    intro hy
    rw [Work.EKLContract.atom, Set.mem_sInter] at hy
    rw [Work.EKLContract.atom, Set.mem_sInter]
    intro t ht
    exact hy (f ⁻¹' t) ⟨(MeasurableSpace.measurableSet_comap).mpr ⟨t, ht.1, rfl⟩, ht.2⟩
  · -- Conversely a comap-measurable `s ∋ x` is `f ⁻¹' t` for some `m`-measurable `t ∋ f x`, and
    -- `f y ∈ [f x]_m ⊆ t` gives `y ∈ s`.
    intro hy
    rw [Work.EKLContract.atom, Set.mem_sInter] at hy
    rw [Work.EKLContract.atom, Set.mem_sInter]
    intro s hs
    obtain ⟨t, ht, rfl⟩ := (MeasurableSpace.measurableSet_comap).mp hs.1
    exact hy t ⟨ht, hs.2⟩

end Work.EKLComp
