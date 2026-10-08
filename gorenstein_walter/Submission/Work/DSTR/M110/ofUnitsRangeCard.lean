import Mathlib
import Submission.Work.DSTR.M110.nonsplitAux

set_option linter.style.haveILetI false

namespace Work.DSTR.M110

/-- Over a finite field `F`, the image of the unit group `Fˣ` inside the units of the ring
`F[X]/(f)` (via `AdjoinRoot.of f`) has exactly `|F| - 1` elements, whenever `f` is not a nonzero
constant (so that `AdjoinRoot.of f` is injective). -/
theorem ofUnitsRangeCard (F : Type*) [Field F] [Fintype F] (f : Polynomial F) (hdeg : f.degree ≠ 0) :
    Nat.card ↥((Units.map (AdjoinRoot.of f).toMonoidHom).range) = Nat.card F - 1 := by
  classical
  -- `f.degree ≠ 0` makes `F[X]/(f)` nontrivial, so `F → F[X]/(f)` is injective (`F` being a field).
  haveI : Nontrivial (AdjoinRoot f) := AdjoinRoot.nontrivial f hdeg
  have hinj : Function.Injective (AdjoinRoot.of f) := by
    rw [← AdjoinRoot.algebraMap_eq]
    exact FaithfulSMul.algebraMap_injective F (AdjoinRoot f)
  -- hence `Units.map` is injective too.
  have hinj' : Function.Injective (Units.map (AdjoinRoot.of f).toMonoidHom) :=
    Units.map_injective hinj
  -- the unit group of a finite field has `|F| - 1` elements.
  have hcardU : Nat.card (Units F) = Nat.card F - 1 := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_units]
  -- an injective map is a bijection onto its range, so the range has the source's cardinality.
  have hbij : Nat.card (Units F) =
      Nat.card ↥((Units.map (AdjoinRoot.of f).toMonoidHom).range) :=
    Nat.card_congr (Equiv.ofBijective
      (MonoidHom.rangeRestrict (Units.map (AdjoinRoot.of f).toMonoidHom))
      ⟨fun a b h => hinj' (Subtype.ext_iff.mp h),
       MonoidHom.rangeRestrict_surjective _⟩)
  rw [← hcardU, hbij]

end Work.DSTR.M110
