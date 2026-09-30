import Mathlib
import Submission.Work.Milnor.UnitSphere

/-!
# `Mk k` is homeomorphic to the image of the inclusion `Mk k → Vk k`

The inclusion `mkToVkFun k : Mk k → Vk k` (`Submission.Work.Milnor.mk_to_vk`) is a continuous
injection (`continuous_mkToVkFun`, `mkToVkFun_injective`) whose image is the unit sphere bundle
`{fibreNormFun k = 1}` (`mem_range_mkToVkFun_iff`).  Here we upgrade this to a homeomorphism
onto the range, with the explicit inverse `unitInv k` (`Submission.Work.Milnor.UnitSphere`),
whose continuity is `continuous_unitInv k`.
-/

namespace Work.Milnor

open Set

noncomputable section

/-- The injection `mkToVkFun k` viewed as a map onto its range. -/
def mkToVkRange (k : ℤ) : Submission.Milnor.Mk k → ↥(Set.range (mkToVkFun k)) :=
  fun z => ⟨mkToVkFun k z, ⟨z, rfl⟩⟩

/-- The inverse map from the range of `mkToVkFun k` back to `Mk k`, obtained by normalising the
fibre coordinate (`unitInv k`). -/
def vkRangeToMk (k : ℤ) : ↥(Set.range (mkToVkFun k)) → Submission.Milnor.Mk k :=
  fun p => unitInv k ⟨p.1, (mem_range_mkToVkFun_iff k p.1).mp p.2⟩

theorem continuous_mkToVkRange (k : ℤ) : Continuous (mkToVkRange k) :=
  Continuous.subtype_mk (continuous_mkToVkFun k) (fun z => ⟨z, rfl⟩)

theorem continuous_vkRangeToMk (k : ℤ) : Continuous (vkRangeToMk k) := by
  refine (continuous_unitInv k).comp ?_
  exact Continuous.subtype_mk continuous_subtype_val
    (fun p => (mem_range_mkToVkFun_iff k p.1).mp p.2)

theorem vkRangeToMk_mkToVkRange (k : ℤ) (z : Submission.Milnor.Mk k) :
    vkRangeToMk k (mkToVkRange k z) = z := by
  apply mkToVkFun_injective k
  show mkToVkFun k (unitInv k ⟨mkToVkFun k z, _⟩) = mkToVkFun k z
  rw [mkToVkFun_unitInv]

theorem mkToVkRange_vkRangeToMk (k : ℤ) (p : ↥(Set.range (mkToVkFun k))) :
    mkToVkRange k (vkRangeToMk k p) = p := by
  apply Subtype.ext
  show mkToVkFun k (unitInv k ⟨p.1, _⟩) = p.1
  rw [mkToVkFun_unitInv]

/-- **`Mk k` is homeomorphic to the image of `mkToVkFun k`.** -/
theorem mkToVkRangeHomeomorph (k : ℤ) :
    Nonempty (Submission.Milnor.Mk k ≃ₜ ↥(Set.range (Work.Milnor.mkToVkFun k))) :=
  ⟨Homeomorph.mk
    { toFun := mkToVkRange k
      invFun := vkRangeToMk k
      left_inv := vkRangeToMk_mkToVkRange k
      right_inv := mkToVkRange_vkRangeToMk k }
    (continuous_mkToVkRange k) (continuous_vkRangeToMk k)⟩

end

end Work.Milnor
