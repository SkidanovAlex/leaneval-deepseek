import Mathlib
import Submission.Work.IntLib.Basic

namespace Work.IntLib

/-- A canonical bit list (no leading zeros) is recovered by `ofBits` followed by `Nat.bits`. -/
theorem bits_ofBits_of_isBits (xs : List Bool) (h : Work.IntLib.IsBits xs) : (Work.IntLib.ofBits xs).bits = xs := by
  have key : (ofBits xs).bits.map Bool.toNat = xs.map Bool.toNat := by
    rw [bits_map_toNat, ofBits_eq_ofDigits]
    refine Nat.digits_ofDigits 2 (by norm_num) _ (fun l hl => ?_) (fun hne => ?_)
    · rcases List.mem_map.mp hl with ⟨b, _, rfl⟩
      cases b <;> decide
    · have hxs : xs ≠ [] := fun h' => hne (by simp [h'])
      have hlast : xs.getLast? = some true := by
        rcases h with hnil | hg
        · exact absurd hnil hxs
        · exact hg
      have hgl : (xs.map Bool.toNat).getLast hne = 1 := by
        rw [List.getLast_eq_iff_getLast?_eq_some hne, List.getLast?_map, hlast]
        rfl
      rw [hgl]
      decide
  exact List.map_injective_iff.mpr (by decide) key

end Work.IntLib
