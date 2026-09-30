import Mathlib
import Submission.Work.BW.subgroup_rayDegAux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- The box of `boxPts` is exactly the product of integer intervals `∏ᵢ [0, mᵢ]`. -/
theorem boxPts_eq_Icc (N : ℕ) (m : Fin N → ℕ) :
    boxPts N m = Finset.Icc (0 : Fin N → ℤ) (fun i => (m i : ℤ)) := by
  ext b
  rw [boxPts, Finset.mem_image, Pi.Icc_eq, Fintype.mem_piFinset]
  constructor
  · rintro ⟨c, hc, rfl⟩ i
    rw [Finset.mem_Icc]
    have hci := Finset.mem_pi.mp hc i (Finset.mem_univ i)
    rw [Finset.mem_range] at hci
    exact ⟨Int.natCast_nonneg _, Int.ofNat_le.mpr (Nat.le_of_lt_succ hci)⟩
  · intro h
    refine ⟨fun i _ => (b i).toNat, ?_, ?_⟩
    · rw [Finset.mem_pi]
      intro i _
      rw [Finset.mem_range, Nat.lt_succ_iff, Int.toNat_le]
      exact (Finset.mem_Icc.mp (h i)).2
    · funext i
      exact Int.toNat_of_nonneg (Finset.mem_Icc.mp (h i)).1

end Work.BW
