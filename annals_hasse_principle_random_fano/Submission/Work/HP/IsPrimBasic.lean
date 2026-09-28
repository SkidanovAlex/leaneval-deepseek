import Mathlib
import Submission.Work.HP.Defs

/-! Shared basic fact about primitive vectors (lead, 09-28 assembly clash fix: one public copy of
`Work.HP.IsPrim.ne_zero` for every consumer, instead of three incompatible local copies). -/

namespace Work.HP

/-- A primitive integer vector is nonzero: the gcd of the all-zero vector is `0 ≠ 1`. -/
lemma IsPrim.ne_zero {ι : Type*} [Fintype ι] {a : ι → ℤ} (ha : IsPrim a) : a ≠ 0 := by
  intro hzero
  have h1 := ha
  rw [hzero] at h1
  simp only [IsPrim] at h1
  have hz : Finset.univ.gcd (0 : ι → ℤ) = 0 := Finset.gcd_eq_zero_iff.mpr (by simp)
  rw [hz] at h1
  exact zero_ne_one h1

end Work.HP
