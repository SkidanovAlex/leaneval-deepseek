import Mathlib
import Submission.Work.Dihedral.Defs
import Submission.Work.FUS.DihedralFacts.zmod_two_mul_eq_zero

namespace Work.FUS.DihedralFacts

/-- In `DihedralGroup n` with `n` even, the only involutions inside the rotation subgroup
`⟨r⟩` are the identity and the "central" rotation `r (n/2)`. Equivalently, the 2-torsion of the
cyclic group `⟨r⟩ ≅ ZMod n` is `{0, n/2}`. -/
theorem rot_involutions (n : ℕ) [NeZero n] (h2 : Even n) (x : DihedralGroup n)
    (hx : x ∈ Work.Dihedral.rot n) (hx2 : x ^ 2 = 1) :
    x = 1 ∨ x = DihedralGroup.r ((n / 2 : ℕ) : ZMod n) := by
  obtain ⟨i, rfl⟩ := Work.Dihedral.mem_rot.mp hx
  -- The hypothesis `x ^ 2 = 1` reads `r (i * 2) = r 0`, i.e. `2 * i = 0` in `ZMod n`.
  have h2i : 2 * i = 0 := by
    have h : (DihedralGroup.r i : DihedralGroup n) ^ 2 = DihedralGroup.r 0 := by
      rw [hx2, DihedralGroup.r_zero]
    rw [DihedralGroup.r_pow] at h
    have h' : i * 2 = 0 := DihedralGroup.r.inj h
    simpa [mul_comm] using h'
  rcases zmod_two_mul_eq_zero n h2 i h2i with h | h
  · exact Or.inl (by rw [h, DihedralGroup.r_zero])
  · exact Or.inr (by rw [h])

end Work.FUS.DihedralFacts
