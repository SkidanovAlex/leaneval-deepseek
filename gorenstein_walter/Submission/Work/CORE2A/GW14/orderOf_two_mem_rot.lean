import Mathlib
import Submission.Work.Dihedral.Defs
import Submission.Work.L2F.Dihedral.centralizer_sr_subset

namespace Work.CORE2A.GW14

theorem orderOf_two_mem_rot {n : ℕ} {x : DihedralGroup n}
    (hx : x ∈ Work.Dihedral.rot n) (h2 : orderOf x = 2) :
    x = DihedralGroup.r ((n / 2 : ℕ) : ZMod n) := by
  obtain ⟨i, rfl⟩ := Work.Dihedral.mem_rot.mp hx
  -- `r i ≠ 1` because its order is `2`
  have hne : (DihedralGroup.r i : DihedralGroup n) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at h2
    omega
  -- `(r i)^2 = 1` rewrites to `i + i = 0` in `ZMod n`
  have hii : i + i = 0 := by
    have h1 : (DihedralGroup.r i : DihedralGroup n) ^ 2 = 1 := by
      rw [← h2]; exact pow_orderOf_eq_one _
    rw [pow_two, DihedralGroup.r_mul_r] at h1
    exact DihedralGroup.r.inj (by rw [h1, DihedralGroup.r_zero])
  have hi0 : i ≠ 0 := fun h => hne (by rw [h, DihedralGroup.r_zero])
  -- two-torsion of `ZMod n`, and `i ≠ 0`, so `i = n / 2`
  rcases Work.L2F.Dihedral.zmod_add_self_eq_zero_or_eq_half i hii with h | h
  · exact absurd h hi0
  · rw [h]

end Work.CORE2A.GW14
