import Mathlib
import Submission.Work.Dihedral.Defs
import Submission.Work.FUS.DihedralFacts.rot_involutions

namespace Work.CORE4.DihFourConjAux

/-- In `DihedralGroup n` with `4 ∣ n`, an involution `u` which is neither `1` nor the central
rotation `r (n/2)` (i.e. a reflection) is conjugate to `u * r (n/2)` by a rotation. -/
theorem exists_rot_conj_mul_center (n : ℕ) [NeZero n] (h4 : 4 ∣ n) (u : DihedralGroup n)
    (hu : u ^ 2 = 1) (hu1 : u ≠ 1)
    (hu2 : u ≠ DihedralGroup.r ((n / 2 : ℕ) : ZMod n)) :
    ∃ s ∈ Work.Dihedral.rot n,
      s * u * s⁻¹ = u * DihedralGroup.r ((n / 2 : ℕ) : ZMod n) := by
  -- `4 ∣ n` in particular makes `n` even.
  obtain ⟨c, hc⟩ := h4
  have hEven : Even n := ⟨2 * c, by omega⟩
  -- A rotation of order ≤ 2 is `1` or the central rotation, so `u` must be a reflection.
  have hnotrot : u ∉ Work.Dihedral.rot n := by
    intro hrot
    rcases Work.FUS.DihedralFacts.rot_involutions n hEven u hrot hu with h | h
    · exact hu1 h
    · exact hu2 h
  obtain ⟨i, hi⟩ := Work.Dihedral.notMem_rot.mp hnotrot
  subst hi
  -- Conjugate by the rotation `r (n/4)`.
  refine ⟨DihedralGroup.r ((n / 4 : ℕ) : ZMod n), Work.Dihedral.r_mem_rot _, ?_⟩
  rw [Work.Dihedral.r_conj_sr, DihedralGroup.sr_mul_r]
  congr 1
  have hdiv : 2 * (n / 4) = n / 2 := by omega
  have hcast : (2 : ZMod n) * ((n / 4 : ℕ) : ZMod n) = ((n / 2 : ℕ) : ZMod n) := by
    have : ((2 * (n / 4) : ℕ) : ZMod n) = ((n / 2 : ℕ) : ZMod n) := by rw [hdiv]
    simpa using this
  have hhalf : ((n / 2 : ℕ) : ZMod n) + ((n / 2 : ℕ) : ZMod n) = 0 := by
    rw [← Nat.cast_add, show n / 2 + n / 2 = n by omega, ZMod.natCast_self]
  have hneg : -(((n / 2 : ℕ)) : ZMod n) = ((n / 2 : ℕ) : ZMod n) :=
    (neg_eq_iff_add_eq_zero).mpr hhalf
  rw [sub_eq_add_neg, hcast, hneg]

end Work.CORE4.DihFourConjAux
