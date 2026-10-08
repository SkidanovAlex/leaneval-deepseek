import Mathlib

namespace Work.DSTR.DihHelp

theorem dih_sr_conj_rot {n : ℕ} (u : ZMod n) {x : DihedralGroup n}
    (hx : ∃ t : ZMod n, x = DihedralGroup.r t) :
    (DihedralGroup.sr u * x = x⁻¹ * DihedralGroup.sr u) ∧
      (x * DihedralGroup.sr u = DihedralGroup.sr u * x⁻¹) := by
  obtain ⟨t, rfl⟩ := hx
  constructor
  · rw [DihedralGroup.sr_mul_r, DihedralGroup.inv_r, DihedralGroup.r_mul_sr]
    congr 1
    ring
  · rw [DihedralGroup.r_mul_sr, DihedralGroup.inv_r, DihedralGroup.sr_mul_r]
    congr 1
    ring

end Work.DSTR.DihHelp
