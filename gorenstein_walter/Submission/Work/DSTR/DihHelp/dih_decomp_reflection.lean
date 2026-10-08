import Mathlib

namespace Work.DSTR.DihHelp

theorem dih_decomp_reflection {n : ℕ} {H : Subgroup (DihedralGroup n)} {u : ZMod n}
    (hs : (DihedralGroup.sr u : DihedralGroup n) ∈ H) {x : DihedralGroup n} (hx : x ∈ H) :
    (∃ k : ZMod n, x = DihedralGroup.r k) ∨
      (∃ k : ZMod n, x = DihedralGroup.r k * DihedralGroup.sr u ∧ DihedralGroup.r k ∈ H) := by
  rcases x with i | i
  · exact Or.inl ⟨i, rfl⟩
  · refine Or.inr ⟨u - i, ?_, ?_⟩
    · rw [DihedralGroup.r_mul_sr, DihedralGroup.sr.injEq]
      ring
    · have hmul : DihedralGroup.r (u - i) = DihedralGroup.sr i * DihedralGroup.sr u := by
        rw [DihedralGroup.sr_mul_sr]
      rw [hmul]
      exact H.mul_mem hx hs

end Work.DSTR.DihHelp
