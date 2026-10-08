import Mathlib
import Submission.Work.Dihedral.Defs

namespace Work.CORE2A.GW14

/-- For `4 ∣ n`, conjugation by the rotation `r (n/4)` (of order 2) sends the reflection
`sr i` to the other element of its `⟨r (n/2)⟩`-coset among the reflections:
`r (n/4) * sr i * (r (n/4))⁻¹ = r (n/2) * sr i`.

Indeed `r t * sr i * (r t)⁻¹ = sr (i - 2 * t)` (`Work.Dihedral.r_conj_sr`) and
`r (n/2) * sr i = sr (i - n/2)` (`DihedralGroup.r_mul_sr`); since `4 ∣ n` we have
`2 * (n/4) = n/2` in `ZMod n`. -/
theorem conj_sr_r_half (n : ℕ) (h4 : 4 ∣ n) (i : ZMod n) :
    ∃ w : DihedralGroup n, w * DihedralGroup.sr i * w⁻¹ =
      DihedralGroup.r ((n / 2 : ℕ) : ZMod n) * DihedralGroup.sr i := by
  obtain ⟨k, rfl⟩ := h4
  refine ⟨DihedralGroup.r ((k : ℕ) : ZMod (4 * k)), ?_⟩
  rw [Work.Dihedral.r_conj_sr, DihedralGroup.r_mul_sr]
  have hk : (4 * k) / 2 = 2 * k := by omega
  rw [hk]
  congr 1
  push_cast
  ring

end Work.CORE2A.GW14
