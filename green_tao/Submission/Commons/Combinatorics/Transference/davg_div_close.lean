import Mathlib
import Submission.Commons.Combinatorics.Transference.davg_smul
import Submission.Commons.Combinatorics.Transference.levelJoin_atom_close

namespace Commons.Combinatorics.Transference

theorem davg_div_close {p : ℕ} [Fact p.Prime] {d : ℕ} {C ε α : ℝ} (hC : 0 < C) (hε : 0 < ε)
    {F : ZMod p → ℝ} {x y : ZMod p}
    (hy : ⌊(davg d (fun z => F z / (2 * C)) y - α) / ε⌋
        = ⌊(davg d (fun z => F z / (2 * C)) x - α) / ε⌋) :
    |davg d F y - davg d F x| ≤ (2 * C) ^ (2 ^ d - 1) * ε := by
  have h2C : (0 : ℝ) < 2 * C := by linarith
  have hne : (2 * C) ≠ 0 := ne_of_gt h2C
  set G : ZMod p → ℝ := fun z => F z / (2 * C) with hG
  have hyG : ⌊(davg d G y - α) / ε⌋ = ⌊(davg d G x - α) / ε⌋ := by
    simpa [hG] using hy
  have hfloor : |davg d G y - davg d G x| < ε := by
    have h := abs_sub_lt_of_floor_div_eq hε hyG
    rwa [show (davg d G y - α) - (davg d G x - α) = davg d G y - davg d G x by ring] at h
  have hsmul := davg_smul (p := p) (d := d) (2 * C) G
  have hfunG : (fun z => 2 * C * G z) = F := by
    funext z
    rw [hG]
    exact mul_div_cancel₀ (F z) hne
  rw [hfunG] at hsmul
  calc |davg d F y - davg d F x|
      = (2 * C) ^ (2 ^ d - 1) * |davg d G y - davg d G x| := by
        rw [congrFun hsmul y, congrFun hsmul x, ← mul_sub, abs_mul,
          abs_of_nonneg (pow_nonneg (le_of_lt h2C) _)]
    _ ≤ (2 * C) ^ (2 ^ d - 1) * ε :=
        mul_le_mul_of_nonneg_left (le_of_lt hfloor) (pow_nonneg (le_of_lt h2C) _)

end Commons.Combinatorics.Transference
