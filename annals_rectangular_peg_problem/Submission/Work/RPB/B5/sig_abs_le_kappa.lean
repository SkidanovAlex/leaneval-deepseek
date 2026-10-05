import Mathlib
import Submission.Work.RPB.B5.RhoPerDefs

namespace Work.RPB.B5

theorem sig_abs_le_kappa {κ δA x : ℝ} (hκ : 0 < κ) (h4 : Real.sqrt 2 * δA ≤ κ / 4)
    (hx : x ∈ Set.Ioc (-Real.sqrt 2) 0) (hxc : x + Real.sqrt 2 ≤ δA) :
    |Work.RPB.B5.sig x| ≤ κ / 4 := by
  have h2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h2sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [Set.mem_Ioc] at hx
  obtain ⟨hxlo, hxhi⟩ := hx
  have hu0 : 0 ≤ Real.sqrt 2 + x := by linarith
  have hu0' : Real.sqrt 2 + x ≤ δA := by linarith
  -- `x² ≤ 2`
  have hx2le : x ^ 2 ≤ 2 := by
    have h1 : |x| ≤ |Real.sqrt 2| := by
      rw [abs_of_nonneg (le_of_lt h2pos), abs_le]
      exact ⟨by linarith, by linarith⟩
    have h2 : x ^ 2 ≤ Real.sqrt 2 ^ 2 := (sq_le_sq).mpr h1
    rwa [h2sq] at h2
  -- `|sig x| = (2 - x²)/2`
  have habs : |Work.RPB.B5.sig x| = (2 - x ^ 2) / 2 := by
    have hle : Work.RPB.B5.sig x ≤ 0 := by
      unfold Work.RPB.B5.sig; linarith
    rw [abs_of_nonpos hle]
    unfold Work.RPB.B5.sig
    ring
  rw [habs]
  -- `2 - x² = (√2 - x)(√2 + x) ≤ 2√2 · δA`
  have hfact : 2 - x ^ 2 = (Real.sqrt 2 - x) * (Real.sqrt 2 + x) := by nlinarith [h2sq]
  have hb1 : Real.sqrt 2 - x ≤ 2 * Real.sqrt 2 := by linarith
  have hprod : 2 - x ^ 2 ≤ 2 * Real.sqrt 2 * δA := by
    rw [hfact]
    calc (Real.sqrt 2 - x) * (Real.sqrt 2 + x)
        ≤ (2 * Real.sqrt 2) * (Real.sqrt 2 + x) :=
          mul_le_mul_of_nonneg_right hb1 hu0
      _ ≤ (2 * Real.sqrt 2) * δA :=
          mul_le_mul_of_nonneg_left hu0'
            (mul_nonneg (by norm_num) (le_of_lt h2pos))
  linarith

end Work.RPB.B5
