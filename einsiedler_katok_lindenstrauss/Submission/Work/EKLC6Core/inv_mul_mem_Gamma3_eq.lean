import Mathlib
import Submission.Work.EKLC6Core.uniform_injective_V_X3
import Submission.Work.EKLComp.inv_mem_V
import Submission.Work.EKLRelCross.flower_balls

namespace Work.EKLC6Core

/-- If `h ∈ V (2ρ)` and `b ∈ V (ρ/2)` with `0 < ρ ≤ 1/100`, then `h⁻¹ * b ∈ V (1/2)`.

Indeed `h⁻¹ ∈ V (10 * (2ρ))` (`Work.EKLComp.inv_mem_V`), and the entrywise product estimate
`Work.EKLRelCross.entries_mul_sub_one_le` gives, for every entry,
`|(h⁻¹ * b) i j - 1 i j| < 10·(2ρ) + ρ/2 + 3·(10·(2ρ))·(ρ/2) = 20.5 ρ + 30 ρ²`,
which is `≤ 1/2` because `ρ ≤ 1/100`. -/
theorem inv_mul_mem_V_half_of_mem_V {ρ : ℝ} (hρ : 0 < ρ) (hρ' : ρ ≤ 1/100)
    {h b : Work.EKLContract.SL3} (hh : h ∈ Work.EKLContract.V (2 * ρ))
    (hb : b ∈ Work.EKLContract.V (ρ / 2)) : h⁻¹ * b ∈ Work.EKLContract.V ((1:ℝ)/2) := by
  have h2ρpos : 0 < 2 * ρ := by linarith
  have h2ρ1 : 2 * ρ ≤ 1 := by linarith
  have hhinv : h⁻¹ ∈ Work.EKLContract.V (10 * (2 * ρ)) :=
    Work.EKLComp.inv_mem_V h2ρpos h2ρ1 hh
  intro i j
  have hbound := Work.EKLRelCross.entries_mul_sub_one_le
    (A := ((h⁻¹ : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ))
    (B := ((b : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ)) i j
    (fun k l => hhinv k l) (fun k l => hb k l)
    (by linarith) (by linarith)
  rw [← Matrix.SpecialLinearGroup.coe_mul] at hbound
  have harith : 10 * (2 * ρ) + ρ / 2 + 3 * (10 * (2 * ρ)) * (ρ / 2) ≤ (1:ℝ)/2 := by
    nlinarith [hρ, hρ']
  linarith [hbound, harith]

theorem inv_mul_mem_Gamma3_eq {ρ : ℝ} (hρ : 0 < ρ) (hρ' : ρ ≤ 1/100) {h b : Work.EKLContract.SL3}
    (hh : h ∈ Work.EKLContract.V (2 * ρ)) (hb : b ∈ Work.EKLContract.V (ρ / 2))
    (hγ : h⁻¹ * b ∈ Work.EKLContract.Γ3) : h = b := by
  have hkey : h⁻¹ * b ∈ Work.EKLContract.V ((1:ℝ)/2) :=
    inv_mul_mem_V_half_of_mem_V hρ hρ' hh hb
  have h1 : h⁻¹ * b = 1 := eq_one_of_mem_Γ3_mem_V_half _ hγ hkey
  exact (mul_left_cancel (by rw [h1, inv_mul_cancel])).symm

end Work.EKLC6Core
