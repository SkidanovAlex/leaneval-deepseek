import Mathlib
import Submission.Work.EKLC6Core.mul_inv_mem_V_of_entrywise_close
import Submission.Work.EKLC6Core.abs_sub_lt_of_floor_div_eq
import Submission.Work.Misiurewicz.vMove_lt_iff

namespace Work.EKLC6Core

/-- Two group elements whose matrix entries have the same floors after division by `η > 0`
differ entrywise by less than `η`.  Combined with `u ∈ V r ⊆ {|· - 1| ≤ 1}` (`r ≤ 1/4`) this
puts `u' * u⁻¹` in `V (24 η)`, and hence in `V sep` when `24 η < sep`. -/
theorem mul_inv_mem_V_of_floor_eq {r η sep : ℝ} (hr : r ≤ 1 / 4) (hη : 0 < η) (h24 : 24 * η < sep)
    {u u' : Work.EKLContract.SL3} (hu : u ∈ Work.EKLContract.V r)
    (hfloor : ∀ i j, ⌊((u : Matrix (Fin 3) (Fin 3) ℝ) i j) / η⌋
      = ⌊((u' : Matrix (Fin 3) (Fin 3) ℝ) i j) / η⌋) :
    u' * u⁻¹ ∈ Work.EKLContract.V sep := by
  -- `u ∈ V r` with `r ≤ 1/4` gives `|u_{ij} - 1_{ij}| ≤ 1`, the box hypothesis needed below.
  have hw : ∀ i j : Fin 3,
      |(u : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1 := by
    intro i j
    have h1 : |(u : Matrix (Fin 3) (Fin 3) ℝ) i j
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < r := hu i j
    linarith
  -- Same floors for `u` and `u'` give entrywise `< η` proximity.
  have hclose : ∀ i j : Fin 3,
      |(u' : Matrix (Fin 3) (Fin 3) ℝ) i j - (u : Matrix (Fin 3) (Fin 3) ℝ) i j| < η := by
    intro i j
    rw [abs_sub_comm]
    exact abs_sub_lt_of_floor_div_eq hη (hfloor i j)
  exact Work.Misiurewicz.V_mono (le_of_lt h24)
    (mul_inv_mem_V_of_entrywise_close u' u hw hη hclose)

end Work.EKLC6Core
