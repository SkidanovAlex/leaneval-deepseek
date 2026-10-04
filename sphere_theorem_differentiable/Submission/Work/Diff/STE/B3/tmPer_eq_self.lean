import Mathlib
import Submission.Work.Diff.STE.B3.transport_tame_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3

theorem tmPer_eq_self {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hsupp : Function.support f ⊆
      Set.pi Set.univ (fun _ : Fin n => Set.Ioo (-(1/2) : ℝ) (1/2)))
    {z : Fin n → ℝ} (hz : ∀ i, z i ∈ Set.Ioo (-(1/2) : ℝ) (1/2)) :
    Work.Diff.STE.B3.tmPer f z = f z := by
  have hsupp' : Function.support (fun w : Fin n → ℝ => ((f w : ℝ) : ℂ)) ⊆
      Set.pi Set.univ (fun _ : Fin n => Set.Ioo (-(1/2) : ℝ) (1/2)) := by
    intro w hw
    refine hsupp ?_
    rw [Function.mem_support] at hw ⊢
    intro h
    exact hw (by simp [h])
  have h := Work.Diff.STE.periodization_eq_self (ι := Fin n) hsupp' hz
  show (∑' m : Fin n → ℤ, ((f (z + Work.Diff.STE.iVec m) : ℝ) : ℂ)).re = f z
  rw [h, Complex.ofReal_re]

end Work.Diff.STE.B3
