import Mathlib
import Submission.Work.NN.Final.Defs
import Submission.Work.NN.Final.flatTwoCore

namespace Work.NN.Final

/-- The open flat `(0,2)` `∂̄`-Poincaré datum on nested polydiscs exists.

This is the packaging of `Work.NN.Final.flatTwoCore` (the analytic content: a linear potential
operator for `∂̄`-closed antisymmetric `(0,2)`-forms on `pd n ρ 4` solving the equation on
`pd n ρ 2`, with a gain of one derivative in the `C^{k,α}` scale and mapping smooth data to
smooth potentials) into the structure `Work.NN.Final.FlatTwo`. -/
theorem flatTwo {n : ℕ} {α : ℝ} {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j)
    (hα0 : 0 < α) (hα1 : α < 1) :
    Nonempty (Work.NN.Final.FlatTwo n α ρ) := by
  obtain ⟨T2, C2, hC2, hsol, hest, hsm⟩ :=
    Work.NN.Final.flatTwoCore (n := n) (α := α) (ρ := ρ) hρ hα0 hα1
  exact ⟨{ hρ := hρ, hα0 := hα0, hα1 := hα1, C2 := C2, hC2 := hC2, T2 := T2,
           T2_solves := hsol, T2_est := hest, T2_smooth := hsm }⟩

end Work.NN.Final
