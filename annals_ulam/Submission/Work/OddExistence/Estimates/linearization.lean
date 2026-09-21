import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Ball
import Submission.Work.OddVolterra.Kernel.Diag
import Submission.Work.OddVolterra.Existence.odd_linearization

/-!
# The linearization of the unperturbed odd Volterra map

The odd-case Volterra equation `(hah44)` is

`Godd n h s (Z s) = ∫_s^1 𝚯 n h s σ (Z σ) dσ + 𝚵 n h s`,

whose unperturbed (`h = 0`) solution is the ball's state `s ↦ baseState s`.  The
paper's Step 2 linearises the equation about that solution; the resulting
linear operator is invertible, and the long-interval fixed point theorem needs
the inverse family `s ↦ (D_Z Godd n 0 s (baseState s))⁻¹` to be *continuous*
and *uniformly bounded* on the slope interval `[a,b]`, `0 < a ≤ b ≤ 1`.

This file repackages the linearization already built in
`Work.OddVolterra.Existence.odd_linearization` -- which computes the derivative
of `z ↦ Godd n 0 s z` at `baseState s` explicitly and inverts it by hand -- as
the estimate-facing statement `Work.OddExistence.Estimates.linearization`.
-/

namespace Work.OddExistence.Estimates

theorem linearization (n : ℕ) (hn : 1 ≤ n) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1) :
    ∃ (A : ℝ → Work.OddVolterra.St ≃L[ℝ] Work.OddVolterra.St) (B : ℝ), 0 < B ∧
      (∀ s ∈ Set.Icc a b, (A s : Work.OddVolterra.St →L[ℝ] Work.OddVolterra.St) =
        fderiv ℝ (fun z => Work.OddVolterra.Godd n 0 s z) (Work.OddVolterra.baseState s)) ∧
      ContinuousOn (fun s => ((A s).symm : Work.OddVolterra.St →L[ℝ] Work.OddVolterra.St))
        (Set.Icc a b) ∧
      (∀ s ∈ Set.Icc a b,
        ‖((A s).symm : Work.OddVolterra.St →L[ℝ] Work.OddVolterra.St)‖ ≤ B) :=
  Work.OddVolterra.Existence.odd_linearization n hn a b ha hab hb

end Work.OddExistence.Estimates
