import Mathlib
import Submission.Work.DSM1p.Family
import Submission.Work.DSM1p.Completion.torsionFree

/-!
# `p`-torsion-freeness passes to the `p`-adic completion (multi-parameter case)

This is the `d`-parameter analogue of `Work.DSM1p.Completion.torsionFree`: if `p` is a
non-zero-divisor of the root closure `A_∞ = R[x₁^{1/p^∞}, …, x_d^{1/p^∞}]`, then it is a
non-zero-divisor of its `p`-adic completion `A′ = (A_∞)^{^}` (`Work.DSM1p.FamCompletion`).

Concretely it is the general statement `Work.DSM1p.Completion.isSMulRegular_adicCompletion`
(if `s` is a non-zero-divisor of `S` then `s` is a non-zero-divisor of the `(s)`-adic
completion of `S`) applied to `S = Work.DSM1p.FamClosure R p x` and `s = p`, together with
the elementary identification of the `S`-scalar action with the self-action of the completion.
-/

namespace Work.DSM1p.Family

theorem torsionFree_completion (R : Type*) [CommRing R] (p : ℕ) {d : ℕ} (x : Fin d → R)
    (hp : IsSMulRegular (Work.DSM1p.FamClosure R p x) (p : Work.DSM1p.FamClosure R p x)) :
    IsSMulRegular (Work.DSM1p.FamCompletion R p x) (p : Work.DSM1p.FamCompletion R p x) := by
  have hgen := Work.DSM1p.Completion.isSMulRegular_adicCompletion
    (Work.DSM1p.FamClosure R p x) (p : Work.DSM1p.FamClosure R p x) hp
  have hsmul : ∀ y : Work.DSM1p.FamCompletion R p x,
      (p : Work.DSM1p.FamCompletion R p x) • y
        = (p : Work.DSM1p.FamClosure R p x) • y := by
    intro y
    rw [Algebra.smul_def]
    congr 1
  have hfun : (fun y : Work.DSM1p.FamCompletion R p x =>
        (p : Work.DSM1p.FamCompletion R p x) • y)
      = fun y : Work.DSM1p.FamCompletion R p x =>
          (p : Work.DSM1p.FamClosure R p x) • y := funext hsmul
  rw [IsSMulRegular, hfun]
  exact hgen

end Work.DSM1p.Family
