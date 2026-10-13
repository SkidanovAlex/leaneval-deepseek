import Mathlib
import Submission.Work.DSM1p.Family
import Submission.Work.DSM1p.Completion.mod_p

/-!
# `mod_p` for the multi-parameter root tower

For any commutative ring `E` and natural number `p`, the level-`1` coordinate projection of the
`p`-adic completion `E^ = AdicCompletion (span {p}) E` is surjective with kernel `(p)`, so the
first isomorphism theorem identifies `E^ ⧸ (p) ≅ E ⧸ (p)`.  This general fact is proved (for an
arbitrary `E`, with no torsion hypothesis) as
`Work.DSM1p.Completion.AdicCompletionModP.adicCompletion_quot_span`.

Here we apply it to `E = FamClosure R p x`, the multi-parameter root closure
`R[x₁^{1/p^∞}, …, x_d^{1/p^∞}]`, whose `p`-adic completion is `FamCompletion R p x`.  The
hypothesis that `p` is a non-zero-divisor of the closure is carried along from the intended use
site (it is not needed for the isomorphism itself).
-/

namespace Work.DSM1p.Family

theorem mod_p (R : Type*) [CommRing R] (p : ℕ) {d : ℕ} (x : Fin d → R)
    (hp : IsSMulRegular (Work.DSM1p.FamClosure R p x) (p : Work.DSM1p.FamClosure R p x)) :
    Nonempty (Work.DSM1p.FamCompletion R p x ⧸
        Ideal.span {(p : Work.DSM1p.FamCompletion R p x)} ≃+*
      Work.DSM1p.FamClosure R p x ⧸
        Ideal.span {(p : Work.DSM1p.FamClosure R p x)}) :=
  Work.DSM1p.Completion.AdicCompletionModP.adicCompletion_quot_span
    (Work.DSM1p.FamClosure R p x) p

end Work.DSM1p.Family
