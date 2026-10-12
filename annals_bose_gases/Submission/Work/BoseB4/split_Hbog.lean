import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.l2Space
import Submission.Work.BoseB4.HbogR
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.split_Hbog` — the Bogoliubov pair row under the split

The image under `Work.BoseB4.split` of FS `eq:HLambdaSecond`'s Bogoliubov pair
row

    `½(2π)⁻³∫ Ŵ₁(k) (a₀†a₀†a_k a_{−k} + h.c.) dk`

(`Work.BoseB4.Hbog`), namely the anti-normal pair

    `monoOp 0 2 (Kbog1 D) + monoOp 2 0 (Kbog2 D)`

of `Work.BoseB4.K2ndDefs`, with

* `Kbog1 D = Σ_{k≠0} (½Ŵ₁(k)) • (annX k ∘ annX (−k))` (the `a₀†a₀†a_k a_{−k}` half),
* `Kbog2 D = Σ_{k≠0} (½Ŵ₁(k)) • (creX k ∘ creX (−k))` (the `h.c.` half).

The proof is `Work.BoseB4.split_HbogR`, which establishes the identity for the
operator `Work.BoseB4.HbogR` — the body of `Hbog` written with the *real* scalar
`(1 / 2 : ℝ)`.  The definition of `Work.BoseB4.Hbog` carries that same real
scalar, so `Hbog D` and `HbogR D` are definitionally equal and the transport
identity transfers.  (The `(1 / 2 : ℝ)` annotation is essential: an
un-annotated `(1 / 2)` in that position elaborates at `ℕ`, where `1 / 2 = 0`, and
the row collapses to `0`.)

## History

An earlier revision of `Submission/Work/BoseB4/H2nd.lean` defined `Hbog` with the
un-annotated `(1 / 2)`, which is the natural-number `0`; the row was then
identically `0`, the transport identity below was *false* as stated, and a
machine-checked counterexample was produced (the two files recording it were
removed once the definition was repaired).  `H2nd.lean` now carries
`(1 / 2 : ℝ)`.
-/

noncomputable section

open scoped lp BigOperators

namespace Work.BoseB4

set_option autoImplicit false

theorem split_Hbog {m : ℕ} [NeZero m] (D : H2ndData m) (x : RealFock m) :
    split (Hbog D x) = (monoOp 0 2 (Kbog1 D) + monoOp 2 0 (Kbog2 D)) (split x) :=
  split_HbogR D x

end Work.BoseB4
