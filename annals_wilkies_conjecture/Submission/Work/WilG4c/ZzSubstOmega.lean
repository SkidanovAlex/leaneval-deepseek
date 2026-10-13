import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilG0.API
import Submission.Work.WilG0.Subst

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

/-!
# `Ω` is closed under coordinate substitution, in the loose format bound

`Work.WilG0.substSet_mem` (the substitution atom of the `Ω`-formula calculus, i.e. the `mem`
case of `G0_calculus`) realizes `{x : ℝ^n | x ∘ ι ∈ A}` for `A ∈ S.Ω F D m` with the *sharp*
format `max (F + n) (n + m) + 1 + m + n` and the exact degree `D + 2`.  Here we only need the
loose bound `F + 2 * (N + m) + 1`, which is what the callers of this lemma (the `Zz`-layer of
the BNZ §5 argument) quote, so we pad the format with `Omega_mono_F`.

The library lemma is built on the `Work.WilG0` vocabulary (`snocIt`, `projLastIter`, `liftNM`,
`diagSet`): `A` is pushed onto the trailing `m` coordinates by iterating `SOMin.prod_left`,
the equation `w = x ∘ σ` is imposed by the single quadratic hypersurface
`∑_j (Z_{N+j} − Z_{σ j})² = 0` (total degree `2`, the source of `D + 2`), and the `m` fresh
coordinates are eliminated again by iterating `SOMin.proj`.
-/

/-- **`Ω` is closed under coordinate substitution (loose format).**
If `A ⊆ ℝ^m` is `Ω F D m` and `σ : Fin m → Fin N`, then `{x : ℝ^N | x ∘ σ ∈ A}` is
`Ω (F + 2*(N+m) + 1) (D+2) N`: one intersection costs one unit of format, the `N` lifts and
the `m` projections together cost `N + m`, and `2*(N+m) + 1` dominates them all; the diagonal
equation contributes the `+2` in the degree slot and nothing else. -/
theorem ZzSubstOmega (S : WilkiesDesign.SOMin) {m N F D : ℕ} (σ : Fin m → Fin N)
    {A : Set (Fin m → ℝ)} (hA : A ∈ S.Ω F D m) :
    {x : Fin N → ℝ | x ∘ σ ∈ A} ∈ S.Ω (F + 2 * (N + m) + 1) (D + 2) N := by
  have h := Work.WilG0.substSet_mem (S := S) hA N σ
  exact Work.WilG0.Omega_mono_F (S := S) (by omega) h

end Work.WilG4c
