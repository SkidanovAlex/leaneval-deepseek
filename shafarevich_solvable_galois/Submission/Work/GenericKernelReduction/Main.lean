/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The reduction of Theorem 14 to the generic-kernel hypothesis

A. Schmidt and K. Wingberg, *Šafarevič's theorem on solvable groups as Galois groups*,
arXiv:math/9809211, §5:

> **Theorem 14.** Let `K/k` be a finite Galois extension of the global field `k` and let
> `φ : G_k ↠ G(K/k) = G`.  Then every split embedding problem
> `1 → H → G ⋊ H → G → 1` over `G_k` with finite nilpotent kernel `H` has a proper solution.
>
> Since a finite nilpotent group is the direct product of its `p`-Sylow subgroups and since every
> finite `G`-operator `p`-group is a quotient of `F^(n) = F^(n)(ν)` for some `n, ν`, it suffices
> to show the following assertion: for every prime number `p`, all `n ∈ ℕ` and all `ν` the split
> embedding problem `1 → F^(n)/F^(n)(ν) → F^(n)/F^(n)(ν) ⋊ G → G → 1` over `k` has a proper
> solution.

This file carries out that reduction over the base field `ℚ` with the generic-kernel hypothesis
`Work.GenericKernelReduction.GenericKernelSolvable` as the only input:

* `genericKernelSolvableInClosure`: the hypothesis in the closure form used by the argument
  (a solution of an embedding problem over `ℚ` can be realised inside `AlgebraicClosure ℚ`);
* `splitEmbeddingTheoremOverRat_of_genericKernel`: **`GenericKernelSolvable →
  Submission.SplitEmbeddingTheoremOverRat`** (Theorem 14 of Schmidt–Wingberg over `ℚ`);
* `realizable_of_genericKernel`: composing with Ore's reduction
  (`Submission.realizable_of_solvable_of_split` from `Submission/ClassicalRoute.lean`), the
  generic-kernel hypothesis implies that every finite solvable group is a Galois group over `ℚ`;
* `minimalNormalKernelStep_of_genericKernel`: the same hypothesis implies the single deep input
  `Submission.MinimalNormalKernelStep` of the development.
-/

import Submission.Work.GenericKernelReduction.Defs
import Submission.Work.GenericKernelReduction.Transport
import Submission.Work.GenericKernelReduction.SinglePrime
import Submission.Work.GenericKernelReduction.Nilpotent
import Submission.Work.GenericKernelReduction.inClosure_of_splitEmbeddingSolvable
import Submission.ClassicalRoute
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.GenericKernelReduction

open scoped Classical

/-- The generic-kernel hypothesis implies its closure form: a proper solution of an embedding
problem over `ℚ` can be realised inside the fixed algebraic closure `AlgebraicClosure ℚ`
(`Work.GenericKernelReduction.inClosure_of_splitEmbeddingSolvable`). -/
theorem genericKernelSolvableInClosure_of_genericKernel (h : GenericKernelSolvable) :
    GenericKernelSolvableInClosure :=
  fun L _ _ p _ n ν ρ Φ hdesc => inClosure_of_splitEmbeddingSolvable (h L p n ν ρ Φ hdesc)

/-- The closure form of the hypothesis implies the primary form (forget that the solution lies in
`AlgebraicClosure ℚ`), so the two forms of `Work.GenericKernelReduction.GenericKernelSolvable`
are equivalent. -/
theorem genericKernelSolvable_of_inClosure (h : GenericKernelSolvableInClosure) :
    GenericKernelSolvable :=
  fun L _ _ p _ n ν ρ Φ hdesc => splitEmbeddingSolvable_of_inClosure (h L p n ν ρ Φ hdesc)

/-- **Reduction of Theorem 14 of Schmidt–Wingberg (over `ℚ`) to the generic-kernel
hypothesis.**  If for every finite Galois `L/ℚ`, every prime `p`, all `n, ν` and every action of
`Gal(L/ℚ)` on `F^(n) = FreeGroup (Fin n)` whose descent to `F^(n)/F^(n)(ν)` is `Φ`, the split
embedding problem with kernel `F^(n)/F^(n)(ν)` and quotient `Gal(L/ℚ)` has a proper solution,
then every split embedding problem over `ℚ` with finite nilpotent kernel has a proper solution. -/
theorem splitEmbeddingTheoremOverRat_of_genericKernel (h : GenericKernelSolvable) :
    Submission.SplitEmbeddingTheoremOverRat := by
  intro L _ _ N _ _ hN φ
  exact splitEmbeddingSolvable_of_inClosure
    (splitEmbeddingSolvedInClosure_of_genericKernel_nilpotent
      (genericKernelSolvableInClosure_of_genericKernel h) L N hN φ)

/-- **Shafarevich's theorem from the generic-kernel hypothesis**: every finite solvable group is
the Galois group of a finite Galois extension of `ℚ`.  This is Ore's reduction
(`Submission.realizable_of_solvable_of_split`) applied to
`splitEmbeddingTheoremOverRat_of_genericKernel`. -/
theorem realizable_of_genericKernel (h : GenericKernelSolvable) :
    ∀ (G : Type) [Group G] [Finite G] [Group.IsSolvable G], Submission.RealizableOver ℚ G :=
  Submission.realizable_of_solvable_of_split (splitEmbeddingTheoremOverRat_of_genericKernel h)

/-- The generic-kernel hypothesis implies the single deep input of the development,
`Submission.MinimalNormalKernelStep`. -/
theorem minimalNormalKernelStep_of_genericKernel (h : GenericKernelSolvable) :
    Submission.MinimalNormalKernelStep.{0} :=
  Submission.minimalNormalKernelStep_of_split (splitEmbeddingTheoremOverRat_of_genericKernel h)

end Work.GenericKernelReduction
