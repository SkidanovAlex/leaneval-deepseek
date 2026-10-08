/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# AREA AUTL2 : the centralizer of `PSL(2,q)` on the projective line is trivial

Step A6/transfer of the area `Submission/Work/AUTL2/` uses the fact that the permutation
group `pslImage F ≤ Sym(ℙ¹(F))` has trivial centralizer (`C_{Sym}(L) = 1` is the hypothesis
under which the conjugation map `N(L)/C(L) → Aut(L)` is injective). Here we prove it.

The argument is elementary and uses only the three standard Möbius elements
`transl b : x ↦ x + b`, `dil a : x ↦ a²x` and (implicitly) the fact that a permutation
commuting with the translation group is affine:

* a permutation `σ` commuting with `transl b` for every `b ∈ F` satisfies
  `σ (x + b) = σ x + b`; since `σ` is injective this forces `σ ∞ = ∞` and `σ x ≠ ∞` for
  finite `x`, so `σ` restricted to `F` is `x ↦ x + c` with `c = σ 0`;
* `σ` also commutes with `dil a` (`x ↦ a²x`, `a ∈ Fˣ`), whence `c = a² c`; as soon as some
  unit has `a² ≠ 1` (which holds e.g. if `F` has at least four elements) this gives `c = 0`,
  so `σ` fixes `F` pointwise and, being a bijection, also `∞`.

The main theorem `Work.AUTL2.Aut.centralizer` specialises this to `F = GaloisField p k`,
`p` odd, `p^k ≥ 5`.
-/
import Mathlib
import Submission.Work.DSTR.M110.Defs
import Submission.Work.DSTR.M110.Mobius
import Submission.Work.DSTR.M110.Stabilizer
import Submission.Work.AUTL2.Aut.centralizer

open scoped MatrixGroups LinearAlgebra.Projectivization
open OnePoint

namespace Work.AUTL2.Aut

open Work.AUTL2


end Work.AUTL2.Aut
